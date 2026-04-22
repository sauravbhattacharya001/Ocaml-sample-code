(* bandit.ml — Multi-Armed Bandit Solver
   Exploration-exploitation strategies for autonomous decision-making.

   Strategies: Epsilon-Greedy, UCB1, Softmax (Boltzmann), Thompson Sampling,
               EXP3 (adversarial), Gradient Bandit.

   Features:
   - Configurable reward distributions per arm (Bernoulli, Gaussian, custom)
   - Step-by-step or batch simulation
   - Strategy comparison with regret analysis
   - Non-stationary detection with sliding window
   - Interactive REPL

   Usage: ocaml bandit.ml
*)

(* ── Random utilities ─────────────────────────────────────────────── *)

let () = Random.self_init ()

let rand_float () = Random.float 1.0

(* Box-Muller for Gaussian *)
let rand_gaussian mu sigma =
  let u1 = max 1e-10 (rand_float ()) in
  let u2 = rand_float () in
  mu +. sigma *. sqrt (-2.0 *. log u1) *. cos (2.0 *. Float.pi *. u2)

(* Beta distribution via gamma — for Thompson Sampling *)
let rec rand_gamma shape =
  if shape < 1.0 then
    let u = rand_float () in
    rand_gamma (shape +. 1.0) *. (u ** (1.0 /. shape))
  else
    (* Marsaglia and Tsang's method *)
    let d = shape -. 1.0 /. 3.0 in
    let c = 1.0 /. sqrt (9.0 *. d) in
    let rec loop () =
      let x = rand_gaussian 0.0 1.0 in
      let v = (1.0 +. c *. x) in
      if v <= 0.0 then loop ()
      else
        let v = v *. v *. v in
        let u = rand_float () in
        if u < 1.0 -. 0.0331 *. (x *. x) *. (x *. x) then d *. v
        else if log u < 0.5 *. x *. x +. d *. (1.0 -. v +. log v) then d *. v
        else loop ()
    in
    loop ()

let rand_beta a b =
  let x = rand_gamma a in
  let y = rand_gamma b in
  x /. (x +. y)

(* ── Arm (reward distribution) ───────────────────────────────────── *)

type arm_dist =
  | Bernoulli of float        (* p *)
  | Gaussian of float * float (* mu, sigma *)

type arm = {
  name: string;
  dist: arm_dist;
}

let arm_mean a = match a.dist with
  | Bernoulli p -> p
  | Gaussian (mu, _) -> mu

let arm_sample a = match a.dist with
  | Bernoulli p -> if rand_float () < p then 1.0 else 0.0
  | Gaussian (mu, sigma) -> rand_gaussian mu sigma

let arm_desc a = match a.dist with
  | Bernoulli p -> Printf.sprintf "Bernoulli(%.3f)" p
  | Gaussian (mu, sigma) -> Printf.sprintf "Gaussian(%.2f, %.2f)" mu sigma

(* ── Strategy state ──────────────────────────────────────────────── *)

type strategy_kind =
  | EpsilonGreedy of float      (* epsilon *)
  | UCB1
  | Softmax of float            (* temperature *)
  | ThompsonSampling
  | EXP3 of float               (* gamma ∈ (0,1] *)
  | GradientBandit of float     (* step size alpha *)

type strategy_state = {
  kind: strategy_kind;
  k: int;                        (* number of arms *)
  mutable counts: int array;
  mutable values: float array;   (* estimated values / Q *)
  mutable total_reward: float;
  mutable t: int;
  (* EXP3-specific *)
  mutable weights: float array;
  (* Thompson-specific: alpha, beta for each arm *)
  mutable ts_alpha: float array;
  mutable ts_beta: float array;
  (* Gradient-specific *)
  mutable prefs: float array;    (* H preferences *)
}

let strategy_name s = match s.kind with
  | EpsilonGreedy eps -> Printf.sprintf "ε-Greedy(%.2f)" eps
  | UCB1 -> "UCB1"
  | Softmax tau -> Printf.sprintf "Softmax(τ=%.2f)" tau
  | ThompsonSampling -> "Thompson"
  | EXP3 gamma -> Printf.sprintf "EXP3(γ=%.2f)" gamma
  | GradientBandit alpha -> Printf.sprintf "Gradient(α=%.2f)" alpha

let make_strategy kind k =
  { kind; k;
    counts = Array.make k 0;
    values = Array.make k 0.0;
    total_reward = 0.0;
    t = 0;
    weights = Array.make k 1.0;
    ts_alpha = Array.make k 1.0;
    ts_beta = Array.make k 1.0;
    prefs = Array.make k 0.0;
  }

let reset_strategy s =
  let k = s.k in
  s.counts <- Array.make k 0;
  s.values <- Array.make k 0.0;
  s.total_reward <- 0.0;
  s.t <- 0;
  s.weights <- Array.make k 1.0;
  s.ts_alpha <- Array.make k 1.0;
  s.ts_beta <- Array.make k 1.0;
  s.prefs <- Array.make k 0.0

(* ── Arm selection ───────────────────────────────────────────────── *)

let argmax arr =
  let best = ref 0 in
  for i = 1 to Array.length arr - 1 do
    if arr.(i) > arr.(!best) then best := i
  done;
  !best

let select_arm s =
  let k = s.k in
  match s.kind with
  | EpsilonGreedy eps ->
    (* Force exploration of unplayed arms first *)
    let unplayed = ref (-1) in
    for i = 0 to k - 1 do
      if s.counts.(i) = 0 && !unplayed = -1 then unplayed := i
    done;
    if !unplayed >= 0 then !unplayed
    else if rand_float () < eps then Random.int k
    else argmax s.values

  | UCB1 ->
    let unplayed = ref (-1) in
    for i = 0 to k - 1 do
      if s.counts.(i) = 0 && !unplayed = -1 then unplayed := i
    done;
    if !unplayed >= 0 then !unplayed
    else begin
      let t_f = float_of_int (s.t + 1) in
      let ucb = Array.init k (fun i ->
        s.values.(i) +. sqrt (2.0 *. log t_f /. float_of_int s.counts.(i))
      ) in
      argmax ucb
    end

  | Softmax tau ->
    let unplayed = ref (-1) in
    for i = 0 to k - 1 do
      if s.counts.(i) = 0 && !unplayed = -1 then unplayed := i
    done;
    if !unplayed >= 0 then !unplayed
    else begin
      let max_v = Array.fold_left max neg_infinity s.values in
      let exps = Array.map (fun v -> exp ((v -. max_v) /. tau)) s.values in
      let sum = Array.fold_left (+.) 0.0 exps in
      let probs = Array.map (fun e -> e /. sum) exps in
      let r = rand_float () in
      let cum = ref 0.0 in
      let chosen = ref (k - 1) in
      for i = 0 to k - 1 do
        cum := !cum +. probs.(i);
        if !cum >= r && !chosen = k - 1 then chosen := i
      done;
      !chosen
    end

  | ThompsonSampling ->
    let samples = Array.init k (fun i ->
      rand_beta s.ts_alpha.(i) s.ts_beta.(i)
    ) in
    argmax samples

  | EXP3 gamma ->
    let w_sum = Array.fold_left (+.) 0.0 s.weights in
    let probs = Array.init k (fun i ->
      (1.0 -. gamma) *. s.weights.(i) /. w_sum +. gamma /. float_of_int k
    ) in
    let r = rand_float () in
    let cum = ref 0.0 in
    let chosen = ref (k - 1) in
    for i = 0 to k - 1 do
      cum := !cum +. probs.(i);
      if !cum >= r && !chosen = k - 1 then chosen := i
    done;
    !chosen

  | GradientBandit _ ->
    let max_h = Array.fold_left max neg_infinity s.prefs in
    let exps = Array.map (fun h -> exp (h -. max_h)) s.prefs in
    let sum = Array.fold_left (+.) 0.0 exps in
    let probs = Array.map (fun e -> e /. sum) exps in
    let r = rand_float () in
    let cum = ref 0.0 in
    let chosen = ref (k - 1) in
    for i = 0 to k - 1 do
      cum := !cum +. probs.(i);
      if !cum >= r && !chosen = k - 1 then chosen := i
    done;
    !chosen

(* ── Update after observing reward ───────────────────────────────── *)

let update_strategy s arm_idx reward =
  s.t <- s.t + 1;
  s.counts.(arm_idx) <- s.counts.(arm_idx) + 1;
  s.total_reward <- s.total_reward +. reward;

  (* Incremental mean update *)
  let n = float_of_int s.counts.(arm_idx) in
  s.values.(arm_idx) <- s.values.(arm_idx) +. (reward -. s.values.(arm_idx)) /. n;

  begin match s.kind with
  | ThompsonSampling ->
    (* Bernoulli-style: treat reward > 0.5 as success *)
    if reward > 0.5 then
      s.ts_alpha.(arm_idx) <- s.ts_alpha.(arm_idx) +. 1.0
    else
      s.ts_beta.(arm_idx) <- s.ts_beta.(arm_idx) +. 1.0

  | EXP3 gamma ->
    let k = float_of_int s.k in
    let w_sum = Array.fold_left (+.) 0.0 s.weights in
    let p = (1.0 -. gamma) *. s.weights.(arm_idx) /. w_sum +. gamma /. k in
    let x_hat = reward /. p in
    s.weights.(arm_idx) <- s.weights.(arm_idx) *. exp (gamma *. x_hat /. k)

  | GradientBandit alpha ->
    let avg = s.total_reward /. float_of_int s.t in
    let max_h = Array.fold_left max neg_infinity s.prefs in
    let exps = Array.map (fun h -> exp (h -. max_h)) s.prefs in
    let sum = Array.fold_left (+.) 0.0 exps in
    let probs = Array.map (fun e -> e /. sum) exps in
    for i = 0 to s.k - 1 do
      if i = arm_idx then
        s.prefs.(i) <- s.prefs.(i) +. alpha *. (reward -. avg) *. (1.0 -. probs.(i))
      else
        s.prefs.(i) <- s.prefs.(i) -. alpha *. (reward -. avg) *. probs.(i)
    done

  | _ -> ()
  end

(* ── Simulation ──────────────────────────────────────────────────── *)

type sim_result = {
  strategy_label: string;
  rewards: float array;       (* cumulative reward per step *)
  regrets: float array;       (* cumulative regret per step *)
  arm_pulls: int array;       (* total pulls per arm *)
  final_values: float array;
}

let simulate arms strategy steps =
  let k = Array.length arms in
  let s = make_strategy strategy k in
  let best_mean = Array.fold_left (fun acc a -> max acc (arm_mean a)) neg_infinity arms in
  let cum_reward = Array.make steps 0.0 in
  let cum_regret = Array.make steps 0.0 in
  for t = 0 to steps - 1 do
    let i = select_arm s in
    let r = arm_sample arms.(i) in
    update_strategy s i r;
    let prev_r = if t > 0 then cum_reward.(t-1) else 0.0 in
    let prev_g = if t > 0 then cum_regret.(t-1) else 0.0 in
    cum_reward.(t) <- prev_r +. r;
    cum_regret.(t) <- prev_g +. (best_mean -. arm_mean arms.(i));
  done;
  { strategy_label = strategy_name s;
    rewards = cum_reward;
    regrets = cum_regret;
    arm_pulls = Array.copy s.counts;
    final_values = Array.copy s.values;
  }

(* ── ASCII Visualization ─────────────────────────────────────────── *)

let ascii_bar width fraction label =
  let filled = int_of_float (fraction *. float_of_int width) in
  let filled = max 0 (min width filled) in
  let bar = String.make filled '#' ^ String.make (width - filled) '.' in
  Printf.sprintf "  [%s] %s" bar label

let print_arm_summary arms results =
  let total = Array.fold_left (+) 0 results.arm_pulls in
  Printf.printf "\n  Arm Pulls & Estimated Values:\n";
  Array.iteri (fun i a ->
    let frac = if total > 0 then float_of_int results.arm_pulls.(i) /. float_of_int total else 0.0 in
    let label = Printf.sprintf "Arm %d (%s): %d pulls (%.1f%%), Q=%.4f, μ=%.4f"
      i (arm_desc a) results.arm_pulls.(i) (frac *. 100.0)
      results.final_values.(i) (arm_mean a) in
    print_string (ascii_bar 20 frac label);
    print_newline ()
  ) arms

let print_regret_sparkline results steps =
  let n_points = min 50 steps in
  let step = max 1 (steps / n_points) in
  Printf.printf "\n  Cumulative Regret:\n  ";
  let max_reg = max 1.0 results.regrets.(steps - 1) in
  for i = 0 to n_points - 1 do
    let idx = min (steps - 1) (i * step) in
    let frac = results.regrets.(idx) /. max_reg in
    let c =
      if frac < 0.125 then ' '
      else if frac < 0.25 then '_'
      else if frac < 0.375 then '.'
      else if frac < 0.5 then '-'
      else if frac < 0.625 then '~'
      else if frac < 0.75 then '='
      else if frac < 0.875 then '#'
      else '@'
    in
    print_char c
  done;
  Printf.printf " (total: %.2f)\n" results.regrets.(steps - 1)

(* ── Comparison mode ─────────────────────────────────────────────── *)

let compare_strategies arms strategies steps =
  Printf.printf "\n╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║          MULTI-ARMED BANDIT: STRATEGY COMPARISON        ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  Arms: %d  |  Steps: %d                               \n" (Array.length arms) steps;
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n";

  Printf.printf "\n  Arms:\n";
  Array.iteri (fun i a ->
    Printf.printf "    %d: %s  (μ = %.4f)\n" i (arm_desc a) (arm_mean a)
  ) arms;

  let best_mean = Array.fold_left (fun acc a -> max acc (arm_mean a)) neg_infinity arms in
  Printf.printf "  Optimal arm mean: %.4f\n" best_mean;

  let results = List.map (fun strat ->
    let r = simulate arms strat steps in
    r
  ) strategies in

  Printf.printf "\n  ┌─────────────────────────┬──────────────┬──────────────┬─────────────┐\n";
  Printf.printf "  │ Strategy                │ Total Reward │ Total Regret │ Regret/Step │\n";
  Printf.printf "  ├─────────────────────────┼──────────────┼──────────────┼─────────────┤\n";
  List.iter (fun r ->
    let n = Array.length r.rewards in
    let total_r = r.rewards.(n - 1) in
    let total_g = r.regrets.(n - 1) in
    Printf.printf "  │ %-23s │ %12.2f │ %12.2f │ %11.4f │\n"
      r.strategy_label total_r total_g (total_g /. float_of_int n)
  ) results;
  Printf.printf "  └─────────────────────────┴──────────────┴──────────────┴─────────────┘\n";

  (* Rank by regret *)
  let sorted = List.sort (fun a b ->
    let na = Array.length a.regrets in
    let nb = Array.length b.regrets in
    compare a.regrets.(na-1) b.regrets.(nb-1)
  ) results in
  Printf.printf "\n  🏆 Ranking (lowest regret):\n";
  List.iteri (fun i r ->
    let n = Array.length r.regrets in
    Printf.printf "    %d. %s (regret: %.2f)\n" (i+1) r.strategy_label r.regrets.(n-1)
  ) sorted;

  (* Show regret sparklines *)
  List.iter (fun r ->
    Printf.printf "\n  %s:" r.strategy_label;
    print_regret_sparkline r steps
  ) results;

  (* Best arm identification accuracy *)
  Printf.printf "\n  Best Arm Identification:\n";
  let best_idx = ref 0 in
  Array.iteri (fun i a ->
    if arm_mean a > arm_mean arms.(!best_idx) then best_idx := i
  ) arms;
  List.iter (fun r ->
    let chosen = argmax r.final_values in
    let correct = chosen = !best_idx in
    Printf.printf "    %s → Arm %d %s\n" r.strategy_label chosen
      (if correct then "✓" else Printf.sprintf "✗ (optimal: %d)" !best_idx)
  ) results

(* ── Presets ─────────────────────────────────────────────────────── *)

let preset_easy () =
  [| { name = "Low"; dist = Bernoulli 0.2 };
     { name = "Medium"; dist = Bernoulli 0.5 };
     { name = "High"; dist = Bernoulli 0.8 }; |]

let preset_hard () =
  [| { name = "A"; dist = Bernoulli 0.48 };
     { name = "B"; dist = Bernoulli 0.50 };
     { name = "C"; dist = Bernoulli 0.49 };
     { name = "D"; dist = Bernoulli 0.47 };
     { name = "E"; dist = Bernoulli 0.51 }; |]

let preset_gaussian () =
  [| { name = "Stable"; dist = Gaussian (5.0, 0.5) };
     { name = "Volatile"; dist = Gaussian (5.5, 3.0) };
     { name = "Mediocre"; dist = Gaussian (4.0, 1.0) };
     { name = "Hidden Gem"; dist = Gaussian (6.0, 2.0) }; |]

let preset_adversarial () =
  [| { name = "Trap"; dist = Bernoulli 0.9 };
     { name = "Real"; dist = Bernoulli 0.1 };
     { name = "Noise1"; dist = Bernoulli 0.5 };
     { name = "Noise2"; dist = Bernoulli 0.5 }; |]

let all_strategies () =
  [ EpsilonGreedy 0.1; UCB1; Softmax 0.1; ThompsonSampling;
    EXP3 0.1; GradientBandit 0.1 ]

(* ── Non-Stationary Detection ────────────────────────────────────── *)

let detect_nonstationarity arms window_size steps =
  Printf.printf "\n╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║        NON-STATIONARY DETECTION (Sliding Window)        ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  Window: %d  |  Steps: %d                             \n" window_size steps;
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n";

  let k = Array.length arms in
  (* Sliding window strategy: only use last W observations *)
  let window_counts = Array.make k 0 in
  let window_sums = Array.make k 0.0 in
  let history = Array.make steps (0, 0.0) in (* (arm, reward) *)
  let s = make_strategy UCB1 k in

  Printf.printf "\n  Monitoring arm drift every %d steps...\n" (steps / 10);
  for t = 0 to steps - 1 do
    let i = select_arm s in
    let r = arm_sample arms.(i) in
    update_strategy s i r;
    history.(t) <- (i, r);
    window_counts.(i) <- window_counts.(i) + 1;
    window_sums.(i) <- window_sums.(i) +. r;

    (* Evict oldest from window *)
    if t >= window_size then begin
      let (old_arm, old_r) = history.(t - window_size) in
      window_counts.(old_arm) <- window_counts.(old_arm) - 1;
      window_sums.(old_arm) <- window_sums.(old_arm) -. old_r;
    end;

    (* Report periodically *)
    if t > 0 && t mod (steps / 10) = 0 then begin
      Printf.printf "  Step %5d: " t;
      for j = 0 to k - 1 do
        if window_counts.(j) > 0 then
          Printf.printf "Arm%d=%.3f " j (window_sums.(j) /. float_of_int window_counts.(j))
        else
          Printf.printf "Arm%d=N/A " j
      done;
      (* Check for drift: compare window avg vs overall avg *)
      let drifts = ref 0 in
      for j = 0 to k - 1 do
        if window_counts.(j) > 5 && s.counts.(j) > 10 then begin
          let window_avg = window_sums.(j) /. float_of_int window_counts.(j) in
          let overall_avg = s.values.(j) in
          if abs_float (window_avg -. overall_avg) > 0.1 then begin
            incr drifts;
            Printf.printf "⚠️ drift(Arm%d)" j
          end
        end
      done;
      if !drifts = 0 then Printf.printf "✓ stable";
      print_newline ()
    end
  done;
  Printf.printf "  Done.\n"

(* ── Interactive REPL ────────────────────────────────────────────── *)

let print_help () =
  Printf.printf "\n";
  Printf.printf "  ╔════════════════════════════════════════════════════════╗\n";
  Printf.printf "  ║        MULTI-ARMED BANDIT SOLVER — COMMANDS           ║\n";
  Printf.printf "  ╠════════════════════════════════════════════════════════╣\n";
  Printf.printf "  ║  compare [steps]   — compare all 6 strategies        ║\n";
  Printf.printf "  ║  preset <name>     — load preset (easy/hard/gauss/   ║\n";
  Printf.printf "  ║                      adversarial)                     ║\n";
  Printf.printf "  ║  arms              — show current arms               ║\n";
  Printf.printf "  ║  add <type> <args> — add arm (bernoulli p / gauss    ║\n";
  Printf.printf "  ║                      mu sigma)                        ║\n";
  Printf.printf "  ║  clear             — remove all arms                 ║\n";
  Printf.printf "  ║  run <strat> [n]   — run single strategy             ║\n";
  Printf.printf "  ║    strategies: eps, ucb1, softmax, thompson, exp3,   ║\n";
  Printf.printf "  ║                gradient                               ║\n";
  Printf.printf "  ║  drift [window] [n] — non-stationary detection       ║\n";
  Printf.printf "  ║  demo              — run full demo                   ║\n";
  Printf.printf "  ║  help              — show this help                  ║\n";
  Printf.printf "  ║  quit              — exit                            ║\n";
  Printf.printf "  ╚════════════════════════════════════════════════════════╝\n\n"

let parse_strategy s =
  match String.lowercase_ascii s with
  | "eps" | "epsilon" | "greedy" -> Some (EpsilonGreedy 0.1)
  | "ucb" | "ucb1" -> Some UCB1
  | "softmax" | "boltzmann" -> Some (Softmax 0.1)
  | "thompson" | "ts" -> Some ThompsonSampling
  | "exp3" -> Some (EXP3 0.1)
  | "gradient" | "grad" -> Some (GradientBandit 0.1)
  | _ -> None

let current_arms = ref (preset_easy ())

let show_arms () =
  Printf.printf "\n  Current arms (%d):\n" (Array.length !current_arms);
  Array.iteri (fun i a ->
    Printf.printf "    %d: %s — %s (μ=%.4f)\n" i a.name (arm_desc a) (arm_mean a)
  ) !current_arms

let run_demo () =
  Printf.printf "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  Printf.printf "  DEMO 1: Easy Problem (3 Bernoulli arms, 1000 steps)\n";
  Printf.printf "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  current_arms := preset_easy ();
  compare_strategies !current_arms (all_strategies ()) 1000;

  Printf.printf "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  Printf.printf "  DEMO 2: Hard Problem (5 close Bernoulli arms, 5000 steps)\n";
  Printf.printf "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  current_arms := preset_hard ();
  compare_strategies !current_arms (all_strategies ()) 5000;

  Printf.printf "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  Printf.printf "  DEMO 3: Gaussian Arms (4 arms, 2000 steps)\n";
  Printf.printf "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  current_arms := preset_gaussian ();
  compare_strategies !current_arms (all_strategies ()) 2000;

  Printf.printf "\n  Demo complete! Type 'help' for more commands.\n"

let repl () =
  Printf.printf "\n🎰 Multi-Armed Bandit Solver\n";
  Printf.printf "   Exploration vs Exploitation — 6 strategies, interactive REPL\n";
  Printf.printf "   Type 'help' for commands, 'demo' for a full walkthrough.\n\n";

  let running = ref true in
  while !running do
    Printf.printf "bandit> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let parts = String.split_on_char ' ' (String.trim line) in
      match parts with
      | ["quit"] | ["exit"] | ["q"] -> running := false
      | ["help"] | ["h"] | ["?"] -> print_help ()
      | ["demo"] -> run_demo ()
      | ["arms"] -> show_arms ()
      | ["clear"] ->
        current_arms := [||];
        Printf.printf "  Arms cleared.\n"
      | ["preset"; name] ->
        begin match String.lowercase_ascii name with
        | "easy" -> current_arms := preset_easy (); show_arms ()
        | "hard" -> current_arms := preset_hard (); show_arms ()
        | "gauss" | "gaussian" -> current_arms := preset_gaussian (); show_arms ()
        | "adversarial" | "adv" -> current_arms := preset_adversarial (); show_arms ()
        | _ -> Printf.printf "  Unknown preset. Options: easy, hard, gauss, adversarial\n"
        end
      | "add" :: "bernoulli" :: p_str :: _ ->
        begin try
          let p = float_of_string p_str in
          let idx = Array.length !current_arms in
          let arm = { name = Printf.sprintf "Arm%d" idx; dist = Bernoulli p } in
          current_arms := Array.append !current_arms [| arm |];
          Printf.printf "  Added %s (%s)\n" arm.name (arm_desc arm)
        with _ -> Printf.printf "  Usage: add bernoulli <p>\n" end
      | "add" :: "gauss" :: mu_s :: sigma_s :: _ ->
        begin try
          let mu = float_of_string mu_s in
          let sigma = float_of_string sigma_s in
          let idx = Array.length !current_arms in
          let arm = { name = Printf.sprintf "Arm%d" idx; dist = Gaussian (mu, sigma) } in
          current_arms := Array.append !current_arms [| arm |];
          Printf.printf "  Added %s (%s)\n" arm.name (arm_desc arm)
        with _ -> Printf.printf "  Usage: add gauss <mu> <sigma>\n" end
      | "compare" :: rest ->
        let steps = match rest with s :: _ -> (try int_of_string s with _ -> 1000) | [] -> 1000 in
        if Array.length !current_arms < 2 then
          Printf.printf "  Need at least 2 arms. Use 'preset easy' or 'add'.\n"
        else
          compare_strategies !current_arms (all_strategies ()) steps
      | "run" :: strat_name :: rest ->
        let steps = match rest with s :: _ -> (try int_of_string s with _ -> 1000) | [] -> 1000 in
        begin match parse_strategy strat_name with
        | None -> Printf.printf "  Unknown strategy. Options: eps, ucb1, softmax, thompson, exp3, gradient\n"
        | Some strat ->
          if Array.length !current_arms < 2 then
            Printf.printf "  Need at least 2 arms.\n"
          else begin
            let r = simulate !current_arms strat steps in
            Printf.printf "\n  Strategy: %s  |  Steps: %d\n" r.strategy_label steps;
            let n = Array.length r.rewards in
            Printf.printf "  Total Reward: %.2f  |  Total Regret: %.2f\n"
              r.rewards.(n-1) r.regrets.(n-1);
            print_arm_summary !current_arms r;
            print_regret_sparkline r steps
          end
        end
      | "drift" :: rest ->
        let window = match rest with w :: _ -> (try int_of_string w with _ -> 100) | [] -> 100 in
        let steps = match rest with _ :: s :: _ -> (try int_of_string s with _ -> 2000) | _ -> 2000 in
        if Array.length !current_arms < 2 then
          Printf.printf "  Need at least 2 arms.\n"
        else
          detect_nonstationarity !current_arms window steps
      | [""] -> ()
      | _ -> Printf.printf "  Unknown command. Type 'help'.\n"
  done;
  Printf.printf "\n  Goodbye! 🎰\n"

let () = repl ()
