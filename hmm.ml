(* Hidden Markov Model - Viterbi, Forward-Backward, Baum-Welch, Interactive REPL
 *
 * Implements a complete HMM toolkit:
 * - Forward algorithm (observation likelihood)
 * - Viterbi algorithm (most likely state sequence)
 * - Forward-Backward algorithm (posterior state probabilities)
 * - Baum-Welch algorithm (parameter estimation / EM learning)
 * - Sequence generation (sampling from the model)
 * - Model anomaly detection (log-likelihood scoring)
 * - Interactive REPL with 3 classic example domains
 *
 * Usage: ocamlfind ocamlopt -package unix -linkpkg hmm.ml -o hmm && ./hmm
 *        or: ocaml hmm.ml
 *)

(* ── Core types ────────────────────────────────────────────────── *)

type hmm = {
  n_states : int;
  n_obs : int;
  state_names : string array;
  obs_names : string array;
  initial : float array;        (* pi[i] *)
  transition : float array array;  (* a[i][j] *)
  emission : float array array;    (* b[i][k] *)
}

(* ── Utility ───────────────────────────────────────────────────── *)

let log_sum_exp a b =
  if a = neg_infinity then b
  else if b = neg_infinity then a
  else
    let mx = max a b in
    mx +. log (exp (a -. mx) +. exp (b -. mx))

let safe_log x = if x <= 0.0 then neg_infinity else log x

let normalize arr =
  let s = Array.fold_left (+.) 0.0 arr in
  if s > 0.0 then Array.map (fun x -> x /. s) arr
  else arr

(* ── Forward algorithm ─────────────────────────────────────────── *)

let forward model obs =
  let t_len = Array.length obs in
  let n = model.n_states in
  let alpha = Array.init t_len (fun _ -> Array.make n neg_infinity) in
  for i = 0 to n - 1 do
    alpha.(0).(i) <- safe_log model.initial.(i) +. safe_log model.emission.(i).(obs.(0))
  done;
  for t = 1 to t_len - 1 do
    for j = 0 to n - 1 do
      let s = ref neg_infinity in
      for i = 0 to n - 1 do
        s := log_sum_exp !s (alpha.(t-1).(i) +. safe_log model.transition.(i).(j))
      done;
      alpha.(t).(j) <- !s +. safe_log model.emission.(j).(obs.(t))
    done
  done;
  alpha

let log_likelihood model obs =
  let alpha = forward model obs in
  let t = Array.length obs - 1 in
  let ll = ref neg_infinity in
  for i = 0 to model.n_states - 1 do
    ll := log_sum_exp !ll alpha.(t).(i)
  done;
  !ll

(* ── Viterbi algorithm ─────────────────────────────────────────── *)

let viterbi model obs =
  let t_len = Array.length obs in
  let n = model.n_states in
  let delta = Array.init t_len (fun _ -> Array.make n neg_infinity) in
  let psi = Array.init t_len (fun _ -> Array.make n 0) in
  for i = 0 to n - 1 do
    delta.(0).(i) <- safe_log model.initial.(i) +. safe_log model.emission.(i).(obs.(0))
  done;
  for t = 1 to t_len - 1 do
    for j = 0 to n - 1 do
      let best_val = ref neg_infinity in
      let best_i = ref 0 in
      for i = 0 to n - 1 do
        let v = delta.(t-1).(i) +. safe_log model.transition.(i).(j) in
        if v > !best_val then begin best_val := v; best_i := i end
      done;
      delta.(t).(j) <- !best_val +. safe_log model.emission.(j).(obs.(t));
      psi.(t).(j) <- !best_i
    done
  done;
  let path = Array.make t_len 0 in
  let best = ref neg_infinity in
  for i = 0 to n - 1 do
    if delta.(t_len-1).(i) > !best then begin best := delta.(t_len-1).(i); path.(t_len-1) <- i end
  done;
  for t = t_len - 2 downto 0 do
    path.(t) <- psi.(t+1).(path.(t+1))
  done;
  (path, !best)

(* ── Backward algorithm ────────────────────────────────────────── *)

let backward model obs =
  let t_len = Array.length obs in
  let n = model.n_states in
  let beta = Array.init t_len (fun _ -> Array.make n neg_infinity) in
  for i = 0 to n - 1 do
    beta.(t_len-1).(i) <- 0.0
  done;
  for t = t_len - 2 downto 0 do
    for i = 0 to n - 1 do
      let s = ref neg_infinity in
      for j = 0 to n - 1 do
        s := log_sum_exp !s
          (safe_log model.transition.(i).(j) +.
           safe_log model.emission.(j).(obs.(t+1)) +.
           beta.(t+1).(j))
      done;
      beta.(t).(i) <- !s
    done
  done;
  beta

(* ── Forward-Backward (posterior) ──────────────────────────────── *)

let forward_backward model obs =
  let alpha = forward model obs in
  let beta = backward model obs in
  let t_len = Array.length obs in
  let n = model.n_states in
  let gamma = Array.init t_len (fun t ->
    let g = Array.init n (fun i -> alpha.(t).(i) +. beta.(t).(i)) in
    let mx = Array.fold_left max neg_infinity g in
    let s = Array.fold_left (fun acc v -> acc +. exp (v -. mx)) 0.0 g in
    let log_s = mx +. log s in
    Array.map (fun v -> exp (v -. log_s)) g
  ) in
  gamma

(* ── Baum-Welch (EM learning) ──────────────────────────────────── *)

let baum_welch model observations max_iter tolerance =
  let n = model.n_states in
  let m = model.n_obs in
  let pi = Array.copy model.initial in
  let a = Array.init n (fun i -> Array.copy model.transition.(i)) in
  let b = Array.init n (fun i -> Array.copy model.emission.(i)) in
  let cur = { model with initial = pi; transition = a; emission = b } in
  let prev_ll = ref neg_infinity in
  let iter_count = ref 0 in
  let converged = ref false in
  while !iter_count < max_iter && not !converged do
    incr iter_count;
    let pi_acc = Array.make n 0.0 in
    let a_num = Array.init n (fun _ -> Array.make n 0.0) in
    let a_den = Array.make n 0.0 in
    let b_num = Array.init n (fun _ -> Array.make m 0.0) in
    let b_den = Array.make n 0.0 in
    let total_ll = ref 0.0 in
    List.iter (fun obs ->
      let t_len = Array.length obs in
      if t_len > 0 then begin
        let alpha = forward cur obs in
        let beta = backward cur obs in
        let ll = ref neg_infinity in
        for i = 0 to n - 1 do ll := log_sum_exp !ll alpha.(t_len-1).(i) done;
        total_ll := !total_ll +. !ll;
        let gamma = Array.init t_len (fun t ->
          Array.init n (fun i -> exp (alpha.(t).(i) +. beta.(t).(i) -. !ll))
        ) in
        for t = 0 to t_len - 2 do
          for i = 0 to n - 1 do
            for j = 0 to n - 1 do
              let xi_ij = exp (alpha.(t).(i) +. safe_log cur.transition.(i).(j) +.
                               safe_log cur.emission.(j).(obs.(t+1)) +.
                               beta.(t+1).(j) -. !ll) in
              a_num.(i).(j) <- a_num.(i).(j) +. xi_ij
            done;
            a_den.(i) <- a_den.(i) +. gamma.(t).(i)
          done
        done;
        for i = 0 to n - 1 do
          pi_acc.(i) <- pi_acc.(i) +. gamma.(0).(i);
          for t = 0 to t_len - 1 do
            b_num.(i).(obs.(t)) <- b_num.(i).(obs.(t)) +. gamma.(t).(i);
            b_den.(i) <- b_den.(i) +. gamma.(t).(i)
          done
        done
      end
    ) observations;
    let n_seq = float_of_int (List.length observations) in
    let new_pi = Array.init n (fun i -> pi_acc.(i) /. n_seq) in
    let sp = Array.fold_left (+.) 0.0 new_pi in
    Array.iteri (fun i _ -> cur.initial.(i) <- new_pi.(i) /. sp) new_pi;
    for i = 0 to n - 1 do
      if a_den.(i) > 0.0 then
        for j = 0 to n - 1 do cur.transition.(i).(j) <- a_num.(i).(j) /. a_den.(i) done;
      if b_den.(i) > 0.0 then
        for k = 0 to m - 1 do cur.emission.(i).(k) <- b_num.(i).(k) /. b_den.(i) done
    done;
    if abs_float (!total_ll -. !prev_ll) < tolerance then converged := true;
    prev_ll := !total_ll
  done;
  (cur, !iter_count, !prev_ll)

(* ── Sequence generation ───────────────────────────────────────── *)

let sample_discrete probs =
  let r = Random.float 1.0 in
  let acc = ref 0.0 in
  let result = ref (Array.length probs - 1) in
  let found = ref false in
  Array.iteri (fun i p ->
    if not !found then begin
      acc := !acc +. p;
      if r < !acc then begin result := i; found := true end
    end
  ) probs;
  !result

let generate model length =
  let states = Array.make length 0 in
  let obs = Array.make length 0 in
  states.(0) <- sample_discrete model.initial;
  obs.(0) <- sample_discrete model.emission.(states.(0));
  for t = 1 to length - 1 do
    states.(t) <- sample_discrete model.transition.(states.(t-1));
    obs.(t) <- sample_discrete model.emission.(states.(t))
  done;
  (states, obs)

(* ── Anomaly detection ─────────────────────────────────────────── *)

let anomaly_score model obs =
  let ll = log_likelihood model obs in
  let avg = ll /. float_of_int (Array.length obs) in
  (ll, avg)

(* ── Example models ────────────────────────────────────────────── *)

let weather_model () = {
  n_states = 2; n_obs = 3;
  state_names = [| "Sunny"; "Rainy" |];
  obs_names = [| "Walk"; "Shop"; "Clean" |];
  initial = [| 0.6; 0.4 |];
  transition = [| [| 0.7; 0.3 |]; [| 0.4; 0.6 |] |];
  emission = [| [| 0.6; 0.3; 0.1 |]; [| 0.1; 0.4; 0.5 |] |];
}

let health_model () = {
  n_states = 3; n_obs = 4;
  state_names = [| "Healthy"; "Mild"; "Severe" |];
  obs_names = [| "Normal"; "Cold"; "Dizzy"; "Fever" |];
  initial = [| 0.7; 0.2; 0.1 |];
  transition = [|
    [| 0.7; 0.2; 0.1 |]; [| 0.3; 0.5; 0.2 |]; [| 0.1; 0.3; 0.6 |];
  |];
  emission = [|
    [| 0.7; 0.2; 0.05; 0.05 |]; [| 0.1; 0.5; 0.2; 0.2 |]; [| 0.05; 0.1; 0.35; 0.5 |];
  |];
}

let stock_model () = {
  n_states = 3; n_obs = 3;
  state_names = [| "Bull"; "Bear"; "Flat" |];
  obs_names = [| "Up"; "Down"; "Steady" |];
  initial = [| 0.4; 0.3; 0.3 |];
  transition = [|
    [| 0.6; 0.2; 0.2 |]; [| 0.2; 0.6; 0.2 |]; [| 0.3; 0.3; 0.4 |];
  |];
  emission = [|
    [| 0.7; 0.1; 0.2 |]; [| 0.1; 0.7; 0.2 |]; [| 0.2; 0.2; 0.6 |];
  |];
}

(* ── Display helpers ───────────────────────────────────────────── *)

let print_model model =
  Printf.printf "\n┌─ HMM Model ─────────────────────────────────────────┐\n";
  Printf.printf "│ States: %s\n" (String.concat ", " (Array.to_list model.state_names));
  Printf.printf "│ Observations: %s\n" (String.concat ", " (Array.to_list model.obs_names));
  Printf.printf "│\n│ Initial probabilities:\n";
  Array.iteri (fun i p -> Printf.printf "│   %s: %.3f\n" model.state_names.(i) p) model.initial;
  Printf.printf "│\n│ Transition matrix:\n│   %s\n"
    (String.concat "  " (Array.to_list (Array.map (Printf.sprintf "%-8s") model.state_names)));
  Array.iteri (fun i row ->
    Printf.printf "│   ";
    Array.iter (fun p -> Printf.printf "%-8.3f" p) row;
    Printf.printf "  <- %s\n" model.state_names.(i)
  ) model.transition;
  Printf.printf "│\n│ Emission matrix:\n│   %s\n"
    (String.concat "  " (Array.to_list (Array.map (Printf.sprintf "%-8s") model.obs_names)));
  Array.iteri (fun i row ->
    Printf.printf "│   ";
    Array.iter (fun p -> Printf.printf "%-8.3f" p) row;
    Printf.printf "  <- %s\n" model.state_names.(i)
  ) model.emission;
  Printf.printf "└──────────────────────────────────────────────────────┘\n"

let print_sequence model states obs =
  Printf.printf "  Time  Observation    Hidden State\n";
  Printf.printf "  ----  -----------    ------------\n";
  Array.iteri (fun t o ->
    Printf.printf "  %3d   %-14s %s\n" (t+1) model.obs_names.(o) model.state_names.(states.(t))
  ) obs

let print_viterbi model obs =
  let (path, log_prob) = viterbi model obs in
  Printf.printf "\n-- Viterbi Decoding --\n";
  Printf.printf "  Observations: %s\n"
    (String.concat " -> " (Array.to_list (Array.map (fun o -> model.obs_names.(o)) obs)));
  Printf.printf "  Best path:    %s\n"
    (String.concat " -> " (Array.to_list (Array.map (fun s -> model.state_names.(s)) path)));
  Printf.printf "  Log-prob:     %.4f\n" log_prob

let print_posterior model obs =
  let gamma = forward_backward model obs in
  Printf.printf "\n-- Posterior Probabilities --\n";
  Printf.printf "  Time  Obs          ";
  Array.iter (fun s -> Printf.printf "%-10s" s) model.state_names;
  Printf.printf "\n  ----  -----------  ";
  Array.iter (fun _ -> Printf.printf "----------") model.state_names;
  Printf.printf "\n";
  Array.iteri (fun t g ->
    Printf.printf "  %3d   %-12s " (t+1) model.obs_names.(obs.(t));
    Array.iter (fun p -> Printf.printf "%-10.4f" p) g;
    Printf.printf "\n"
  ) gamma

let parse_obs model s =
  let tokens = String.split_on_char ' ' (String.trim s) in
  let tokens = List.filter (fun t -> t <> "") tokens in
  try
    Some (Array.of_list (List.map (fun tok ->
      let lower = String.lowercase_ascii tok in
      let found = ref (-1) in
      Array.iteri (fun i name ->
        if String.lowercase_ascii name = lower then found := i
      ) model.obs_names;
      if !found >= 0 then !found
      else int_of_string tok
    ) tokens))
  with _ -> None

(* ── REPL ──────────────────────────────────────────────────────── *)

let () =
  Random.self_init ();
  let model = ref (weather_model ()) in
  Printf.printf "==========================================================\n";
  Printf.printf "        Hidden Markov Model -- Interactive Toolkit         \n";
  Printf.printf "==========================================================\n";
  Printf.printf "  Algorithms: Forward, Viterbi, Forward-Backward,\n";
  Printf.printf "              Baum-Welch (EM), Generation, Anomaly\n";
  Printf.printf "==========================================================\n\n";
  Printf.printf "Commands:\n";
  Printf.printf "  model              Show current model parameters\n";
  Printf.printf "  use <name>         Switch model (weather|health|stock)\n";
  Printf.printf "  viterbi <obs...>   Find most likely state sequence\n";
  Printf.printf "  posterior <obs..>  Show posterior state probabilities\n";
  Printf.printf "  likelihood <obs.>  Compute observation log-likelihood\n";
  Printf.printf "  generate <len>     Sample a sequence from the model\n";
  Printf.printf "  anomaly <obs...>   Score sequence for anomaly detection\n";
  Printf.printf "  learn <n_iter>     Run Baum-Welch on random sequences\n";
  Printf.printf "  demo               Run a full demonstration\n";
  Printf.printf "  help               Show this help\n";
  Printf.printf "  quit               Exit\n\n";
  Printf.printf "Observations use names (e.g., walk shop clean) or indices.\n";
  Printf.printf "Active model: Weather (Sunny/Rainy -> Walk/Shop/Clean)\n\n";
  let running = ref true in
  while !running do
    Printf.printf "hmm> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let parts = String.split_on_char ' ' (String.trim line) in
      let parts = List.filter (fun s -> s <> "") parts in
      match parts with
      | [] -> ()
      | cmd :: args ->
        let cmd = String.lowercase_ascii cmd in
        match cmd with
        | "quit" | "exit" | "q" -> running := false
        | "help" | "h" | "?" ->
          Printf.printf "Commands: model, use, viterbi, posterior, likelihood, generate, anomaly, learn, demo, quit\n"
        | "model" | "m" -> print_model !model
        | "use" ->
          (match args with
           | [name] ->
             let name = String.lowercase_ascii name in
             (match name with
              | "weather" -> model := weather_model (); Printf.printf "Switched to Weather model.\n"
              | "health" -> model := health_model (); Printf.printf "Switched to Health model.\n"
              | "stock" | "stocks" -> model := stock_model (); Printf.printf "Switched to Stock model.\n"
              | _ -> Printf.printf "Unknown model: %s. Try: weather, health, stock\n" name)
           | _ -> Printf.printf "Usage: use <weather|health|stock>\n")
        | "viterbi" | "v" ->
          let obs_str = String.concat " " args in
          (match parse_obs !model obs_str with
           | Some obs when Array.length obs > 0 -> print_viterbi !model obs
           | _ -> Printf.printf "Usage: viterbi <obs1> <obs2> ... (use names or indices)\n")
        | "posterior" | "p" ->
          let obs_str = String.concat " " args in
          (match parse_obs !model obs_str with
           | Some obs when Array.length obs > 0 -> print_posterior !model obs
           | _ -> Printf.printf "Usage: posterior <obs1> <obs2> ...\n")
        | "likelihood" | "l" ->
          let obs_str = String.concat " " args in
          (match parse_obs !model obs_str with
           | Some obs when Array.length obs > 0 ->
             let ll = log_likelihood !model obs in
             Printf.printf "Log-likelihood: %.4f (probability: %.6e)\n" ll (exp ll)
           | _ -> Printf.printf "Usage: likelihood <obs1> <obs2> ...\n")
        | "generate" | "g" ->
          let len = match args with [n] -> (try int_of_string n with _ -> 10) | _ -> 10 in
          let len = max 1 (min 100 len) in
          let (states, obs) = generate !model len in
          Printf.printf "\n-- Generated Sequence (length %d) --\n" len;
          print_sequence !model states obs
        | "anomaly" | "a" ->
          let obs_str = String.concat " " args in
          (match parse_obs !model obs_str with
           | Some obs when Array.length obs > 0 ->
             let (ll, avg) = anomaly_score !model obs in
             Printf.printf "\n-- Anomaly Score --\n";
             Printf.printf "  Total log-likelihood:     %.4f\n" ll;
             Printf.printf "  Per-observation average:  %.4f\n" avg;
             let severity =
               if avg > -1.0 then "Normal"
               else if avg > -2.0 then "Slightly unusual"
               else if avg > -3.0 then "Suspicious"
               else "Highly anomalous" in
             Printf.printf "  Assessment: %s\n" severity
           | _ -> Printf.printf "Usage: anomaly <obs1> <obs2> ...\n")
        | "learn" ->
          let n_iter = match args with [n] -> (try int_of_string n with _ -> 50) | _ -> 50 in
          Printf.printf "Generating 20 training sequences (length 10-30)...\n";
          let training = List.init 20 (fun _ ->
            let len = 10 + Random.int 21 in
            let (_, obs) = generate !model len in
            obs
          ) in
          Printf.printf "Running Baum-Welch EM (max %d iterations)...\n" n_iter;
          let noisy = {
            !model with
            initial = normalize (Array.init !model.n_states (fun _ -> Random.float 1.0));
            transition = Array.init !model.n_states (fun _ ->
              normalize (Array.init !model.n_states (fun _ -> Random.float 1.0)));
            emission = Array.init !model.n_states (fun _ ->
              normalize (Array.init !model.n_obs (fun _ -> Random.float 1.0)));
          } in
          let (learned, iters, ll) = baum_welch noisy training n_iter 1e-6 in
          Printf.printf "Converged after %d iterations (log-likelihood: %.4f)\n" iters ll;
          Printf.printf "\nLearned model:\n";
          print_model learned;
          Printf.printf "\nOriginal model for comparison:\n";
          print_model !model;
          Printf.printf "(Note: state ordering may differ -- compare distributions, not labels)\n"
        | "demo" | "d" ->
          Printf.printf "\n=== HMM Demo: Weather Model ===\n";
          let m = weather_model () in
          model := m;
          print_model m;
          let obs = [| 0; 1; 2; 0; 2 |] in
          Printf.printf "\nObserved activities: Walk -> Shop -> Clean -> Walk -> Clean\n";
          print_viterbi m obs;
          print_posterior m obs;
          let ll = log_likelihood m obs in
          Printf.printf "\nLog-likelihood: %.4f\n" ll;
          Printf.printf "\n=== Generated Sequence ===\n";
          let (states, gen_obs) = generate m 8 in
          print_sequence m states gen_obs;
          Printf.printf "\n=== Anomaly Detection ===\n";
          let normal = [| 0; 0; 1; 0; 0; 0; 1 |] in
          let weird = [| 2; 2; 2; 2; 2; 2; 2 |] in
          let (_, avg1) = anomaly_score m normal in
          let (_, avg2) = anomaly_score m weird in
          Printf.printf "  Normal (Walk Walk Shop Walk Walk Walk Shop): avg=%.3f\n" avg1;
          Printf.printf "  Weird  (Clean Clean Clean Clean ...):        avg=%.3f\n" avg2;
          Printf.printf "\nDemo complete! Try your own sequences.\n"
        | _ -> Printf.printf "Unknown command: %s. Type 'help' for commands.\n" cmd
  done;
  Printf.printf "Goodbye!\n"
