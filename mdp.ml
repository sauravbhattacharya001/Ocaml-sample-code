(* mdp.ml - Markov Decision Process Solver
   
   Features:
   - Value Iteration & Policy Iteration algorithms
   - Q-Learning (model-free reinforcement learning)
   - Built-in gridworld environments (4x4, Cliff Walking, Windy Gridworld)
   - Configurable discount factor and convergence threshold
   - ASCII visualization of policies and value functions
   - Interactive REPL with commands for solving, training, and inspecting
   
   Usage: ocamlfind ocamlopt -package unix -linkpkg mdp.ml -o mdp && ./mdp
   Or:    ocaml mdp.ml
*)

(* ==================== Core MDP Types ==================== *)

type action = Up | Down | Left | Right

type transition = {
  next_state: int;
  probability: float;
  reward: float;
}

type mdp = {
  n_states: int;
  n_actions: int;
  transitions: (int * action * transition list) list;  (* state, action -> transitions *)
  terminal_states: int list;
  gamma: float;  (* discount factor *)
}

type gridworld = {
  rows: int;
  cols: int;
  walls: (int * int) list;
  start: int * int;
  goals: (int * int * float) list;  (* row, col, reward *)
  traps: (int * int * float) list;  (* row, col, penalty *)
  wind: int array;  (* per-column upward wind strength *)
  slip_prob: float;  (* probability of slipping to random adjacent *)
  step_reward: float;
}

(* ==================== Utility ==================== *)

let action_to_string = function
  | Up -> "Up" | Down -> "Down" | Left -> "Left" | Right -> "Right"

let action_to_arrow = function
  | Up -> "↑" | Down -> "↓" | Left -> "←" | Right -> "→"

let all_actions = [Up; Down; Left; Right]

let action_to_int = function
  | Up -> 0 | Down -> 1 | Left -> 2 | Right -> 3

let int_to_action = function
  | 0 -> Up | 1 -> Down | 2 -> Left | 3 -> Right | _ -> Up

(* ==================== Gridworld Construction ==================== *)

let rc_to_state cols r c = r * cols + c
let state_to_rc cols s = (s / cols, s mod cols)

let build_gridworld (gw : gridworld) : mdp =
  let n = gw.rows * gw.cols in
  let is_wall r c = List.exists (fun (wr, wc) -> wr = r && wc = c) gw.walls in
  let is_goal r c = List.exists (fun (gr, gc, _) -> gr = r && gc = c) gw.goals in
  let goal_reward r c =
    match List.find_opt (fun (gr, gc, _) -> gr = r && gc = c) gw.goals with
    | Some (_, _, rw) -> rw | None -> 0.0
  in
  let is_trap r c = List.exists (fun (tr, tc, _) -> tr = r && tc = c) gw.traps in
  let trap_penalty r c =
    match List.find_opt (fun (tr, tc, _) -> tr = r && tc = c) gw.traps with
    | Some (_, _, p) -> p | None -> 0.0
  in
  let terminals = List.map (fun (gr, gc, _) -> rc_to_state gw.cols gr gc) gw.goals in
  let move_delta = function
    | Up -> (-1, 0) | Down -> (1, 0) | Left -> (0, -1) | Right -> (0, 1)
  in
  let try_move r c a =
    let (dr, dc) = move_delta a in
    let wind_push = if c >= 0 && c < Array.length gw.wind then gw.wind.(c) else 0 in
    let nr = r + dr - wind_push in
    let nc = c + dc in
    let nr = max 0 (min (gw.rows - 1) nr) in
    let nc = max 0 (min (gw.cols - 1) nc) in
    if is_wall nr nc then (r, c) else (nr, nc)
  in
  let transitions = ref [] in
  for r = 0 to gw.rows - 1 do
    for c = 0 to gw.cols - 1 do
      let s = rc_to_state gw.cols r c in
      if not (is_wall r c) && not (is_goal r c) then begin
        List.iter (fun a ->
          let ts = ref [] in
          if gw.slip_prob > 0.0 then begin
            (* With slip: intended direction with (1-slip), each other with slip/3 *)
            List.iter (fun a2 ->
              let p = if a2 = a then (1.0 -. gw.slip_prob) else gw.slip_prob /. 3.0 in
              if p > 0.0 then begin
                let (nr, nc) = try_move r c a2 in
                let ns = rc_to_state gw.cols nr nc in
                let rw = if is_goal nr nc then goal_reward nr nc
                          else if is_trap nr nc then trap_penalty nr nc
                          else gw.step_reward in
                ts := { next_state = ns; probability = p; reward = rw } :: !ts
              end
            ) all_actions
          end else begin
            let (nr, nc) = try_move r c a in
            let ns = rc_to_state gw.cols nr nc in
            let rw = if is_goal nr nc then goal_reward nr nc
                      else if is_trap nr nc then trap_penalty nr nc
                      else gw.step_reward in
            ts := [{ next_state = ns; probability = 1.0; reward = rw }]
          end;
          (* Merge duplicate next_states *)
          let merged = Hashtbl.create 8 in
          List.iter (fun t ->
            match Hashtbl.find_opt merged t.next_state with
            | Some (p, r) -> Hashtbl.replace merged t.next_state (p +. t.probability, r)
            | None -> Hashtbl.replace merged t.next_state (t.probability, t.reward)
          ) !ts;
          let final_ts = Hashtbl.fold (fun ns (p, rw) acc ->
            { next_state = ns; probability = p; reward = rw } :: acc
          ) merged [] in
          transitions := (s, a, final_ts) :: !transitions
        ) all_actions
      end
    done
  done;
  { n_states = n; n_actions = 4; transitions = !transitions;
    terminal_states = terminals; gamma = 0.99 }

(* ==================== Built-in Environments ==================== *)

let classic_4x4 () =
  build_gridworld {
    rows = 4; cols = 4;
    walls = [];
    start = (3, 0);
    goals = [(0, 3, 1.0)];
    traps = [(1, 1, -1.0)];
    wind = [|0;0;0;0|];
    slip_prob = 0.0;
    step_reward = -0.04;
  }

let cliff_walking () =
  let traps = List.init 10 (fun i -> (3, i + 1, -100.0)) in
  build_gridworld {
    rows = 4; cols = 12;
    walls = [];
    start = (3, 0);
    goals = [(3, 11, 1.0)];
    traps;
    wind = Array.make 12 0;
    slip_prob = 0.0;
    step_reward = -1.0;
  }

let windy_gridworld () =
  build_gridworld {
    rows = 7; cols = 10;
    walls = [];
    start = (3, 0);
    goals = [(3, 7, 1.0)];
    traps = [];
    wind = [|0;0;0;1;1;1;2;2;1;0|];
    slip_prob = 0.0;
    step_reward = -1.0;
  }

let frozen_lake () =
  build_gridworld {
    rows = 4; cols = 4;
    walls = [];
    start = (0, 0);
    goals = [(3, 3, 1.0)];
    traps = [(1, 1, -1.0); (1, 3, -1.0); (2, 3, -1.0); (3, 0, -1.0)];
    wind = [|0;0;0;0|];
    slip_prob = 0.2;
    step_reward = -0.01;
  }

(* ==================== Transition Lookup ==================== *)

let get_transitions mdp s a =
  match List.find_opt (fun (s2, a2, _) -> s2 = s && a2 = a) mdp.transitions with
  | Some (_, _, ts) -> ts
  | None -> []

let is_terminal mdp s = List.mem s mdp.terminal_states

(* ==================== Value Iteration ==================== *)

let value_iteration ?(theta=1e-6) ?(max_iter=1000) mdp =
  let v = Array.make mdp.n_states 0.0 in
  let policy = Array.make mdp.n_states Up in
  let iter_count = ref 0 in
  let converged = ref false in
  while not !converged && !iter_count < max_iter do
    incr iter_count;
    let delta = ref 0.0 in
    for s = 0 to mdp.n_states - 1 do
      if not (is_terminal mdp s) then begin
        let old_v = v.(s) in
        let best = ref neg_infinity in
        let best_a = ref Up in
        List.iter (fun a ->
          let ts = get_transitions mdp s a in
          let q = List.fold_left (fun acc t ->
            acc +. t.probability *. (t.reward +. mdp.gamma *. v.(t.next_state))
          ) 0.0 ts in
          if q > !best then begin best := q; best_a := a end
        ) all_actions;
        if !best > neg_infinity then begin
          v.(s) <- !best;
          policy.(s) <- !best_a
        end;
        delta := max !delta (abs_float (v.(s) -. old_v))
      end
    done;
    if !delta < theta then converged := true
  done;
  (v, policy, !iter_count)

(* ==================== Policy Iteration ==================== *)

let policy_evaluation ?(theta=1e-6) ?(max_iter=500) mdp policy v =
  let converged = ref false in
  let iters = ref 0 in
  while not !converged && !iters < max_iter do
    incr iters;
    let delta = ref 0.0 in
    for s = 0 to mdp.n_states - 1 do
      if not (is_terminal mdp s) then begin
        let old_v = v.(s) in
        let ts = get_transitions mdp s policy.(s) in
        v.(s) <- List.fold_left (fun acc t ->
          acc +. t.probability *. (t.reward +. mdp.gamma *. v.(t.next_state))
        ) 0.0 ts;
        delta := max !delta (abs_float (v.(s) -. old_v))
      end
    done;
    if !delta < theta then converged := true
  done;
  !iters

let policy_iteration ?(max_iter=100) mdp =
  let v = Array.make mdp.n_states 0.0 in
  let policy = Array.make mdp.n_states Up in
  let stable = ref false in
  let iter_count = ref 0 in
  while not !stable && !iter_count < max_iter do
    incr iter_count;
    let _eval_iters = policy_evaluation mdp policy v in
    stable := true;
    for s = 0 to mdp.n_states - 1 do
      if not (is_terminal mdp s) then begin
        let old_a = policy.(s) in
        let best = ref neg_infinity in
        let best_a = ref Up in
        List.iter (fun a ->
          let ts = get_transitions mdp s a in
          let q = List.fold_left (fun acc t ->
            acc +. t.probability *. (t.reward +. mdp.gamma *. v.(t.next_state))
          ) 0.0 ts in
          if q > !best then begin best := q; best_a := a end
        ) all_actions;
        policy.(s) <- !best_a;
        if old_a <> !best_a then stable := false
      end
    done
  done;
  (v, policy, !iter_count)

(* ==================== Q-Learning ==================== *)

type qlearning_params = {
  alpha: float;      (* learning rate *)
  epsilon: float;    (* exploration rate *)
  episodes: int;
  max_steps: int;
  decay_epsilon: bool;
}

let default_ql_params = {
  alpha = 0.1;
  epsilon = 0.3;
  episodes = 5000;
  max_steps = 200;
  decay_epsilon = true;
}

let q_learning mdp params start_state =
  let q = Array.init mdp.n_states (fun _ -> Array.make 4 0.0) in
  let total_rewards = Array.make params.episodes 0.0 in
  let rng = Random.State.make_self_init () in
  for ep = 0 to params.episodes - 1 do
    let s = ref start_state in
    let total_r = ref 0.0 in
    let eps = if params.decay_epsilon then
      params.epsilon *. (1.0 -. float_of_int ep /. float_of_int params.episodes)
    else params.epsilon in
    let step = ref 0 in
    while not (is_terminal mdp !s) && !step < params.max_steps do
      incr step;
      (* Epsilon-greedy action selection *)
      let a = if Random.State.float rng 1.0 < eps then
        int_to_action (Random.State.int rng 4)
      else begin
        let best_ai = ref 0 in
        let best_q = ref q.(!s).(0) in
        for ai = 1 to 3 do
          if q.(!s).(ai) > !best_q then begin best_q := q.(!s).(ai); best_ai := ai end
        done;
        int_to_action !best_ai
      end in
      let ai = action_to_int a in
      let ts = get_transitions mdp !s a in
      (* Sample next state from transitions *)
      let roll = Random.State.float rng 1.0 in
      let cum = ref 0.0 in
      let next = ref !s in
      let reward = ref 0.0 in
      let found = ref false in
      List.iter (fun t ->
        if not !found then begin
          cum := !cum +. t.probability;
          if roll < !cum then begin
            next := t.next_state;
            reward := t.reward;
            found := true
          end
        end
      ) ts;
      (* Q-update *)
      let max_q_next = Array.fold_left max neg_infinity q.(!next) in
      let max_q_next = if is_terminal mdp !next then 0.0 else max_q_next in
      q.(!s).(ai) <- q.(!s).(ai) +.
        params.alpha *. (!reward +. mdp.gamma *. max_q_next -. q.(!s).(ai));
      total_r := !total_r +. !reward;
      s := !next
    done;
    total_rewards.(ep) <- !total_r
  done;
  (* Extract policy from Q-table *)
  let policy = Array.init mdp.n_states (fun s ->
    let best_ai = ref 0 in
    let best_q = ref q.(s).(0) in
    for ai = 1 to 3 do
      if q.(s).(ai) > !best_q then begin best_q := q.(s).(ai); best_ai := ai end
    done;
    int_to_action !best_ai
  ) in
  let v = Array.init mdp.n_states (fun s ->
    Array.fold_left max neg_infinity q.(s)
  ) in
  (q, v, policy, total_rewards)

(* ==================== Visualization ==================== *)

let print_grid_values mdp cols v =
  let rows = mdp.n_states / cols in
  Printf.printf "\n  Value Function:\n";
  Printf.printf "  %s\n" (String.make (cols * 8 + 1) '-');
  for r = 0 to rows - 1 do
    Printf.printf "  |";
    for c = 0 to cols - 1 do
      let s = rc_to_state cols r c in
      if is_terminal mdp s then
        Printf.printf "  GOAL |"
      else
        Printf.printf " %5.2f |" v.(s)
    done;
    Printf.printf "\n";
    Printf.printf "  %s\n" (String.make (cols * 8 + 1) '-')
  done

let print_grid_policy mdp cols policy =
  let rows = mdp.n_states / cols in
  Printf.printf "\n  Policy (arrows):\n";
  Printf.printf "  %s\n" (String.make (cols * 4 + 1) '-');
  for r = 0 to rows - 1 do
    Printf.printf "  |";
    for c = 0 to cols - 1 do
      let s = rc_to_state cols r c in
      if is_terminal mdp s then
        Printf.printf " G |"
      else
        Printf.printf " %s |" (action_to_arrow policy.(s))
    done;
    Printf.printf "\n";
    Printf.printf "  %s\n" (String.make (cols * 4 + 1) '-')
  done

(* ==================== REPL ==================== *)

type env_info = {
  name: string;
  mdp: mdp;
  cols: int;
  start_state: int;
  description: string;
}

let make_env name desc mdp cols start_r start_c =
  { name; description = desc; mdp; cols;
    start_state = rc_to_state cols start_r start_c }

let environments () = [
  make_env "4x4" "Classic 4x4 grid. Goal at top-right, trap at (1,1)."
    (classic_4x4 ()) 4 3 0;
  make_env "cliff" "Cliff Walking: 4x12 grid with cliff along bottom."
    (cliff_walking ()) 12 3 0;
  make_env "windy" "Windy Gridworld: 7x10 with upward wind columns."
    (windy_gridworld ()) 10 3 0;
  make_env "frozen" "Frozen Lake: 4x4 with slippery surface (20% slip)."
    (frozen_lake ()) 4 0 0;
]

let print_help () =
  Printf.printf "\n";
  Printf.printf "  ╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "  ║           MDP Solver — Interactive REPL             ║\n";
  Printf.printf "  ╠══════════════════════════════════════════════════════╣\n";
  Printf.printf "  ║  env <name>     Switch environment                  ║\n";
  Printf.printf "  ║  envs           List available environments         ║\n";
  Printf.printf "  ║  vi             Run Value Iteration                 ║\n";
  Printf.printf "  ║  pi             Run Policy Iteration                ║\n";
  Printf.printf "  ║  ql [episodes]  Run Q-Learning (default 5000)       ║\n";
  Printf.printf "  ║  compare        Run all 3 solvers and compare       ║\n";
  Printf.printf "  ║  gamma <f>      Set discount factor (0-1)           ║\n";
  Printf.printf "  ║  alpha <f>      Set Q-learning rate (0-1)           ║\n";
  Printf.printf "  ║  epsilon <f>    Set exploration rate (0-1)          ║\n";
  Printf.printf "  ║  simulate <n>   Simulate n episodes with policy     ║\n";
  Printf.printf "  ║  help           Show this help                      ║\n";
  Printf.printf "  ║  quit           Exit                                ║\n";
  Printf.printf "  ╚══════════════════════════════════════════════════════╝\n";
  Printf.printf "\n"

let () =
  Printf.printf "\n";
  Printf.printf "  ╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "  ║     🎯 MDP Solver — Markov Decision Processes      ║\n";
  Printf.printf "  ║                                                      ║\n";
  Printf.printf "  ║  Value Iteration · Policy Iteration · Q-Learning    ║\n";
  Printf.printf "  ║  4 Built-in Gridworld Environments                  ║\n";
  Printf.printf "  ╚══════════════════════════════════════════════════════╝\n";
  Printf.printf "\n";

  let envs = environments () in
  let current_env = ref (List.hd envs) in
  let last_policy = ref None in
  let ql_params = ref default_ql_params in

  let update_gamma g =
    let e = !current_env in
    let mdp = { e.mdp with gamma = g } in
    current_env := { e with mdp }
  in

  print_help ();
  Printf.printf "  Current environment: %s\n" !current_env.name;
  Printf.printf "  %s\n\n" !current_env.description;

  let running = ref true in
  while !running do
    Printf.printf "mdp> ";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let parts = String.split_on_char ' ' (String.trim line) in
      match parts with
      | ["quit"] | ["exit"] | ["q"] ->
        Printf.printf "  Goodbye!\n"; running := false
      | ["help"] | ["h"] | ["?"] -> print_help ()
      | ["envs"] ->
        Printf.printf "\n  Available environments:\n";
        List.iter (fun e ->
          let marker = if e.name = !current_env.name then " ← current" else "" in
          Printf.printf "    %-8s  %s%s\n" e.name e.description marker
        ) envs;
        Printf.printf "\n"
      | ["env"; name] ->
        (match List.find_opt (fun e -> e.name = name) envs with
         | Some e ->
           current_env := e;
           last_policy := None;
           Printf.printf "  Switched to: %s\n  %s\n\n" e.name e.description
         | None -> Printf.printf "  Unknown environment: %s (try 'envs')\n" name)
      | ["vi"] ->
        let e = !current_env in
        Printf.printf "  Running Value Iteration (γ=%.3f)...\n" e.mdp.gamma;
        let (v, policy, iters) = value_iteration e.mdp in
        Printf.printf "  Converged in %d iterations.\n" iters;
        print_grid_values e.mdp e.cols v;
        print_grid_policy e.mdp e.cols policy;
        last_policy := Some policy;
        Printf.printf "\n"
      | ["pi"] ->
        let e = !current_env in
        Printf.printf "  Running Policy Iteration (γ=%.3f)...\n" e.mdp.gamma;
        let (v, policy, iters) = policy_iteration e.mdp in
        Printf.printf "  Converged in %d policy improvement steps.\n" iters;
        print_grid_values e.mdp e.cols v;
        print_grid_policy e.mdp e.cols policy;
        last_policy := Some policy;
        Printf.printf "\n"
      | "ql" :: rest ->
        let episodes = match rest with
          | [n] -> (try int_of_string n with _ -> !ql_params.episodes)
          | _ -> !ql_params.episodes
        in
        let p = { !ql_params with episodes } in
        let e = !current_env in
        Printf.printf "  Running Q-Learning (%d episodes, α=%.2f, ε=%.2f, γ=%.3f)...\n"
          p.episodes p.alpha p.epsilon e.mdp.gamma;
        let (_q, v, policy, rewards) = q_learning e.mdp p e.start_state in
        (* Print average reward over last 100 episodes *)
        let last_n = min 100 episodes in
        let avg = ref 0.0 in
        for i = episodes - last_n to episodes - 1 do
          avg := !avg +. rewards.(i)
        done;
        avg := !avg /. float_of_int last_n;
        Printf.printf "  Done. Avg reward (last %d eps): %.2f\n" last_n !avg;
        print_grid_values e.mdp e.cols v;
        print_grid_policy e.mdp e.cols policy;
        last_policy := Some policy;
        Printf.printf "\n"
      | ["compare"] ->
        let e = !current_env in
        Printf.printf "  ═══ Comparing all solvers on '%s' (γ=%.3f) ═══\n\n" e.name e.mdp.gamma;
        Printf.printf "  [Value Iteration]\n";
        let (v1, p1, i1) = value_iteration e.mdp in
        Printf.printf "  Converged in %d iterations.\n" i1;
        print_grid_policy e.mdp e.cols p1;
        Printf.printf "\n  [Policy Iteration]\n";
        let (v2, p2, i2) = policy_iteration e.mdp in
        Printf.printf "  Converged in %d steps.\n" i2;
        print_grid_policy e.mdp e.cols p2;
        Printf.printf "\n  [Q-Learning (%d episodes)]\n" !ql_params.episodes;
        let (_, v3, p3, _) = q_learning e.mdp !ql_params e.start_state in
        print_grid_policy e.mdp e.cols p3;
        (* Agreement check *)
        let agree_vi_pi = ref 0 in
        let agree_vi_ql = ref 0 in
        let total = ref 0 in
        for s = 0 to e.mdp.n_states - 1 do
          if not (is_terminal e.mdp s) then begin
            incr total;
            if p1.(s) = p2.(s) then incr agree_vi_pi;
            if p1.(s) = p3.(s) then incr agree_vi_ql
          end
        done;
        Printf.printf "\n  Policy Agreement:\n";
        Printf.printf "    VI vs PI: %d/%d (%.0f%%)\n" !agree_vi_pi !total
          (100.0 *. float_of_int !agree_vi_pi /. float_of_int (max 1 !total));
        Printf.printf "    VI vs QL: %d/%d (%.0f%%)\n" !agree_vi_ql !total
          (100.0 *. float_of_int !agree_vi_ql /. float_of_int (max 1 !total));
        Printf.printf "\n  Value Comparison (mean |V|):\n";
        let mean arr = Array.fold_left (fun a x -> a +. abs_float x) 0.0 arr
                       /. float_of_int (Array.length arr) in
        Printf.printf "    VI: %.4f | PI: %.4f | QL: %.4f\n\n" (mean v1) (mean v2) (mean v3);
        last_policy := Some p1
      | ["gamma"; g] ->
        (try let gf = float_of_string g in
          if gf >= 0.0 && gf <= 1.0 then begin
            update_gamma gf;
            Printf.printf "  Discount factor set to %.4f\n" gf
          end else Printf.printf "  Gamma must be between 0 and 1.\n"
        with _ -> Printf.printf "  Invalid number.\n")
      | ["alpha"; a] ->
        (try let af = float_of_string a in
          if af > 0.0 && af <= 1.0 then begin
            ql_params := { !ql_params with alpha = af };
            Printf.printf "  Learning rate set to %.4f\n" af
          end else Printf.printf "  Alpha must be between 0 and 1.\n"
        with _ -> Printf.printf "  Invalid number.\n")
      | ["epsilon"; e] ->
        (try let ef = float_of_string e in
          if ef >= 0.0 && ef <= 1.0 then begin
            ql_params := { !ql_params with epsilon = ef };
            Printf.printf "  Exploration rate set to %.4f\n" ef
          end else Printf.printf "  Epsilon must be between 0 and 1.\n"
        with _ -> Printf.printf "  Invalid number.\n")
      | ["simulate"; n_str] ->
        (match !last_policy with
         | None -> Printf.printf "  No policy yet. Run vi, pi, or ql first.\n"
         | Some policy ->
           let n = try int_of_string n_str with _ -> 10 in
           let e = !current_env in
           let rng = Random.State.make_self_init () in
           let total_r = ref 0.0 in
           let total_steps = ref 0 in
           let successes = ref 0 in
           Printf.printf "  Simulating %d episodes...\n" n;
           for _ = 1 to n do
             let s = ref e.start_state in
             let ep_r = ref 0.0 in
             let steps = ref 0 in
             while not (is_terminal e.mdp !s) && !steps < 200 do
               incr steps;
               let a = policy.(!s) in
               let ts = get_transitions e.mdp !s a in
               let roll = Random.State.float rng 1.0 in
               let cum = ref 0.0 in
               let found = ref false in
               List.iter (fun t ->
                 if not !found then begin
                   cum := !cum +. t.probability;
                   if roll < !cum then begin
                     ep_r := !ep_r +. t.reward;
                     s := t.next_state;
                     found := true
                   end
                 end
               ) ts
             done;
             total_r := !total_r +. !ep_r;
             total_steps := !total_steps + !steps;
             if is_terminal e.mdp !s then incr successes
           done;
           Printf.printf "  Results over %d episodes:\n" n;
           Printf.printf "    Success rate: %d/%d (%.0f%%)\n" !successes n
             (100.0 *. float_of_int !successes /. float_of_int n);
           Printf.printf "    Avg reward:   %.2f\n" (!total_r /. float_of_int n);
           Printf.printf "    Avg steps:    %.1f\n\n"
             (float_of_int !total_steps /. float_of_int n))
      | [""] -> ()
      | _ -> Printf.printf "  Unknown command. Type 'help' for commands.\n"
  done
