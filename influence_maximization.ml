(* Influence Maximization via Greedy Seed Selection
   ================================================
   Implements the classic influence maximization problem:
   Given a social network, find k seed nodes that maximize
   information spread under the Independent Cascade (IC) model.

   Features:
   - Independent Cascade diffusion model with configurable propagation probability
   - Monte Carlo simulation for spread estimation
   - Greedy algorithm with lazy evaluation (CELF optimization)
   - Linear Threshold model as alternative diffusion model
   - Multiple graph generators (random, small-world, scale-free, star, grid)
   - Autonomous seed budget advisor that recommends optimal k
   - Influence trajectory tracking and marginal gain analysis
   - Interactive REPL with visualization

   Usage: Run with: ocaml influence_maximization.ml
*)

(* ─── Graph Representation ─── *)

module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

type edge = { target: int; weight: float }

type graph = {
  n: int;
  adj: edge list IntMap.t;
}

let empty_graph n = { n; adj = IntMap.empty }

let add_edge g src dst w =
  let existing = try IntMap.find src g.adj with Not_found -> [] in
  { g with adj = IntMap.add src ({ target = dst; weight = w } :: existing) g.adj }

let neighbors g v =
  try IntMap.find v g.adj with Not_found -> []

let all_nodes g =
  let s = ref IntSet.empty in
  for i = 0 to g.n - 1 do s := IntSet.add i !s done;
  !s

(* ─── Graph Generators ─── *)

let random_graph n m prob =
  let g = ref (empty_graph n) in
  let edges = ref 0 in
  while !edges < m do
    let u = Random.int n in
    let v = Random.int n in
    if u <> v then begin
      g := add_edge !g u v prob;
      incr edges
    end
  done;
  !g

let small_world_graph n k prob edge_prob =
  (* Watts-Strogatz-like: ring lattice + random rewiring *)
  let g = ref (empty_graph n) in
  (* Ring lattice *)
  for i = 0 to n - 1 do
    for j = 1 to k / 2 do
      let neighbor = (i + j) mod n in
      g := add_edge !g i neighbor prob;
      g := add_edge !g neighbor i prob
    done
  done;
  (* Random rewiring *)
  for i = 0 to n - 1 do
    for j = 1 to k / 2 do
      if Random.float 1.0 < edge_prob then begin
        let new_target = Random.int n in
        if new_target <> i then begin
          g := add_edge !g i new_target prob
        end
      end
    done
  done;
  !g

let scale_free_graph n m0 prob =
  (* Barabási-Albert preferential attachment *)
  let g = ref (empty_graph n) in
  let degree = Array.make n 0 in
  (* Initial complete graph of m0 nodes *)
  for i = 0 to m0 - 1 do
    for j = i + 1 to m0 - 1 do
      g := add_edge !g i j prob;
      g := add_edge !g j i prob;
      degree.(i) <- degree.(i) + 1;
      degree.(j) <- degree.(j) + 1
    done
  done;
  (* Attach remaining nodes *)
  for new_node = m0 to n - 1 do
    let total_deg = Array.fold_left (+) 0 degree in
    let added = ref IntSet.empty in
    let attempts = ref 0 in
    while IntSet.cardinal !added < min m0 new_node && !attempts < n * 10 do
      incr attempts;
      let r = Random.int (max 1 total_deg) in
      let cum = ref 0 in
      let chosen = ref 0 in
      let found = ref false in
      for v = 0 to new_node - 1 do
        if not !found then begin
          cum := !cum + degree.(v);
          if !cum > r then begin
            chosen := v;
            found := true
          end
        end
      done;
      if not (IntSet.mem !chosen !added) then begin
        g := add_edge !g new_node !chosen prob;
        g := add_edge !g !chosen new_node prob;
        degree.(new_node) <- degree.(new_node) + 1;
        degree.(!chosen) <- degree.(!chosen) + 1;
        added := IntSet.add !chosen !added
      end
    done
  done;
  !g

let star_graph n prob =
  let g = ref (empty_graph n) in
  for i = 1 to n - 1 do
    g := add_edge !g 0 i prob;
    g := add_edge !g i 0 prob
  done;
  !g

let grid_graph rows cols prob =
  let n = rows * cols in
  let g = ref (empty_graph n) in
  for r = 0 to rows - 1 do
    for c = 0 to cols - 1 do
      let id = r * cols + c in
      if c + 1 < cols then begin
        let right = r * cols + (c + 1) in
        g := add_edge !g id right prob;
        g := add_edge !g right id prob
      end;
      if r + 1 < rows then begin
        let down = (r + 1) * cols + c in
        g := add_edge !g id down prob;
        g := add_edge !g down id prob
      end
    done
  done;
  !g

(* ─── Diffusion Models ─── *)

(* Independent Cascade: each active node gets one chance to activate
   each inactive neighbor with probability = edge weight *)
let simulate_ic g seeds =
  let active = Hashtbl.create 64 in
  let queue = Queue.create () in
  IntSet.iter (fun s ->
    Hashtbl.replace active s true;
    Queue.push s queue
  ) seeds;
  while not (Queue.is_empty queue) do
    let v = Queue.pop queue in
    List.iter (fun e ->
      if not (Hashtbl.mem active e.target) then begin
        if Random.float 1.0 < e.weight then begin
          Hashtbl.replace active e.target true;
          Queue.push e.target queue
        end
      end
    ) (neighbors g v)
  done;
  Hashtbl.length active

(* Linear Threshold: each node has random threshold; activates when
   sum of active neighbor weights exceeds threshold *)
let simulate_lt g seeds =
  let n = g.n in
  let active = Array.make n false in
  let thresholds = Array.init n (fun _ -> Random.float 1.0) in
  IntSet.iter (fun s -> active.(s) <- true) seeds;
  let changed = ref true in
  while !changed do
    changed := false;
    for v = 0 to n - 1 do
      if not active.(v) then begin
        (* Compute influence from active in-neighbors *)
        let influence = ref 0.0 in
        for u = 0 to n - 1 do
          if active.(u) then
            List.iter (fun e ->
              if e.target = v then
                influence := !influence +. e.weight
            ) (neighbors g u)
        done;
        if !influence >= thresholds.(v) then begin
          active.(v) <- true;
          changed := true
        end
      end
    done
  done;
  Array.fold_left (fun acc a -> if a then acc + 1 else acc) 0 active

(* ─── Spread Estimation ─── *)

type diffusion_model = IC | LT

let estimate_spread g seeds model num_sims =
  let total = ref 0 in
  for _ = 1 to num_sims do
    let spread = match model with
      | IC -> simulate_ic g seeds
      | LT -> simulate_lt g seeds
    in
    total := !total + spread
  done;
  float_of_int !total /. float_of_int num_sims

(* ─── Greedy Seed Selection (with CELF optimization) ─── *)

(* CELF = Cost-Effective Lazy Forward evaluation
   Key insight: marginal gain is submodular, so we can skip re-evaluation
   of nodes whose marginal gain upper bound is below the current best *)

type celf_entry = {
  node: int;
  mutable mg: float;      (* marginal gain *)
  mutable iteration: int; (* last evaluated iteration *)
}

let greedy_influence_max g k model num_sims =
  let seeds = ref IntSet.empty in
  let trajectory = Array.make k (0, 0.0, 0.0) in (* (node, spread, marginal_gain) *)
  let current_spread = ref 0.0 in

  (* Initialize: evaluate all nodes *)
  let entries = Array.init g.n (fun v ->
    let s = IntSet.singleton v in
    let spread = estimate_spread g s model num_sims in
    { node = v; mg = spread; iteration = 0 }
  ) in

  (* Sort descending by marginal gain *)
  Array.sort (fun a b -> compare b.mg a.mg) entries;

  for iter = 1 to k do
    (* CELF: find best node with up-to-date marginal gain *)
    let found = ref false in
    let idx = ref 0 in
    while not !found && !idx < Array.length entries do
      let e = entries.(!idx) in
      if IntSet.mem e.node !seeds then
        incr idx
      else if e.iteration = iter then begin
        (* Up-to-date, this is the best *)
        seeds := IntSet.add e.node !seeds;
        current_spread := !current_spread +. e.mg;
        trajectory.(iter - 1) <- (e.node, !current_spread, e.mg);
        found := true
      end else begin
        (* Re-evaluate marginal gain *)
        let new_seeds = IntSet.add e.node !seeds in
        let new_spread = estimate_spread g new_seeds model num_sims in
        e.mg <- new_spread -. !current_spread;
        e.iteration <- iter;
        (* Re-sort from this position *)
        let j = ref !idx in
        while !j + 1 < Array.length entries && entries.(!j).mg < entries.(!j + 1).mg do
          let tmp = entries.(!j) in
          entries.(!j) <- entries.(!j + 1);
          entries.(!j + 1) <- tmp;
          incr j
        done;
        (* Don't increment idx, check same position again *)
      end
    done;
    if not !found then
      Printf.printf "Warning: could not find seed for iteration %d\n" iter
  done;
  (!seeds, trajectory)

(* ─── Autonomous Budget Advisor ─── *)

let recommend_budget g model num_sims max_k =
  let limit = min max_k (min 10 g.n) in
  Printf.printf "\n🤖 Autonomous Budget Advisor\n";
  Printf.printf "  Testing k = 1..%d to find diminishing returns...\n\n" limit;
  let seeds = ref IntSet.empty in
  let current_spread = ref 0.0 in
  let gains = Array.make limit 0.0 in
  let best_ratio_k = ref 1 in
  let best_ratio = ref 0.0 in
  for i = 0 to limit - 1 do
    let best_node = ref (-1) in
    let best_mg = ref neg_infinity in
    for v = 0 to g.n - 1 do
      if not (IntSet.mem v !seeds) then begin
        let s = IntSet.add v !seeds in
        let spread = estimate_spread g s model num_sims in
        let mg = spread -. !current_spread in
        if mg > !best_mg then begin
          best_mg := mg;
          best_node := v
        end
      end
    done;
    if !best_node >= 0 then begin
      seeds := IntSet.add !best_node !seeds;
      current_spread := !current_spread +. !best_mg;
      gains.(i) <- !best_mg;
      let ratio = !current_spread /. float_of_int (i + 1) in
      if ratio > !best_ratio then begin
        best_ratio := ratio;
        best_ratio_k := i + 1
      end;
      Printf.printf "  k=%-2d  spread=%.1f  marginal_gain=%.2f  efficiency=%.2f\n"
        (i + 1) !current_spread !best_mg ratio
    end
  done;
  (* Detect elbow: where marginal gain drops below 50% of initial *)
  let elbow_k = ref limit in
  if gains.(0) > 0.0 then
    for i = 1 to limit - 1 do
      if gains.(i) < gains.(0) *. 0.5 && !elbow_k = limit then
        elbow_k := i
    done;
  let recommended = min !elbow_k !best_ratio_k in
  Printf.printf "\n  📊 Recommendation: k = %d\n" recommended;
  Printf.printf "     Elbow point: k = %d (marginal gain < 50%% of first)\n" !elbow_k;
  Printf.printf "     Best efficiency: k = %d (highest spread/k ratio)\n" !best_ratio_k;
  recommended

(* ─── Degree Heuristic Baseline ─── *)

let degree_heuristic g k =
  let degrees = Array.init g.n (fun v ->
    (List.length (neighbors g v), v)
  ) in
  Array.sort (fun (d1, _) (d2, _) -> compare d2 d1) degrees;
  let seeds = ref IntSet.empty in
  let i = ref 0 in
  while IntSet.cardinal !seeds < k && !i < Array.length degrees do
    let (_, v) = degrees.(!i) in
    seeds := IntSet.add v !seeds;
    incr i
  done;
  !seeds

(* ─── Display ─── *)

let print_bar width value max_val label =
  let filled = if max_val > 0.0 then int_of_float (value /. max_val *. float_of_int width) else 0 in
  let filled = min width (max 0 filled) in
  Printf.printf "  %s [" label;
  for _ = 1 to filled do print_char '#' done;
  for _ = filled + 1 to width do print_char '.' done;
  Printf.printf "] %.1f\n" value

let display_results g seeds trajectory k model num_sims =
  Printf.printf "\n╔══════════════════════════════════════════╗\n";
  Printf.printf "║    INFLUENCE MAXIMIZATION RESULTS        ║\n";
  Printf.printf "╠══════════════════════════════════════════╣\n";
  Printf.printf "║  Network: %d nodes                       \n" g.n;
  Printf.printf "║  Model: %s                               \n"
    (match model with IC -> "Independent Cascade" | LT -> "Linear Threshold");
  Printf.printf "║  Budget: k = %d seeds                    \n" k;
  Printf.printf "║  Simulations: %d                         \n" num_sims;
  Printf.printf "╚══════════════════════════════════════════╝\n\n";

  Printf.printf "🌱 Selected Seeds (in order):\n";
  let max_spread = if k > 0 then let (_, s, _) = trajectory.(k - 1) in s else 0.0 in
  for i = 0 to k - 1 do
    let (node, spread, mg) = trajectory.(i) in
    Printf.printf "  %d. Node %-3d  spread=%.1f  Δ=+%.2f\n" (i + 1) node spread mg;
    print_bar 30 spread max_spread (Printf.sprintf "     k=%-2d" (i + 1))
  done;

  Printf.printf "\n📊 Comparison with Degree Heuristic:\n";
  let deg_seeds = degree_heuristic g k in
  let deg_spread = estimate_spread g deg_seeds model num_sims in
  let greedy_spread = estimate_spread g seeds model num_sims in
  Printf.printf "  Greedy:  %.1f expected reach (%.1f%% of network)\n"
    greedy_spread (greedy_spread /. float_of_int g.n *. 100.0);
  Printf.printf "  Degree:  %.1f expected reach (%.1f%% of network)\n"
    deg_spread (deg_spread /. float_of_int g.n *. 100.0);
  if deg_spread > 0.0 then
    Printf.printf "  Greedy advantage: %.1f%% better\n"
      ((greedy_spread -. deg_spread) /. deg_spread *. 100.0)

(* ─── REPL ─── *)

let current_graph = ref (random_graph 30 90 0.1)
let current_model = ref IC
let current_sims = ref 500
let current_k = ref 3

let print_help () =
  Printf.printf "\n📖 Influence Maximization Commands:\n";
  Printf.printf "  graph random <n> <edges> <prob>  - Random directed graph\n";
  Printf.printf "  graph small-world <n> <k> <prob> - Watts-Strogatz small-world\n";
  Printf.printf "  graph scale-free <n> <m0> <prob> - Barabási-Albert scale-free\n";
  Printf.printf "  graph star <n> <prob>            - Star topology\n";
  Printf.printf "  graph grid <rows> <cols> <prob>  - Grid lattice\n";
  Printf.printf "  model ic                         - Use Independent Cascade\n";
  Printf.printf "  model lt                         - Use Linear Threshold\n";
  Printf.printf "  sims <n>                         - Set Monte Carlo simulations\n";
  Printf.printf "  seeds <k>                        - Set seed budget\n";
  Printf.printf "  run                              - Run greedy influence maximization\n";
  Printf.printf "  spread <node1,node2,...>          - Estimate spread for given seeds\n";
  Printf.printf "  advise                           - Autonomous budget recommendation\n";
  Printf.printf "  compare                          - Compare IC vs LT models\n";
  Printf.printf "  info                             - Show current settings\n";
  Printf.printf "  help                             - Show this help\n";
  Printf.printf "  quit                             - Exit\n\n"

let show_info () =
  Printf.printf "\n⚙ Current Settings:\n";
  Printf.printf "  Network: %d nodes\n" !current_graph.n;
  let edge_count = IntMap.fold (fun _ edges acc -> acc + List.length edges) !current_graph.adj 0 in
  Printf.printf "  Edges: %d\n" edge_count;
  Printf.printf "  Model: %s\n" (match !current_model with IC -> "Independent Cascade" | LT -> "Linear Threshold");
  Printf.printf "  Simulations: %d\n" !current_sims;
  Printf.printf "  Seed budget: %d\n\n" !current_k

let parse_int_opt s = try Some (int_of_string s) with _ -> None
let parse_float_opt s = try Some (float_of_string s) with _ -> None

let run_repl () =
  Printf.printf "\n╔══════════════════════════════════════════════╗\n";
  Printf.printf "║  🌐 Influence Maximization Simulator         ║\n";
  Printf.printf "║  Greedy seed selection with CELF             ║\n";
  Printf.printf "║  Independent Cascade & Linear Threshold      ║\n";
  Printf.printf "╚══════════════════════════════════════════════╝\n";
  print_help ();
  show_info ();
  let running = ref true in
  while !running do
    Printf.printf "influence> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let parts = String.split_on_char ' ' (String.trim line) in
      match parts with
      | ["quit"] | ["exit"] | ["q"] -> running := false
      | ["help"] | ["h"] -> print_help ()
      | ["info"] | ["i"] -> show_info ()
      | ["graph"; "random"; sn; sm; sp] ->
        (match parse_int_opt sn, parse_int_opt sm, parse_float_opt sp with
         | Some n, Some m, Some p ->
           current_graph := random_graph n m p;
           Printf.printf "  ✅ Random graph: %d nodes, %d edges, prob=%.2f\n" n m p
         | _ -> Printf.printf "  ❌ Usage: graph random <n> <edges> <prob>\n")
      | ["graph"; "small-world"; sn; sk; sp] ->
        (match parse_int_opt sn, parse_int_opt sk, parse_float_opt sp with
         | Some n, Some k, Some p ->
           current_graph := small_world_graph n k p 0.3;
           Printf.printf "  ✅ Small-world graph: %d nodes, k=%d, prob=%.2f\n" n k p
         | _ -> Printf.printf "  ❌ Usage: graph small-world <n> <k> <prob>\n")
      | ["graph"; "scale-free"; sn; sm0; sp] ->
        (match parse_int_opt sn, parse_int_opt sm0, parse_float_opt sp with
         | Some n, Some m0, Some p ->
           current_graph := scale_free_graph n m0 p;
           Printf.printf "  ✅ Scale-free graph: %d nodes, m0=%d, prob=%.2f\n" n m0 p
         | _ -> Printf.printf "  ❌ Usage: graph scale-free <n> <m0> <prob>\n")
      | ["graph"; "star"; sn; sp] ->
        (match parse_int_opt sn, parse_float_opt sp with
         | Some n, Some p ->
           current_graph := star_graph n p;
           Printf.printf "  ✅ Star graph: %d nodes, prob=%.2f\n" n p
         | _ -> Printf.printf "  ❌ Usage: graph star <n> <prob>\n")
      | ["graph"; "grid"; sr; sc; sp] ->
        (match parse_int_opt sr, parse_int_opt sc, parse_float_opt sp with
         | Some r, Some c, Some p ->
           current_graph := grid_graph r c p;
           Printf.printf "  ✅ Grid graph: %dx%d (%d nodes), prob=%.2f\n" r c (r * c) p
         | _ -> Printf.printf "  ❌ Usage: graph grid <rows> <cols> <prob>\n")
      | ["model"; "ic"] ->
        current_model := IC;
        Printf.printf "  ✅ Model set to Independent Cascade\n"
      | ["model"; "lt"] ->
        current_model := LT;
        Printf.printf "  ✅ Model set to Linear Threshold\n"
      | ["sims"; sn] ->
        (match parse_int_opt sn with
         | Some n -> current_sims := n; Printf.printf "  ✅ Simulations set to %d\n" n
         | None -> Printf.printf "  ❌ Usage: sims <number>\n")
      | ["seeds"; sk] ->
        (match parse_int_opt sk with
         | Some k -> current_k := k; Printf.printf "  ✅ Seed budget set to %d\n" k
         | None -> Printf.printf "  ❌ Usage: seeds <number>\n")
      | ["run"] ->
        Printf.printf "\n  🔄 Running greedy influence maximization (k=%d, %d sims)...\n"
          !current_k !current_sims;
        let (seeds, trajectory) = greedy_influence_max !current_graph !current_k !current_model !current_sims in
        display_results !current_graph seeds trajectory !current_k !current_model !current_sims
      | ["spread"; node_str] ->
        let nodes = String.split_on_char ',' node_str in
        let seed_set = List.fold_left (fun acc s ->
          match parse_int_opt s with Some v -> IntSet.add v acc | None -> acc
        ) IntSet.empty nodes in
        let spread = estimate_spread !current_graph seed_set !current_model !current_sims in
        Printf.printf "  📊 Spread from {%s}: %.1f (%.1f%% of network)\n"
          (String.concat "," (List.map string_of_int (IntSet.elements seed_set)))
          spread (spread /. float_of_int !current_graph.n *. 100.0)
      | ["advise"] ->
        let _ = recommend_budget !current_graph !current_model !current_sims 10 in ()
      | ["compare"] ->
        Printf.printf "\n  🔄 Comparing IC vs LT models (k=%d)...\n" !current_k;
        let (ic_seeds, _) = greedy_influence_max !current_graph !current_k IC !current_sims in
        let (lt_seeds, _) = greedy_influence_max !current_graph !current_k LT !current_sims in
        let ic_spread = estimate_spread !current_graph ic_seeds IC !current_sims in
        let lt_spread = estimate_spread !current_graph lt_seeds LT !current_sims in
        Printf.printf "\n  Independent Cascade:  seeds={%s}  spread=%.1f\n"
          (String.concat "," (List.map string_of_int (IntSet.elements ic_seeds))) ic_spread;
        Printf.printf "  Linear Threshold:    seeds={%s}  spread=%.1f\n"
          (String.concat "," (List.map string_of_int (IntSet.elements lt_seeds))) lt_spread;
        let ic_cross = estimate_spread !current_graph ic_seeds LT !current_sims in
        let lt_cross = estimate_spread !current_graph lt_seeds IC !current_sims in
        Printf.printf "  IC seeds under LT: %.1f  |  LT seeds under IC: %.1f\n" ic_cross lt_cross
      | [""] -> ()
      | _ -> Printf.printf "  ❓ Unknown command. Type 'help' for usage.\n"
  done;
  Printf.printf "\nGoodbye! 👋\n"

let () =
  Random.self_init ();
  run_repl ()
