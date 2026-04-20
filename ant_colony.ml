(* Ant Colony Optimization (ACO) Simulator
   =========================================
   Implements Ant System (AS) and Max-Min Ant System (MMAS) for the
   Travelling Salesman Problem. Features:
   - Multiple ACO variants (AS, MMAS, Elitist AS)
   - Built-in benchmark cities (random, circle, cluster, grid)
   - Pheromone visualization (ASCII heatmap)
   - Convergence tracking with stagnation detection
   - Interactive REPL for parameter tuning and experimentation
   
   Usage: ocamlfind ocamlopt -package unix -linkpkg ant_colony.ml -o ant_colony && ./ant_colony
   Or:    ocaml ant_colony.ml
*)

let () = Random.self_init ()

(* ── Types ─────────────────────────────────────────────────── *)

type city = { id : int; x : float; y : float; name : string }

type aco_variant = AntSystem | MaxMinAS | ElitistAS

type config = {
  n_ants : int;
  n_iterations : int;
  alpha : float;
  beta : float;
  rho : float;
  q : float;
  variant : aco_variant;
  elitist_weight : float;
  tau_min : float;
  tau_max : float;
  stagnation_limit : int;
}

type result = {
  best_tour : int array;
  best_cost : float;
  history : float array;
  pheromone : float array array;
  iterations_run : int;
  stagnated : bool;
}

let default_config = {
  n_ants = 20;
  n_iterations = 200;
  alpha = 1.0;
  beta = 3.0;
  rho = 0.1;
  q = 100.0;
  variant = AntSystem;
  elitist_weight = 5.0;
  tau_min = 0.01;
  tau_max = 10.0;
  stagnation_limit = 30;
}

(* ── Utility ───────────────────────────────────────────────── *)

let dist c1 c2 =
  let dx = c1.x -. c2.x and dy = c1.y -. c2.y in
  sqrt (dx *. dx +. dy *. dy)

let tour_cost cities tour =
  let n = Array.length tour in
  let total = ref 0.0 in
  for i = 0 to n - 1 do
    total := !total +. dist cities.(tour.(i)) cities.(tour.((i + 1) mod n))
  done;
  !total

(* ── City generators ──────────────────────────────────────── *)

let random_cities n =
  Array.init n (fun i ->
    { id = i; x = Random.float 100.0; y = Random.float 100.0;
      name = Printf.sprintf "C%d" i })

let circle_cities n =
  Array.init n (fun i ->
    let angle = 2.0 *. Float.pi *. float_of_int i /. float_of_int n in
    { id = i; x = 50.0 +. 40.0 *. cos angle; y = 50.0 +. 40.0 *. sin angle;
      name = Printf.sprintf "C%d" i })

let cluster_cities n_clusters pts_per =
  let cities = Array.make (n_clusters * pts_per) { id = 0; x = 0.; y = 0.; name = "" } in
  for c = 0 to n_clusters - 1 do
    let cx = 10.0 +. Random.float 80.0 and cy = 10.0 +. Random.float 80.0 in
    for p = 0 to pts_per - 1 do
      let idx = c * pts_per + p in
      cities.(idx) <- {
        id = idx;
        x = cx +. (Random.float 16.0 -. 8.0);
        y = cy +. (Random.float 16.0 -. 8.0);
        name = Printf.sprintf "C%d" idx
      }
    done
  done;
  cities

let grid_cities side =
  let n = side * side in
  Array.init n (fun i ->
    let r = i / side and c = i mod side in
    { id = i;
      x = float_of_int c *. (100.0 /. float_of_int (side - 1));
      y = float_of_int r *. (100.0 /. float_of_int (side - 1));
      name = Printf.sprintf "C%d" i })

(* ── ACO solver ───────────────────────────────────────────── *)

let solve cfg cities =
  let n = Array.length cities in
  if n < 2 then failwith "Need at least 2 cities";
  let d = Array.init n (fun i -> Array.init n (fun j -> dist cities.(i) cities.(j))) in
  let tau = Array.init n (fun _ -> Array.make n 1.0) in
  let eta = Array.init n (fun i ->
    Array.init n (fun j -> if i = j then 0.0 else 1.0 /. d.(i).(j))) in
  let best_tour = ref (Array.init n Fun.id) in
  let best_cost = ref infinity in
  let history = Array.make cfg.n_iterations infinity in
  let stag_count = ref 0 in
  let iter_done = ref 0 in
  let stagnated = ref false in

  for iter = 0 to cfg.n_iterations - 1 do
    if not !stagnated then begin
      iter_done := iter + 1;
      let ant_tours = Array.make cfg.n_ants [||] in
      let ant_costs = Array.make cfg.n_ants infinity in
      for a = 0 to cfg.n_ants - 1 do
        let visited = Array.make n false in
        let tour = Array.make n 0 in
        let start = Random.int n in
        tour.(0) <- start;
        visited.(start) <- true;
        for step = 1 to n - 1 do
          let curr = tour.(step - 1) in
          let probs = Array.make n 0.0 in
          let total = ref 0.0 in
          for j = 0 to n - 1 do
            if not visited.(j) then begin
              let p = (tau.(curr).(j) ** cfg.alpha) *. (eta.(curr).(j) ** cfg.beta) in
              probs.(j) <- p;
              total := !total +. p
            end
          done;
          let r = Random.float !total in
          let cum = ref 0.0 in
          let chosen = ref 0 in
          let found = ref false in
          for j = 0 to n - 1 do
            if not !found && not visited.(j) then begin
              cum := !cum +. probs.(j);
              if !cum >= r then (chosen := j; found := true)
            end
          done;
          tour.(step) <- !chosen;
          visited.(!chosen) <- true
        done;
        ant_tours.(a) <- tour;
        ant_costs.(a) <- tour_cost cities tour
      done;

      let ib = ref 0 in
      for a = 1 to cfg.n_ants - 1 do
        if ant_costs.(a) < ant_costs.(!ib) then ib := a
      done;
      let prev_best = !best_cost in
      if ant_costs.(!ib) < !best_cost then begin
        best_cost := ant_costs.(!ib);
        best_tour := Array.copy ant_tours.(!ib);
        stag_count := 0
      end else
        incr stag_count;
      history.(iter) <- !best_cost;

      for i = 0 to n - 1 do
        for j = 0 to n - 1 do
          tau.(i).(j) <- tau.(i).(j) *. (1.0 -. cfg.rho)
        done
      done;

      let deposit tour cost =
        let contrib = cfg.q /. cost in
        let len = Array.length tour in
        for s = 0 to len - 1 do
          let i = tour.(s) and j = tour.((s + 1) mod len) in
          tau.(i).(j) <- tau.(i).(j) +. contrib;
          tau.(j).(i) <- tau.(j).(i) +. contrib
        done
      in
      (match cfg.variant with
       | AntSystem ->
         for a = 0 to cfg.n_ants - 1 do
           deposit ant_tours.(a) ant_costs.(a)
         done
       | ElitistAS ->
         for a = 0 to cfg.n_ants - 1 do
           deposit ant_tours.(a) ant_costs.(a)
         done;
         let contrib = cfg.elitist_weight *. cfg.q /. !best_cost in
         let len = Array.length !best_tour in
         for s = 0 to len - 1 do
           let i = (!best_tour).(s) and j = (!best_tour).((s + 1) mod len) in
           tau.(i).(j) <- tau.(i).(j) +. contrib;
           tau.(j).(i) <- tau.(j).(i) +. contrib
         done
       | MaxMinAS ->
         deposit ant_tours.(!ib) ant_costs.(!ib);
         for i = 0 to n - 1 do
           for j = 0 to n - 1 do
             tau.(i).(j) <- max cfg.tau_min (min cfg.tau_max tau.(i).(j))
           done
         done);

      if !stag_count >= cfg.stagnation_limit && prev_best = !best_cost then
        stagnated := true
    end
  done;
  { best_tour = !best_tour; best_cost = !best_cost;
    history = Array.sub history 0 !iter_done;
    pheromone = tau; iterations_run = !iter_done; stagnated = !stagnated }

(* ── Visualization ─────────────────────────────────────────── *)

let show_tour cities tour =
  let n = Array.length tour in
  Printf.printf "\n  Tour: ";
  Array.iter (fun i -> Printf.printf "%s -> " cities.(i).name) tour;
  Printf.printf "%s\n" cities.(tour.(0)).name;
  Printf.printf "  Cost: %.2f  (%d cities)\n\n" (tour_cost cities tour) n

let show_convergence history =
  let n = Array.length history in
  if n = 0 then (print_endline "  No history."; ())
  else begin
    let mn = Array.fold_left min infinity history in
    let mx = Array.fold_left max neg_infinity history in
    let h = 12 in
    let w = min 60 n in
    let step = max 1 (n / w) in
    Printf.printf "\n  Convergence (%d iterations, best=%.2f)\n" n mn;
    print_string "  ";
    for _ = 0 to w + 1 do print_char '-' done;
    print_newline ();
    for row = h - 1 downto 0 do
      let thresh = mn +. (mx -. mn) *. float_of_int row /. float_of_int (h - 1) in
      Printf.printf "  |";
      for col = 0 to w - 1 do
        let idx = col * step in
        if idx < n && history.(idx) >= thresh then print_char '*'
        else print_char ' '
      done;
      Printf.printf "| %.1f\n" thresh
    done;
    print_string "  ";
    for _ = 0 to w + 1 do print_char '-' done;
    Printf.printf "\n  0%s%d\n\n"
      (String.make (w / 2) ' ') (n - 1)
  end

let show_pheromone_heatmap pher =
  let n = Array.length pher in
  if n > 20 then
    Printf.printf "  (Pheromone heatmap skipped: %d cities > 20 limit)\n\n" n
  else begin
    let mx = ref 0.0 in
    Array.iter (Array.iter (fun v -> if v > !mx then mx := v)) pher;
    let chars = [| ' '; '.'; 'o'; 'O'; '#' |] in
    Printf.printf "\n  Pheromone Heatmap (max=%.2f)\n    " !mx;
    for j = 0 to n - 1 do Printf.printf "%2d" j done;
    print_newline ();
    for i = 0 to n - 1 do
      Printf.printf "  %2d " i;
      for j = 0 to n - 1 do
        let level = int_of_float (pher.(i).(j) /. !mx *. 4.0) in
        let level = min 4 (max 0 level) in
        Printf.printf "%c " chars.(level)
      done;
      print_newline ()
    done;
    print_endline ""
  end

let show_city_map cities _tour =
  let w = 60 and h = 25 in
  let grid = Array.init h (fun _ -> Array.make w ' ') in
  let n = Array.length cities in
  for i = 0 to n - 1 do
    let c = cities.(i) in
    let cx = int_of_float (c.x /. 100.0 *. float_of_int (w - 1)) in
    let cy = int_of_float (c.y /. 100.0 *. float_of_int (h - 1)) in
    let cx = max 0 (min (w - 1) cx) and cy = max 0 (min (h - 1) cy) in
    grid.(h - 1 - cy).(cx) <- Char.chr (if i < 26 then Char.code 'A' + i
                                         else if i < 36 then Char.code '0' + i - 26
                                         else Char.code '*')
  done;
  Printf.printf "\n  City Map (%d cities)\n" n;
  print_string "  +";
  for _ = 0 to w - 1 do print_char '-' done;
  print_endline "+";
  Array.iter (fun row ->
    print_string "  |";
    Array.iter print_char row;
    print_endline "|"
  ) grid;
  print_string "  +";
  for _ = 0 to w - 1 do print_char '-' done;
  print_endline "+\n"

(* ── Nearest-Neighbor baseline ─────────────────────────────── *)

let nn_tour cities =
  let n = Array.length cities in
  let visited = Array.make n false in
  let tour = Array.make n 0 in
  visited.(0) <- true;
  for step = 1 to n - 1 do
    let curr = tour.(step - 1) in
    let best_j = ref (-1) in
    let best_d = ref infinity in
    for j = 0 to n - 1 do
      if not visited.(j) then begin
        let d = dist cities.(curr) cities.(j) in
        if d < !best_d then (best_d := d; best_j := j)
      end
    done;
    tour.(step) <- !best_j;
    visited.(!best_j) <- true
  done;
  tour

(* ── REPL ──────────────────────────────────────────────────── *)

let variant_name = function
  | AntSystem -> "Ant System"
  | MaxMinAS -> "Max-Min AS"
  | ElitistAS -> "Elitist AS"

let show_config cfg =
  Printf.printf "  +-- ACO Configuration -------------------+\n";
  Printf.printf "  | Variant:     %-28s|\n" (variant_name cfg.variant);
  Printf.printf "  | Ants:        %-28d|\n" cfg.n_ants;
  Printf.printf "  | Iterations:  %-28d|\n" cfg.n_iterations;
  Printf.printf "  | Alpha:       %-28.2f|\n" cfg.alpha;
  Printf.printf "  | Beta:        %-28.2f|\n" cfg.beta;
  Printf.printf "  | Rho (evap):  %-28.2f|\n" cfg.rho;
  Printf.printf "  | Q:           %-28.2f|\n" cfg.q;
  Printf.printf "  | Stagnation:  %-28d|\n" cfg.stagnation_limit;
  Printf.printf "  +----------------------------------------+\n\n"

let print_help () =
  print_endline "";
  print_endline "  === Ant Colony Optimization Simulator ===";
  print_endline "";
  print_endline "  CITIES";
  print_endline "    random <n>          Random cities";
  print_endline "    circle <n>          Cities on a circle";
  print_endline "    cluster <k> <n>     k clusters, n pts each";
  print_endline "    grid <side>         side x side grid";
  print_endline "";
  print_endline "  SOLVE";
  print_endline "    run                 Solve with current config";
  print_endline "    compare             Run all 3 variants + NN baseline";
  print_endline "";
  print_endline "  CONFIGURE";
  print_endline "    set <param> <val>   Set parameter";
  print_endline "      params: ants, iter, alpha, beta, rho, q, stag";
  print_endline "    variant <as|mmas|eas>  Set ACO variant";
  print_endline "    config              Show current configuration";
  print_endline "";
  print_endline "  VISUALIZE";
  print_endline "    map                 Show city map";
  print_endline "    tour                Show last best tour";
  print_endline "    convergence         Show convergence chart";
  print_endline "    pheromone           Show pheromone heatmap";
  print_endline "";
  print_endline "  OTHER";
  print_endline "    demo                Run a full demo";
  print_endline "    help                Show this help";
  print_endline "    quit                Exit";
  print_endline ""

let () =
  print_endline "\n  Ant Colony Optimization Simulator";
  print_endline "  =================================";
  print_endline "  Type 'help' for commands, 'demo' for a quick tour.\n";

  let cfg = ref default_config in
  let cities = ref (random_cities 15) in
  let last_result = ref None in

  let do_run c cs =
    Printf.printf "  Running %s with %d ants, %d iterations on %d cities...\n"
      (variant_name c.variant) c.n_ants c.n_iterations (Array.length cs);
    let r = solve c cs in
    Printf.printf "  Done! Best cost: %.2f (%d iterations%s)\n"
      r.best_cost r.iterations_run
      (if r.stagnated then ", stagnated" else "");
    last_result := Some (cs, r);
    r
  in

  let running = ref true in
  while !running do
    print_string "  ACO> ";
    flush stdout;
    match input_line stdin |> String.trim |> String.split_on_char ' ' with
    | exception End_of_file -> running := false
    | ["quit"] | ["exit"] -> running := false
    | ["help"] -> print_help ()
    | ["config"] -> show_config !cfg

    | ["random"; n] ->
      let n = int_of_string n in
      cities := random_cities n;
      Printf.printf "  Generated %d random cities.\n" n

    | ["circle"; n] ->
      let n = int_of_string n in
      cities := circle_cities n;
      Printf.printf "  Generated %d cities on a circle.\n" n

    | ["cluster"; k; n] ->
      let k = int_of_string k and n = int_of_string n in
      cities := cluster_cities k n;
      Printf.printf "  Generated %d cities in %d clusters.\n" (k * n) k

    | ["grid"; s] ->
      let s = int_of_string s in
      cities := grid_cities s;
      Printf.printf "  Generated %d cities in %dx%d grid.\n" (s * s) s s

    | ["variant"; v] ->
      let var = match v with
        | "as" -> AntSystem | "mmas" -> MaxMinAS | "eas" -> ElitistAS
        | _ -> Printf.printf "  Unknown variant (as, mmas, eas).\n"; !cfg.variant
      in
      cfg := { !cfg with variant = var };
      Printf.printf "  Variant: %s\n" (variant_name !cfg.variant)

    | ["set"; p; v] ->
      (match p with
       | "ants" -> cfg := { !cfg with n_ants = int_of_string v }
       | "iter" -> cfg := { !cfg with n_iterations = int_of_string v }
       | "alpha" -> cfg := { !cfg with alpha = float_of_string v }
       | "beta" -> cfg := { !cfg with beta = float_of_string v }
       | "rho" -> cfg := { !cfg with rho = float_of_string v }
       | "q" -> cfg := { !cfg with q = float_of_string v }
       | "stag" -> cfg := { !cfg with stagnation_limit = int_of_string v }
       | _ -> Printf.printf "  Unknown param: %s\n" p);
      Printf.printf "  Set %s = %s\n" p v

    | ["run"] ->
      ignore (do_run !cfg !cities)

    | ["compare"] ->
      Printf.printf "\n  +-- Variant Comparison --------------------+\n";
      let nn = nn_tour !cities in
      let nn_c = tour_cost !cities nn in
      Printf.printf "  | NN Baseline:   cost = %-20.2f|\n" nn_c;
      let variants = [AntSystem; MaxMinAS; ElitistAS] in
      List.iter (fun v ->
        let c = { !cfg with variant = v } in
        let r = solve c !cities in
        let improv = (nn_c -. r.best_cost) /. nn_c *. 100.0 in
        Printf.printf "  | %-14s cost = %-8.2f (%+.1f%% vs NN)|\n"
          (variant_name v) r.best_cost improv;
        if v = !cfg.variant then last_result := Some (!cities, r)
      ) variants;
      Printf.printf "  +--------------------------------------------+\n\n"

    | ["map"] -> show_city_map !cities (match !last_result with Some (_, r) -> r.best_tour | None -> [||])
    | ["tour"] ->
      (match !last_result with
       | Some (cs, r) -> show_tour cs r.best_tour
       | None -> print_endline "  No tour yet. Run 'run' first.")
    | ["convergence"] ->
      (match !last_result with
       | Some (_, r) -> show_convergence r.history
       | None -> print_endline "  No history. Run 'run' first.")
    | ["pheromone"] ->
      (match !last_result with
       | Some (_, r) -> show_pheromone_heatmap r.pheromone
       | None -> print_endline "  No pheromone data. Run 'run' first.")

    | ["demo"] ->
      print_endline "\n  === ACO Demo ===\n";
      print_endline "  Step 1: Generate 12 clustered cities (3 clusters x 4 pts)";
      cities := cluster_cities 3 4;
      show_city_map !cities [||];

      print_endline "  Step 2: Nearest-neighbor baseline";
      let nn = nn_tour !cities in
      Printf.printf "  NN cost: %.2f\n\n" (tour_cost !cities nn);

      print_endline "  Step 3: Run Ant System";
      cfg := { default_config with n_ants = 15; n_iterations = 100 };
      let r = do_run !cfg !cities in
      show_tour !cities r.best_tour;
      show_convergence r.history;

      print_endline "  Step 4: Compare all variants";
      let variants = [AntSystem; MaxMinAS; ElitistAS] in
      List.iter (fun v ->
        let c = { !cfg with variant = v } in
        let r = solve c !cities in
        Printf.printf "  %-14s -> %.2f\n" (variant_name v) r.best_cost
      ) variants;
      print_endline "\n  === Demo complete! ===\n"

    | [""] -> ()
    | tokens ->
      Printf.printf "  Unknown command: %s (type 'help')\n"
        (String.concat " " tokens)
  done;
  print_endline "  Goodbye!"
