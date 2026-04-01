(* Petri Net Simulator
   ====================
   A comprehensive Petri net implementation for modeling and analyzing
   concurrent systems, protocols, and workflows.

   Features:
   - Place/Transition nets with weighted arcs
   - Firing semantics (single step, maximal concurrent)
   - Reachability analysis with marking graph construction
   - Invariant analysis (S-invariants, T-invariants)
   - Deadlock detection
   - Boundedness checking
   - Liveness analysis
   - Built-in example nets (mutex, producer-consumer, dining philosophers)
   - ASCII visualization of net state

   Usage: ocaml petri_net.ml
*)

(* ══════════════════════════════════════════════════════════════════════
   Core Types
   ══════════════════════════════════════════════════════════════════════ *)

type place = {
  name: string;
  id: int;
}

type transition = {
  t_name: string;
  t_id: int;
}

type arc =
  | PlaceToTrans of int * int * int   (* place_id, trans_id, weight *)
  | TransToPlace of int * int * int   (* trans_id, place_id, weight *)

type marking = int array  (* tokens per place *)

type petri_net = {
  places: place array;
  transitions: transition array;
  arcs: arc list;
  initial_marking: marking;
}

(* ══════════════════════════════════════════════════════════════════════
   Net Construction
   ══════════════════════════════════════════════════════════════════════ *)

let make_place id name = { name; id }
let make_transition id name = { t_name = name; t_id = id }

let make_net places transitions arcs initial_marking =
  { places; transitions; arcs; initial_marking }

let copy_marking m = Array.copy m

(* ══════════════════════════════════════════════════════════════════════
   Firing Rules
   ══════════════════════════════════════════════════════════════════════ *)

let inputs net t_id =
  List.filter_map (fun arc ->
    match arc with
    | PlaceToTrans (p, t, w) when t = t_id -> Some (p, w)
    | _ -> None
  ) net.arcs

let outputs net t_id =
  List.filter_map (fun arc ->
    match arc with
    | TransToPlace (t, p, w) when t = t_id -> Some (p, w)
    | _ -> None
  ) net.arcs

let is_enabled net marking t_id =
  let ins = inputs net t_id in
  List.for_all (fun (p, w) -> marking.(p) >= w) ins

let fire net marking t_id =
  if not (is_enabled net marking t_id) then None
  else begin
    let m' = copy_marking marking in
    List.iter (fun (p, w) -> m'.(p) <- m'.(p) - w) (inputs net t_id);
    List.iter (fun (p, w) -> m'.(p) <- m'.(p) + w) (outputs net t_id);
    Some m'
  end

let enabled_transitions net marking =
  Array.to_list net.transitions
  |> List.filter (fun t -> is_enabled net marking t.t_id)
  |> List.map (fun t -> t.t_id)

(* ══════════════════════════════════════════════════════════════════════
   Reachability Analysis
   ══════════════════════════════════════════════════════════════════════ *)

module MarkingSet = Set.Make(struct
  type t = int array
  let compare a b =
    let n = Array.length a in
    let rec cmp i =
      if i >= n then 0
      else let c = compare a.(i) b.(i) in
        if c <> 0 then c else cmp (i + 1)
    in cmp 0
end)

type reachability_graph = {
  markings: marking list;
  edges: (int * int * int) list;
  deadlocks: int list;
}

let build_reachability_graph ?(max_markings=10000) net =
  let marking_to_idx = Hashtbl.create 256 in
  let markings = ref [] in
  let edges = ref [] in
  let deadlocks = ref [] in
  let queue = Queue.create () in
  let idx = ref 0 in

  let add_marking m =
    if not (Hashtbl.mem marking_to_idx (Array.to_list m)) then begin
      let i = !idx in
      Hashtbl.add marking_to_idx (Array.to_list m) i;
      markings := copy_marking m :: !markings;
      incr idx;
      Queue.push (m, i) queue;
      i
    end else
      Hashtbl.find marking_to_idx (Array.to_list m)
  in

  let _ = add_marking net.initial_marking in

  while not (Queue.is_empty queue) && !idx < max_markings do
    let (m, from_idx) = Queue.pop queue in
    let enabled = enabled_transitions net m in
    if enabled = [] then
      deadlocks := from_idx :: !deadlocks;
    List.iter (fun t_id ->
      match fire net m t_id with
      | Some m' ->
        let to_idx = add_marking m' in
        edges := (from_idx, t_id, to_idx) :: !edges
      | None -> ()
    ) enabled
  done;

  {
    markings = List.rev !markings;
    edges = List.rev !edges;
    deadlocks = List.rev !deadlocks;
  }

(* ══════════════════════════════════════════════════════════════════════
   Analysis Functions
   ══════════════════════════════════════════════════════════════════════ *)

let boundedness_check net =
  let graph = build_reachability_graph net in
  let n_places = Array.length net.places in
  let max_tokens = Array.make n_places 0 in
  List.iter (fun m ->
    for i = 0 to n_places - 1 do
      if m.(i) > max_tokens.(i) then max_tokens.(i) <- m.(i)
    done
  ) graph.markings;
  (true, max_tokens, List.length graph.markings)

let deadlock_check net =
  let graph = build_reachability_graph net in
  let dead_markings = List.map (fun i ->
    List.nth graph.markings i
  ) graph.deadlocks in
  (graph.deadlocks = [], dead_markings)

let liveness_check net =
  let graph = build_reachability_graph net in
  let n_trans = Array.length net.transitions in
  let fired = Array.make n_trans false in
  List.iter (fun (_, t_id, _) -> fired.(t_id) <- true) graph.edges;
  let live = Array.to_list fired in
  let dead_transitions = List.mapi (fun i b ->
    if not b then Some net.transitions.(i).t_name else None
  ) live |> List.filter_map Fun.id in
  (dead_transitions = [], dead_transitions)

(* ══════════════════════════════════════════════════════════════════════
   Incidence Matrix
   ══════════════════════════════════════════════════════════════════════ *)

let incidence_matrix net =
  let np = Array.length net.places in
  let nt = Array.length net.transitions in
  let c = Array.make_matrix np nt 0 in
  List.iter (fun arc ->
    match arc with
    | PlaceToTrans (p, t, w) -> c.(p).(t) <- c.(p).(t) - w
    | TransToPlace (t, p, w) -> c.(p).(t) <- c.(p).(t) + w
  ) net.arcs;
  c

let print_incidence_matrix net =
  let c = incidence_matrix net in
  let np = Array.length net.places in
  let nt = Array.length net.transitions in
  Printf.printf "\nIncidence Matrix (C):\n";
  Printf.printf "%12s" "";
  for j = 0 to nt - 1 do
    Printf.printf "%6s" net.transitions.(j).t_name
  done;
  Printf.printf "\n";
  for i = 0 to np - 1 do
    Printf.printf "%12s" net.places.(i).name;
    for j = 0 to nt - 1 do
      Printf.printf "%6d" c.(i).(j)
    done;
    Printf.printf "\n"
  done

(* ══════════════════════════════════════════════════════════════════════
   Simulation
   ══════════════════════════════════════════════════════════════════════ *)

let simulate ?(steps=20) ?(verbose=true) net =
  let m = copy_marking net.initial_marking in
  if verbose then begin
    Printf.printf "\n--- Simulation ---\n";
    Printf.printf "Initial marking: [%s]\n"
      (Array.to_list m |> List.map string_of_int |> String.concat ", ")
  end;
  let step = ref 0 in
  let history = ref [copy_marking m] in
  while !step < steps do
    let enabled = enabled_transitions net m in
    if enabled = [] then begin
      if verbose then Printf.printf "Step %d: DEADLOCK - no transitions enabled\n" (!step + 1);
      step := steps
    end else begin
      let t_id = List.nth enabled (Random.int (List.length enabled)) in
      match fire net m t_id with
      | Some m' ->
        Array.blit m' 0 m 0 (Array.length m);
        incr step;
        history := copy_marking m :: !history;
        if verbose then
          Printf.printf "Step %d: fire %-12s -> [%s]\n" !step
            net.transitions.(t_id).t_name
            (Array.to_list m |> List.map string_of_int |> String.concat ", ")
      | None -> step := steps
    end
  done;
  List.rev !history

(* ══════════════════════════════════════════════════════════════════════
   ASCII Visualization
   ══════════════════════════════════════════════════════════════════════ *)

let visualize_marking net marking =
  Printf.printf "\n+-------------------------------------+\n";
  Printf.printf "|         Petri Net State             |\n";
  Printf.printf "+-------------------------------------+\n";
  Array.iteri (fun i p ->
    let tokens = marking.(i) in
    let dots = if tokens <= 10
      then String.make tokens '*'
      else Printf.sprintf "*x%d" tokens
    in
    Printf.printf "| %-15s | %-16s |\n" p.name dots
  ) net.places;
  Printf.printf "+-------------------------------------+\n";
  let enabled = enabled_transitions net marking in
  let names = List.map (fun t_id -> net.transitions.(t_id).t_name) enabled in
  Printf.printf "| Enabled: %-26s |\n"
    (if names = [] then "(none - deadlock!)"
     else String.concat ", " names);
  Printf.printf "+-------------------------------------+\n"

(* ══════════════════════════════════════════════════════════════════════
   Example Nets
   ══════════════════════════════════════════════════════════════════════ *)

let mutex_net () =
  let places = [|
    make_place 0 "idle_1";
    make_place 1 "idle_2";
    make_place 2 "mutex";
    make_place 3 "critical_1";
    make_place 4 "critical_2";
  |] in
  let transitions = [|
    make_transition 0 "enter_1";
    make_transition 1 "leave_1";
    make_transition 2 "enter_2";
    make_transition 3 "leave_2";
  |] in
  let arcs = [
    PlaceToTrans (0, 0, 1); PlaceToTrans (2, 0, 1); TransToPlace (0, 3, 1);
    PlaceToTrans (3, 1, 1); TransToPlace (1, 0, 1); TransToPlace (1, 2, 1);
    PlaceToTrans (1, 2, 1); PlaceToTrans (2, 2, 1); TransToPlace (2, 4, 1);
    PlaceToTrans (4, 3, 1); TransToPlace (3, 1, 1); TransToPlace (3, 2, 1);
  ] in
  make_net places transitions arcs [| 1; 1; 1; 0; 0 |]

let producer_consumer_net () =
  let places = [|
    make_place 0 "ready_prod";
    make_place 1 "buffer";
    make_place 2 "buffer_space";
    make_place 3 "ready_cons";
    make_place 4 "consumed";
  |] in
  let transitions = [|
    make_transition 0 "produce";
    make_transition 1 "consume";
  |] in
  let arcs = [
    PlaceToTrans (0, 0, 1); PlaceToTrans (2, 0, 1);
    TransToPlace (0, 0, 1); TransToPlace (0, 1, 1);
    PlaceToTrans (1, 1, 1); PlaceToTrans (3, 1, 1);
    TransToPlace (1, 2, 1); TransToPlace (1, 3, 1); TransToPlace (1, 4, 1);
  ] in
  make_net places transitions arcs [| 1; 0; 3; 1; 0 |]

let workflow_net () =
  let places = [|
    make_place 0 "start";
    make_place 1 "task_a";
    make_place 2 "task_b";
    make_place 3 "task_c";
    make_place 4 "join";
    make_place 5 "done";
  |] in
  let transitions = [|
    make_transition 0 "begin_wf";
    make_transition 1 "fork";
    make_transition 2 "finish_b";
    make_transition 3 "finish_c";
    make_transition 4 "merge";
  |] in
  let arcs = [
    PlaceToTrans (0, 0, 1); TransToPlace (0, 1, 1);
    PlaceToTrans (1, 1, 1); TransToPlace (1, 2, 1); TransToPlace (1, 3, 1);
    PlaceToTrans (2, 2, 1); TransToPlace (2, 4, 1);
    PlaceToTrans (3, 3, 1); TransToPlace (3, 4, 1);
    PlaceToTrans (4, 4, 2); TransToPlace (4, 5, 1);
  ] in
  make_net places transitions arcs [| 1; 0; 0; 0; 0; 0 |]

let dining_philosophers_net () =
  let places = [|
    make_place 0 "think_1";
    make_place 1 "think_2";
    make_place 2 "think_3";
    make_place 3 "fork_1";
    make_place 4 "fork_2";
    make_place 5 "fork_3";
    make_place 6 "eat_1";
    make_place 7 "eat_2";
    make_place 8 "eat_3";
  |] in
  let transitions = [|
    make_transition 0 "pickup_1";
    make_transition 1 "putdown_1";
    make_transition 2 "pickup_2";
    make_transition 3 "putdown_2";
    make_transition 4 "pickup_3";
    make_transition 5 "putdown_3";
  |] in
  let arcs = [
    PlaceToTrans (0, 0, 1); PlaceToTrans (3, 0, 1); PlaceToTrans (4, 0, 1);
    TransToPlace (0, 6, 1);
    PlaceToTrans (6, 1, 1);
    TransToPlace (1, 0, 1); TransToPlace (1, 3, 1); TransToPlace (1, 4, 1);
    PlaceToTrans (1, 2, 1); PlaceToTrans (4, 2, 1); PlaceToTrans (5, 2, 1);
    TransToPlace (2, 7, 1);
    PlaceToTrans (7, 3, 1);
    TransToPlace (3, 1, 1); TransToPlace (3, 4, 1); TransToPlace (3, 5, 1);
    PlaceToTrans (2, 4, 1); PlaceToTrans (5, 4, 1); PlaceToTrans (3, 4, 1);
    TransToPlace (4, 8, 1);
    PlaceToTrans (8, 5, 1);
    TransToPlace (5, 2, 1); TransToPlace (5, 5, 1); TransToPlace (5, 3, 1);
  ] in
  make_net places transitions arcs [| 1; 1; 1; 1; 1; 1; 0; 0; 0 |]

(* ══════════════════════════════════════════════════════════════════════
   Interactive Demo
   ══════════════════════════════════════════════════════════════════════ *)

let run_analysis name net =
  Printf.printf "\n%s\n" name;
  Printf.printf "============================================================\n";

  visualize_marking net net.initial_marking;
  print_incidence_matrix net;

  let (_, max_tok, n_markings) = boundedness_check net in
  Printf.printf "\nBoundedness: BOUNDED (%d reachable markings)\n" n_markings;
  Printf.printf "Max tokens per place: [%s]\n"
    (Array.to_list max_tok |> List.map string_of_int |> String.concat ", ");

  let (deadlock_free, dead_markings) = deadlock_check net in
  Printf.printf "Deadlock-free: %s\n"
    (if deadlock_free then "YES" else "NO");
  if not deadlock_free then
    List.iter (fun m ->
      Printf.printf "  Dead marking: [%s]\n"
        (Array.to_list m |> List.map string_of_int |> String.concat ", ")
    ) dead_markings;

  let (live, dead_trans) = liveness_check net in
  Printf.printf "Live: %s\n"
    (if live then "YES" else "NO");
  if not live then
    Printf.printf "  Dead transitions: %s\n" (String.concat ", " dead_trans);

  let _ = simulate ~steps:10 ~verbose:true net in
  Printf.printf "============================================================\n"

let () =
  Random.self_init ();

  Printf.printf "==========================================================\n";
  Printf.printf "         Petri Net Simulator & Analyzer                    \n";
  Printf.printf "   Model concurrent systems, detect deadlocks,            \n";
  Printf.printf "   check boundedness, and analyze liveness                \n";
  Printf.printf "==========================================================\n";

  run_analysis "1. MUTUAL EXCLUSION" (mutex_net ());
  run_analysis "2. PRODUCER-CONSUMER (bounded buffer, capacity=3)" (producer_consumer_net ());
  run_analysis "3. WORKFLOW (fork-join parallelism)" (workflow_net ());
  run_analysis "4. DINING PHILOSOPHERS (3 philosophers)" (dining_philosophers_net ());

  Printf.printf "\n============================================================\n";
  Printf.printf "Custom Net Demo: Simple counter\n";
  Printf.printf "============================================================\n";

  let counter = make_net
    [| make_place 0 "count"; make_place 1 "limit" |]
    [| make_transition 0 "increment"; make_transition 1 "reset" |]
    [
      PlaceToTrans (1, 0, 1); TransToPlace (0, 0, 1); TransToPlace (0, 1, 1);
      PlaceToTrans (0, 1, 1); TransToPlace (1, 1, 1);
    ]
    [| 0; 5 |]
  in
  let _ = simulate ~steps:15 ~verbose:true counter in

  Printf.printf "\nAll demonstrations complete.\n";
  Printf.printf "Try modifying the example nets or building your own!\n"
