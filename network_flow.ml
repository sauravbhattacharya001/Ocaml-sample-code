(* ================================================================
   Network Flow Algorithms
   ================================================================
   - Edmonds-Karp (BFS-based Ford-Fulkerson) max flow O(VE²)
   - Min-cut extraction from max flow residual graph
   - Bipartite matching via max flow reduction
   - Multi-source/multi-sink max flow
   - Flow decomposition into paths
   - Minimum cost max flow (Bellman-Ford based)
   ================================================================ *)

(* ---------- Flow Network representation ---------- *)

module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

type edge = {
  dst: int;
  cap: int;
  mutable flow: int;
  rev_idx: int;  (* index of reverse edge in dst's adjacency list *)
}

type network = {
  n: int;
  adj: edge list array;  (* mutable adjacency lists *)
}

(* We use a mutable array of mutable lists for efficiency *)
type flow_network = {
  num_nodes: int;
  mutable edges: (int * int * int * int) list;
  (* (src, dst, capacity, cost) — cost=0 for basic max flow *)
}

let create_flow_network n = { num_nodes = n; edges = [] }

let add_edge fn src dst cap =
  fn.edges <- (src, dst, cap, 0) :: fn.edges

let add_edge_with_cost fn src dst cap cost =
  fn.edges <- (src, dst, cap, cost) :: fn.edges

(* Build internal adjacency structure with reverse edges *)
type internal_net = {
  size: int;
  adj_list: edge array array;  (* adj_list.(v) = array of edges from v *)
}

(* Build the residual graph *)
let build_internal fn =
  let n = fn.num_nodes in
  (* First pass: count edges per node *)
  let counts = Array.make n 0 in
  List.iter (fun (s, d, _, _) ->
    counts.(s) <- counts.(s) + 1;
    counts.(d) <- counts.(d) + 1  (* reverse edge *)
  ) fn.edges;
  (* Allocate arrays *)
  let adj = Array.init n (fun i -> Array.make counts.(i) { dst=0; cap=0; flow=0; rev_idx=0 }) in
  let pos = Array.make n 0 in
  (* Second pass: fill edges *)
  List.iter (fun (s, d, c, _) ->
    let si = pos.(s) in
    let di = pos.(d) in
    adj.(s).(si) <- { dst = d; cap = c; flow = 0; rev_idx = di };
    adj.(d).(di) <- { dst = s; cap = 0; flow = 0; rev_idx = si };  (* reverse *)
    pos.(s) <- si + 1;
    pos.(d) <- di + 1
  ) fn.edges;
  { size = n; adj_list = adj }

(* ---------- BFS for Edmonds-Karp ---------- *)

let bfs (net : internal_net) source sink =
  let parent = Array.make net.size (-1, -1) in  (* (node, edge_index) *)
  let visited = Array.make net.size false in
  let q = Queue.create () in
  visited.(source) <- true;
  Queue.push source q;
  let found = ref false in
  while not (Queue.is_empty q) && not !found do
    let u = Queue.pop q in
    Array.iteri (fun i e ->
      if not visited.(e.dst) && e.cap - e.flow > 0 then begin
        visited.(e.dst) <- true;
        parent.(e.dst) <- (u, i);
        if e.dst = sink then found := true
        else Queue.push e.dst q
      end
    ) net.adj_list.(u)
  done;
  if !found then Some parent else None

(* ---------- Edmonds-Karp Max Flow ---------- *)

let edmonds_karp_internal (net : internal_net) source sink =
  let total_flow = ref 0 in
  let continue = ref true in
  while !continue do
    match bfs net source sink with
    | None -> continue := false
    | Some parent ->
      (* Find bottleneck *)
      let bottleneck = ref max_int in
      let v = ref sink in
      while !v <> source do
        let (u, ei) = parent.(!v) in
        let e = net.adj_list.(u).(ei) in
        bottleneck := min !bottleneck (e.cap - e.flow);
        v := u
      done;
      (* Update flow *)
      let b = !bottleneck in
      v := sink;
      while !v <> source do
        let (u, ei) = parent.(!v) in
        let e = net.adj_list.(u).(ei) in
        e.flow <- e.flow + b;
        let rev = net.adj_list.(!v).(e.rev_idx) in
        rev.flow <- rev.flow - b;
        v := u
      done;
      total_flow := !total_flow + b
  done;
  !total_flow

let max_flow fn source sink =
  let net = build_internal fn in
  edmonds_karp_internal net source sink

(* ---------- Min-Cut ---------- *)

type min_cut_result = {
  max_flow_value: int;
  s_side: int list;   (* nodes reachable from source in residual *)
  t_side: int list;   (* remaining nodes *)
  cut_edges: (int * int * int) list;  (* (src, dst, capacity) of cut edges *)
}

let min_cut fn source sink =
  let net = build_internal fn in
  let flow_val = edmonds_karp_internal net source sink in
  (* BFS on residual graph to find S-side *)
  let visited = Array.make net.size false in
  let q = Queue.create () in
  visited.(source) <- true;
  Queue.push source q;
  while not (Queue.is_empty q) do
    let u = Queue.pop q in
    Array.iter (fun e ->
      if not visited.(e.dst) && e.cap - e.flow > 0 then begin
        visited.(e.dst) <- true;
        Queue.push e.dst q
      end
    ) net.adj_list.(u)
  done;
  let s_side = ref [] in
  let t_side = ref [] in
  for i = 0 to net.size - 1 do
    if visited.(i) then s_side := i :: !s_side
    else t_side := i :: !t_side
  done;
  (* Find cut edges: edges from S to T with positive capacity *)
  let cut = ref [] in
  Array.iteri (fun u _ ->
    if visited.(u) then
      Array.iter (fun e ->
        if not visited.(e.dst) && e.cap > 0 then
          cut := (u, e.dst, e.cap) :: !cut
      ) net.adj_list.(u)
  ) net.adj_list;
  { max_flow_value = flow_val;
    s_side = List.rev !s_side;
    t_side = List.rev !t_side;
    cut_edges = List.rev !cut }

(* ---------- Bipartite Matching ---------- *)

type matching_result = {
  matching_size: int;
  pairs: (int * int) list;  (* (left_node, right_node) in original indexing *)
}

(* left_nodes: 0..left_n-1, right_nodes: 0..right_n-1
   edges: (left_idx, right_idx) list *)
let bipartite_matching left_n right_n edges =
  (* Build flow network:
     source = left_n + right_n
     sink = left_n + right_n + 1
     left nodes: 0..left_n-1
     right nodes: left_n..left_n+right_n-1 *)
  let source = left_n + right_n in
  let sink = source + 1 in
  let fn = create_flow_network (sink + 1) in
  (* Source to left *)
  for i = 0 to left_n - 1 do
    add_edge fn source i 1
  done;
  (* Right to sink *)
  for j = 0 to right_n - 1 do
    add_edge fn (left_n + j) sink 1
  done;
  (* Left to right *)
  List.iter (fun (l, r) ->
    add_edge fn l (left_n + r) 1
  ) edges;
  let net = build_internal fn in
  let flow_val = edmonds_karp_internal net source sink in
  (* Extract matching *)
  let pairs = ref [] in
  for l = 0 to left_n - 1 do
    Array.iter (fun e ->
      if e.dst >= left_n && e.dst < left_n + right_n && e.flow = 1 then
        pairs := (l, e.dst - left_n) :: !pairs
    ) net.adj_list.(l)
  done;
  { matching_size = flow_val; pairs = List.rev !pairs }

(* ---------- Multi-source/multi-sink ---------- *)

let multi_source_sink_max_flow fn sources sinks =
  (* Add super-source and super-sink *)
  let super_s = fn.num_nodes in
  let super_t = super_s + 1 in
  let fn2 = create_flow_network (super_t + 1) in
  fn2.edges <- fn.edges;
  List.iter (fun (s, cap) -> add_edge fn2 super_s s cap) sources;
  List.iter (fun (t, cap) -> add_edge fn2 t super_t cap) sinks;
  max_flow fn2 super_s super_t

(* ---------- Flow Decomposition ---------- *)

type flow_path = {
  path: int list;
  path_flow: int;
}

let decompose_flow fn source sink =
  let net = build_internal fn in
  let _ = edmonds_karp_internal net source sink in
  (* Repeatedly find paths with positive flow via DFS *)
  let paths = ref [] in
  let continue = ref true in
  while !continue do
    (* DFS to find a path from source to sink with positive flow *)
    let visited = Array.make net.size false in
    let stack = Stack.create () in
    Stack.push (source, [source], max_int) stack;
    let found = ref None in
    while not (Stack.is_empty stack) && Option.is_none !found do
      let (u, path, bottleneck) = Stack.pop stack in
      if u = sink then
        found := Some (List.rev path, bottleneck)
      else if not visited.(u) then begin
        visited.(u) <- true;
        Array.iter (fun e ->
          if not visited.(e.dst) && e.flow > 0 then
            Stack.push (e.dst, e.dst :: path, min bottleneck e.flow) stack
        ) net.adj_list.(u)
      end
    done;
    match !found with
    | None -> continue := false
    | Some (path, bottleneck) ->
      (* Subtract flow along path *)
      let rec subtract = function
        | u :: v :: rest ->
          Array.iter (fun e ->
            if e.dst = v && e.flow >= bottleneck then
              e.flow <- e.flow - bottleneck
          ) net.adj_list.(u);
          subtract (v :: rest)
        | _ -> ()
      in
      subtract path;
      paths := { path; path_flow = bottleneck } :: !paths
  done;
  List.rev !paths

(* ---------- Minimum Cost Max Flow (MCMF) ---------- *)

type cost_edge = {
  c_dst: int;
  c_cap: int;
  mutable c_flow: int;
  c_cost: int;
  c_rev_idx: int;
}

type cost_network = {
  c_size: int;
  c_adj: cost_edge array array;
}

let build_cost_internal fn =
  let n = fn.num_nodes in
  let counts = Array.make n 0 in
  List.iter (fun (s, d, _, _) ->
    counts.(s) <- counts.(s) + 1;
    counts.(d) <- counts.(d) + 1
  ) fn.edges;
  let adj = Array.init n (fun i ->
    Array.make counts.(i) { c_dst=0; c_cap=0; c_flow=0; c_cost=0; c_rev_idx=0 }
  ) in
  let pos = Array.make n 0 in
  List.iter (fun (s, d, c, cost) ->
    let si = pos.(s) in
    let di = pos.(d) in
    adj.(s).(si) <- { c_dst=d; c_cap=c; c_flow=0; c_cost=cost; c_rev_idx=di };
    adj.(d).(di) <- { c_dst=s; c_cap=0; c_flow=0; c_cost=(-cost); c_rev_idx=si };
    pos.(s) <- si + 1;
    pos.(d) <- di + 1
  ) fn.edges;
  { c_size = n; c_adj = adj }

(* Bellman-Ford shortest path on residual cost graph *)
let bellman_ford (net : cost_network) source sink =
  let dist = Array.make net.c_size max_int in
  let parent = Array.make net.c_size (-1, -1) in
  let in_queue = Array.make net.c_size false in
  dist.(source) <- 0;
  let q = Queue.create () in
  Queue.push source q;
  in_queue.(source) <- true;
  while not (Queue.is_empty q) do
    let u = Queue.pop q in
    in_queue.(u) <- false;
    Array.iteri (fun i e ->
      if e.c_cap - e.c_flow > 0 && dist.(u) <> max_int &&
         dist.(u) + e.c_cost < dist.(e.c_dst) then begin
        dist.(e.c_dst) <- dist.(u) + e.c_cost;
        parent.(e.c_dst) <- (u, i);
        if not in_queue.(e.c_dst) then begin
          in_queue.(e.c_dst) <- true;
          Queue.push e.c_dst q
        end
      end
    ) net.c_adj.(u)
  done;
  if dist.(sink) < max_int then Some (dist.(sink), parent) else None

type mcmf_result = {
  mcmf_flow: int;
  mcmf_cost: int;
}

let min_cost_max_flow fn source sink =
  let net = build_cost_internal fn in
  let total_flow = ref 0 in
  let total_cost = ref 0 in
  let continue = ref true in
  while !continue do
    match bellman_ford net source sink with
    | None -> continue := false
    | Some (_cost, parent) ->
      (* Find bottleneck *)
      let bottleneck = ref max_int in
      let v = ref sink in
      while !v <> source do
        let (u, ei) = parent.(!v) in
        let e = net.c_adj.(u).(ei) in
        bottleneck := min !bottleneck (e.c_cap - e.c_flow);
        v := u
      done;
      let b = !bottleneck in
      (* Update flow *)
      v := sink;
      while !v <> source do
        let (u, ei) = parent.(!v) in
        let e = net.c_adj.(u).(ei) in
        e.c_flow <- e.c_flow + b;
        total_cost := !total_cost + b * e.c_cost;
        let rev = net.c_adj.(!v).(e.c_rev_idx) in
        rev.c_flow <- rev.c_flow - b;
        v := u
      done;
      total_flow := !total_flow + b
  done;
  { mcmf_flow = !total_flow; mcmf_cost = !total_cost }

(* ---------- Utility: edge connectivity ---------- *)

let edge_connectivity fn u v =
  (* Edge connectivity between u and v = max flow from u to v *)
  max_flow fn u v

(* ---------- Utility: is the graph connected ---------- *)

let is_bipartite n edges =
  let adj = Array.make n [] in
  List.iter (fun (u, v) ->
    adj.(u) <- v :: adj.(u);
    adj.(v) <- u :: adj.(v)
  ) edges;
  let color = Array.make n (-1) in
  let q = Queue.create () in
  let result = ref true in
  for start = 0 to n - 1 do
    if color.(start) = -1 then begin
      color.(start) <- 0;
      Queue.push start q;
      while not (Queue.is_empty q) && !result do
        let u = Queue.pop q in
        List.iter (fun v ->
          if color.(v) = -1 then begin
            color.(v) <- 1 - color.(u);
            Queue.push v q
          end else if color.(v) = color.(u) then
            result := false
        ) adj.(u)
      done
    end
  done;
  if !result then
    let left = ref [] and right = ref [] in
    for i = 0 to n - 1 do
      if color.(i) = 0 then left := i :: !left
      else right := i :: !right
    done;
    Some (List.rev !left, List.rev !right)
  else None

(* ---------- Pretty printing ---------- *)

let string_of_flow_path fp =
  let path_str = String.concat " -> " (List.map string_of_int fp.path) in
  Printf.sprintf "  %s  (flow: %d)" path_str fp.path_flow

let print_min_cut_result r =
  Printf.printf "Max Flow Value: %d\n" r.max_flow_value;
  Printf.printf "S-side: {%s}\n" (String.concat ", " (List.map string_of_int r.s_side));
  Printf.printf "T-side: {%s}\n" (String.concat ", " (List.map string_of_int r.t_side));
  Printf.printf "Cut edges:\n";
  List.iter (fun (u, v, c) ->
    Printf.printf "  %d -> %d (cap: %d)\n" u v c
  ) r.cut_edges

let print_matching_result r =
  Printf.printf "Matching size: %d\n" r.matching_size;
  List.iter (fun (l, r) ->
    Printf.printf "  L%d -- R%d\n" l r
  ) r.pairs

(* ================================================================
   Tests — uses shared test_framework for assertions
   ================================================================ *)

(* Re-use the shared test framework instead of duplicating assertion helpers.
   When compiled standalone, define minimal stubs; when linked with
   test_framework.ml the shared counters are used automatically. *)

let _nf_assert_equal name expected actual =
  assert_equal ~msg:name (string_of_int expected) (string_of_int actual)

let _nf_assert_true name cond =
  assert_true ~msg:name cond

let run_tests () =
  Printf.printf "\n=== Network Flow Tests ===\n\n";

  (* --- Basic max flow --- *)
  Printf.printf "-- Basic Max Flow --\n";

  (* Simple 2-node *)
  let fn = create_flow_network 2 in
  add_edge fn 0 1 10;
  _nf_assert_equal "simple 2-node" 10 (max_flow fn 0 1);

  (* Linear chain *)
  let fn = create_flow_network 4 in
  add_edge fn 0 1 10;
  add_edge fn 1 2 5;
  add_edge fn 2 3 8;
  _nf_assert_equal "linear chain bottleneck" 5 (max_flow fn 0 3);

  (* Parallel paths *)
  let fn = create_flow_network 4 in
  add_edge fn 0 1 5;
  add_edge fn 0 2 3;
  add_edge fn 1 3 5;
  add_edge fn 2 3 3;
  _nf_assert_equal "parallel paths" 8 (max_flow fn 0 3);

  (* Diamond graph *)
  let fn = create_flow_network 4 in
  add_edge fn 0 1 10;
  add_edge fn 0 2 10;
  add_edge fn 1 3 10;
  add_edge fn 2 3 10;
  add_edge fn 1 2 1;
  _nf_assert_equal "diamond graph" 20 (max_flow fn 0 3);

  (* Classic example: Ford-Fulkerson challenge *)
  let fn = create_flow_network 6 in
  add_edge fn 0 1 16;
  add_edge fn 0 2 13;
  add_edge fn 1 2 10;
  add_edge fn 1 3 12;
  add_edge fn 2 1 4;
  add_edge fn 2 4 14;
  add_edge fn 3 2 9;
  add_edge fn 3 5 20;
  add_edge fn 4 3 7;
  add_edge fn 4 5 4;
  _nf_assert_equal "classic CLRS example" 23 (max_flow fn 0 5);

  (* Zero capacity *)
  let fn = create_flow_network 3 in
  add_edge fn 0 1 0;
  add_edge fn 1 2 5;
  _nf_assert_equal "zero capacity edge" 0 (max_flow fn 0 2);

  (* No path *)
  let fn = create_flow_network 3 in
  add_edge fn 0 1 5;
  _nf_assert_equal "disconnected sink" 0 (max_flow fn 0 2);

  (* Single node *)
  let fn = create_flow_network 1 in
  _nf_assert_equal "single node (source=sink)" 0 (max_flow fn 0 0);

  (* Multiple edges same pair *)
  let fn = create_flow_network 2 in
  add_edge fn 0 1 5;
  add_edge fn 0 1 3;
  _nf_assert_equal "multiple edges same pair" 8 (max_flow fn 0 1);

  (* Large fan-out *)
  let fn = create_flow_network 6 in
  for i = 1 to 4 do
    add_edge fn 0 i 3;
    add_edge fn i 5 3
  done;
  _nf_assert_equal "fan out 4 paths" 12 (max_flow fn 0 5);

  Printf.printf "\n-- Min Cut --\n";

  (* Simple min cut *)
  let fn = create_flow_network 4 in
  add_edge fn 0 1 3;
  add_edge fn 0 2 2;
  add_edge fn 1 3 2;
  add_edge fn 2 3 3;
  let mc = min_cut fn 0 3 in
  _nf_assert_equal "min cut value" 5 mc.max_flow_value;
  _nf_assert_true "min cut s_side has source" (List.mem 0 mc.s_side);
  _nf_assert_true "min cut t_side has sink" (List.mem 3 mc.t_side);
  _nf_assert_true "cut edges non-empty" (mc.cut_edges <> []);

  (* Bottleneck min cut *)
  let fn = create_flow_network 3 in
  add_edge fn 0 1 100;
  add_edge fn 1 2 1;
  let mc = min_cut fn 0 2 in
  _nf_assert_equal "bottleneck cut value" 1 mc.max_flow_value;
  _nf_assert_equal "bottleneck cut edges count" 1 (List.length mc.cut_edges);

  Printf.printf "\n-- Bipartite Matching --\n";

  (* Perfect matching *)
  let r = bipartite_matching 3 3 [(0,0); (1,1); (2,2)] in
  _nf_assert_equal "perfect matching size" 3 r.matching_size;

  (* No matching possible *)
  let r = bipartite_matching 2 2 [] in
  _nf_assert_equal "empty matching" 0 r.matching_size;

  (* Partial matching *)
  let r = bipartite_matching 3 2 [(0,0); (1,0); (2,1)] in
  _nf_assert_equal "partial matching" 2 r.matching_size;

  (* Complete bipartite K3,3 *)
  let edges = List.init 3 (fun i -> List.init 3 (fun j -> (i, j))) |> List.flatten in
  let r = bipartite_matching 3 3 edges in
  _nf_assert_equal "K3,3 matching" 3 r.matching_size;

  (* Single left, multiple right *)
  let r = bipartite_matching 1 3 [(0,0); (0,1); (0,2)] in
  _nf_assert_equal "single left" 1 r.matching_size;

  (* Job assignment *)
  let r = bipartite_matching 4 4 [(0,0); (0,1); (1,1); (1,2); (2,2); (2,3); (3,3)] in
  _nf_assert_equal "job assignment" 4 r.matching_size;

  Printf.printf "\n-- Multi-source/sink --\n";

  let fn = create_flow_network 4 in
  add_edge fn 0 2 5;
  add_edge fn 1 2 3;
  add_edge fn 0 3 4;
  add_edge fn 1 3 2;
  let v = multi_source_sink_max_flow fn
    [(0, 100); (1, 100)]
    [(2, 100); (3, 100)] in
  _nf_assert_equal "multi source/sink" 14 v;

  Printf.printf "\n-- Flow Decomposition --\n";

  let fn = create_flow_network 4 in
  add_edge fn 0 1 3;
  add_edge fn 0 2 2;
  add_edge fn 1 3 3;
  add_edge fn 2 3 2;
  let paths = decompose_flow fn 0 3 in
  let total = List.fold_left (fun acc p -> acc + p.path_flow) 0 paths in
  _nf_assert_equal "decomposition total flow" 5 total;
  _nf_assert_true "at least 1 path" (List.length paths >= 1);
  (* Each path starts at source and ends at sink *)
  List.iter (fun p ->
    _nf_assert_true "path starts at source" (List.hd p.path = 0);
    _nf_assert_true "path ends at sink" (List.nth p.path (List.length p.path - 1) = 3)
  ) paths;

  Printf.printf "\n-- Min Cost Max Flow --\n";

  (* Simple MCMF *)
  let fn = create_flow_network 4 in
  add_edge_with_cost fn 0 1 2 1;
  add_edge_with_cost fn 0 2 2 5;
  add_edge_with_cost fn 1 3 2 1;
  add_edge_with_cost fn 2 3 2 1;
  let r = min_cost_max_flow fn 0 3 in
  _nf_assert_equal "mcmf flow" 4 r.mcmf_flow;
  (* Cheapest: 2 units via 0->1->3 (cost 4), then 2 via 0->2->3 (cost 12) = 16 *)
  _nf_assert_equal "mcmf cost" 16 r.mcmf_cost;

  (* MCMF: prefer cheap path *)
  let fn = create_flow_network 4 in
  add_edge_with_cost fn 0 1 10 1;   (* cheap *)
  add_edge_with_cost fn 0 2 10 100; (* expensive *)
  add_edge_with_cost fn 1 3 5 1;
  add_edge_with_cost fn 2 3 10 1;
  let r = min_cost_max_flow fn 0 3 in
  _nf_assert_equal "mcmf prefers cheap" 15 r.mcmf_flow;
  (* 5 units via cheap (cost 5*2=10), 10 via expensive (cost 10*101=1010) = 1020 *)
  _nf_assert_equal "mcmf cost cheap+expensive" 1020 r.mcmf_cost;

  (* MCMF: zero cost *)
  let fn = create_flow_network 2 in
  add_edge_with_cost fn 0 1 5 0;
  let r = min_cost_max_flow fn 0 1 in
  _nf_assert_equal "mcmf zero cost flow" 5 r.mcmf_flow;
  _nf_assert_equal "mcmf zero cost" 0 r.mcmf_cost;

  Printf.printf "\n-- Edge Connectivity --\n";

  let fn = create_flow_network 4 in
  add_edge fn 0 1 1;
  add_edge fn 0 2 1;
  add_edge fn 1 3 1;
  add_edge fn 2 3 1;
  _nf_assert_equal "edge connectivity" 2 (edge_connectivity fn 0 3);

  let fn = create_flow_network 3 in
  add_edge fn 0 1 1;
  add_edge fn 1 2 1;
  _nf_assert_equal "bridge connectivity" 1 (edge_connectivity fn 0 2);

  Printf.printf "\n-- Bipartite Check --\n";

  _nf_assert_true "empty graph bipartite" (is_bipartite 1 [] <> None);
  _nf_assert_true "path bipartite" (is_bipartite 3 [(0,1); (1,2)] <> None);
  _nf_assert_true "triangle not bipartite" (is_bipartite 3 [(0,1); (1,2); (0,2)] = None);
  _nf_assert_true "even cycle bipartite" (is_bipartite 4 [(0,1); (1,2); (2,3); (3,0)] <> None);
  _nf_assert_true "K2,2 bipartite" (is_bipartite 4 [(0,2); (0,3); (1,2); (1,3)] <> None);

  Printf.printf "\n-- Stress Tests --\n";

  (* Chain of 100 nodes *)
  let fn = create_flow_network 100 in
  for i = 0 to 98 do add_edge fn i (i+1) 1000 done;
  _nf_assert_equal "long chain" 1000 (max_flow fn 0 99);

  (* Wide fan: source->N intermediates->sink *)
  let n = 50 in
  let fn = create_flow_network (n + 2) in
  for i = 1 to n do
    add_edge fn 0 i 1;
    add_edge fn i (n+1) 1
  done;
  _nf_assert_equal "wide fan 50" 50 (max_flow fn 0 (n+1));

  (* Grid-like graph *)
  let fn = create_flow_network 9 in
  (* 3x3 grid: node i*3+j *)
  for i = 0 to 2 do
    for j = 0 to 2 do
      let v = i * 3 + j in
      if j < 2 then add_edge fn v (v+1) 2;
      if i < 2 then add_edge fn v (v+3) 2
    done
  done;
  let grid_flow = max_flow fn 0 8 in
  _nf_assert_equal "3x3 grid flow" 4 grid_flow;

  (* Matching verification *)
  let r = bipartite_matching 5 5
    [(0,0); (0,1); (1,1); (1,2); (2,2); (2,3); (3,3); (3,4); (4,4); (4,0)] in
  _nf_assert_equal "5x5 circular matching" 5 r.matching_size;

  test_summary ()

let () = run_tests ()
