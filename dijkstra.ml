(* Weighted Graph with Dijkstra's Shortest Path Algorithm *)
(* Demonstrates: weighted adjacency lists, binary min-heap priority queue,
   Dijkstra's algorithm, shortest path reconstruction, weighted MST (Prim's) *)

module IntMap = Map.Make(Int)

type weighted_graph = {
  adj: (int * float) list IntMap.t;  (* vertex -> list of (neighbor, weight) *)
  directed: bool;
}

(* Create an empty weighted graph *)
let empty_graph ~directed = { adj = IntMap.empty; directed }

(* Add a vertex *)
let add_vertex g v =
  if IntMap.mem v g.adj then g
  else { g with adj = IntMap.add v [] g.adj }

(* Add a weighted edge *)
let add_edge g u v w =
  let add_neighbor src dst weight adj =
    let ns = try IntMap.find src adj with Not_found -> [] in
    (* Replace existing edge or add new one *)
    let ns = List.filter (fun (d, _) -> d <> dst) ns in
    IntMap.add src ((dst, weight) :: ns) adj
  in
  let adj = add_neighbor u v w g.adj in
  let adj = if not g.directed then add_neighbor v u w adj else adj in
  let adj = if not (IntMap.mem v adj) then IntMap.add v [] adj else adj in
  let adj = if not (IntMap.mem u adj) then IntMap.add u [] adj else adj in
  { g with adj }

(* Get all vertices *)
let vertices g =
  IntMap.fold (fun k _ acc -> k :: acc) g.adj []
  |> List.sort compare

(* Get weighted neighbors *)
let neighbors g v =
  try IntMap.find v g.adj
  with Not_found -> []

let num_vertices g = IntMap.cardinal g.adj

let num_edges g =
  let total = IntMap.fold (fun _ ns acc -> acc + List.length ns) g.adj 0 in
  if g.directed then total else total / 2

(* --- Priority Queue (binary min-heap) --- *)
(* Array-backed binary min-heap: O(log n) insert and extract-min.
   Replaces the previous sorted-list implementation which was O(n)
   per insertion due to linear scan for the correct position.
   Polymorphic in the value type: works with plain ints (Dijkstra)
   and edge tuples (Prim's) alike. *)

module MinHeap : sig
  type 'a t
  val empty : 'a t
  val insert : 'a t -> (float * 'a) -> 'a t
  val pop : 'a t -> ((float * 'a) * 'a t) option
  val is_empty : 'a t -> bool
end = struct
  type 'a t = {
    data : (float * 'a) array;
    len  : int;
  }

  let empty = { data = Array.make 0 (0.0, Obj.magic 0); len = 0 }

  let swap a i j =
    let tmp = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- tmp

  let sift_up a idx =
    let i = ref idx in
    while !i > 0 do
      let parent = (!i - 1) / 2 in
      if fst a.(!i) < fst a.(parent) then begin
        swap a !i parent;
        i := parent
      end else
        i := 0  (* break *)
    done

  let sift_down a len idx =
    let i = ref idx in
    let continue_ = ref true in
    while !continue_ do
      let left = 2 * !i + 1 in
      let right = 2 * !i + 2 in
      let smallest = ref !i in
      if left < len && fst a.(left) < fst a.(!smallest) then
        smallest := left;
      if right < len && fst a.(right) < fst a.(!smallest) then
        smallest := right;
      if !smallest <> !i then begin
        swap a !i !smallest;
        i := !smallest
      end else
        continue_ := false
    done

  let insert h (priority, value) =
    let cap = Array.length h.data in
    let data =
      if h.len >= cap then begin
        let new_cap = max 8 (cap * 2) in
        let new_data = Array.make new_cap (0.0, Obj.magic 0) in
        Array.blit h.data 0 new_data 0 h.len;
        new_data
      end else
        (* Copy array so the heap remains purely functional *)
        Array.copy h.data
    in
    data.(h.len) <- (priority, value);
    sift_up data h.len;
    { data; len = h.len + 1 }

  let pop h =
    if h.len = 0 then None
    else begin
      let min_elem = h.data.(0) in
      let data = Array.copy h.data in
      data.(0) <- data.(h.len - 1);
      let new_len = h.len - 1 in
      if new_len > 0 then sift_down data new_len 0;
      Some (min_elem, { data; len = new_len })
    end

  let is_empty h = h.len = 0
end

(* Compatibility shims so Dijkstra/Prim callers stay unchanged *)
let pq_empty = MinHeap.empty
let pq_insert pq (priority, value) = MinHeap.insert pq (priority, value)
let pq_pop pq = MinHeap.pop pq

(* --- Dijkstra's Algorithm --- *)
(* Returns a map from each reachable vertex to (distance, predecessor option) *)
(* Uses a recursive loop instead of a mutable while-flag — idiomatic OCaml. *)

let dijkstra g source =
  let dist = Hashtbl.create (num_vertices g) in
  let prev = Hashtbl.create (num_vertices g) in
  let visited = Hashtbl.create (num_vertices g) in

  Hashtbl.replace dist source 0.0;

  let rec loop pq =
    match pq_pop pq with
    | None -> ()
    | Some ((d, u), rest) ->
      if Hashtbl.mem visited u then
        loop rest
      else begin
        Hashtbl.replace visited u true;
        let pq' = List.fold_left (fun q (v, w) ->
          let new_dist = d +. w in
          let old_dist = try Hashtbl.find dist v with Not_found -> infinity in
          if new_dist < old_dist then begin
            Hashtbl.replace dist v new_dist;
            Hashtbl.replace prev v u;
            pq_insert q (new_dist, v)
          end else q
        ) rest (neighbors g u)
        in
        loop pq'
      end
  in
  loop (pq_insert pq_empty (0.0, source));
  (dist, prev)

(* Get shortest distance from source to target *)
let shortest_distance g source target =
  let (dist, _) = dijkstra g source in
  try Some (Hashtbl.find dist target)
  with Not_found -> None

(* Get shortest path from source to target *)
let shortest_path g source target =
  let (dist, prev) = dijkstra g source in
  if not (Hashtbl.mem dist target) then None
  else begin
    let rec build v acc =
      if v = source then v :: acc
      else
        try build (Hashtbl.find prev v) (v :: acc)
        with Not_found -> v :: acc
    in
    Some (build target [], Hashtbl.find dist target)
  end

(* --- All-Pairs Shortest Paths (Floyd-Warshall) --- *)
(* Returns [Some (verts, dist, idx)] on success, or [None] if the graph
   contains a negative weight cycle (detected by a negative diagonal entry
   after relaxation).  Note: Dijkstra's algorithm assumes non-negative edge
   weights and will produce incorrect results if negative edges are present. *)

exception Negative_cycle

let floyd_warshall g =
  let verts = vertices g in
  let n = List.length verts in
  let idx = Hashtbl.create n in
  List.iteri (fun i v -> Hashtbl.replace idx v i) verts;

  (* Initialize distance matrix *)
  let dist = Array.make_matrix n n infinity in
  for i = 0 to n - 1 do dist.(i).(i) <- 0.0 done;

  IntMap.iter (fun u ns ->
    let i = Hashtbl.find idx u in
    List.iter (fun (v, w) ->
      let j = Hashtbl.find idx v in
      dist.(i).(j) <- min dist.(i).(j) w
    ) ns
  ) g.adj;

  (* Relax *)
  for k = 0 to n - 1 do
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        let through_k = dist.(i).(k) +. dist.(k).(j) in
        if through_k < dist.(i).(j) then
          dist.(i).(j) <- through_k
      done
    done
  done;

  (* Detect negative weight cycles: if any diagonal entry is negative,
     a negative cycle exists and the distance matrix is meaningless. *)
  let has_neg_cycle = ref false in
  for i = 0 to n - 1 do
    if dist.(i).(i) < 0.0 then has_neg_cycle := true
  done;
  if !has_neg_cycle then None
  else Some (verts, dist, idx)

(* --- Prim's Minimum Spanning Tree (undirected only) --- *)
(* Returns list of (u, v, weight) edges in the MST.
   Uses proper (from, to) edge tuples in the priority queue instead
   of the previous int-encoding hack (u * 10000 + v) which silently
   produced wrong results for vertex IDs >= 10000. *)

let prim_mst g =
  if g.directed then failwith "MST requires undirected graph";
  match vertices g with
  | [] -> []
  | start :: _ ->
    let in_mst = Hashtbl.create (num_vertices g) in
    let edges = ref [] in

    Hashtbl.replace in_mst start true;
    let init_pq = List.fold_left (fun q (v, w) ->
      pq_insert q (w, (start, v))
    ) pq_empty (neighbors g start)
    in

    let rec loop pq =
      match pq_pop pq with
      | None -> ()
      | Some ((w, (u, v)), rest) ->
        if Hashtbl.mem in_mst v then
          loop rest
        else begin
          Hashtbl.replace in_mst v true;
          edges := (u, v, w) :: !edges;
          let pq' = List.fold_left (fun q (next, nw) ->
            if Hashtbl.mem in_mst next then q
            else pq_insert q (nw, (v, next))
          ) rest (neighbors g v)
          in
          loop pq'
        end
    in
    loop init_pq;
    List.rev !edges

(* --- Pretty Printing --- *)

let print_graph g =
  let kind = if g.directed then "Directed" else "Undirected" in
  Printf.printf "%s weighted graph: %d vertices, %d edges\n"
    kind (num_vertices g) (num_edges g);
  List.iter (fun v ->
    let ns = neighbors g v in
    let ns_str = List.map (fun (n, w) ->
      Printf.sprintf "(%d, %.1f)" n w
    ) ns in
    Printf.printf "  %d -> [%s]\n" v (String.concat "; " ns_str)
  ) (vertices g)

(* === Examples === *)

let () =
  print_endline "=== Weighted Undirected Graph ===";
  let g = empty_graph ~directed:false in
  let g = List.fold_left (fun g (u, v, w) -> add_edge g u v w) g
    [(1, 2, 4.0); (1, 3, 2.0); (2, 3, 1.0);
     (2, 4, 5.0); (3, 4, 8.0); (3, 5, 10.0);
     (4, 5, 2.0); (4, 6, 6.0); (5, 6, 3.0)] in
  print_graph g;
  print_newline ();

  print_endline "--- Dijkstra's Shortest Paths from vertex 1 ---";
  let (dist, _) = dijkstra g 1 in
  List.iter (fun v ->
    let d = try Hashtbl.find dist v with Not_found -> infinity in
    Printf.printf "  Distance to %d: %.1f\n" v d
  ) (vertices g);
  print_newline ();

  print_endline "--- Shortest Path from 1 to 6 ---";
  (match shortest_path g 1 6 with
  | None -> print_endline "  No path found"
  | Some (path, cost) ->
    let path_str = List.map string_of_int path |> String.concat " -> " in
    Printf.printf "  Path: %s (cost: %.1f)\n" path_str cost);
  print_newline ();

  print_endline "--- Shortest Path from 1 to 5 ---";
  (match shortest_path g 1 5 with
  | None -> print_endline "  No path found"
  | Some (path, cost) ->
    let path_str = List.map string_of_int path |> String.concat " -> " in
    Printf.printf "  Path: %s (cost: %.1f)\n" path_str cost);
  print_newline ();

  print_endline "--- Floyd-Warshall All-Pairs Shortest Paths ---";
  (match floyd_warshall g with
  | None -> print_endline "  Negative weight cycle detected!"
  | Some (verts, fw_dist, idx) ->
    Printf.printf "     ";
    List.iter (fun v -> Printf.printf "%6d" v) verts;
    print_newline ();
    List.iter (fun u ->
      Printf.printf "  %d: " u;
      let i = Hashtbl.find idx u in
      List.iter (fun v ->
        let j = Hashtbl.find idx v in
        if fw_dist.(i).(j) = infinity then Printf.printf "   inf"
        else Printf.printf "%6.1f" fw_dist.(i).(j)
      ) verts;
      print_newline ()
    ) verts);
  print_newline ();

  print_endline "--- Prim's Minimum Spanning Tree ---";
  let mst = prim_mst g in
  let total = List.fold_left (fun acc (_, _, w) -> acc +. w) 0.0 mst in
  List.iter (fun (u, v, w) ->
    Printf.printf "  %d -- %d (weight %.1f)\n" u v w
  ) mst;
  Printf.printf "  Total MST weight: %.1f\n" total;
  print_newline ();

  print_endline "=== Weighted Directed Graph ===";
  let dg = empty_graph ~directed:true in
  let dg = List.fold_left (fun g (u, v, w) -> add_edge g u v w) dg
    [(0, 1, 10.0); (0, 2, 3.0); (1, 2, 1.0);
     (1, 3, 2.0); (2, 1, 4.0); (2, 3, 8.0);
     (2, 4, 2.0); (3, 4, 7.0); (4, 3, 9.0)] in
  print_graph dg;
  print_newline ();

  print_endline "--- Dijkstra from vertex 0 ---";
  List.iter (fun target ->
    match shortest_path dg 0 target with
    | None -> Printf.printf "  0 -> %d: no path\n" target
    | Some (path, cost) ->
      let path_str = List.map string_of_int path |> String.concat " -> " in
      Printf.printf "  0 -> %d: %s (cost: %.1f)\n" target path_str cost
  ) (vertices dg)
