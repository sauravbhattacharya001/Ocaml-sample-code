(* Weighted Graph with Dijkstra's Shortest Path Algorithm *)
(* Demonstrates: weighted adjacency lists, priority queues via sorted lists,
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

(* --- Priority Queue (min-heap via sorted list) --- *)
(* Simple implementation suitable for educational purposes *)

let pq_empty = []

let pq_insert pq (priority, value) =
  let rec insert = function
    | [] -> [(priority, value)]
    | ((p, _) as h) :: t ->
      if priority <= p then (priority, value) :: h :: t
      else h :: insert t
  in
  insert pq

let pq_pop = function
  | [] -> None
  | (p, v) :: rest -> Some ((p, v), rest)

(* --- Dijkstra's Algorithm --- *)
(* Returns a map from each reachable vertex to (distance, predecessor option) *)

let dijkstra g source =
  let dist = Hashtbl.create (num_vertices g) in
  let prev = Hashtbl.create (num_vertices g) in
  let visited = Hashtbl.create (num_vertices g) in

  Hashtbl.replace dist source 0.0;
  let pq = ref (pq_insert pq_empty (0.0, source)) in

  let continue = ref true in
  while !continue do
    match pq_pop !pq with
    | None -> continue := false
    | Some ((d, u), rest) ->
      pq := rest;
      if not (Hashtbl.mem visited u) then begin
        Hashtbl.replace visited u true;
        List.iter (fun (v, w) ->
          let new_dist = d +. w in
          let old_dist = try Hashtbl.find dist v with Not_found -> infinity in
          if new_dist < old_dist then begin
            Hashtbl.replace dist v new_dist;
            Hashtbl.replace prev v u;
            pq := pq_insert !pq (new_dist, v)
          end
        ) (neighbors g u)
      end
  done;
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
(* Returns a 2D distance matrix as a hashtable of (i,j) -> distance *)

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

  (verts, dist, idx)

(* --- Prim's Minimum Spanning Tree (undirected only) --- *)
(* Returns list of (u, v, weight) edges in the MST *)

let prim_mst g =
  if g.directed then failwith "MST requires undirected graph";
  match vertices g with
  | [] -> []
  | start :: _ ->
    let in_mst = Hashtbl.create (num_vertices g) in
    let edges = ref [] in
    let pq = ref pq_empty in

    Hashtbl.replace in_mst start true;
    List.iter (fun (v, w) ->
      pq := pq_insert !pq (w, (start * 10000 + v))  (* encode edge as single int *)
    ) (neighbors g start);

    let continue = ref true in
    while !continue do
      match pq_pop !pq with
      | None -> continue := false
      | Some ((w, encoded), rest) ->
        pq := rest;
        let u = encoded / 10000 in
        let v = encoded mod 10000 in
        if not (Hashtbl.mem in_mst v) then begin
          Hashtbl.replace in_mst v true;
          edges := (u, v, w) :: !edges;
          List.iter (fun (next, nw) ->
            if not (Hashtbl.mem in_mst next) then
              pq := pq_insert !pq (nw, (v * 10000 + next))
          ) (neighbors g v)
        end
    done;
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
  let (verts, fw_dist, idx) = floyd_warshall g in
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
  ) verts;
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
