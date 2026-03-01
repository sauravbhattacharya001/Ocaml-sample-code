(* Graph algorithms with adjacency list representation *)
(* Demonstrates: modules (Map, Set, Queue), BFS, DFS, topological sort,
   cycle detection, connected components, imperative queues *)

(* --- Graph representation using Map of int -> int list --- *)

module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

type graph = {
  adj: int list IntMap.t;   (* adjacency list *)
  directed: bool;
}

(* Create an empty graph *)
let empty_graph ~directed = { adj = IntMap.empty; directed }

(* Add a vertex (no-op if it already exists) *)
let add_vertex g v =
  if IntMap.mem v g.adj then g
  else { g with adj = IntMap.add v [] g.adj }

(* Insert into a sorted list, maintaining order. Returns the list unchanged
   if the element already exists (deduplication). *)
let rec sorted_insert x = function
  | [] -> [x]
  | h :: t as lst ->
    if x < h then x :: lst
    else if x = h then lst (* already present *)
    else h :: sorted_insert x t

(* Add an edge; creates vertices if they don't exist.
   Adjacency lists are maintained in sorted order so neighbors
   returns results without an extra sort pass. *)
let add_edge g u v =
  let add_neighbor src dst adj =
    let ns = try IntMap.find src adj with Not_found -> [] in
    IntMap.add src (sorted_insert dst ns) adj
  in
  let adj = add_neighbor u v g.adj in
  let adj = if not g.directed then add_neighbor v u adj else adj in
  let adj = if not (IntMap.mem v adj) then IntMap.add v [] adj else adj in
  { g with adj }

(* Get all vertices *)
let vertices g =
  IntMap.fold (fun k _ acc -> k :: acc) g.adj []
  |> List.sort compare

(* Get neighbors of a vertex (already sorted from insertion) *)
let neighbors g v =
  try IntMap.find v g.adj
  with Not_found -> []

(* Number of vertices *)
let num_vertices g = IntMap.cardinal g.adj

(* Number of edges *)
let num_edges g =
  let total = IntMap.fold (fun _ ns acc -> acc + List.length ns) g.adj 0 in
  if g.directed then total else total / 2

(* --- BFS: Breadth-First Search --- *)
(* Returns vertices in BFS order from a starting node *)
(* Uses OCaml's Queue module for O(1) enqueue/dequeue *)

let bfs g start =
  if not (IntMap.mem start g.adj) then []
  else begin
    let visited = Hashtbl.create (num_vertices g) in
    let queue = Queue.create () in
    let result = ref [] in
    Queue.push start queue;
    Hashtbl.replace visited start true;
    while not (Queue.is_empty queue) do
      let v = Queue.pop queue in
      result := v :: !result;
      List.iter (fun w ->
        if not (Hashtbl.mem visited w) then begin
          Hashtbl.replace visited w true;
          Queue.push w queue
        end
      ) (neighbors g v)
    done;
    List.rev !result
  end

(* BFS shortest path: returns the path from start to goal, or None *)
let bfs_path g start goal =
  if not (IntMap.mem start g.adj) || not (IntMap.mem goal g.adj) then None
  else if start = goal then Some [start]
  else begin
    let visited = Hashtbl.create (num_vertices g) in
    let parent = Hashtbl.create (num_vertices g) in
    let queue = Queue.create () in
    Queue.push start queue;
    Hashtbl.replace visited start true;
    let found = ref false in
    while not (Queue.is_empty queue) && not !found do
      let v = Queue.pop queue in
      List.iter (fun w ->
        if not (Hashtbl.mem visited w) then begin
          Hashtbl.replace visited w true;
          Hashtbl.replace parent w v;
          if w = goal then found := true
          else Queue.push w queue
        end
      ) (neighbors g v)
    done;
    if not !found then None
    else begin
      (* Reconstruct path by following parent pointers *)
      let rec build_path v acc =
        if v = start then v :: acc
        else build_path (Hashtbl.find parent v) (v :: acc)
      in
      Some (build_path goal [])
    end
  end

(* --- DFS: Depth-First Search --- *)
(* Recursive DFS returning vertices in discovery order *)

let dfs g start =
  if not (IntMap.mem start g.adj) then []
  else begin
    let visited = Hashtbl.create (num_vertices g) in
    let result = ref [] in
    let rec explore v =
      if not (Hashtbl.mem visited v) then begin
        Hashtbl.replace visited v true;
        result := v :: !result;
        List.iter explore (neighbors g v)
      end
    in
    explore start;
    List.rev !result
  end

(* --- Connected Components (undirected graphs) --- *)
(* Returns a list of components, each a sorted list of vertices *)

(* Internal DFS that uses a shared visited Hashtbl — avoids
   creating a new table for every connected component. *)
let dfs_collect g start visited =
  let result = ref [] in
  let rec explore v =
    if not (Hashtbl.mem visited v) then begin
      Hashtbl.replace visited v true;
      result := v :: !result;
      List.iter explore (neighbors g v)
    end
  in
  explore start;
  List.rev !result

(* Returns a list of components, each a sorted list of vertices.
   Uses a single shared visited table instead of creating one per component. *)
let connected_components g =
  let visited = Hashtbl.create (num_vertices g) in
  let components = ref [] in
  List.iter (fun v ->
    if not (Hashtbl.mem visited v) then begin
      let component = dfs_collect g v visited in
      components := List.sort compare component :: !components
    end
  ) (vertices g);
  List.rev !components

(* --- Cycle Detection --- *)
(* For directed graphs: DFS with three-color marking (White/Gray/Black).
   A back edge to a Gray node indicates a cycle.
   For undirected graphs: DFS with parent tracking.
   A visited neighbor that is not the parent indicates a cycle. *)

type color = White | Gray | Black

let has_cycle g =
  if g.directed then begin
    (* Directed: standard three-color DFS *)
    let color = Hashtbl.create (num_vertices g) in
    List.iter (fun v -> Hashtbl.replace color v White) (vertices g);
    let found_cycle = ref false in
    let rec visit v =
      if !found_cycle then ()
      else begin
        Hashtbl.replace color v Gray;
        List.iter (fun w ->
          if not !found_cycle then
            match Hashtbl.find color w with
            | Gray -> found_cycle := true
            | White -> visit w
            | Black -> ()
        ) (neighbors g v);
        Hashtbl.replace color v Black
      end
    in
    List.iter (fun v ->
      if Hashtbl.find color v = White then visit v
    ) (vertices g);
    !found_cycle
  end else begin
    (* Undirected: DFS with parent tracking to skip the trivial back-edge *)
    let visited = Hashtbl.create (num_vertices g) in
    let found_cycle = ref false in
    let rec visit v parent =
      if !found_cycle then ()
      else begin
        Hashtbl.replace visited v true;
        List.iter (fun w ->
          if not !found_cycle then
            if Hashtbl.mem visited w then begin
              if w <> parent then found_cycle := true
            end else
              visit w v
        ) (neighbors g v)
      end
    in
    List.iter (fun v ->
      if not (Hashtbl.mem visited v) then visit v (-1)
    ) (vertices g);
    !found_cycle
  end

(* --- Topological Sort (directed acyclic graphs) --- *)
(* Returns Some sorted_list if no cycle, None if cycle detected *)
(* Uses Kahn's algorithm with in-degree counting *)
(* Cycle detection is built-in: if output has fewer vertices than the graph, *)
(* a cycle exists. No separate has_cycle pass needed. *)

let topological_sort g =
  (* Compute in-degrees *)
  let in_deg = Hashtbl.create (num_vertices g) in
  List.iter (fun v -> Hashtbl.replace in_deg v 0) (vertices g);
  IntMap.iter (fun _ ns ->
    List.iter (fun w ->
      let d = try Hashtbl.find in_deg w with Not_found -> 0 in
      Hashtbl.replace in_deg w (d + 1)
    ) ns
  ) g.adj;
  (* Start with all vertices of in-degree 0 *)
  let queue = Queue.create () in
  Hashtbl.iter (fun v d -> if d = 0 then Queue.push v queue) in_deg;
  let result = ref [] in
  while not (Queue.is_empty queue) do
    let v = Queue.pop queue in
    result := v :: !result;
    List.iter (fun w ->
      let d = Hashtbl.find in_deg w - 1 in
      Hashtbl.replace in_deg w d;
      if d = 0 then Queue.push w queue
    ) (neighbors g v)
  done;
  let sorted = List.rev !result in
  (* If Kahn's didn't visit all vertices, a cycle exists *)
  if List.length sorted <> num_vertices g then None
  else Some sorted

(* --- Pretty printing --- *)

let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

let print_graph g =
  let kind = if g.directed then "Directed" else "Undirected" in
  Printf.printf "%s graph: %d vertices, %d edges\n" kind (num_vertices g) (num_edges g);
  List.iter (fun v ->
    Printf.printf "  %d -> %s\n" v (string_of_int_list (neighbors g v))
  ) (vertices g)

(* === Example usage === *)

let () =
  print_endline "=== Undirected Graph ===";
  let g = empty_graph ~directed:false in
  let g = List.fold_left (fun g (u, v) -> add_edge g u v)
    g [(1,2); (1,3); (2,4); (3,4); (4,5); (6,7)] in
  print_graph g;
  print_newline ();

  Printf.printf "BFS from 1: %s\n" (string_of_int_list (bfs g 1));
  Printf.printf "DFS from 1: %s\n" (string_of_int_list (dfs g 1));
  print_newline ();

  (match bfs_path g 1 5 with
  | None -> print_endline "No path from 1 to 5"
  | Some path -> Printf.printf "Shortest path 1->5: %s\n" (string_of_int_list path));
  (match bfs_path g 1 7 with
  | None -> print_endline "No path from 1 to 7 (different component)"
  | Some path -> Printf.printf "Path 1->7: %s\n" (string_of_int_list path));
  print_newline ();

  let components = connected_components g in
  Printf.printf "Connected components: %d\n" (List.length components);
  List.iteri (fun i c ->
    Printf.printf "  Component %d: %s\n" (i + 1) (string_of_int_list c)
  ) components;
  print_newline ();

  print_endline "=== Undirected Cycle Detection ===";
  (* Tree: no cycle *)
  let tree = empty_graph ~directed:false in
  let tree = List.fold_left (fun g (u, v) -> add_edge g u v)
    tree [(1,2); (2,3)] in
  Printf.printf "Tree (1-2-3) has cycle: %b (expected false)\n" (has_cycle tree);
  (* Undirected graph with cycle *)
  Printf.printf "Graph with cycle (1-2,2-4,3-4,1-3) has cycle: %b (expected true)\n" (has_cycle g);
  print_newline ();

  print_endline "=== Directed Acyclic Graph (DAG) ===";
  let dag = empty_graph ~directed:true in
  let dag = List.fold_left (fun g (u, v) -> add_edge g u v)
    dag [(1,2); (1,3); (2,4); (3,4); (4,5)] in
  print_graph dag;
  Printf.printf "Has cycle: %b\n" (has_cycle dag);
  (match topological_sort dag with
  | None -> print_endline "Topological sort failed (cycle detected)"
  | Some order -> Printf.printf "Topological order: %s\n" (string_of_int_list order));
  print_newline ();

  print_endline "=== Directed Graph with Cycle ===";
  let cyclic = empty_graph ~directed:true in
  let cyclic = List.fold_left (fun g (u, v) -> add_edge g u v)
    cyclic [(1,2); (2,3); (3,1); (3,4)] in
  print_graph cyclic;
  Printf.printf "Has cycle: %b\n" (has_cycle cyclic);
  (match topological_sort cyclic with
  | None -> print_endline "Topological sort failed (cycle detected)"
  | Some order -> Printf.printf "Topological order: %s\n" (string_of_int_list order));
  print_newline ();

  print_endline "=== BFS/DFS on Directed Graph ===";
  let dg = empty_graph ~directed:true in
  let dg = List.fold_left (fun g (u, v) -> add_edge g u v)
    dg [(1,2); (1,3); (2,4); (3,4); (4,5); (5,6)] in
  Printf.printf "BFS from 1: %s\n" (string_of_int_list (bfs dg 1));
  Printf.printf "DFS from 1: %s\n" (string_of_int_list (dfs dg 1));
  (match bfs_path dg 1 6 with
  | None -> print_endline "No path"
  | Some path -> Printf.printf "Shortest path 1->6: %s\n" (string_of_int_list path))
