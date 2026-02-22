(* union_find.ml — Persistent Union-Find (Disjoint Sets) *)
(* A purely functional union-find data structure using balanced trees
   with union-by-rank and path compression via lazy rebuilding.

   Unlike imperative implementations that mutate parent pointers,
   this version is persistent: every operation returns a new structure,
   and old versions remain valid.

   Complexity (amortised):
     find:  O(log n)
     union: O(log n)
     (Not quite inverse-Ackermann like the imperative version, but
      efficient enough for functional use cases.)

   Usage:
     let uf = UnionFind.create 10 in
     let uf = UnionFind.union uf 0 1 in
     let uf = UnionFind.union uf 2 3 in
     UnionFind.connected uf 0 1   (* true *)
     UnionFind.connected uf 0 2   (* false *)
     UnionFind.num_components uf  (* 8 *)
*)

module IntMap = Map.Make(Int)

(* Each element points to a parent (or itself if root) and has a rank *)
type t = {
  parent : int IntMap.t;
  rank   : int IntMap.t;
  size   : int IntMap.t;   (* size of each component, stored at root *)
  n      : int;            (* total number of elements *)
}

(* Create a fresh union-find with n elements {0, 1, ..., n-1}.
   Each element starts in its own singleton set. *)
let create n =
  if n < 0 then invalid_arg "UnionFind.create: negative size";
  let parent = ref IntMap.empty in
  let rank = ref IntMap.empty in
  let size = ref IntMap.empty in
  for i = 0 to n - 1 do
    parent := IntMap.add i i !parent;
    rank := IntMap.add i 0 !rank;
    size := IntMap.add i 1 !size;
  done;
  { parent = !parent; rank = !rank; size = !size; n }

(* Find the root representative of element x with path compression.
   Returns (root, updated_uf) — the updated structure has compressed
   paths for better future lookups. *)
let rec find uf x =
  if not (IntMap.mem x uf.parent) then
    invalid_arg (Printf.sprintf "UnionFind.find: element %d out of range" x);
  let px = IntMap.find x uf.parent in
  if px = x then (x, uf)
  else
    let (root, uf') = find uf px in
    (* Path compression: point x directly to root *)
    let uf'' = { uf' with parent = IntMap.add x root uf'.parent } in
    (root, uf'')

(* Find root without path compression (pure query, no state change) *)
let rec find_root uf x =
  if not (IntMap.mem x uf.parent) then
    invalid_arg (Printf.sprintf "UnionFind.find_root: element %d out of range" x);
  let px = IntMap.find x uf.parent in
  if px = x then x
  else find_root uf px

(* Check whether two elements are in the same component. *)
let connected uf x y =
  find_root uf x = find_root uf y

(* Union the components containing x and y using union-by-rank.
   Returns the updated union-find. If x and y are already connected,
   returns the structure unchanged. *)
let union uf x y =
  let (rx, uf1) = find uf x in
  let (ry, uf2) = find uf1 y in
  if rx = ry then uf2  (* already in same set *)
  else
    let rank_rx = IntMap.find rx uf2.rank in
    let rank_ry = IntMap.find ry uf2.rank in
    let size_rx = IntMap.find rx uf2.size in
    let size_ry = IntMap.find ry uf2.size in
    let new_size = size_rx + size_ry in
    if rank_rx < rank_ry then
      (* Attach rx under ry *)
      { uf2 with
        parent = IntMap.add rx ry uf2.parent;
        size = IntMap.add ry new_size uf2.size }
    else if rank_rx > rank_ry then
      (* Attach ry under rx *)
      { uf2 with
        parent = IntMap.add ry rx uf2.parent;
        size = IntMap.add rx new_size uf2.size }
    else
      (* Same rank: attach ry under rx and increment rx's rank *)
      { uf2 with
        parent = IntMap.add ry rx uf2.parent;
        rank = IntMap.add rx (rank_rx + 1) uf2.rank;
        size = IntMap.add rx new_size uf2.size }

(* Return the number of distinct components. *)
let num_components uf =
  IntMap.fold (fun k v count ->
    if k = v then count + 1 else count
  ) uf.parent 0

(* Return the size of the component containing element x. *)
let component_size uf x =
  let root = find_root uf x in
  IntMap.find root uf.size

(* Return a list of all root representatives. *)
let roots uf =
  IntMap.fold (fun k v acc ->
    if k = v then k :: acc else acc
  ) uf.parent []
  |> List.rev

(* Return all elements in the same component as x. *)
let component_members uf x =
  let root = find_root uf x in
  IntMap.fold (fun k _v acc ->
    if find_root uf k = root then k :: acc else acc
  ) uf.parent []
  |> List.rev

(* Return a list of all components, each as a sorted list of members. *)
let all_components uf =
  let tbl = Hashtbl.create 16 in
  IntMap.iter (fun k _v ->
    let root = find_root uf k in
    let existing = try Hashtbl.find tbl root with Not_found -> [] in
    Hashtbl.replace tbl root (k :: existing)
  ) uf.parent;
  Hashtbl.fold (fun _root members acc ->
    (List.sort compare members) :: acc
  ) tbl []
  |> List.sort compare

(* Total number of elements in the structure. *)
let cardinal uf = uf.n

(* Check if the structure has exactly one component. *)
let is_single_component uf = num_components uf = 1

(* Create a union-find from a list of union pairs.
   Elements are assumed to be in range [0, n). *)
let of_unions n pairs =
  let uf = create n in
  List.fold_left (fun acc (x, y) -> union acc x y) uf pairs

(* Apply Kruskal's MST algorithm using this union-find.
   edges: list of (weight, u, v) sorted by weight ascending.
   n: number of vertices.
   Returns: list of (weight, u, v) edges in the MST. *)
let kruskal n edges =
  let sorted_edges = List.sort (fun (w1, _, _) (w2, _, _) -> compare w1 w2) edges in
  let rec aux uf mst = function
    | [] -> List.rev mst
    | (w, u, v) :: rest ->
      if connected uf u v then
        aux uf mst rest
      else
        let uf' = union uf u v in
        aux uf' ((w, u, v) :: mst) rest
  in
  aux (create n) [] sorted_edges

(* Detect whether adding edge (u, v) would create a cycle. *)
let would_cycle uf u v = connected uf u v

(* Pretty-print the union-find structure. *)
let to_string uf =
  let components = all_components uf in
  let comp_strs = List.map (fun members ->
    "{" ^ String.concat ", " (List.map string_of_int members) ^ "}"
  ) components in
  Printf.sprintf "UnionFind(%d elems, %d components): %s"
    uf.n (num_components uf) (String.concat " " comp_strs)
