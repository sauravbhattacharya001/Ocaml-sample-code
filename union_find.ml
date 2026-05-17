(** {1 Persistent Union-Find (Disjoint Sets)}

    A purely functional union-find data structure backed by balanced
    integer maps. Each operation returns a new structure; older versions
    remain valid (and shared in memory).

    Compared with the classic imperative union-find that mutates parent
    arrays in place, this version trades the inverse-Ackermann amortised
    bound for a clean [O(log n)] amortised cost per operation —
    fast enough for most functional use cases.

    {2 Complexity (amortised)}
    - {!find} : [O(log n)]
    - {!union} : [O(log n)]
    - {!connected}, {!num_components}, {!component_size} : [O(log n)]

    {2 Example}
    {[
      let uf = create 10 in
      let uf = union uf 0 1 in
      let uf = union uf 2 3 in
      assert (connected uf 0 1);          (* true  *)
      assert (not (connected uf 0 2));    (* true  *)
      assert (num_components uf = 8)
    ]}
*)

module IntMap = Map.Make(Int)

(** Internal state. Each element maps to a parent (itself if root),
    plus per-root rank and component size. *)
type t = {
  parent : int IntMap.t;
  rank   : int IntMap.t;
  size   : int IntMap.t;   (** size of each component, stored at its root *)
  n      : int;            (** total number of elements *)
}

(** [create n] builds a fresh union-find on elements [\{0, 1, ..., n-1\}],
    each in its own singleton component.
    @raise Invalid_argument if [n < 0]. *)
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

(** [find uf x] returns [(root, uf')] where [root] is the representative
    of [x]'s component and [uf'] is [uf] with path compression applied
    along the lookup path. Pass [uf'] forward to benefit from compression.
    @raise Invalid_argument if [x] is out of range. *)
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

(** [find_root uf x] returns the representative of [x]'s component
    without mutating [uf] (no path compression). Cheaper to call when
    you only need the root and won't reuse the compressed structure.
    @raise Invalid_argument if [x] is out of range. *)
let rec find_root uf x =
  if not (IntMap.mem x uf.parent) then
    invalid_arg (Printf.sprintf "UnionFind.find_root: element %d out of range" x);
  let px = IntMap.find x uf.parent in
  if px = x then x
  else find_root uf px

(** [connected uf x y] is [true] iff [x] and [y] are in the same
    component. Does not modify [uf]. *)
let connected uf x y =
  find_root uf x = find_root uf y

(** [union uf x y] merges the components containing [x] and [y] using
    union-by-rank. If they are already connected, [uf] is returned
    unchanged. *)
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

(** [num_components uf] returns the number of disjoint components. *)
let num_components uf =
  IntMap.fold (fun k v count ->
    if k = v then count + 1 else count
  ) uf.parent 0

(** [component_size uf x] is the number of elements in the same
    component as [x]. *)
let component_size uf x =
  let root = find_root uf x in
  IntMap.find root uf.size

(** [roots uf] returns the sorted list of all component representatives. *)
let roots uf =
  IntMap.fold (fun k v acc ->
    if k = v then k :: acc else acc
  ) uf.parent []
  |> List.rev

(** [component_members uf x] returns the sorted list of elements in the
    same component as [x]. *)
let component_members uf x =
  let root = find_root uf x in
  IntMap.fold (fun k _v acc ->
    if find_root uf k = root then k :: acc else acc
  ) uf.parent []
  |> List.rev

(** [all_components uf] returns every component as a sorted list of
    members; the outer list is itself sorted lexicographically. *)
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

(** [cardinal uf] is the total number of elements in [uf]. *)
let cardinal uf = uf.n

(** [is_single_component uf] is [true] iff every element is in the same
    component (i.e. [num_components uf = 1]). *)
let is_single_component uf = num_components uf = 1

(** [of_unions n pairs] builds a union-find on [n] elements and applies
    each [(x, y)] pair in [pairs] as a union. *)
let of_unions n pairs =
  let uf = create n in
  List.fold_left (fun acc (x, y) -> union acc x y) uf pairs

(** [kruskal n edges] runs Kruskal's MST algorithm.
    [edges] is a list of [(weight, u, v)] triples; vertices are in
    [\[0, n)]. Returns the MST as a list of [(weight, u, v)] in the
    order they were chosen (ascending weight). *)
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

(** [would_cycle uf u v] is [true] iff adding the edge [(u, v)] to
    the implied graph would close a cycle. *)
let would_cycle uf u v = connected uf u v

(** [to_string uf] renders [uf] as a human-readable summary of the form
    ["UnionFind(N elems, K components): {...} {...}"]. *)
let to_string uf =
  let components = all_components uf in
  let comp_strs = List.map (fun members ->
    "{" ^ String.concat ", " (List.map string_of_int members) ^ "}"
  ) components in
  Printf.sprintf "UnionFind(%d elems, %d components): %s"
    uf.n (num_components uf) (String.concat " " comp_strs)
