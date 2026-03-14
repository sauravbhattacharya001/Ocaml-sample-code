(* kd_tree.ml — k-dimensional binary search tree for spatial queries.
 *
 * A KD-tree recursively partitions k-dimensional space by alternating
 * the splitting axis at each level.  This provides efficient nearest-
 * neighbour, k-nearest-neighbour, and axis-aligned range queries in
 * O(log n) average case.
 *
 * Features:
 *   - Generic over dimensionality (works with any k)
 *   - Median-of-points construction for balanced trees
 *   - Nearest neighbour search (1-NN)
 *   - K-nearest neighbours (k-NN) with a max-heap
 *   - Axis-aligned rectangular range queries
 *   - Point insertion
 *   - Fold / iter / to_list traversals
 *   - Tree depth and size metrics
 *   - Pretty-print for debugging
 *
 * Complexity (balanced tree, n points, k dimensions):
 *   Build:        O(n k log n)  — median finding at each level
 *   1-NN lookup:  O(log n) avg, O(n) worst
 *   k-NN lookup:  O(log n) avg + O(k_nn log k_nn)
 *   Range query:  O(√n + m) avg  (m = number of reported points)
 *   Insert:       O(log n) avg   (may unbalance tree)
 *
 * Usage:
 *   let points = [| [|1.0; 2.0|]; [|3.0; 4.0|]; [|5.0; 1.0|] |] in
 *   let tree = KdTree.build 2 points in
 *   let nn = KdTree.nearest tree [|2.0; 3.0|] in
 *   let knn = KdTree.k_nearest tree [|2.0; 3.0|] 2 in
 *   let range = KdTree.range_query tree [|0.0; 0.0|] [|4.0; 5.0|] in
 *   ...
 *)

(* ── Core types ────────────────────────────────────────────────── *)

(** A point is a float array of length k. *)
type point = float array

(** A KD-tree node. *)
type t =
  | Leaf
  | Node of {
      point : point;       (** The point stored at this node *)
      left  : t;           (** Points with coord[axis] < split *)
      right : t;           (** Points with coord[axis] >= split *)
      axis  : int;         (** Splitting axis (0..k-1) *)
      dim   : int;         (** Dimensionality k *)
    }

(** Squared Euclidean distance between two points. *)
let sq_dist (a : point) (b : point) : float =
  let n = Array.length a in
  let sum = ref 0.0 in
  for i = 0 to n - 1 do
    let d = a.(i) -. b.(i) in
    sum := !sum +. d *. d
  done;
  !sum

(* ── Construction ──────────────────────────────────────────────── *)

(** Build a balanced KD-tree from an array of points.
    [k] is the dimensionality.  All points must have length [k]. *)
let build (k : int) (points : point array) : t =
  if k < 1 then invalid_arg "KdTree.build: k must be >= 1";
  let n = Array.length points in
  if n = 0 then Leaf
  else begin
    (* Validate dimensions *)
    Array.iter (fun p ->
      if Array.length p <> k then
        invalid_arg (Printf.sprintf
          "KdTree.build: expected %d-dimensional point, got %d" k (Array.length p))
    ) points;
    (* Copy so we don't mutate the caller's array *)
    let pts = Array.copy points in
    let rec aux arr depth =
      let len = Array.length arr in
      if len = 0 then Leaf
      else
        let axis = depth mod k in
        (* Sort by the current axis and pick the median *)
        Array.sort (fun a b -> compare a.(axis) b.(axis)) arr;
        let mid = len / 2 in
        let median = arr.(mid) in
        let left_arr  = Array.sub arr 0 mid in
        let right_arr = Array.sub arr (mid + 1) (len - mid - 1) in
        Node {
          point = median;
          left  = aux left_arr  (depth + 1);
          right = aux right_arr (depth + 1);
          axis;
          dim = k;
        }
    in
    aux pts 0
  end

(** Create a tree containing a single point. *)
let singleton (k : int) (p : point) : t =
  if Array.length p <> k then
    invalid_arg "KdTree.singleton: point dimension mismatch";
  Node { point = p; left = Leaf; right = Leaf; axis = 0; dim = k }

(** Insert a point into an existing tree.
    Note: repeated insertions without rebuilding may unbalance the tree. *)
let rec insert (tree : t) (p : point) : t =
  match tree with
  | Leaf ->
    (* Infer dimensionality from the point *)
    let k = Array.length p in
    Node { point = p; left = Leaf; right = Leaf; axis = 0; dim = k }
  | Node n ->
    if Array.length p <> n.dim then
      invalid_arg "KdTree.insert: point dimension mismatch";
    let next_axis = (n.axis + 1) mod n.dim in
    if p.(n.axis) < n.point.(n.axis) then
      Node { n with left = insert_at n.left p next_axis n.dim }
    else
      Node { n with right = insert_at n.right p next_axis n.dim }

and insert_at (tree : t) (p : point) (axis : int) (dim : int) : t =
  match tree with
  | Leaf ->
    Node { point = p; left = Leaf; right = Leaf; axis; dim }
  | Node n ->
    let next_axis = (n.axis + 1) mod n.dim in
    if p.(n.axis) < n.point.(n.axis) then
      Node { n with left = insert_at n.left p next_axis n.dim }
    else
      Node { n with right = insert_at n.right p next_axis n.dim }

(* ── Queries ───────────────────────────────────────────────────── *)

(** Find the nearest neighbour to [query].
    Returns [None] for an empty tree, [Some (point, squared_distance)]
    otherwise. *)
let nearest (tree : t) (query : point) : (point * float) option =
  let best_pt  = ref [||] in
  let best_dist = ref infinity in
  let rec search node =
    match node with
    | Leaf -> ()
    | Node n ->
      let d = sq_dist n.point query in
      if d < !best_dist then begin
        best_dist := d;
        best_pt   := n.point
      end;
      let diff = query.(n.axis) -. n.point.(n.axis) in
      let near, far = if diff < 0.0 then (n.left, n.right)
                       else (n.right, n.left) in
      search near;
      (* Only search far subtree if the splitting plane is closer
         than the current best. *)
      if diff *. diff < !best_dist then
        search far
  in
  search tree;
  if !best_pt = [||] then None
  else Some (!best_pt, !best_dist)

(** A bounded max-heap for k-NN (keeps the k closest points). *)
module MaxHeap = struct
  type entry = { pt : point; dist : float }

  type heap = {
    mutable data : entry array;
    mutable size : int;
    capacity : int;
  }

  let create cap = {
    data = Array.make cap { pt = [||]; dist = infinity };
    size = 0;
    capacity = cap;
  }

  let swap h i j =
    let tmp = h.data.(i) in
    h.data.(i) <- h.data.(j);
    h.data.(j) <- tmp

  let sift_up h idx =
    let i = ref idx in
    while !i > 0 do
      let parent = (!i - 1) / 2 in
      if h.data.(!i).dist > h.data.(parent).dist then begin
        swap h !i parent;
        i := parent
      end else
        i := 0  (* break *)
    done

  let sift_down h idx =
    let i = ref idx in
    let cont = ref true in
    while !cont do
      let left  = 2 * !i + 1 in
      let right = 2 * !i + 2 in
      let largest = ref !i in
      if left < h.size && h.data.(left).dist > h.data.(!largest).dist then
        largest := left;
      if right < h.size && h.data.(right).dist > h.data.(!largest).dist then
        largest := right;
      if !largest <> !i then begin
        swap h !i !largest;
        i := !largest
      end else
        cont := false
    done

  let max_dist h =
    if h.size = 0 then infinity
    else h.data.(0).dist

  let push h pt dist =
    if h.size < h.capacity then begin
      h.data.(h.size) <- { pt; dist };
      h.size <- h.size + 1;
      sift_up h (h.size - 1)
    end else if dist < h.data.(0).dist then begin
      h.data.(0) <- { pt; dist };
      sift_down h 0
    end

  let to_list h =
    let entries = Array.sub h.data 0 h.size in
    let sorted = Array.copy entries in
    Array.sort (fun a b -> compare a.dist b.dist) sorted;
    Array.to_list sorted |> List.map (fun e -> (e.pt, e.dist))
end

(** Find the [k_nn] nearest neighbours to [query].
    Returns a list of [(point, squared_distance)] sorted by distance
    (closest first).  Returns fewer than [k_nn] if the tree has
    fewer points. *)
let k_nearest (tree : t) (query : point) (k_nn : int) : (point * float) list =
  if k_nn <= 0 then []
  else
    let heap = MaxHeap.create k_nn in
    let rec search node =
      match node with
      | Leaf -> ()
      | Node n ->
        let d = sq_dist n.point query in
        MaxHeap.push heap n.point d;
        let diff = query.(n.axis) -. n.point.(n.axis) in
        let near, far = if diff < 0.0 then (n.left, n.right)
                         else (n.right, n.left) in
        search near;
        if diff *. diff < MaxHeap.max_dist heap then
          search far
    in
    search tree;
    MaxHeap.to_list heap

(** Find all points inside the axis-aligned bounding box
    defined by [lo] and [hi] (inclusive on both ends).
    Returns the list of matching points. *)
let range_query (tree : t) (lo : point) (hi : point) : point list =
  let results = ref [] in
  let rec search node =
    match node with
    | Leaf -> ()
    | Node n ->
      (* Check if this point is inside the box *)
      let inside = ref true in
      for i = 0 to n.dim - 1 do
        if n.point.(i) < lo.(i) || n.point.(i) > hi.(i) then
          inside := false
      done;
      if !inside then
        results := n.point :: !results;
      (* Prune: only visit subtrees that could intersect the box *)
      if lo.(n.axis) < n.point.(n.axis) then
        search n.left;
      if hi.(n.axis) >= n.point.(n.axis) then
        search n.right
  in
  search tree;
  List.rev !results

(** Find all points within squared distance [radius_sq] of [center]. *)
let radius_query (tree : t) (center : point) (radius_sq : float) : (point * float) list =
  let results = ref [] in
  let rec search node =
    match node with
    | Leaf -> ()
    | Node n ->
      let d = sq_dist n.point center in
      if d <= radius_sq then
        results := (n.point, d) :: !results;
      let diff = center.(n.axis) -. n.point.(n.axis) in
      let near, far = if diff < 0.0 then (n.left, n.right)
                       else (n.right, n.left) in
      search near;
      if diff *. diff <= radius_sq then
        search far
  in
  search tree;
  List.rev !results

(* ── Traversal ─────────────────────────────────────────────────── *)

(** Fold over all points in the tree (in-order). *)
let rec fold (f : 'a -> point -> 'a) (acc : 'a) (tree : t) : 'a =
  match tree with
  | Leaf -> acc
  | Node n ->
    let acc = fold f acc n.left in
    let acc = f acc n.point in
    fold f acc n.right

(** Iterate a function over all points (in-order). *)
let iter (f : point -> unit) (tree : t) : unit =
  fold (fun () p -> f p) () tree

(** Collect all points into a list (in-order). *)
let to_list (tree : t) : point list =
  List.rev (fold (fun acc p -> p :: acc) [] tree)

(** Number of points in the tree. *)
let size (tree : t) : int =
  fold (fun n _ -> n + 1) 0 tree

(** Maximum depth of the tree (Leaf = 0). *)
let rec depth (tree : t) : int =
  match tree with
  | Leaf -> 0
  | Node n -> 1 + max (depth n.left) (depth n.right)

(** Check if the tree is empty. *)
let is_empty (tree : t) : bool =
  match tree with
  | Leaf -> true
  | Node _ -> false

(** Compute the axis-aligned bounding box of all points.
    Returns [None] for an empty tree, [Some (lo, hi)] otherwise. *)
let bounding_box (tree : t) : (point * point) option =
  match tree with
  | Leaf -> None
  | Node n ->
    let k = n.dim in
    let lo = Array.copy (to_list tree |> List.hd) in
    let hi = Array.copy lo in
    iter (fun p ->
      for i = 0 to k - 1 do
        if p.(i) < lo.(i) then lo.(i) <- p.(i);
        if p.(i) > hi.(i) then hi.(i) <- p.(i)
      done
    ) tree;
    Some (lo, hi)

(* ── Pretty-printing ───────────────────────────────────────────── *)

(** Format a point as a string like "(1.0, 2.0, 3.0)". *)
let string_of_point (p : point) : string =
  let parts = Array.to_list p |> List.map (Printf.sprintf "%.4g") in
  "(" ^ String.concat ", " parts ^ ")"

(** Pretty-print the tree structure. *)
let pp (tree : t) : string =
  let buf = Buffer.create 256 in
  let rec aux indent node =
    match node with
    | Leaf ->
      Buffer.add_string buf indent;
      Buffer.add_string buf "·\n"
    | Node n ->
      Buffer.add_string buf indent;
      Buffer.add_string buf
        (Printf.sprintf "%s [axis=%d]\n" (string_of_point n.point) n.axis);
      aux (indent ^ "  ├─") n.left;
      aux (indent ^ "  └─") n.right
  in
  aux "" tree;
  Buffer.contents buf

(* ── Tests ─────────────────────────────────────────────────────── *)

let () =
  let module A = Alcotest in

  (* ── Helpers ──────────────────────────────────────────────── *)

  let pt_eq a b =
    Array.length a = Array.length b &&
    Array.for_all2 (fun x y -> Float.abs (x -. y) < 1e-10) a b
  in
  let float_close a b = Float.abs (a -. b) < 1e-9 in

  (* ── Test data ────────────────────────────────────────────── *)

  let pts_2d = [|
    [|2.0; 3.0|]; [|5.0; 4.0|]; [|9.0; 6.0|];
    [|4.0; 7.0|]; [|8.0; 1.0|]; [|7.0; 2.0|];
  |] in
  let pts_3d = [|
    [|1.0; 2.0; 3.0|]; [|4.0; 5.0; 6.0|]; [|7.0; 8.0; 9.0|];
    [|2.0; 1.0; 5.0|]; [|6.0; 3.0; 4.0|]; [|3.0; 7.0; 1.0|];
  |] in

  (* ── Build ────────────────────────────────────────────────── *)

  let test_build_empty () =
    let t = build 2 [||] in
    A.check A.bool "empty tree" true (is_empty t);
    A.check A.int "size 0" 0 (size t)
  in

  let test_build_single () =
    let t = build 2 [| [|1.0; 2.0|] |] in
    A.check A.int "size 1" 1 (size t);
    A.check A.int "depth 1" 1 (depth t)
  in

  let test_build_2d () =
    let t = build 2 pts_2d in
    A.check A.int "size" 6 (size t);
    A.check A.bool "not empty" false (is_empty t);
    (* All points should be in the tree *)
    let all = to_list t in
    Array.iter (fun p ->
      A.check A.bool (Printf.sprintf "%s in tree" (string_of_point p))
        true (List.exists (pt_eq p) all)
    ) pts_2d
  in

  let test_build_3d () =
    let t = build 3 pts_3d in
    A.check A.int "size" 6 (size t)
  in

  let test_build_invalid_dim () =
    let threw = ref false in
    (try ignore (build 3 [| [|1.0; 2.0|] |]) with Invalid_argument _ -> threw := true);
    A.check A.bool "dimension mismatch raises" true !threw
  in

  let test_build_invalid_k () =
    let threw = ref false in
    (try ignore (build 0 [||]) with Invalid_argument _ -> threw := true);
    A.check A.bool "k=0 raises" true !threw
  in

  (* ── Singleton ────────────────────────────────────────────── *)

  let test_singleton () =
    let t = singleton 3 [|1.0; 2.0; 3.0|] in
    A.check A.int "size" 1 (size t);
    A.check A.int "depth" 1 (depth t);
    let pts = to_list t in
    A.check A.bool "contains point" true (pt_eq (List.hd pts) [|1.0; 2.0; 3.0|])
  in

  let test_singleton_dim_mismatch () =
    let threw = ref false in
    (try ignore (singleton 2 [|1.0; 2.0; 3.0|]) with Invalid_argument _ -> threw := true);
    A.check A.bool "mismatch raises" true !threw
  in

  (* ── Insert ───────────────────────────────────────────────── *)

  let test_insert_into_leaf () =
    let t = insert Leaf [|1.0; 2.0|] in
    A.check A.int "size" 1 (size t)
  in

  let test_insert_multiple () =
    let t = build 2 [| [|1.0; 2.0|]; [|3.0; 4.0|] |] in
    let t = insert t [|5.0; 6.0|] in
    let t = insert t [|0.0; 0.0|] in
    A.check A.int "size after inserts" 4 (size t);
    let pts = to_list t in
    A.check A.bool "new point present" true
      (List.exists (pt_eq [|5.0; 6.0|]) pts)
  in

  let test_insert_dim_mismatch () =
    let t = build 2 [| [|1.0; 2.0|] |] in
    let threw = ref false in
    (try ignore (insert t [|1.0; 2.0; 3.0|]) with Invalid_argument _ -> threw := true);
    A.check A.bool "dim mismatch raises" true !threw
  in

  (* ── Nearest ──────────────────────────────────────────────── *)

  let test_nearest_empty () =
    let t = build 2 [||] in
    A.check A.bool "empty → None" true (nearest t [|0.0; 0.0|] = None)
  in

  let test_nearest_exact_match () =
    let t = build 2 pts_2d in
    match nearest t [|5.0; 4.0|] with
    | None -> A.fail "expected Some"
    | Some (p, d) ->
      A.check A.bool "exact match" true (pt_eq p [|5.0; 4.0|]);
      A.check A.bool "dist = 0" true (float_close d 0.0)
  in

  let test_nearest_closest () =
    let t = build 2 pts_2d in
    (* Query (3, 3) — closest should be (2,3) at dist 1 *)
    match nearest t [|3.0; 3.0|] with
    | None -> A.fail "expected Some"
    | Some (p, d) ->
      A.check A.bool "closest is (2,3)" true (pt_eq p [|2.0; 3.0|]);
      A.check A.bool "dist = 1.0" true (float_close d 1.0)
  in

  let test_nearest_3d () =
    let t = build 3 pts_3d in
    match nearest t [|1.5; 1.5; 4.0|] with
    | None -> A.fail "expected Some"
    | Some (p, _) ->
      (* Should be close to (1,2,3) or (2,1,5) *)
      A.check A.bool "some point returned" true (Array.length p = 3)
  in

  (* ── K-nearest ────────────────────────────────────────────── *)

  let test_knn_empty () =
    let t = build 2 [||] in
    let res = k_nearest t [|0.0; 0.0|] 3 in
    A.check A.int "empty → 0 results" 0 (List.length res)
  in

  let test_knn_k0 () =
    let t = build 2 pts_2d in
    let res = k_nearest t [|0.0; 0.0|] 0 in
    A.check A.int "k=0 → 0 results" 0 (List.length res)
  in

  let test_knn_sorted () =
    let t = build 2 pts_2d in
    let res = k_nearest t [|3.0; 3.0|] 3 in
    A.check A.int "3 results" 3 (List.length res);
    (* Check sorted by distance *)
    let dists = List.map snd res in
    let sorted = List.sort compare dists in
    A.check A.bool "sorted" true (dists = sorted)
  in

  let test_knn_all () =
    let t = build 2 pts_2d in
    let res = k_nearest t [|0.0; 0.0|] 100 in
    A.check A.int "returns all points" 6 (List.length res)
  in

  let test_knn_exact_match () =
    let t = build 2 pts_2d in
    let res = k_nearest t [|5.0; 4.0|] 1 in
    A.check A.int "1 result" 1 (List.length res);
    let (p, d) = List.hd res in
    A.check A.bool "exact match" true (pt_eq p [|5.0; 4.0|]);
    A.check A.bool "dist 0" true (float_close d 0.0)
  in

  (* ── Range query ──────────────────────────────────────────── *)

  let test_range_empty () =
    let t = build 2 [||] in
    let res = range_query t [|0.0; 0.0|] [|10.0; 10.0|] in
    A.check A.int "empty → 0" 0 (List.length res)
  in

  let test_range_all () =
    let t = build 2 pts_2d in
    let res = range_query t [|0.0; 0.0|] [|10.0; 10.0|] in
    A.check A.int "all in range" 6 (List.length res)
  in

  let test_range_none () =
    let t = build 2 pts_2d in
    let res = range_query t [|100.0; 100.0|] [|200.0; 200.0|] in
    A.check A.int "none in range" 0 (List.length res)
  in

  let test_range_partial () =
    let t = build 2 pts_2d in
    (* Box [0,0]–[5,5] should include (2,3), (5,4), (4,7)→ no, 7>5 *)
    let res = range_query t [|0.0; 0.0|] [|5.0; 5.0|] in
    (* (2,3), (5,4) should be in; (4,7) y=7>5 out *)
    List.iter (fun p ->
      A.check A.bool "in x range" true (p.(0) >= 0.0 && p.(0) <= 5.0);
      A.check A.bool "in y range" true (p.(1) >= 0.0 && p.(1) <= 5.0)
    ) res;
    A.check A.bool "some found" true (List.length res > 0)
  in

  let test_range_exact_boundary () =
    let t = build 2 [| [|5.0; 5.0|]; [|10.0; 10.0|] |] in
    let res = range_query t [|5.0; 5.0|] [|5.0; 5.0|] in
    A.check A.int "exact boundary" 1 (List.length res);
    A.check A.bool "correct point" true (pt_eq (List.hd res) [|5.0; 5.0|])
  in

  (* ── Radius query ─────────────────────────────────────────── *)

  let test_radius_empty () =
    let t = build 2 [||] in
    let res = radius_query t [|0.0; 0.0|] 100.0 in
    A.check A.int "empty → 0" 0 (List.length res)
  in

  let test_radius_basic () =
    let t = build 2 pts_2d in
    (* Radius² = 5 around (2,3): should find (2,3) at d²=0 *)
    let res = radius_query t [|2.0; 3.0|] 5.0 in
    A.check A.bool "at least self" true (List.length res >= 1);
    A.check A.bool "contains (2,3)" true
      (List.exists (fun (p, _) -> pt_eq p [|2.0; 3.0|]) res);
    List.iter (fun (_, d) ->
      A.check A.bool "within radius" true (d <= 5.0)
    ) res
  in

  let test_radius_zero () =
    let t = build 2 pts_2d in
    let res = radius_query t [|2.0; 3.0|] 0.0 in
    A.check A.int "radius 0 → exact match only" 1 (List.length res)
  in

  let test_radius_large () =
    let t = build 2 pts_2d in
    let res = radius_query t [|5.0; 5.0|] 10000.0 in
    A.check A.int "huge radius → all" 6 (List.length res)
  in

  (* ── Traversal ────────────────────────────────────────────── *)

  let test_fold_sum () =
    let t = build 2 [| [|1.0; 2.0|]; [|3.0; 4.0|]; [|5.0; 6.0|] |] in
    let total_x = fold (fun acc p -> acc +. p.(0)) 0.0 t in
    A.check A.bool "sum x = 9" true (float_close total_x 9.0)
  in

  let test_to_list_size () =
    let t = build 2 pts_2d in
    let lst = to_list t in
    A.check A.int "to_list length" 6 (List.length lst)
  in

  let test_iter_count () =
    let t = build 2 pts_2d in
    let count = ref 0 in
    iter (fun _ -> incr count) t;
    A.check A.int "iter count" 6 !count
  in

  (* ── Metrics ──────────────────────────────────────────────── *)

  let test_depth_balanced () =
    (* 6 points → balanced depth should be 3 (log2(6) ≈ 2.58, ceil = 3) *)
    let t = build 2 pts_2d in
    let d = depth t in
    A.check A.bool "depth 2..4" true (d >= 2 && d <= 4)
  in

  let test_depth_leaf () =
    A.check A.int "leaf depth = 0" 0 (depth Leaf)
  in

  (* ── Bounding box ─────────────────────────────────────────── *)

  let test_bbox_empty () =
    A.check A.bool "empty → None" true (bounding_box Leaf = None)
  in

  let test_bbox_2d () =
    let t = build 2 pts_2d in
    match bounding_box t with
    | None -> A.fail "expected Some"
    | Some (lo, hi) ->
      A.check A.bool "lo x" true (float_close lo.(0) 2.0);
      A.check A.bool "lo y" true (float_close lo.(1) 1.0);
      A.check A.bool "hi x" true (float_close hi.(0) 9.0);
      A.check A.bool "hi y" true (float_close hi.(1) 7.0)
  in

  (* ── Pretty print ─────────────────────────────────────────── *)

  let test_pp_empty () =
    let s = pp Leaf in
    A.check A.bool "leaf prints ·" true (String.length s > 0)
  in

  let test_pp_nonempty () =
    let t = build 2 [| [|1.0; 2.0|]; [|3.0; 4.0|] |] in
    let s = pp t in
    A.check A.bool "contains axis" true (String.length s > 10)
  in

  let test_string_of_point () =
    let s = string_of_point [|1.0; 2.5; 3.0|] in
    A.check A.bool "formatted" true (s = "(1, 2.5, 3)")
  in

  (* ── 1D edge case ─────────────────────────────────────────── *)

  let test_1d () =
    let t = build 1 [| [|3.0|]; [|1.0|]; [|4.0|]; [|1.5|]; [|9.0|] |] in
    A.check A.int "size" 5 (size t);
    match nearest t [|2.0|] with
    | None -> A.fail "expected Some"
    | Some (p, d) ->
      A.check A.bool "nearest to 2.0 is 1.5" true (float_close p.(0) 1.5);
      A.check A.bool "dist = 0.25" true (float_close d 0.25)
  in

  (* ── High dimension ───────────────────────────────────────── *)

  let test_high_dim () =
    let k = 10 in
    let pts = Array.init 20 (fun i ->
      Array.init k (fun j -> float_of_int (i * k + j))
    ) in
    let t = build k pts in
    A.check A.int "size" 20 (size t);
    let nn = nearest t (Array.make k 0.0) in
    A.check A.bool "found nn" true (nn <> None)
  in

  (* ── Duplicate points ─────────────────────────────────────── *)

  let test_duplicates () =
    let pts = [| [|1.0; 1.0|]; [|1.0; 1.0|]; [|1.0; 1.0|]; [|2.0; 2.0|] |] in
    let t = build 2 pts in
    A.check A.int "size with dups" 4 (size t);
    let res = k_nearest t [|1.0; 1.0|] 4 in
    A.check A.int "knn returns all" 4 (List.length res)
  in

  (* ── Run all tests ────────────────────────────────────────── *)

  let open Alcotest in
  run "KdTree" [
    "build", [
      test_case "empty"           `Quick test_build_empty;
      test_case "single"          `Quick test_build_single;
      test_case "2d"              `Quick test_build_2d;
      test_case "3d"              `Quick test_build_3d;
      test_case "invalid dim"     `Quick test_build_invalid_dim;
      test_case "invalid k"       `Quick test_build_invalid_k;
    ];
    "singleton", [
      test_case "basic"           `Quick test_singleton;
      test_case "dim mismatch"    `Quick test_singleton_dim_mismatch;
    ];
    "insert", [
      test_case "into leaf"       `Quick test_insert_into_leaf;
      test_case "multiple"        `Quick test_insert_multiple;
      test_case "dim mismatch"    `Quick test_insert_dim_mismatch;
    ];
    "nearest", [
      test_case "empty"           `Quick test_nearest_empty;
      test_case "exact match"     `Quick test_nearest_exact_match;
      test_case "closest"         `Quick test_nearest_closest;
      test_case "3d"              `Quick test_nearest_3d;
    ];
    "k_nearest", [
      test_case "empty"           `Quick test_knn_empty;
      test_case "k=0"             `Quick test_knn_k0;
      test_case "sorted"          `Quick test_knn_sorted;
      test_case "all"             `Quick test_knn_all;
      test_case "exact match"     `Quick test_knn_exact_match;
    ];
    "range_query", [
      test_case "empty"           `Quick test_range_empty;
      test_case "all"             `Quick test_range_all;
      test_case "none"            `Quick test_range_none;
      test_case "partial"         `Quick test_range_partial;
      test_case "exact boundary"  `Quick test_range_exact_boundary;
    ];
    "radius_query", [
      test_case "empty"           `Quick test_radius_empty;
      test_case "basic"           `Quick test_radius_basic;
      test_case "zero radius"     `Quick test_radius_zero;
      test_case "large radius"    `Quick test_radius_large;
    ];
    "traversal", [
      test_case "fold sum"        `Quick test_fold_sum;
      test_case "to_list size"    `Quick test_to_list_size;
      test_case "iter count"      `Quick test_iter_count;
    ];
    "metrics", [
      test_case "depth balanced"  `Quick test_depth_balanced;
      test_case "depth leaf"      `Quick test_depth_leaf;
    ];
    "bounding_box", [
      test_case "empty"           `Quick test_bbox_empty;
      test_case "2d"              `Quick test_bbox_2d;
    ];
    "pretty_print", [
      test_case "empty"           `Quick test_pp_empty;
      test_case "nonempty"        `Quick test_pp_nonempty;
      test_case "string_of_point" `Quick test_string_of_point;
    ];
    "edge_cases", [
      test_case "1d"              `Quick test_1d;
      test_case "high dimension"  `Quick test_high_dim;
      test_case "duplicates"      `Quick test_duplicates;
    ];
  ]
