(* Segment Tree — efficient range queries and point updates *)
(* Supports range sum, min, and max queries in O(log n) time *)
(* with O(n) space. Point updates also run in O(log n).     *)
(* Demonstrates: functors, modules, recursive data structures *)

(* ── Module signature for combining elements ──────────────── *)

module type MONOID = sig
  type t
  val identity : t
  val combine : t -> t -> t
end

(* ── Segment Tree functor ─────────────────────────────────── *)

module Make (M : MONOID) = struct

  type tree =
    | Leaf of { idx: int; value: M.t }
    | Node of { left: tree; right: tree; lo: int; hi: int; aggregate: M.t }
    | Empty

  (* Build a segment tree from an array (list) of values *)
  let build (arr : M.t list) : tree =
    let a = Array.of_list arr in
    let n = Array.length a in
    if n = 0 then Empty
    else
      let rec aux lo hi =
        if lo = hi then
          Leaf { idx = lo; value = a.(lo) }
        else
          let mid = lo + (hi - lo) / 2 in
          let l = aux lo mid in
          let r = aux (mid + 1) hi in
          let agg = M.combine (aggregate_of l) (aggregate_of r) in
          Node { left = l; right = r; lo; hi; aggregate = agg }
      and aggregate_of = function
        | Empty -> M.identity
        | Leaf { value; _ } -> value
        | Node { aggregate; _ } -> aggregate
      in
      aux 0 (n - 1)

  (* Query the aggregate over range [ql, qr] inclusive *)
  let rec query ql qr = function
    | Empty -> M.identity
    | Leaf { idx; value } ->
      if idx >= ql && idx <= qr then value
      else M.identity
    | Node { left; right; lo; hi; aggregate; _ } ->
      if ql <= lo && hi <= qr then aggregate       (* fully contained *)
      else if qr < lo || ql > hi then M.identity   (* disjoint *)
      else M.combine (query ql qr left) (query ql qr right)

  (* Update the value at index i to new_val *)
  let rec update i new_val = function
    | Empty -> Empty
    | Leaf { idx; _ } as leaf ->
      if idx = i then Leaf { idx; value = new_val }
      else leaf
    | Node { left; right; lo; hi; _ } ->
      let left' = update i new_val left in
      let right' = update i new_val right in
      let agg = M.combine (aggregate_of left') (aggregate_of right') in
      Node { left = left'; right = right'; lo; hi; aggregate = agg }

  and aggregate_of = function
    | Empty -> M.identity
    | Leaf { value; _ } -> value
    | Node { aggregate; _ } -> aggregate

  (* Fold over all leaves left-to-right *)
  let rec fold_leaves f acc = function
    | Empty -> acc
    | Leaf { idx; value } -> f acc idx value
    | Node { left; right; _ } -> fold_leaves f (fold_leaves f acc left) right

  (* Convert tree contents to a list of (index, value) pairs *)
  let to_list tree =
    List.rev (fold_leaves (fun acc idx value -> (idx, value) :: acc) [] tree)

  (* Pretty-print the tree structure *)
  let rec pp fmt_val indent = function
    | Empty -> Printf.printf "%sEmpty\n" indent
    | Leaf { idx; value } ->
      Printf.printf "%sLeaf[%d] = %s\n" indent idx (fmt_val value)
    | Node { left; right; lo; hi; aggregate; _ } ->
      Printf.printf "%sNode[%d..%d] agg=%s\n" indent lo hi (fmt_val aggregate);
      pp fmt_val (indent ^ "  ") left;
      pp fmt_val (indent ^ "  ") right

end

(* ── Concrete instantiations ──────────────────────────────── *)

(* Sum monoid *)
module SumMonoid = struct
  type t = int
  let identity = 0
  let combine = ( + )
end

(* Min monoid *)
module MinMonoid = struct
  type t = int
  let identity = max_int
  let combine a b = if a < b then a else b
end

(* Max monoid *)
module MaxMonoid = struct
  type t = int
  let identity = min_int
  let combine a b = if a > b then a else b
end

module SumTree = Make(SumMonoid)
module MinTree = Make(MinMonoid)
module MaxTree = Make(MaxMonoid)

(* ── Demo ─────────────────────────────────────────────────── *)

let () =
  let data = [5; 3; 7; 1; 4; 6; 2; 8] in
  Printf.printf "=== Segment Tree Demo ===\n\n";
  Printf.printf "Input: [%s]\n\n"
    (String.concat "; " (List.map string_of_int data));

  (* Sum queries *)
  let sum_tree = SumTree.build data in
  Printf.printf "Sum Tree:\n";
  SumTree.pp string_of_int "  " sum_tree;
  Printf.printf "\n";
  Printf.printf "Sum[0..7] = %d  (expected 36)\n" (SumTree.query 0 7 sum_tree);
  Printf.printf "Sum[2..5] = %d  (expected 18)\n" (SumTree.query 2 5 sum_tree);
  Printf.printf "Sum[0..0] = %d  (expected 5)\n" (SumTree.query 0 0 sum_tree);

  (* Update and re-query *)
  let sum_tree' = SumTree.update 3 10 sum_tree in
  Printf.printf "\nAfter update index 3 -> 10:\n";
  Printf.printf "Sum[0..7] = %d  (expected 45)\n" (SumTree.query 0 7 sum_tree');
  Printf.printf "Sum[2..5] = %d  (expected 27)\n" (SumTree.query 2 5 sum_tree');

  (* Min queries *)
  Printf.printf "\n--- Min Tree ---\n";
  let min_tree = MinTree.build data in
  Printf.printf "Min[0..7] = %d  (expected 1)\n" (MinTree.query 0 7 min_tree);
  Printf.printf "Min[0..3] = %d  (expected 1)\n" (MinTree.query 0 3 min_tree);
  Printf.printf "Min[4..7] = %d  (expected 2)\n" (MinTree.query 4 7 min_tree);

  (* Max queries *)
  Printf.printf "\n--- Max Tree ---\n";
  let max_tree = MaxTree.build data in
  Printf.printf "Max[0..7] = %d  (expected 8)\n" (MaxTree.query 0 7 max_tree);
  Printf.printf "Max[0..3] = %d  (expected 7)\n" (MaxTree.query 0 3 max_tree);
  Printf.printf "Max[2..5] = %d  (expected 7)\n" (MaxTree.query 2 5 max_tree);

  Printf.printf "\n=== Done ===\n"
