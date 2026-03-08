(* test_segment_tree.ml — Tests for Segment Tree module *)
(* Covers: build, query (sum/min/max), point update, edge cases,
   to_list, fold_leaves, empty tree, single element, large inputs. *)

(* ── Inline the module since OCaml doesn't support multi-file linking
   without a build system.  We replicate the core types and functor. ── *)

module type MONOID = sig
  type t
  val identity : t
  val combine : t -> t -> t
end

module Make (M : MONOID) = struct

  type tree =
    | Leaf of { idx: int; value: M.t }
    | Node of { left: tree; right: tree; lo: int; hi: int; aggregate: M.t }
    | Empty

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

  let rec query ql qr = function
    | Empty -> M.identity
    | Leaf { idx; value } ->
      if idx >= ql && idx <= qr then value
      else M.identity
    | Node { left; right; lo; hi; aggregate; _ } ->
      if ql <= lo && hi <= qr then aggregate
      else if qr < lo || ql > hi then M.identity
      else M.combine (query ql qr left) (query ql qr right)

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

  let rec fold_leaves f acc = function
    | Empty -> acc
    | Leaf { idx; value } -> f acc idx value
    | Node { left; right; _ } -> fold_leaves f (fold_leaves f acc left) right

  let to_list tree =
    List.rev (fold_leaves (fun acc idx value -> (idx, value) :: acc) [] tree)
end

(* ── Concrete monoids ─────────────────────────────────────── *)

module SumMonoid = struct
  type t = int
  let identity = 0
  let combine = ( + )
end

module MinMonoid = struct
  type t = int
  let identity = max_int
  let combine a b = if a < b then a else b
end

module MaxMonoid = struct
  type t = int
  let identity = min_int
  let combine a b = if a > b then a else b
end

module SumTree = Make(SumMonoid)
module MinTree = Make(MinMonoid)
module MaxTree = Make(MaxMonoid)

(* ── Test framework ───────────────────────────────────────── *)

let passed = ref 0
let failed = ref 0
let total  = ref 0

let assert_equal ~msg expected actual =
  incr total;
  if expected = actual then
    incr passed
  else begin
    incr failed;
    Printf.printf "  FAIL: %s — expected %d, got %d\n" msg expected actual
  end

let assert_true ~msg cond =
  incr total;
  if cond then incr passed
  else begin
    incr failed;
    Printf.printf "  FAIL: %s\n" msg
  end

let assert_list_equal ~msg expected actual =
  incr total;
  if expected = actual then incr passed
  else begin
    incr failed;
    let fmt lst = String.concat "; "
      (List.map (fun (i, v) -> Printf.sprintf "(%d,%d)" i v) lst) in
    Printf.printf "  FAIL: %s — expected [%s], got [%s]\n" msg (fmt expected) (fmt actual)
  end

let suite name f =
  Printf.printf "--- %s ---\n" name;
  f ()

(* ── Tests ────────────────────────────────────────────────── *)

let test_sum_build_and_query () = suite "Sum: build & query" (fun () ->
  let data = [5; 3; 7; 1; 4; 6; 2; 8] in
  let tree = SumTree.build data in
  assert_equal ~msg:"full range sum" 36 (SumTree.query 0 7 tree);
  assert_equal ~msg:"subrange [2..5]" 18 (SumTree.query 2 5 tree);
  assert_equal ~msg:"single element [0..0]" 5 (SumTree.query 0 0 tree);
  assert_equal ~msg:"single element [7..7]" 8 (SumTree.query 7 7 tree);
  assert_equal ~msg:"first half [0..3]" 16 (SumTree.query 0 3 tree);
  assert_equal ~msg:"second half [4..7]" 20 (SumTree.query 4 7 tree);
  assert_equal ~msg:"middle pair [3..4]" 5 (SumTree.query 3 4 tree);
)

let test_sum_update () = suite "Sum: point update" (fun () ->
  let data = [5; 3; 7; 1; 4; 6; 2; 8] in
  let tree = SumTree.build data in
  let tree' = SumTree.update 3 10 tree in
  assert_equal ~msg:"after update full range" 45 (SumTree.query 0 7 tree');
  assert_equal ~msg:"after update [2..5]" 27 (SumTree.query 2 5 tree');
  (* Original tree should be unchanged (immutable) *)
  assert_equal ~msg:"original unchanged" 36 (SumTree.query 0 7 tree);
)

let test_sum_multiple_updates () = suite "Sum: multiple updates" (fun () ->
  let data = [1; 2; 3; 4; 5] in
  let tree = SumTree.build data in
  let tree = SumTree.update 0 10 tree in
  let tree = SumTree.update 4 50 tree in
  assert_equal ~msg:"after two updates" 69 (SumTree.query 0 4 tree);
  assert_equal ~msg:"middle unchanged" 9 (SumTree.query 1 3 tree);
)

let test_min_queries () = suite "Min: queries" (fun () ->
  let data = [5; 3; 7; 1; 4; 6; 2; 8] in
  let tree = MinTree.build data in
  assert_equal ~msg:"full range min" 1 (MinTree.query 0 7 tree);
  assert_equal ~msg:"[0..3] min" 1 (MinTree.query 0 3 tree);
  assert_equal ~msg:"[4..7] min" 2 (MinTree.query 4 7 tree);
  assert_equal ~msg:"[0..1] min" 3 (MinTree.query 0 1 tree);
  assert_equal ~msg:"[6..7] min" 2 (MinTree.query 6 7 tree);
  assert_equal ~msg:"single [2..2]" 7 (MinTree.query 2 2 tree);
)

let test_min_update () = suite "Min: update" (fun () ->
  let data = [5; 3; 7; 1; 4; 6; 2; 8] in
  let tree = MinTree.build data in
  let tree' = MinTree.update 3 0 tree in
  assert_equal ~msg:"new global min" 0 (MinTree.query 0 7 tree');
  assert_equal ~msg:"[0..3] new min" 0 (MinTree.query 0 3 tree');
  assert_equal ~msg:"[4..7] unchanged" 2 (MinTree.query 4 7 tree');
)

let test_max_queries () = suite "Max: queries" (fun () ->
  let data = [5; 3; 7; 1; 4; 6; 2; 8] in
  let tree = MaxTree.build data in
  assert_equal ~msg:"full range max" 8 (MaxTree.query 0 7 tree);
  assert_equal ~msg:"[0..3] max" 7 (MaxTree.query 0 3 tree);
  assert_equal ~msg:"[2..5] max" 7 (MaxTree.query 2 5 tree);
  assert_equal ~msg:"[4..7] max" 8 (MaxTree.query 4 7 tree);
  assert_equal ~msg:"single [0..0]" 5 (MaxTree.query 0 0 tree);
)

let test_max_update () = suite "Max: update" (fun () ->
  let data = [5; 3; 7; 1; 4; 6; 2; 8] in
  let tree = MaxTree.build data in
  let tree' = MaxTree.update 0 100 tree in
  assert_equal ~msg:"new global max" 100 (MaxTree.query 0 7 tree');
  assert_equal ~msg:"[0..0] updated" 100 (MaxTree.query 0 0 tree');
  assert_equal ~msg:"[1..7] old max" 8 (MaxTree.query 1 7 tree');
)

let test_empty_tree () = suite "Empty tree" (fun () ->
  let tree = SumTree.build [] in
  assert_equal ~msg:"query empty" 0 (SumTree.query 0 10 tree);
  assert_list_equal ~msg:"to_list empty" [] (SumTree.to_list tree);
  let tree' = SumTree.update 0 42 tree in
  assert_equal ~msg:"update empty" 0 (SumTree.query 0 0 tree');
)

let test_single_element () = suite "Single element" (fun () ->
  let tree = SumTree.build [42] in
  assert_equal ~msg:"query single" 42 (SumTree.query 0 0 tree);
  assert_equal ~msg:"query out of range" 0 (SumTree.query 1 5 tree);
  let tree' = SumTree.update 0 99 tree in
  assert_equal ~msg:"update single" 99 (SumTree.query 0 0 tree');
  assert_list_equal ~msg:"to_list single" [(0, 42)] (SumTree.to_list tree);
)

let test_two_elements () = suite "Two elements" (fun () ->
  let tree = SumTree.build [10; 20] in
  assert_equal ~msg:"sum both" 30 (SumTree.query 0 1 tree);
  assert_equal ~msg:"first only" 10 (SumTree.query 0 0 tree);
  assert_equal ~msg:"second only" 20 (SumTree.query 1 1 tree);
)

let test_to_list () = suite "to_list" (fun () ->
  let data = [5; 3; 7; 1] in
  let tree = SumTree.build data in
  let lst = SumTree.to_list tree in
  assert_list_equal ~msg:"to_list preserves order"
    [(0, 5); (1, 3); (2, 7); (3, 1)] lst;
)

let test_fold_leaves () = suite "fold_leaves" (fun () ->
  let data = [1; 2; 3; 4; 5] in
  let tree = SumTree.build data in
  let sum = SumTree.fold_leaves (fun acc _ v -> acc + v) 0 tree in
  assert_equal ~msg:"fold sum" 15 sum;
  let count = SumTree.fold_leaves (fun acc _ _ -> acc + 1) 0 tree in
  assert_equal ~msg:"fold count" 5 count;
)

let test_disjoint_query () = suite "Disjoint query ranges" (fun () ->
  let data = [1; 2; 3; 4; 5; 6; 7; 8] in
  let tree = SumTree.build data in
  (* Query range completely outside *)
  assert_equal ~msg:"query past end" 0 (SumTree.query 8 10 tree);
  assert_equal ~msg:"query before start" 0 (SumTree.query (-5) (-1) tree);
)

let test_power_of_two_size () = suite "Power-of-2 size" (fun () ->
  let data = [1; 2; 3; 4] in
  let tree = SumTree.build data in
  assert_equal ~msg:"sum all 4" 10 (SumTree.query 0 3 tree);
  assert_equal ~msg:"[0..1]" 3 (SumTree.query 0 1 tree);
  assert_equal ~msg:"[2..3]" 7 (SumTree.query 2 3 tree);
)

let test_odd_size () = suite "Odd-count input" (fun () ->
  let data = [1; 2; 3; 4; 5; 6; 7] in
  let tree = SumTree.build data in
  assert_equal ~msg:"sum 7 elements" 28 (SumTree.query 0 6 tree);
  let min_tree = MinTree.build data in
  assert_equal ~msg:"min 7 elements" 1 (MinTree.query 0 6 min_tree);
  let max_tree = MaxTree.build data in
  assert_equal ~msg:"max 7 elements" 7 (MaxTree.query 0 6 max_tree);
)

let test_large_input () = suite "Large input (1000 elements)" (fun () ->
  let data = List.init 1000 (fun i -> i + 1) in
  let tree = SumTree.build data in
  assert_equal ~msg:"sum 1..1000" 500500 (SumTree.query 0 999 tree);
  assert_equal ~msg:"first 100" 5050 (SumTree.query 0 99 tree);
  let min_tree = MinTree.build data in
  assert_equal ~msg:"min 1..1000" 1 (MinTree.query 0 999 min_tree);
  assert_equal ~msg:"min [500..999]" 501 (MinTree.query 500 999 min_tree);
  let max_tree = MaxTree.build data in
  assert_equal ~msg:"max 1..1000" 1000 (MaxTree.query 0 999 max_tree);
  assert_equal ~msg:"max [0..499]" 500 (MaxTree.query 0 499 max_tree);
)

let test_update_preserves_immutability () = suite "Immutability" (fun () ->
  let data = [10; 20; 30; 40; 50] in
  let t0 = SumTree.build data in
  let t1 = SumTree.update 2 100 t0 in
  let t2 = SumTree.update 2 0 t0 in
  assert_equal ~msg:"t0 unchanged after update1" 150 (SumTree.query 0 4 t0);
  assert_equal ~msg:"t1 has update1" 220 (SumTree.query 0 4 t1);
  assert_equal ~msg:"t2 has update2" 120 (SumTree.query 0 4 t2);
  assert_equal ~msg:"t1[2] is 100" 100 (SumTree.query 2 2 t1);
  assert_equal ~msg:"t2[2] is 0" 0 (SumTree.query 2 2 t2);
)

let test_all_negative () = suite "All negative values" (fun () ->
  let data = [-5; -3; -7; -1] in
  let tree = SumTree.build data in
  assert_equal ~msg:"sum negatives" (-16) (SumTree.query 0 3 tree);
  let min_tree = MinTree.build data in
  assert_equal ~msg:"min negatives" (-7) (MinTree.query 0 3 min_tree);
  let max_tree = MaxTree.build data in
  assert_equal ~msg:"max negatives" (-1) (MaxTree.query 0 3 max_tree);
)

let test_all_zeros () = suite "All zeros" (fun () ->
  let data = [0; 0; 0; 0; 0] in
  let tree = SumTree.build data in
  assert_equal ~msg:"sum zeros" 0 (SumTree.query 0 4 tree);
  let tree' = SumTree.update 2 1 tree in
  assert_equal ~msg:"after update" 1 (SumTree.query 0 4 tree');
)

let test_consecutive_updates () = suite "Consecutive updates same index" (fun () ->
  let data = [1; 2; 3; 4; 5] in
  let tree = SumTree.build data in
  let tree = SumTree.update 2 10 tree in
  let tree = SumTree.update 2 20 tree in
  let tree = SumTree.update 2 30 tree in
  assert_equal ~msg:"last update wins" 30 (SumTree.query 2 2 tree);
  assert_equal ~msg:"total correct" 42 (SumTree.query 0 4 tree);
)

(* ── Main ─────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Segment Tree Tests ===\n\n";
  test_sum_build_and_query ();
  test_sum_update ();
  test_sum_multiple_updates ();
  test_min_queries ();
  test_min_update ();
  test_max_queries ();
  test_max_update ();
  test_empty_tree ();
  test_single_element ();
  test_two_elements ();
  test_to_list ();
  test_fold_leaves ();
  test_disjoint_query ();
  test_power_of_two_size ();
  test_odd_size ();
  test_large_input ();
  test_update_preserves_immutability ();
  test_all_negative ();
  test_all_zeros ();
  test_consecutive_updates ();
  Printf.printf "\n=== Results: %d/%d passed, %d failed ===\n" !passed !total !failed;
  if !failed > 0 then exit 1
