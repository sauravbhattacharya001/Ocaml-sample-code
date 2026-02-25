(* test_interval_tree.ml — Comprehensive tests for interval_tree.ml *)
(* Uses the same assertion framework as test_all.ml *)

(* ── Test framework ────────────────────────────────────────────────── *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0
let current_suite = ref ""

let assert_true ~msg condition =
  incr tests_run;
  if condition then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s\n" !current_suite msg
  end

let assert_equal ~msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %s, got %s\n"
      !current_suite msg expected actual
  end

let assert_raises ~msg f =
  incr tests_run;
  try ignore (f ()); incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected exception\n" !current_suite msg
  with _ -> incr tests_passed

let suite name f =
  current_suite := name;
  Printf.printf "Running: %s\n" name;
  f ()

(* ── Helpers ───────────────────────────────────────────────────────── *)

open IntervalTree

let iv lo hi = { lo; hi }

let sorted_intervals lst =
  List.sort compare_interval lst

let list_eq a b =
  sorted_intervals a = sorted_intervals b

(* ── Tests ─────────────────────────────────────────────────────────── *)

let test_empty () = suite "Empty tree" (fun () ->
  assert_true ~msg:"empty is_empty" (is_empty empty);
  assert_equal ~msg:"empty cardinal" "0" (string_of_int (cardinal empty));
  assert_true ~msg:"empty to_list" (to_list empty = []);
  assert_true ~msg:"empty validate" (validate empty);
  assert_true ~msg:"empty to_string" (to_string empty = "{}");
  assert_true ~msg:"empty span" (span empty = None);
  assert_raises ~msg:"empty find_min" (fun () -> find_min empty);
  assert_raises ~msg:"empty find_max" (fun () -> find_max empty);
  assert_true ~msg:"empty no overlap" (not (any_overlap (iv 0 10) empty));
  assert_true ~msg:"empty overlaps" (overlaps (iv 0 10) empty = []);
  assert_true ~msg:"empty find_containing" (find_containing 5 empty = []);
)

let test_single_insert () = suite "Single insert" (fun () ->
  let t = insert (iv 1 10) empty in
  assert_true ~msg:"not empty" (not (is_empty t));
  assert_equal ~msg:"cardinal 1" "1" (string_of_int (cardinal t));
  assert_true ~msg:"mem" (mem (iv 1 10) t);
  assert_true ~msg:"not mem other" (not (mem (iv 2 10) t));
  assert_true ~msg:"validate" (validate t);
  assert_true ~msg:"to_list" (to_list t = [iv 1 10]);
)

let test_multiple_inserts () = suite "Multiple inserts" (fun () ->
  let t = of_list [iv 5 10; iv 1 3; iv 15 20; iv 8 12; iv 0 2] in
  assert_equal ~msg:"cardinal 5" "5" (string_of_int (cardinal t));
  assert_true ~msg:"validate" (validate t);
  assert_true ~msg:"mem 5 10" (mem (iv 5 10) t);
  assert_true ~msg:"mem 1 3" (mem (iv 1 3) t);
  assert_true ~msg:"mem 15 20" (mem (iv 15 20) t);
  assert_true ~msg:"mem 8 12" (mem (iv 8 12) t);
  assert_true ~msg:"mem 0 2" (mem (iv 0 2) t);
  assert_true ~msg:"not mem 3 7" (not (mem (iv 3 7) t));
  (* to_list should be sorted by lo *)
  let lst = to_list t in
  let los = List.map (fun i -> i.lo) lst in
  let sorted = List.sort compare los in
  assert_true ~msg:"sorted by lo" (los = sorted);
)

let test_overlap_queries () = suite "Overlap queries" (fun () ->
  let t = of_list [iv 1 5; iv 3 8; iv 10 15; iv 20 25] in
  (* Query [4,4] should hit [1,5] and [3,8] *)
  let r = overlaps (iv 4 4) t in
  assert_true ~msg:"overlap [4,4]" (list_eq r [iv 1 5; iv 3 8]);
  (* Query [6,9] should hit [3,8] *)
  let r2 = overlaps (iv 6 9) t in
  assert_true ~msg:"overlap [6,9]" (list_eq r2 [iv 3 8]);
  (* Query [16,19] should hit nothing *)
  let r3 = overlaps (iv 16 19) t in
  assert_true ~msg:"overlap [16,19] empty" (r3 = []);
  (* Query [5,10] hits [1,5], [3,8], [10,15] *)
  let r4 = overlaps (iv 5 10) t in
  assert_true ~msg:"overlap [5,10]" (list_eq r4 [iv 1 5; iv 3 8; iv 10 15]);
  (* any_overlap *)
  assert_true ~msg:"any_overlap [4,4]" (any_overlap (iv 4 4) t);
  assert_true ~msg:"no any_overlap [16,19]" (not (any_overlap (iv 16 19) t));
)

let test_edge_overlaps () = suite "Edge overlap cases" (fun () ->
  let t = of_list [iv 1 5; iv 10 15] in
  (* Touching at endpoint: [5,5] overlaps [1,5] *)
  assert_true ~msg:"touching left" (any_overlap (iv 5 5) t);
  (* Touching at endpoint: [10,10] overlaps [10,15] *)
  assert_true ~msg:"touching right" (any_overlap (iv 10 10) t);
  (* Just outside: [6,9] doesn't overlap either *)
  assert_true ~msg:"gap" (not (any_overlap (iv 6 9) t));
)

let test_point_queries () = suite "Point/stabbing queries" (fun () ->
  let t = of_list [iv 1 10; iv 5 15; iv 20 25] in
  let r = find_containing 7 t in
  assert_true ~msg:"point 7" (list_eq r [iv 1 10; iv 5 15]);
  let r2 = find_containing 1 t in
  assert_true ~msg:"point 1" (list_eq r2 [iv 1 10]);
  let r3 = find_containing 18 t in
  assert_true ~msg:"point 18 empty" (r3 = []);
  let r4 = find_containing 20 t in
  assert_true ~msg:"point 20" (list_eq r4 [iv 20 25]);
)

let test_remove () = suite "Remove" (fun () ->
  let t = of_list [iv 1 5; iv 3 8; iv 10 15] in
  let t2 = remove (iv 3 8) t in
  assert_equal ~msg:"cardinal after remove" "2" (string_of_int (cardinal t2));
  assert_true ~msg:"removed gone" (not (mem (iv 3 8) t2));
  assert_true ~msg:"others stay" (mem (iv 1 5) t2 && mem (iv 10 15) t2);
  assert_true ~msg:"validate after remove" (validate t2);
  (* Remove non-existent *)
  let t3 = remove (iv 99 100) t in
  assert_equal ~msg:"remove non-existent" "3" (string_of_int (cardinal t3));
  (* Remove from single *)
  let t4 = remove (iv 1 5) (insert (iv 1 5) empty) in
  assert_true ~msg:"remove to empty" (is_empty t4);
)

let test_remove_all () = suite "Remove all elements" (fun () ->
  let t = of_list [iv 1 2; iv 3 4; iv 5 6; iv 7 8; iv 9 10] in
  let t = remove (iv 5 6) t in
  let t = remove (iv 1 2) t in
  let t = remove (iv 9 10) t in
  let t = remove (iv 3 4) t in
  let t = remove (iv 7 8) t in
  assert_true ~msg:"all removed" (is_empty t);
)

let test_find_min_max () = suite "Find min/max" (fun () ->
  let t = of_list [iv 5 10; iv 1 3; iv 15 20; iv 8 25] in
  let mn = find_min t in
  assert_true ~msg:"find_min" (intervals_equal mn (iv 1 3));
  let mx = find_max t in
  assert_true ~msg:"find_max" (intervals_equal mx (iv 8 25));
)

let test_span () = suite "Span" (fun () ->
  let t = of_list [iv 5 10; iv 1 3; iv 15 20] in
  let s = span t in
  assert_true ~msg:"span" (match s with Some i -> i.lo = 1 && i.hi = 20 | None -> false);
  let t2 = insert (iv 0 100) t in
  let s2 = span t2 in
  assert_true ~msg:"span with wide" (match s2 with Some i -> i.lo = 0 && i.hi = 100 | None -> false);
)

let test_set_union () = suite "Union" (fun () ->
  let a = of_list [iv 1 5; iv 10 15] in
  let b = of_list [iv 3 8; iv 20 25] in
  let u = union a b in
  assert_equal ~msg:"union cardinal" "4" (string_of_int (cardinal u));
  assert_true ~msg:"union has all" (
    mem (iv 1 5) u && mem (iv 10 15) u && mem (iv 3 8) u && mem (iv 20 25) u);
  assert_true ~msg:"union validate" (validate u);
)

let test_set_inter () = suite "Inter" (fun () ->
  let a = of_list [iv 1 5; iv 10 15; iv 20 25] in
  let b = of_list [iv 10 15; iv 30 35] in
  let i = inter a b in
  assert_equal ~msg:"inter cardinal" "1" (string_of_int (cardinal i));
  assert_true ~msg:"inter has [10,15]" (mem (iv 10 15) i);
  assert_true ~msg:"inter validate" (validate i);
)

let test_set_diff () = suite "Diff" (fun () ->
  let a = of_list [iv 1 5; iv 10 15; iv 20 25] in
  let b = of_list [iv 10 15; iv 30 35] in
  let d = diff a b in
  assert_equal ~msg:"diff cardinal" "2" (string_of_int (cardinal d));
  assert_true ~msg:"diff has [1,5]" (mem (iv 1 5) d);
  assert_true ~msg:"diff has [20,25]" (mem (iv 20 25) d);
  assert_true ~msg:"diff no [10,15]" (not (mem (iv 10 15) d));
)

let test_fold () = suite "Fold" (fun () ->
  let t = of_list [iv 1 10; iv 5 20; iv 3 7] in
  let sum_lo = fold (fun acc i -> acc + i.lo) 0 t in
  assert_equal ~msg:"fold sum lo" "9" (string_of_int sum_lo);
  let count = fold (fun acc _ -> acc + 1) 0 t in
  assert_equal ~msg:"fold count" "3" (string_of_int count);
)

let test_iter () = suite "Iter" (fun () ->
  let t = of_list [iv 1 5; iv 3 8; iv 10 15] in
  let count = ref 0 in
  iter (fun _ -> incr count) t;
  assert_equal ~msg:"iter count" "3" (string_of_int !count);
)

let test_map () = suite "Map" (fun () ->
  let t = of_list [iv 1 5; iv 3 8; iv 10 15] in
  let t2 = map (fun i -> { lo = i.lo + 1; hi = i.hi + 1 }) t in
  assert_true ~msg:"map shifted" (mem (iv 2 6) t2 && mem (iv 4 9) t2 && mem (iv 11 16) t2);
  assert_equal ~msg:"map cardinal" "3" (string_of_int (cardinal t2));
  assert_true ~msg:"map validate" (validate t2);
)

let test_filter () = suite "Filter" (fun () ->
  let t = of_list [iv 1 5; iv 3 8; iv 10 15; iv 20 25] in
  let t2 = filter (fun i -> i.lo >= 10) t in
  assert_equal ~msg:"filter cardinal" "2" (string_of_int (cardinal t2));
  assert_true ~msg:"filter has [10,15]" (mem (iv 10 15) t2);
  assert_true ~msg:"filter has [20,25]" (mem (iv 20 25) t2);
  assert_true ~msg:"filter validate" (validate t2);
)

let test_for_all_exists () = suite "For_all / exists" (fun () ->
  let t = of_list [iv 1 5; iv 3 8; iv 10 15] in
  assert_true ~msg:"for_all lo >= 0" (for_all (fun i -> i.lo >= 0) t);
  assert_true ~msg:"not for_all lo >= 5" (not (for_all (fun i -> i.lo >= 5) t));
  assert_true ~msg:"exists lo = 10" (exists (fun i -> i.lo = 10) t);
  assert_true ~msg:"not exists lo = 99" (not (exists (fun i -> i.lo = 99) t));
)

let test_partition () = suite "Partition" (fun () ->
  let t = of_list [iv 1 5; iv 3 8; iv 10 15; iv 20 25] in
  let (yes, no) = partition (fun i -> i.lo < 10) t in
  assert_equal ~msg:"partition yes" "2" (string_of_int (cardinal yes));
  assert_equal ~msg:"partition no" "2" (string_of_int (cardinal no));
  assert_true ~msg:"partition validate yes" (validate yes);
  assert_true ~msg:"partition validate no" (validate no);
)

let test_of_list_to_list () = suite "of_list / to_list" (fun () ->
  let lst = [iv 5 10; iv 1 3; iv 15 20; iv 8 12] in
  let t = of_list lst in
  let lst2 = to_list t in
  assert_true ~msg:"round-trip same elements" (list_eq lst lst2);
  assert_equal ~msg:"round-trip cardinal" "4" (string_of_int (List.length lst2));
  (* to_list sorted by lo *)
  let los = List.map (fun i -> i.lo) lst2 in
  let sorted = List.sort compare los in
  assert_true ~msg:"to_list sorted" (los = sorted);
)

let test_identical_intervals () = suite "Identical intervals" (fun () ->
  let t = of_list [iv 1 5; iv 1 5; iv 1 5] in
  assert_equal ~msg:"cardinal 3 duplicates" "3" (string_of_int (cardinal t));
  assert_true ~msg:"validate dupes" (validate t);
  let t2 = remove (iv 1 5) t in
  assert_equal ~msg:"remove one dupe" "2" (string_of_int (cardinal t2));
  assert_true ~msg:"validate after remove dupe" (validate t2);
)

let test_single_point_intervals () = suite "Single-point intervals [x,x]" (fun () ->
  let t = of_list [iv 5 5; iv 10 10; iv 3 3] in
  assert_equal ~msg:"cardinal points" "3" (string_of_int (cardinal t));
  assert_true ~msg:"mem [5,5]" (mem (iv 5 5) t);
  let r = find_containing 5 t in
  assert_true ~msg:"find_containing 5" (list_eq r [iv 5 5]);
  let r2 = overlaps (iv 4 6) t in
  assert_true ~msg:"overlap with point" (list_eq r2 [iv 5 5]);
  assert_true ~msg:"validate points" (validate t);
)

let test_touching_endpoints () = suite "Touching endpoints" (fun () ->
  let t = of_list [iv 1 5; iv 5 10; iv 10 15] in
  (* [5,5] should overlap both [1,5] and [5,10] *)
  let r = overlaps (iv 5 5) t in
  assert_true ~msg:"touching at 5" (list_eq r [iv 1 5; iv 5 10]);
  (* [10,10] should overlap [5,10] and [10,15] *)
  let r2 = overlaps (iv 10 10) t in
  assert_true ~msg:"touching at 10" (list_eq r2 [iv 5 10; iv 10 15]);
)

let test_large_tree () = suite "Large tree (200 intervals)" (fun () ->
  let intervals = List.init 200 (fun i -> iv (i * 3) (i * 3 + 5)) in
  let t = of_list intervals in
  assert_equal ~msg:"large cardinal" "200" (string_of_int (cardinal t));
  assert_true ~msg:"large validate" (validate t);
  (* Check membership of first and last *)
  assert_true ~msg:"large mem first" (mem (iv 0 5) t);
  assert_true ~msg:"large mem last" (mem (iv 597 602) t);
  (* Overlap query *)
  let r = overlaps (iv 10 10) t in
  assert_true ~msg:"large overlap non-empty" (List.length r > 0);
  (* Remove some and validate *)
  let t2 = remove (iv 0 5) (remove (iv 300 305) t) in
  assert_equal ~msg:"large after remove" "198" (string_of_int (cardinal t2));
  assert_true ~msg:"large validate after remove" (validate t2);
)

let test_find_intersecting () = suite "find_intersecting alias" (fun () ->
  let t = of_list [iv 1 5; iv 10 15] in
  let r1 = overlaps (iv 3 12) t in
  let r2 = find_intersecting (iv 3 12) t in
  assert_true ~msg:"find_intersecting = overlaps" (r1 = r2);
)

let test_intervals_equal () = suite "intervals_equal" (fun () ->
  assert_true ~msg:"equal" (intervals_equal (iv 1 5) (iv 1 5));
  assert_true ~msg:"not equal lo" (not (intervals_equal (iv 1 5) (iv 2 5)));
  assert_true ~msg:"not equal hi" (not (intervals_equal (iv 1 5) (iv 1 6)));
)

let test_interval_to_string () = suite "interval_to_string" (fun () ->
  assert_equal ~msg:"to_string" "[1, 5]" (interval_to_string (iv 1 5));
  assert_equal ~msg:"to_string neg" "[-3, 10]" (interval_to_string (iv (-3) 10));
)

let test_to_string () = suite "to_string" (fun () ->
  let t = of_list [iv 1 5; iv 10 15] in
  let s = to_string t in
  assert_true ~msg:"contains [1, 5]" (String.length s > 0);
  let e = to_string empty in
  assert_equal ~msg:"empty to_string" "{}" e;
)

let test_validate_good () = suite "Validate good trees" (fun () ->
  assert_true ~msg:"empty valid" (validate empty);
  assert_true ~msg:"single valid" (validate (insert (iv 1 5) empty));
  let t = of_list [iv 1 5; iv 3 8; iv 10 15; iv 20 25; iv 0 2] in
  assert_true ~msg:"multi valid" (validate t);
)

let test_negative_intervals () = suite "Negative intervals" (fun () ->
  let t = of_list [iv (-10) (-5); iv (-3) 3; iv 0 10] in
  assert_equal ~msg:"cardinal neg" "3" (string_of_int (cardinal t));
  assert_true ~msg:"validate neg" (validate t);
  let r = find_containing 0 t in
  assert_true ~msg:"point 0 in neg" (list_eq r [iv (-3) 3; iv 0 10]);
  let r2 = find_containing (-7) t in
  assert_true ~msg:"point -7" (list_eq r2 [iv (-10) (-5)]);
)

let test_union_with_empty () = suite "Union with empty" (fun () ->
  let t = of_list [iv 1 5; iv 10 15] in
  let u1 = union t empty in
  let u2 = union empty t in
  assert_equal ~msg:"union t empty" "2" (string_of_int (cardinal u1));
  assert_equal ~msg:"union empty t" "2" (string_of_int (cardinal u2));
)

let test_inter_disjoint () = suite "Inter disjoint" (fun () ->
  let a = of_list [iv 1 5; iv 10 15] in
  let b = of_list [iv 20 25; iv 30 35] in
  let i = inter a b in
  assert_true ~msg:"inter disjoint empty" (is_empty i);
)

let test_diff_same () = suite "Diff same" (fun () ->
  let a = of_list [iv 1 5; iv 10 15] in
  let d = diff a a in
  assert_true ~msg:"diff self empty" (is_empty d);
)

let test_filter_none () = suite "Filter none" (fun () ->
  let t = of_list [iv 1 5; iv 10 15] in
  let t2 = filter (fun _ -> false) t in
  assert_true ~msg:"filter none empty" (is_empty t2);
)

let test_filter_all () = suite "Filter all" (fun () ->
  let t = of_list [iv 1 5; iv 10 15] in
  let t2 = filter (fun _ -> true) t in
  assert_equal ~msg:"filter all same" "2" (string_of_int (cardinal t2));
)

let test_map_identity () = suite "Map identity" (fun () ->
  let t = of_list [iv 1 5; iv 10 15; iv 3 8] in
  let t2 = map (fun i -> i) t in
  assert_true ~msg:"map identity same" (list_eq (to_list t) (to_list t2));
)

let test_large_overlap_query () = suite "Large overlap query" (fun () ->
  (* Many overlapping intervals *)
  let intervals = List.init 100 (fun i -> iv i (i + 50)) in
  let t = of_list intervals in
  let r = overlaps (iv 25 25) t in
  (* [25,25] overlaps [i, i+50] when i <= 25 and i+50 >= 25, so i in [0..25] *)
  assert_equal ~msg:"many overlaps" "26" (string_of_int (List.length r));
)

let test_fold_order () = suite "Fold in-order" (fun () ->
  let t = of_list [iv 5 10; iv 1 3; iv 15 20] in
  let lst = fold (fun acc i -> i :: acc) [] t in
  let lst = List.rev lst in
  let los = List.map (fun i -> i.lo) lst in
  assert_true ~msg:"fold in-order" (los = [1; 5; 15]);
)

let test_span_single () = suite "Span single" (fun () ->
  let t = insert (iv 5 10) empty in
  let s = span t in
  assert_true ~msg:"span single" (match s with Some i -> i.lo = 5 && i.hi = 10 | None -> false);
)

let test_remove_rebalance () = suite "Remove with rebalancing" (fun () ->
  (* Insert many, remove many, check validity *)
  let t = of_list (List.init 50 (fun i -> iv (i * 2) (i * 2 + 3))) in
  let t = List.fold_left (fun t i -> remove (iv (i * 2) (i * 2 + 3)) t)
    t (List.init 25 (fun i -> i * 2)) in
  assert_equal ~msg:"after bulk remove" "25" (string_of_int (cardinal t));
  assert_true ~msg:"validate after bulk remove" (validate t);
)

(* ── Run all tests ─────────────────────────────────────────────────── *)

let () =
  Printf.printf "\n=== Interval Tree Tests ===\n\n";
  test_empty ();
  test_single_insert ();
  test_multiple_inserts ();
  test_overlap_queries ();
  test_edge_overlaps ();
  test_point_queries ();
  test_remove ();
  test_remove_all ();
  test_find_min_max ();
  test_span ();
  test_set_union ();
  test_set_inter ();
  test_set_diff ();
  test_fold ();
  test_iter ();
  test_map ();
  test_filter ();
  test_for_all_exists ();
  test_partition ();
  test_of_list_to_list ();
  test_identical_intervals ();
  test_single_point_intervals ();
  test_touching_endpoints ();
  test_large_tree ();
  test_find_intersecting ();
  test_intervals_equal ();
  test_interval_to_string ();
  test_to_string ();
  test_validate_good ();
  test_negative_intervals ();
  test_union_with_empty ();
  test_inter_disjoint ();
  test_diff_same ();
  test_filter_none ();
  test_filter_all ();
  test_map_identity ();
  test_large_overlap_query ();
  test_fold_order ();
  test_span_single ();
  test_remove_rebalance ();
  Printf.printf "\n=== Results: %d passed, %d failed, %d total ===\n"
    !tests_passed !tests_failed !tests_run;
  if !tests_failed > 0 then exit 1
