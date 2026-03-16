(* test_skip_list.ml — Dedicated tests for skip_list.ml *)
(* Tests the SkipList module's full public API:
   create, insert, mem, find, remove, size, is_empty, to_list,
   min_elt, max_elt, fold, iter, of_list, range_query,
   height, floor, ceil.

   Compile: ocamlopt -o test_skip_list skip_list.ml test_skip_list.ml *)

open Skip_list.SkipList

let passed = ref 0
let failed = ref 0
let current_test = ref ""

let assert_true msg cond =
  if cond then incr passed
  else begin
    incr failed;
    Printf.eprintf "  FAIL [%s]: %s\n" !current_test msg
  end

let assert_equal msg expected actual =
  if expected = actual then incr passed
  else begin
    incr failed;
    Printf.eprintf "  FAIL [%s]: %s — expected %s, got %s\n"
      !current_test msg expected actual
  end

let test name f =
  current_test := name;
  (try f () with exn ->
    incr failed;
    Printf.eprintf "  FAIL [%s]: exception %s\n" name (Printexc.to_string exn))

(* ===== Creation & Empty ===== *)

let test_empty () =
  test "empty: is_empty" (fun () ->
    let sl = SkipList.create () in
    assert_true "should be empty" (SkipList.is_empty sl));
  test "empty: size" (fun () ->
    let sl = SkipList.create () in
    assert_equal "size" "0" (string_of_int (SkipList.size sl)));
  test "empty: height" (fun () ->
    let sl = SkipList.create () in
    assert_equal "height" "0" (string_of_int (SkipList.height sl)));
  test "empty: to_list" (fun () ->
    let sl = SkipList.create () in
    assert_true "should be []" (SkipList.to_list sl = []));
  test "empty: min_elt" (fun () ->
    let sl = SkipList.create () in
    assert_true "should be None" (SkipList.min_elt sl = None));
  test "empty: max_elt" (fun () ->
    let sl = SkipList.create () in
    assert_true "should be None" (SkipList.max_elt sl = None));
  test "empty: mem" (fun () ->
    let sl = SkipList.create () in
    assert_true "should not find 42" (not (SkipList.mem 42 sl)));
  test "empty: find" (fun () ->
    let sl = SkipList.create () in
    assert_true "should be None" (SkipList.find 42 sl = None));
  test "empty: remove" (fun () ->
    let sl = SkipList.create () in
    assert_true "should return false" (not (SkipList.remove 1 sl)));
  test "empty: floor" (fun () ->
    let sl = SkipList.create () in
    assert_true "should be None" (SkipList.floor 5 sl = None));
  test "empty: ceil" (fun () ->
    let sl = SkipList.create () in
    assert_true "should be None" (SkipList.ceil 5 sl = None));
  test "empty: range_query" (fun () ->
    let sl = SkipList.create () in
    assert_true "should be []" (SkipList.range_query ~lo:0 ~hi:10 sl = []))

(* ===== Single Element ===== *)

let test_single () =
  test "single: insert and mem" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_true "should find 42" (SkipList.mem 42 sl);
    assert_true "should not find 99" (not (SkipList.mem 99 sl)));
  test "single: size" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_equal "size" "1" (string_of_int (SkipList.size sl)));
  test "single: not empty" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_true "should not be empty" (not (SkipList.is_empty sl)));
  test "single: find" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_true "should find 42" (SkipList.find 42 sl = Some 42));
  test "single: to_list" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_true "should be [42]" (SkipList.to_list sl = [42]));
  test "single: min_elt" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_true "min should be 42" (SkipList.min_elt sl = Some 42));
  test "single: max_elt" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_true "max should be 42" (SkipList.max_elt sl = Some 42));
  test "single: remove" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_true "remove should return true" (SkipList.remove 42 sl);
    assert_true "should be empty after remove" (SkipList.is_empty sl);
    assert_true "should not find 42" (not (SkipList.mem 42 sl)));
  test "single: height >= 1" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 42 sl;
    assert_true "height >= 1" (SkipList.height sl >= 1))

(* ===== Multiple Elements ===== *)

let test_multiple () =
  let mk () =
    let sl = SkipList.create () in
    List.iter (fun x -> SkipList.insert x sl) [5; 3; 8; 1; 7; 2; 9; 4; 6; 10];
    sl
  in
  test "multi: sorted order" (fun () ->
    let sl = mk () in
    assert_true "should be sorted" (SkipList.to_list sl = [1;2;3;4;5;6;7;8;9;10]));
  test "multi: size" (fun () ->
    let sl = mk () in
    assert_equal "size" "10" (string_of_int (SkipList.size sl)));
  test "multi: mem all" (fun () ->
    let sl = mk () in
    for i = 1 to 10 do
      assert_true (Printf.sprintf "should find %d" i) (SkipList.mem i sl)
    done);
  test "multi: not mem absent" (fun () ->
    let sl = mk () in
    assert_true "should not find 0" (not (SkipList.mem 0 sl));
    assert_true "should not find 11" (not (SkipList.mem 11 sl)));
  test "multi: min_elt" (fun () ->
    let sl = mk () in
    assert_true "min should be 1" (SkipList.min_elt sl = Some 1));
  test "multi: max_elt" (fun () ->
    let sl = mk () in
    assert_true "max should be 10" (SkipList.max_elt sl = Some 10));
  test "multi: remove middle" (fun () ->
    let sl = mk () in
    assert_true "remove 5" (SkipList.remove 5 sl);
    assert_true "5 gone" (not (SkipList.mem 5 sl));
    assert_equal "size after remove" "9" (string_of_int (SkipList.size sl)));
  test "multi: remove min" (fun () ->
    let sl = mk () in
    assert_true "remove 1" (SkipList.remove 1 sl);
    assert_true "new min is 2" (SkipList.min_elt sl = Some 2));
  test "multi: remove max" (fun () ->
    let sl = mk () in
    assert_true "remove 10" (SkipList.remove 10 sl);
    assert_true "new max is 9" (SkipList.max_elt sl = Some 9));
  test "multi: remove nonexistent" (fun () ->
    let sl = mk () in
    assert_true "remove 99 returns false" (not (SkipList.remove 99 sl));
    assert_equal "size unchanged" "10" (string_of_int (SkipList.size sl)))

(* ===== Duplicates ===== *)

let test_duplicates () =
  test "dup: insert same element twice" (fun () ->
    let sl = SkipList.create () in
    SkipList.insert 5 sl;
    SkipList.insert 5 sl;
    assert_equal "size should be 1" "1" (string_of_int (SkipList.size sl));
    assert_true "to_list should be [5]" (SkipList.to_list sl = [5]));
  test "dup: of_list with duplicates" (fun () ->
    let sl = SkipList.of_list [5; 3; 5; 1; 3; 1] in
    assert_equal "size should be 3" "3" (string_of_int (SkipList.size sl));
    assert_true "sorted unique" (SkipList.to_list sl = [1; 3; 5]))

(* ===== Range Queries ===== *)

let test_range () =
  let sl = SkipList.create () in
  List.iter (fun x -> SkipList.insert x sl) [5; 10; 15; 20; 25; 30; 35; 40];
  test "range: [10,30]" (fun () ->
    assert_true "[10,30]" (SkipList.range_query ~lo:10 ~hi:30 sl = [10;15;20;25;30]));
  test "range: [1,5]" (fun () ->
    assert_true "[1,5]" (SkipList.range_query ~lo:1 ~hi:5 sl = [5]));
  test "range: [36,100]" (fun () ->
    assert_true "[36,100]" (SkipList.range_query ~lo:36 ~hi:100 sl = [40]));
  test "range: [100,200]" (fun () ->
    assert_true "[100,200]" (SkipList.range_query ~lo:100 ~hi:200 sl = []));
  test "range: inverted" (fun () ->
    assert_true "hi < lo" (SkipList.range_query ~lo:30 ~hi:10 sl = []));
  test "range: single match" (fun () ->
    assert_true "[20,20]" (SkipList.range_query ~lo:20 ~hi:20 sl = [20]));
  test "range: full" (fun () ->
    assert_true "[0,999]"
      (SkipList.range_query ~lo:0 ~hi:999 sl = [5;10;15;20;25;30;35;40]))

(* ===== Floor & Ceil ===== *)

let test_floor_ceil () =
  let sl = SkipList.of_list [10; 20; 30; 40; 50] in
  test "floor: exact match" (fun () ->
    assert_true "floor 30" (SkipList.floor 30 sl = Some 30));
  test "floor: between elements" (fun () ->
    assert_true "floor 25" (SkipList.floor 25 sl = Some 20));
  test "floor: below min" (fun () ->
    assert_true "floor 5" (SkipList.floor 5 sl = None));
  test "floor: above max" (fun () ->
    assert_true "floor 99" (SkipList.floor 99 sl = Some 50));
  test "ceil: exact match" (fun () ->
    assert_true "ceil 30" (SkipList.ceil 30 sl = Some 30));
  test "ceil: between elements" (fun () ->
    assert_true "ceil 25" (SkipList.ceil 25 sl = Some 30));
  test "ceil: above max" (fun () ->
    assert_true "ceil 99" (SkipList.ceil 99 sl = None));
  test "ceil: below min" (fun () ->
    assert_true "ceil 5" (SkipList.ceil 5 sl = Some 10))

(* ===== Fold & Iter ===== *)

let test_fold_iter () =
  let sl = SkipList.of_list [1; 2; 3; 4; 5] in
  test "fold: sum" (fun () ->
    let total = SkipList.fold (fun acc x -> acc + x) 0 sl in
    assert_equal "sum" "15" (string_of_int total));
  test "fold: product" (fun () ->
    let product = SkipList.fold (fun acc x -> acc * x) 1 sl in
    assert_equal "product" "120" (string_of_int product));
  test "fold: collect" (fun () ->
    let lst = SkipList.fold (fun acc x -> x :: acc) [] sl in
    assert_true "reversed list" (lst = [5; 4; 3; 2; 1]));
  test "iter: count" (fun () ->
    let count = ref 0 in
    SkipList.iter (fun _ -> incr count) sl;
    assert_equal "iter count" "5" (string_of_int !count));
  test "iter: order" (fun () ->
    let buf = Buffer.create 16 in
    SkipList.iter (fun x -> Buffer.add_string buf (string_of_int x ^ ",")) sl;
    assert_equal "iter order" "1,2,3,4,5," (Buffer.contents buf))

(* ===== Reverse Order ===== *)

let test_reverse () =
  let sl = SkipList.create ~compare:(fun a b -> compare b a) () in
  List.iter (fun x -> SkipList.insert x sl) [1; 5; 3; 2; 4];
  test "reverse: to_list descending" (fun () ->
    assert_true "descending" (SkipList.to_list sl = [5; 4; 3; 2; 1]));
  test "reverse: min_elt is largest value" (fun () ->
    assert_true "min_elt = 5" (SkipList.min_elt sl = Some 5));
  test "reverse: max_elt is smallest value" (fun () ->
    assert_true "max_elt = 1" (SkipList.max_elt sl = Some 1))

(* ===== String Keys ===== *)

let test_strings () =
  let sl = SkipList.create ~compare:String.compare () in
  List.iter (fun s -> SkipList.insert s sl)
    ["banana"; "apple"; "cherry"; "date"; "elderberry"];
  test "string: sorted" (fun () ->
    assert_true "alphabetical"
      (SkipList.to_list sl = ["apple";"banana";"cherry";"date";"elderberry"]));
  test "string: mem" (fun () ->
    assert_true "find cherry" (SkipList.mem "cherry" sl);
    assert_true "not find fig" (not (SkipList.mem "fig" sl)));
  test "string: find" (fun () ->
    assert_true "find date" (SkipList.find "date" sl = Some "date"));
  test "string: min" (fun () ->
    assert_true "min is apple" (SkipList.min_elt sl = Some "apple"));
  test "string: max" (fun () ->
    assert_true "max is elderberry" (SkipList.max_elt sl = Some "elderberry"));
  test "string: range" (fun () ->
    assert_true "[b,d]"
      (SkipList.range_query ~lo:"b" ~hi:"d" sl = ["banana"; "cherry"; "date"]))

(* ===== of_list ===== *)

let test_of_list () =
  test "of_list: basic" (fun () ->
    let sl = SkipList.of_list [9; 3; 7; 1; 5] in
    assert_true "sorted" (SkipList.to_list sl = [1;3;5;7;9]);
    assert_equal "size" "5" (string_of_int (SkipList.size sl)));
  test "of_list: single" (fun () ->
    let sl = SkipList.of_list [42] in
    assert_true "to_list" (SkipList.to_list sl = [42]));
  test "of_list: empty raises" (fun () ->
    let raised = ref false in
    (try ignore (SkipList.of_list []) with Invalid_argument _ -> raised := true);
    assert_true "should raise Invalid_argument" !raised)

(* ===== Stress Test ===== *)

let test_stress () =
  test "stress: 1000 elements insert/remove" (fun () ->
    let sl = SkipList.create () in
    for i = 1 to 1000 do SkipList.insert i sl done;
    assert_equal "size 1000" "1000" (string_of_int (SkipList.size sl));
    assert_true "min 1" (SkipList.min_elt sl = Some 1);
    assert_true "max 1000" (SkipList.max_elt sl = Some 1000);
    (* Remove odds *)
    for i = 1 to 1000 do
      if i mod 2 = 1 then ignore (SkipList.remove i sl)
    done;
    assert_equal "size 500" "500" (string_of_int (SkipList.size sl));
    assert_true "min 2" (SkipList.min_elt sl = Some 2);
    assert_true "max 1000" (SkipList.max_elt sl = Some 1000);
    (* Verify sorted order *)
    let lst = SkipList.to_list sl in
    let rec is_sorted = function
      | [] | [_] -> true
      | a :: (b :: _ as rest) -> a < b && is_sorted rest
    in
    assert_true "sorted after removals" (is_sorted lst);
    assert_equal "list length" "500" (string_of_int (List.length lst)))

(* ===== Remove All ===== *)

let test_remove_all () =
  test "remove_all: insert and remove all" (fun () ->
    let sl = SkipList.create () in
    for i = 1 to 20 do SkipList.insert i sl done;
    for i = 1 to 20 do ignore (SkipList.remove i sl) done;
    assert_true "empty after removing all" (SkipList.is_empty sl);
    assert_equal "size 0" "0" (string_of_int (SkipList.size sl));
    assert_true "to_list []" (SkipList.to_list sl = []);
    assert_equal "height 0" "0" (string_of_int (SkipList.height sl)));
  test "remove_all: re-insert after clearing" (fun () ->
    let sl = SkipList.create () in
    for i = 1 to 5 do SkipList.insert i sl done;
    for i = 1 to 5 do ignore (SkipList.remove i sl) done;
    SkipList.insert 99 sl;
    assert_equal "size 1" "1" (string_of_int (SkipList.size sl));
    assert_true "mem 99" (SkipList.mem 99 sl))

(* ===== Custom Comparator ===== *)

let test_custom_compare () =
  test "custom: absolute value ordering" (fun () ->
    let abs_cmp a b = compare (abs a) (abs b) in
    let sl = SkipList.create ~compare:abs_cmp () in
    List.iter (fun x -> SkipList.insert x sl) [3; -1; 4; -2; 5];
    let lst = SkipList.to_list sl in
    assert_equal "size" "5" (string_of_int (SkipList.size sl));
    (* Elements sorted by absolute value: -1, -2, 3, 4, 5 *)
    let abs_sorted = List.for_all2 (fun a b -> abs a <= abs b)
      (List.filteri (fun i _ -> i < List.length lst - 1) lst)
      (List.tl lst)
    in
    assert_true "sorted by abs" abs_sorted)

(* ===== Run All ===== *)

let () =
  Printf.printf "Testing SkipList...\n";
  test_empty ();
  test_single ();
  test_multiple ();
  test_duplicates ();
  test_range ();
  test_floor_ceil ();
  test_fold_iter ();
  test_reverse ();
  test_strings ();
  test_of_list ();
  test_stress ();
  test_remove_all ();
  test_custom_compare ();
  Printf.printf "SkipList tests: %d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
