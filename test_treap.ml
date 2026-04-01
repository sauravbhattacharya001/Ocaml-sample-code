(* test_treap.ml — Tests for Treap module *)
(* Run: ocaml test_treap.ml *)

#use "test_framework.ml";;
#use "treap.ml";;

let () = Printf.printf "Testing Treap...\n"

(* ============================================================ *)
(* Empty treap                                                   *)
(* ============================================================ *)
let () = suite "empty" (fun () ->
  let t : int treap = None in
  assert_true  ~msg:"empty size is 0" (size t = 0);
  assert_false ~msg:"mem on empty" (mem 1 t);
  assert_true  ~msg:"to_list empty" (to_list t = []);
  assert_true  ~msg:"min_elt empty" (min_elt t = None);
  assert_true  ~msg:"max_elt empty" (max_elt t = None);
  assert_true  ~msg:"kth 1 empty" (kth 1 t = None);
  assert_true  ~msg:"verify empty" (verify t)
)

(* ============================================================ *)
(* Single element                                                *)
(* ============================================================ *)
let () = suite "singleton" (fun () ->
  let t = insert 42 None in
  assert_true  ~msg:"size 1" (size t = 1);
  assert_true  ~msg:"mem 42" (mem 42 t);
  assert_false ~msg:"not mem 0" (mem 0 t);
  assert_true  ~msg:"to_list" (to_list t = [42]);
  assert_true  ~msg:"min_elt" (min_elt t = Some 42);
  assert_true  ~msg:"max_elt" (max_elt t = Some 42);
  assert_true  ~msg:"kth 1" (kth 1 t = Some 42);
  assert_true  ~msg:"kth 2 is None" (kth 2 t = None);
  assert_true  ~msg:"verify" (verify t)
)

(* ============================================================ *)
(* Insert & ordering                                             *)
(* ============================================================ *)
let () = suite "insert ordering" (fun () ->
  let t = of_list [5; 3; 8; 1; 4; 7; 9; 2; 6; 10] in
  assert_true ~msg:"size 10" (size t = 10);
  assert_true ~msg:"sorted" (to_list t = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]);
  assert_true ~msg:"verify" (verify t)
)

(* ============================================================ *)
(* No duplicates                                                 *)
(* ============================================================ *)
let () = suite "no duplicates" (fun () ->
  let t = of_list [3; 1; 3; 2; 1; 2; 3] in
  assert_true ~msg:"size 3" (size t = 3);
  assert_true ~msg:"sorted unique" (to_list t = [1; 2; 3]);
  assert_true ~msg:"verify" (verify t)
)

(* ============================================================ *)
(* Delete                                                        *)
(* ============================================================ *)
let () = suite "delete" (fun () ->
  let t = of_list [1; 2; 3; 4; 5] in
  let t2 = delete 3 t in
  assert_true  ~msg:"size after delete" (size t2 = 4);
  assert_false ~msg:"3 removed" (mem 3 t2);
  assert_true  ~msg:"others present" (mem 1 t2 && mem 2 t2 && mem 4 t2 && mem 5 t2);
  assert_true  ~msg:"sorted after delete" (to_list t2 = [1; 2; 4; 5]);
  assert_true  ~msg:"verify after delete" (verify t2);

  (* Delete non-existent *)
  let t3 = delete 99 t in
  assert_true ~msg:"delete non-existent" (size t3 = 5);
  assert_true ~msg:"verify after no-op delete" (verify t3);

  (* Delete from empty *)
  let t4 = delete 1 None in
  assert_true ~msg:"delete from empty" (t4 = None)
)

(* ============================================================ *)
(* Delete all elements                                           *)
(* ============================================================ *)
let () = suite "delete all" (fun () ->
  let t = of_list [3; 1; 4; 1; 5; 9; 2; 6] in
  let t = delete 3 t in
  let t = delete 1 t in
  let t = delete 4 t in
  let t = delete 5 t in
  let t = delete 9 t in
  let t = delete 2 t in
  let t = delete 6 t in
  assert_true ~msg:"all deleted" (size t = 0);
  assert_true ~msg:"empty after all deleted" (to_list t = [])
)

(* ============================================================ *)
(* Search (mem)                                                  *)
(* ============================================================ *)
let () = suite "search" (fun () ->
  let t = of_list [10; 20; 30; 40; 50] in
  assert_true  ~msg:"mem 10" (mem 10 t);
  assert_true  ~msg:"mem 30" (mem 30 t);
  assert_true  ~msg:"mem 50" (mem 50 t);
  assert_false ~msg:"not mem 0" (mem 0 t);
  assert_false ~msg:"not mem 25" (mem 25 t);
  assert_false ~msg:"not mem 60" (mem 60 t)
)

(* ============================================================ *)
(* Kth smallest                                                  *)
(* ============================================================ *)
let () = suite "kth smallest" (fun () ->
  let t = of_list [5; 3; 8; 1; 4] in
  assert_true ~msg:"1st" (kth 1 t = Some 1);
  assert_true ~msg:"2nd" (kth 2 t = Some 3);
  assert_true ~msg:"3rd" (kth 3 t = Some 4);
  assert_true ~msg:"4th" (kth 4 t = Some 5);
  assert_true ~msg:"5th" (kth 5 t = Some 8);
  assert_true ~msg:"0th is None" (kth 0 t = None);
  assert_true ~msg:"6th is None" (kth 6 t = None)
)

(* ============================================================ *)
(* Min / Max                                                     *)
(* ============================================================ *)
let () = suite "min/max" (fun () ->
  let t = of_list [7; 2; 9; 4; 11; 1] in
  assert_true ~msg:"min" (min_elt t = Some 1);
  assert_true ~msg:"max" (max_elt t = Some 11)
)

(* ============================================================ *)
(* Range queries                                                 *)
(* ============================================================ *)
let () = suite "range" (fun () ->
  let t = of_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] in
  assert_true ~msg:"range [3,7]" (range 3 7 t = [3; 4; 5; 6; 7]);
  assert_true ~msg:"range [1,1]" (range 1 1 t = [1]);
  assert_true ~msg:"range [10,10]" (range 10 10 t = [10]);
  assert_true ~msg:"range [5,5]" (range 5 5 t = [5]);
  assert_true ~msg:"range [0,0] empty" (range 0 0 t = []);
  assert_true ~msg:"range [11,20] empty" (range 11 20 t = []);
  assert_true ~msg:"count_range [3,7]" (count_range 3 7 t = 5);
  assert_true ~msg:"count_range [0,0]" (count_range 0 0 t = 0)
)

(* ============================================================ *)
(* Split                                                         *)
(* ============================================================ *)
let () = suite "split" (fun () ->
  let t = of_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] in
  let (l, r) = split 6 t in
  assert_true ~msg:"left < 6" (to_list l = [1; 2; 3; 4; 5]);
  assert_true ~msg:"right >= 6" (to_list r = [6; 7; 8; 9; 10]);
  assert_true ~msg:"left size" (size l = 5);
  assert_true ~msg:"right size" (size r = 5);

  (* Split at boundary *)
  let (l2, r2) = split 1 t in
  assert_true ~msg:"split at min left" (to_list l2 = []);
  assert_true ~msg:"split at min right" (to_list r2 = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]);

  let (l3, r3) = split 11 t in
  assert_true ~msg:"split past max left" (to_list l3 = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]);
  assert_true ~msg:"split past max right" (to_list r3 = [])
)

(* ============================================================ *)
(* Merge                                                         *)
(* ============================================================ *)
let () = suite "merge" (fun () ->
  let a = of_list [1; 3; 5] in
  let b = of_list [7; 9; 11] in
  let m = merge a b in
  assert_true ~msg:"merged sorted" (to_list m = [1; 3; 5; 7; 9; 11]);
  assert_true ~msg:"merged size" (size m = 6);
  assert_true ~msg:"verify merged" (verify m);

  (* Merge with empty *)
  let m2 = merge a None in
  assert_true ~msg:"merge with empty" (to_list m2 = [1; 3; 5]);
  let m3 = merge None b in
  assert_true ~msg:"merge empty with" (to_list m3 = [7; 9; 11])
)

(* ============================================================ *)
(* Split + Merge roundtrip                                       *)
(* ============================================================ *)
let () = suite "split-merge roundtrip" (fun () ->
  let t = of_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] in
  let (l, r) = split 6 t in
  let m = merge l r in
  assert_true ~msg:"roundtrip sorted" (to_list m = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]);
  assert_true ~msg:"roundtrip verify" (verify m)
)

(* ============================================================ *)
(* Set operations                                                *)
(* ============================================================ *)
let () = suite "set operations" (fun () ->
  let a = of_list [1; 3; 5; 7; 9] in
  let b = of_list [2; 3; 5; 8; 9] in

  let u = union a b in
  assert_true ~msg:"union" (to_list u = [1; 2; 3; 5; 7; 8; 9]);

  let i = intersection a b in
  assert_true ~msg:"intersection" (to_list i = [3; 5; 9]);

  let d = difference a b in
  assert_true ~msg:"difference" (to_list d = [1; 7])
)

(* ============================================================ *)
(* Set operations edge cases                                     *)
(* ============================================================ *)
let () = suite "set ops edge cases" (fun () ->
  let a = of_list [1; 2; 3] in

  let u = union a None in
  assert_true ~msg:"union with empty" (to_list u = [1; 2; 3]);

  let i = intersection a None in
  assert_true ~msg:"intersection with empty" (to_list i = []);

  let d = difference a None in
  assert_true ~msg:"difference with empty" (to_list d = [1; 2; 3]);

  let d2 = difference a a in
  assert_true ~msg:"difference with self" (to_list d2 = [])
)

(* ============================================================ *)
(* Height / balance                                              *)
(* ============================================================ *)
let () = suite "height" (fun () ->
  let t = of_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] in
  let h = height t in
  (* For 15 elements, a balanced tree has height ~4, treap should be < 15 *)
  assert_true ~msg:"height reasonable" (h > 0 && h < 15);
  assert_true ~msg:"height >= log2(n)" (h >= 4)
)

(* ============================================================ *)
(* of_list / to_list roundtrip                                   *)
(* ============================================================ *)
let () = suite "of_list/to_list" (fun () ->
  let lst = [9; 1; 5; 3; 7; 2; 8; 4; 6; 10] in
  let t = of_list lst in
  let sorted = List.sort compare lst in
  assert_true ~msg:"roundtrip sorted" (to_list t = sorted)
)

(* ============================================================ *)
(* Large treap stress test                                       *)
(* ============================================================ *)
let () = suite "stress test" (fun () ->
  (* Insert 0..99 in scrambled order *)
  let values = List.init 100 (fun i -> (i * 37 + 13) mod 100) in
  let t = of_list values in
  let expected = List.init 100 (fun i -> i) in
  assert_true ~msg:"100 elements sorted" (to_list t = expected);
  assert_true ~msg:"100 elements verify" (verify t);
  assert_true ~msg:"100 elements size" (size t = 100);

  (* Delete even numbers *)
  let t2 = List.fold_left (fun acc i -> delete (i * 2) acc) t (List.init 50 (fun i -> i)) in
  let odds = List.init 50 (fun i -> i * 2 + 1) in
  assert_true ~msg:"50 odds remain" (to_list t2 = odds);
  assert_true ~msg:"50 odds verify" (verify t2)
)

(* ============================================================ *)
(* Pretty print (smoke test)                                     *)
(* ============================================================ *)
let () = suite "pretty_print" (fun () ->
  let t = of_list [3; 1; 5] in
  let s = pretty_print string_of_int t in
  assert_true ~msg:"pretty_print non-empty" (String.length s > 0);

  let s2 = pretty_print string_of_int None in
  assert_true ~msg:"pretty_print empty" (s2 = "(empty treap)\n")
)

(* ============================================================ *)
(* Summary                                                       *)
(* ============================================================ *)
let () = test_summary ()
