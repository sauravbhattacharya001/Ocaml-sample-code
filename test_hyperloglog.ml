(* test_hyperloglog.ml — Tests for HyperLogLog probabilistic cardinality estimator *)

(* Inline the module under test *)
#use "hyperloglog.ml"

let tests_run = ref 0
let tests_passed = ref 0

let assert_true msg cond =
  incr tests_run;
  if cond then incr tests_passed
  else Printf.printf "FAIL: %s\n" msg

let assert_float_range msg v lo hi =
  incr tests_run;
  if v >= lo && v <= hi then incr tests_passed
  else Printf.printf "FAIL: %s — got %.2f, expected [%.2f, %.2f]\n" msg v lo hi

let () =
  Printf.printf "=== HyperLogLog Tests ===\n\n";

  (* Test 1: create with valid precisions *)
  Printf.printf "-- create --\n";
  let h4 = HyperLogLog.create ~precision:4 () in
  assert_true "precision 4" (HyperLogLog.precision h4 = 4);
  assert_true "registers 16" (HyperLogLog.num_registers h4 = 16);
  let h16 = HyperLogLog.create ~precision:16 () in
  assert_true "precision 16" (HyperLogLog.precision h16 = 16);
  assert_true "registers 65536" (HyperLogLog.num_registers h16 = 65536);

  (* Test 2: create with invalid precision *)
  let bad_prec label p =
    try
      let _ = HyperLogLog.create ~precision:p () in
      assert_true (label ^ " should fail") false
    with Failure _ -> assert_true (label ^ " raises") true
  in
  bad_prec "precision 3" 3;
  bad_prec "precision 17" 17;

  (* Test 3: is_empty on fresh sketch *)
  Printf.printf "-- is_empty --\n";
  let h = HyperLogLog.create ~precision:10 () in
  assert_true "fresh is_empty" (HyperLogLog.is_empty h);
  let h = HyperLogLog.add h "x" in
  assert_true "after add not empty" (not (HyperLogLog.is_empty h));

  (* Test 4: single element cardinality *)
  Printf.printf "-- single element --\n";
  let h = HyperLogLog.create ~precision:14 () in
  let h = HyperLogLog.add h "hello" in
  let c = HyperLogLog.cardinality h in
  assert_float_range "single element ~1" c 0.5 3.0;

  (* Test 5: duplicate elements should not increase cardinality *)
  Printf.printf "-- duplicates --\n";
  let h = HyperLogLog.create ~precision:12 () in
  let h = ref h in
  for _ = 1 to 500 do h := HyperLogLog.add !h "same" done;
  let c = HyperLogLog.cardinality !h in
  assert_float_range "500 duplicates ~1" c 0.5 3.0;

  (* Test 6: known cardinality estimation accuracy *)
  Printf.printf "-- accuracy at n=5000, p=14 --\n";
  let h = ref (HyperLogLog.create ~precision:14 ()) in
  for i = 0 to 4999 do h := HyperLogLog.add !h (string_of_int i) done;
  let c = HyperLogLog.cardinality !h in
  assert_float_range "5000 elements" c 4500.0 5500.0;

  (* Test 7: accuracy at n=50000 *)
  Printf.printf "-- accuracy at n=50000, p=14 --\n";
  let h = ref (HyperLogLog.create ~precision:14 ()) in
  for i = 0 to 49999 do h := HyperLogLog.add !h (string_of_int i) done;
  let c = HyperLogLog.cardinality !h in
  assert_float_range "50000 elements" c 45000.0 55000.0;

  (* Test 8: merge *)
  Printf.printf "-- merge --\n";
  let a = ref (HyperLogLog.create ~precision:12 ()) in
  let b = ref (HyperLogLog.create ~precision:12 ()) in
  for i = 0 to 2999 do a := HyperLogLog.add !a (string_of_int i) done;
  for i = 2000 to 4999 do b := HyperLogLog.add !b (string_of_int i) done;
  let u = HyperLogLog.merge !a !b in
  let cu = HyperLogLog.cardinality u in
  assert_float_range "merge union ~5000" cu 4250.0 5750.0;

  (* Test 9: merge precision mismatch *)
  Printf.printf "-- merge mismatch --\n";
  (try
    let _ = HyperLogLog.merge
      (HyperLogLog.create ~precision:10 ())
      (HyperLogLog.create ~precision:12 ()) in
    assert_true "merge mismatch should fail" false
  with Failure _ -> assert_true "merge mismatch raises" true);

  (* Test 10: intersection_cardinality *)
  Printf.printf "-- intersection --\n";
  let ic = HyperLogLog.intersection_cardinality !a !b in
  assert_float_range "intersection ~1000" ic 0.0 3000.0;

  (* Test 11: jaccard *)
  Printf.printf "-- jaccard --\n";
  let j = HyperLogLog.jaccard !a !b in
  assert_float_range "jaccard in [0,1]" j 0.0 1.0;

  (* Test 12: jaccard of empty sketches *)
  let e1 = HyperLogLog.create ~precision:10 () in
  let e2 = HyperLogLog.create ~precision:10 () in
  let j0 = HyperLogLog.jaccard e1 e2 in
  assert_float_range "jaccard empty = 0" j0 0.0 0.0;

  (* Test 13: serialization round-trip *)
  Printf.printf "-- serialization --\n";
  let h = ref (HyperLogLog.create ~precision:10 ()) in
  for i = 0 to 999 do h := HyperLogLog.add !h (string_of_int i) done;
  let before = HyperLogLog.cardinality !h in
  let s = HyperLogLog.serialize !h in
  let h2 = HyperLogLog.deserialize s in
  let after = HyperLogLog.cardinality h2 in
  assert_true "serialize round-trip" (before = after);
  assert_true "precision preserved" (HyperLogLog.precision h2 = 10);
  assert_true "registers preserved" (HyperLogLog.num_registers h2 = 1024);

  (* Test 14: deserialize invalid data *)
  Printf.printf "-- deserialize errors --\n";
  (try let _ = HyperLogLog.deserialize "GARBAGE" in
    assert_true "bad deserialize should fail" false
  with Failure _ -> assert_true "bad deserialize raises" true);
  (try let _ = HyperLogLog.deserialize "HLL:10:short" in
    assert_true "size mismatch should fail" false
  with Failure _ -> assert_true "size mismatch raises" true);

  (* Test 15: add_hash *)
  Printf.printf "-- add_hash --\n";
  let h = HyperLogLog.create ~precision:10 () in
  let h = HyperLogLog.add_hash h 42 in
  let h = HyperLogLog.add_hash h 123456 in
  let c = HyperLogLog.cardinality h in
  assert_float_range "add_hash 2 values" c 1.0 5.0;

  (* Test 16: memory_bytes *)
  Printf.printf "-- memory_bytes --\n";
  let h = HyperLogLog.create ~precision:10 () in
  assert_true "memory = num_registers" (HyperLogLog.memory_bytes h = HyperLogLog.num_registers h);

  (* Test 17: relative_error *)
  Printf.printf "-- relative_error --\n";
  let h14 = HyperLogLog.create ~precision:14 () in
  let err = HyperLogLog.relative_error h14 in
  assert_float_range "relative_error p=14" err 0.005 0.015;

  (* Test 18: to_string contains key info *)
  Printf.printf "-- to_string --\n";
  let h = HyperLogLog.create ~precision:8 () in
  let s = HyperLogLog.to_string h in
  assert_true "to_string has content" (String.length s > 10);

  (* Test 19: default precision is 14 *)
  Printf.printf "-- default precision --\n";
  let h = HyperLogLog.create () in
  assert_true "default precision 14" (HyperLogLog.precision h = 14);

  (* Summary *)
  Printf.printf "\n=== Results: %d/%d passed ===\n" !tests_passed !tests_run;
  if !tests_passed = !tests_run then
    Printf.printf "All tests passed!\n"
  else begin
    Printf.printf "SOME TESTS FAILED\n";
    exit 1
  end
