(* test_bloom_filter.ml — Tests for BloomFilter module *)

#use "test_framework.ml";;
#use "bloom_filter.ml";;

open BloomFilter

let () =
  (* ── create / basic properties ── *)
  suite "create" (fun () ->
    let bf = create () in
    assert_true ~msg:"default size is 1024" (size bf = 1024);
    assert_true ~msg:"default k is 7" (num_hashes bf = 7);
    assert_true ~msg:"count starts at 0" (count bf = 0);
    assert_true ~msg:"is_empty on new filter" (is_empty bf);

    let bf2 = create ~m:256 ~k:3 () in
    assert_true ~msg:"custom m" (size bf2 = 256);
    assert_true ~msg:"custom k" (num_hashes bf2 = 3);

    (* m clamped to at least 8 *)
    let bf3 = create ~m:1 ~k:1 () in
    assert_true ~msg:"m clamped to 8 minimum" (size bf3 >= 8);

    (* k clamped to at least 1 *)
    let bf4 = create ~m:64 ~k:0 () in
    assert_true ~msg:"k clamped to 1 minimum" (num_hashes bf4 >= 1)
  );

  (* ── create_optimal ── *)
  suite "create_optimal" (fun () ->
    let bf = create_optimal ~expected_elements:100 ~fp_rate:0.01 in
    assert_true ~msg:"optimal m > 0" (size bf > 0);
    assert_true ~msg:"optimal k > 0" (num_hashes bf > 0);
    assert_true ~msg:"optimal m large enough for 100 elts at 1%"
      (size bf >= 500)  (* ln(2)^2 formula gives ~958 *)
  );

  (* ── add / mem: no false negatives ── *)
  suite "add and mem" (fun () ->
    let bf = create ~m:4096 ~k:5 () in
    let bf = add "hello" bf in
    let bf = add "world" bf in
    let bf = add 42 bf in
    assert_true  ~msg:"mem finds 'hello'" (mem "hello" bf);
    assert_true  ~msg:"mem finds 'world'" (mem "world" bf);
    assert_true  ~msg:"mem finds 42" (mem 42 bf);
    assert_true  ~msg:"count is 3" (count bf = 3);
    assert_false ~msg:"not empty after add" (is_empty bf);

    (* absent element — could be false positive but very unlikely
       with m=4096, k=5, n=3 *)
    assert_false ~msg:"'missing' likely absent"
      (mem "this_string_was_never_added_12345" bf)
  );

  (* ── immutability ── *)
  suite "immutability" (fun () ->
    let bf1 = create ~m:512 ~k:3 () in
    let bf2 = add "x" bf1 in
    assert_true  ~msg:"original unchanged" (count bf1 = 0);
    assert_true  ~msg:"new filter has element" (count bf2 = 1);
    assert_false ~msg:"original doesn't see 'x'" (mem "x" bf1);
    assert_true  ~msg:"new filter sees 'x'" (mem "x" bf2)
  );

  (* ── popcount / saturation ── *)
  suite "popcount and saturation" (fun () ->
    let bf = create ~m:64 ~k:3 () in
    assert_true ~msg:"empty popcount is 0" (popcount bf = 0);
    assert_true ~msg:"empty saturation is 0.0" (saturation bf = 0.0);

    let bf = add "a" bf in
    assert_true ~msg:"popcount > 0 after add" (popcount bf > 0);
    assert_true ~msg:"popcount <= k" (popcount bf <= 3);
    let sat = saturation bf in
    assert_true ~msg:"saturation > 0 after add" (sat > 0.0);
    assert_true ~msg:"saturation <= 1.0" (sat <= 1.0)
  );

  (* ── false_positive_rate ── *)
  suite "false_positive_rate" (fun () ->
    let bf = create ~m:1024 ~k:7 () in
    assert_true ~msg:"FPR is 0 for empty filter"
      (false_positive_rate bf = 0.0);

    let bf = add "x" bf in
    let fpr = false_positive_rate bf in
    assert_true ~msg:"FPR > 0 after add" (fpr > 0.0);
    assert_true ~msg:"FPR < 1 with low fill" (fpr < 1.0);

    (* FPR grows with more elements *)
    let bf2 = List.fold_left (fun acc i -> add i acc) bf
        (List.init 100 (fun i -> i)) in
    assert_true ~msg:"FPR increases with fill"
      (false_positive_rate bf2 > fpr)
  );

  (* ── of_list ── *)
  suite "of_list" (fun () ->
    let items = ["alpha"; "beta"; "gamma"; "delta"] in
    let bf = of_list ~m:2048 ~k:5 items in
    assert_true ~msg:"count matches list length" (count bf = 4);
    assert_true ~msg:"all items found" (mem_all items bf)
  );

  (* ── mem_all / mem_any ── *)
  suite "mem_all and mem_any" (fun () ->
    let bf = of_list ~m:4096 ~k:5 [1; 2; 3] in
    assert_true  ~msg:"mem_all present" (mem_all [1; 2; 3] bf);
    assert_true  ~msg:"mem_any present" (mem_any [1; 2; 3] bf);
    (* With enough bits and few elements, absent items should not match *)
    assert_false ~msg:"mem_all with absent item"
      (mem_all [1; 2; 999999] bf);
    assert_true  ~msg:"mem_any with mix"
      (mem_any [1; 999999] bf)
  );

  (* ── union ── *)
  suite "union" (fun () ->
    let bf1 = of_list ~m:1024 ~k:5 ["a"; "b"] in
    let bf2 = of_list ~m:1024 ~k:5 ["c"; "d"] in
    let combined = union bf1 bf2 in
    assert_true ~msg:"union count = sum" (count combined = 4);
    assert_true ~msg:"union has 'a'" (mem "a" combined);
    assert_true ~msg:"union has 'c'" (mem "c" combined);
    assert_true ~msg:"union has 'd'" (mem "d" combined);

    (* incompatible filters *)
    let bf3 = create ~m:512 ~k:5 () in
    assert_raises ~msg:"union rejects incompatible m"
      (fun () -> ignore (union bf1 bf3))
  );

  (* ── clear ── *)
  suite "clear" (fun () ->
    let bf = of_list [10; 20; 30] in
    let cleared = clear bf in
    assert_true ~msg:"cleared count is 0" (count cleared = 0);
    assert_true ~msg:"cleared same m" (size cleared = size bf);
    assert_true ~msg:"cleared same k" (num_hashes cleared = num_hashes bf);
    assert_false ~msg:"cleared doesn't find old elem" (mem 10 cleared)
  );

  (* ── copy ── *)
  suite "copy" (fun () ->
    let bf = of_list ~m:256 ~k:3 ["x"; "y"] in
    let cp = copy bf in
    assert_true ~msg:"copy has same count" (count cp = count bf);
    assert_true ~msg:"copy finds 'x'" (mem "x" cp);
    (* adding to copy doesn't affect original *)
    let cp2 = add "z" cp in
    assert_true  ~msg:"copy2 finds 'z'" (mem "z" cp2);
    assert_true  ~msg:"original count unchanged" (count bf = 2)
  );

  (* ── to_string ── *)
  suite "to_string" (fun () ->
    let bf = create ~m:128 ~k:4 () in
    let s = to_string bf in
    assert_true ~msg:"to_string contains 'BloomFilter'"
      (String.length s > 0 && String.sub s 0 11 = "BloomFilter")
  );

  (* ── stress: false-positive rate is bounded ── *)
  suite "stress: FP rate bounded" (fun () ->
    (* Insert 100 elements, test 1000 absent ones.
       With m=10000, k=7, theoretical FPR ≈ 0.0008.
       We allow up to 5% empirical FPR to account for variance. *)
    let bf = ref (create ~m:10000 ~k:7 ()) in
    for i = 0 to 99 do
      bf := add (Printf.sprintf "present_%d" i) !bf
    done;
    let false_positives = ref 0 in
    for i = 0 to 999 do
      if mem (Printf.sprintf "absent_%d" i) !bf then
        incr false_positives
    done;
    assert_true ~msg:"empirical FPR < 5%"
      (!false_positives < 50)
  );

  test_summary ()
