(* test_count_min_sketch.ml - Tests for CountMinSketch module.

   Focus: correctness, the never-underestimate invariant, merge/inner_product,
   heavy hitter detection, and the hash-independence regression that motivated
   the seeded_hash fix (mirrors bloom_filter issue #102 for CMS).

   Run:  ocaml test_count_min_sketch.ml
   (Script-style test: pulled in by `make test-extended`.) *)

#use "test_framework.ml";;
#use "count_min_sketch.ml";;

open CountMinSketch

let () =

  (* — create / dimensions — *)
  suite "create" (fun () ->
    let cms = create ~w:64 ~d:5 in
    assert_true ~msg:"width" (cms.w = 64);
    assert_true ~msg:"depth" (cms.d = 5);
    assert_true ~msg:"empty total" (total cms = 0);
    assert_raises ~msg:"w<=0 rejected" (fun () -> create ~w:0 ~d:5);
    assert_raises ~msg:"d<=0 rejected" (fun () -> create ~w:8 ~d:0)
  );

  suite "create_eps" (fun () ->
    let cms = create_eps ~epsilon:0.01 ~delta:0.01 in
    assert_true ~msg:"w >= ceil(e/eps)" (cms.w >= 272);
    assert_true ~msg:"d >= ceil(ln(1/delta))" (cms.d >= 5);
    assert_raises ~msg:"epsilon<=0 rejected"
      (fun () -> create_eps ~epsilon:0.0 ~delta:0.01);
    assert_raises ~msg:"delta<=0 rejected"
      (fun () -> create_eps ~epsilon:0.01 ~delta:0.0)
  );

  (* — add / count / never underestimate — *)
  suite "add and count basic" (fun () ->
    let cms = create ~w:256 ~d:5 in
    let cms = add cms "apple" ~n:100 () in
    let cms = add cms "banana" ~n:50 () in
    let cms = add cms "cherry" ~n:10 () in
    let cms = add cms "date" ~n:1 () in
    assert_true ~msg:"total=161" (total cms = 161);
    (* Never underestimate is the defining CMS invariant. *)
    assert_true ~msg:"apple >= 100" (count cms "apple" >= 100);
    assert_true ~msg:"banana >= 50" (count cms "banana" >= 50);
    assert_true ~msg:"cherry >= 10" (count cms "cherry" >= 10);
    assert_true ~msg:"date >= 1"    (count cms "date"   >= 1);
    (* An absent element may have a positive estimate (false-positive noise)
       but cannot be negative. *)
    assert_true ~msg:"ghost >= 0" (count cms "ghost" >= 0)
  );

  suite "default n=1" (fun () ->
    let cms = create ~w:64 ~d:4 in
    let cms = add cms "x" () in
    let cms = add cms "x" () in
    let cms = add cms "x" () in
    assert_true ~msg:"x estimated >= 3" (count cms "x" >= 3);
    assert_true ~msg:"total=3" (total cms = 3)
  );

  suite "point_query alias" (fun () ->
    let cms = of_list ~w:128 ~d:5 ["a"; "a"; "b"] in
    assert_true ~msg:"point_query = count" (point_query cms "a" = count cms "a")
  );

  (* — immutability: add returns a new sketch — *)
  suite "immutability" (fun () ->
    let cms = create ~w:64 ~d:4 in
    let cms2 = add cms "y" ~n:5 () in
    assert_true ~msg:"original total still 0" (total cms = 0);
    assert_true ~msg:"original sees no y"     (count cms "y" = 0);
    assert_true ~msg:"new total = 5"          (total cms2 = 5);
    assert_true ~msg:"new sees y >= 5"        (count cms2 "y" >= 5)
  );

  (* — merge — *)
  suite "merge" (fun () ->
    let a = of_list ~w:256 ~d:5 ["x"; "x"; "x"; "y"; "y"; "z"] in
    let b = of_list ~w:256 ~d:5 ["x"; "y"; "y"; "y"; "w"] in
    let m = merge a b in
    assert_true ~msg:"merged total = 11" (total m = 11);
    assert_true ~msg:"x >= 4 (3+1)" (count m "x" >= 4);
    assert_true ~msg:"y >= 5 (2+3)" (count m "y" >= 5);
    assert_true ~msg:"z >= 1"       (count m "z" >= 1);
    assert_true ~msg:"w >= 1"       (count m "w" >= 1);
    assert_raises ~msg:"merge mismatched widths"
      (fun () ->
        let p = create ~w:64 ~d:5 in
        let q = create ~w:32 ~d:5 in
        merge p q);
    assert_raises ~msg:"merge mismatched depths"
      (fun () ->
        let p = create ~w:64 ~d:5 in
        let q = create ~w:64 ~d:3 in
        merge p q)
  );

  (* — inner_product — *)
  suite "inner_product" (fun () ->
    let a = of_list ~w:512 ~d:6 ["x"; "x"; "x"; "y"; "y"; "z"] in
    let b = of_list ~w:512 ~d:6 ["x"; "y"; "y"; "y"; "w"] in
    let ip = inner_product a b in
    (* True inner product = 3*1 + 2*3 + 1*0 + 0*1 = 9. CMS upper-bounds it. *)
    assert_true ~msg:"inner product >= true 9" (ip >= 9);
    assert_raises ~msg:"inner_product mismatched dims"
      (fun () ->
        let p = create ~w:64 ~d:5 in
        let q = create ~w:64 ~d:3 in
        inner_product p q)
  );

  (* — heavy_hitters — *)
  suite "heavy_hitters" (fun () ->
    let cms = create ~w:512 ~d:5 in
    let cms = add cms "apple"  ~n:100 () in
    let cms = add cms "banana" ~n:50  () in
    let cms = add cms "cherry" ~n:10  () in
    let cms = add cms "date"   ~n:1   () in
    let hh = heavy_hitters cms
      ["apple"; "banana"; "cherry"; "date"; "ghost"] ~threshold:20 in
    assert_true ~msg:"apple in hitters"   (List.mem "apple" hh);
    assert_true ~msg:"banana in hitters"  (List.mem "banana" hh);
    assert_true ~msg:"cherry not in hitters" (not (List.mem "cherry" hh));
    assert_true ~msg:"date not in hitters"   (not (List.mem "date" hh))
  );

  (* — reset / copy — *)
  suite "reset" (fun () ->
    let cms = add (create ~w:64 ~d:4) "k" ~n:7 () in
    let r = reset cms in
    assert_true ~msg:"reset total=0" (total r = 0);
    assert_true ~msg:"reset count=0" (count r "k" = 0);
    assert_true ~msg:"reset preserves width" (r.w = 64);
    assert_true ~msg:"reset preserves depth" (r.d = 4);
    assert_true ~msg:"reset does not mutate original" (total cms = 7)
  );

  suite "copy" (fun () ->
    let cms = add (create ~w:64 ~d:4) "k" ~n:3 () in
    let c = copy cms in
    let c = add c "k" ~n:5 () in
    assert_true ~msg:"original unchanged" (count cms "k" = 3);
    assert_true ~msg:"copy advanced"      (count c   "k" >= 8)
  );

  (* — of_list — *)
  suite "of_list" (fun () ->
    let cms = of_list ~w:128 ~d:5 ["a"; "a"; "b"; "c"; "c"; "c"] in
    assert_true ~msg:"total = 6" (total cms = 6);
    assert_true ~msg:"a >= 2" (count cms "a" >= 2);
    assert_true ~msg:"c >= 3" (count cms "c" >= 3)
  );

  (* — saturation — *)
  suite "saturation" (fun () ->
    let cms = create ~w:64 ~d:4 in
    assert_float_eq ~msg:"empty saturation = 0" 0.0 (saturation cms);
    let cms = ref cms in
    for i = 0 to 49 do cms := add !cms i () done;
    let s = saturation !cms in
    assert_true ~msg:"saturation in [0,1]" (s >= 0.0 && s <= 1.0);
    assert_true ~msg:"saturation > 0 after inserts" (s > 0.0)
  );

  (* — regression: hash independence (mirrors bloom_filter #102) —

     With Hashtbl.hash for h1 and Hashtbl.hash (x, salt) for h2, integer keys
     produced highly correlated h1/h2 streams, so a query for an absent key
     would land on the *same* counter across many rows when a nearby key was
     present. The fix uses two seeded_hash with distinct seeds.

     We don't try to measure exact FPR here (too noisy for unit tests).
     Instead we check a basic property the buggy version would violate
     pathologically: for many absent integer keys against a small inserted
     prefix, the median estimate should be close to (and at most) the true
     load on the sketch, not a constant multiple of inserted counts. *)
  suite "hash independence regression (int keys)" (fun () ->
    let cms = ref (create ~w:512 ~d:7) in
    for i = 0 to 99 do cms := add !cms i () done;
    let absent_estimates =
      List.init 200 (fun j -> count !cms (1_000_000 + j))
    in
    let sorted = List.sort compare absent_estimates in
    let median = List.nth sorted (List.length sorted / 2) in
    (* Sketch took 100 insertions total. With well-mixed hashes the median
       collision count for absent integers must be well below 100. Buggy
       correlated hashes routinely pushed this above 50 on this w/d. *)
    assert_true ~msg:"median absent estimate << inserted count"
      (median <= 25);
    (* Also: every estimate is >= 0 and <= inserted count (CMS invariant). *)
    assert_true ~msg:"all absent estimates >= 0"
      (List.for_all (fun v -> v >= 0) absent_estimates);
    assert_true ~msg:"no absent estimate exceeds inserted total"
      (List.for_all (fun v -> v <= 100) absent_estimates)
  );

  test_summary ()
