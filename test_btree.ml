(* test_btree.ml — Tests for the B-Tree implementation *)

#use "test_framework.ml";;
#use "btree.ml";;

let () =
  Printf.printf "\n═══ B-Tree Tests ═══\n\n";

  (* ── Construction ──────────────────────────────── *)

  suite "Construction" (fun () ->
    assert_true ~msg:"empty tree has size 0"
      (size (create ~t:2) = 0);

    assert_true ~msg:"empty tree has height 0"
      (height (create ~t:2) = 0);

    assert_true ~msg:"invalid degree raises"
      (try let _ = create ~t:1 in false
       with Invalid_argument _ -> true);

    assert_true ~msg:"t=2 accepted"
      (size (create ~t:2) = 0);

    assert_true ~msg:"t=10 accepted"
      (size (create ~t:10) = 0)
  );

  (* ── Single insert ────────────────────────────── *)

  suite "Single insert" (fun () ->
    let t = insert 42 (create ~t:2) in

    assert_true ~msg:"size is 1 after insert"
      (size t = 1);

    assert_true ~msg:"search finds inserted key"
      (search 42 t.root);

    assert_true ~msg:"search misses absent key"
      (not (search 99 t.root));

    assert_true ~msg:"sorted list is [42]"
      (to_sorted_list t = [42])
  );

  (* ── Multiple inserts & ordering ──────────────── *)

  suite "Multiple inserts" (fun () ->
    let vals = [10; 20; 5; 6; 12; 30; 7; 17] in
    let t = List.fold_left (fun tr v -> insert v tr) (create ~t:2) vals in

    assert_true ~msg:"size matches insert count"
      (size t = List.length vals);

    assert_true ~msg:"all keys found"
      (List.for_all (fun k -> search k t.root) vals);

    assert_true ~msg:"absent keys not found"
      (not (search 99 t.root) && not (search 0 t.root));

    let sorted = to_sorted_list t in
    assert_true ~msg:"in-order traversal is sorted"
      (sorted = List.sort compare vals)
  );

  (* ── Root splitting ───────────────────────────── *)

  suite "Root splitting (t=2)" (fun () ->
    (* t=2 means max 3 keys per node; 4th insert forces split *)
    let t = create ~t:2 in
    let t = List.fold_left (fun tr v -> insert v tr) t [1; 2; 3; 4] in

    assert_true ~msg:"height > 0 after split"
      (height t > 0);

    assert_true ~msg:"size is 4"
      (size t = 4);

    assert_true ~msg:"sorted output correct"
      (to_sorted_list t = [1; 2; 3; 4])
  );

  (* ── Larger trees ─────────────────────────────── *)

  suite "Larger tree (50 elements, t=2)" (fun () ->
    let vals = List.init 50 (fun i -> i) in
    let t = List.fold_left (fun tr v -> insert v tr) (create ~t:2) vals in

    assert_true ~msg:"size is 50"
      (size t = 50);

    assert_true ~msg:"all elements found"
      (List.for_all (fun k -> search k t.root) vals);

    assert_true ~msg:"sorted traversal matches"
      (to_sorted_list t = vals);

    assert_true ~msg:"height is reasonable (<=6 for 50 elems t=2)"
      (height t <= 6)
  );

  suite "Larger tree (100 elements, t=3)" (fun () ->
    let vals = List.init 100 (fun i -> i * 2 + 1) in
    let t = List.fold_left (fun tr v -> insert v tr) (create ~t:3) vals in

    assert_true ~msg:"size is 100"
      (size t = 100);

    assert_true ~msg:"sorted traversal correct"
      (to_sorted_list t = List.sort compare vals);

    assert_true ~msg:"height is reasonable (<=4 for 100 elems t=3)"
      (height t <= 4)
  );

  (* ── Duplicate handling ───────────────────────── *)

  suite "Duplicate keys" (fun () ->
    let t = List.fold_left (fun tr v -> insert v tr) (create ~t:2) [5; 5; 5] in

    assert_true ~msg:"duplicates stored (size=3)"
      (size t = 3);

    assert_true ~msg:"search finds duplicate key"
      (search 5 t.root)
  );

  (* ── Reverse insertion order ──────────────────── *)

  suite "Reverse order insertion" (fun () ->
    let vals = List.init 30 (fun i -> 30 - i) in
    let t = List.fold_left (fun tr v -> insert v tr) (create ~t:2) vals in

    assert_true ~msg:"size correct"
      (size t = 30);

    assert_true ~msg:"sorted output correct"
      (to_sorted_list t = List.init 30 (fun i -> i + 1))
  );

  (* ── Different minimum degrees ────────────────── *)

  suite "Various minimum degrees" (fun () ->
    let vals = List.init 40 Fun.id in
    List.iter (fun deg ->
      let t = List.fold_left (fun tr v -> insert v tr) (create ~t:deg) vals in
      assert_true ~msg:(Printf.sprintf "t=%d: size correct" deg)
        (size t = 40);
      assert_true ~msg:(Printf.sprintf "t=%d: sorted correct" deg)
        (to_sorted_list t = vals)
    ) [2; 3; 5; 10; 20]
  );

  (* ── B-Tree height property ──────────────────── *)

  suite "Height bound property" (fun () ->
    (* For n keys and min degree t, height <= log_t((n+1)/2) *)
    let vals = List.init 1000 Fun.id in
    let t = List.fold_left (fun tr v -> insert v tr) (create ~t:3) vals in

    assert_true ~msg:"height within theoretical bound for 1000 keys t=3"
      (height t <= 7);  (* log_3(500) ~ 5.6, generous bound *)

    assert_true ~msg:"all 1000 keys searchable"
      (List.for_all (fun k -> search k t.root) vals)
  );

  test_summary ()
