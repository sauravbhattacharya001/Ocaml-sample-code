(* Test suite for crdt.ml *)
(* Uses #use pattern consistent with the repo *)

#use "crdt.ml";;

(* The main tests are embedded in crdt.ml's let () block.
   This file exercises additional edge cases. *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let test name f =
    try
      f ();
      incr passed;
      Printf.printf "  ✓ %s\n" name
    with ex ->
      incr failed;
      Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string ex)
  in
  let assert_eq a b msg =
    if a <> b then failwith (Printf.sprintf "%s: expected %d, got %d" msg a b)
  in
  let assert_true b msg = if not b then failwith msg in

  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "  CRDT Edge Case Tests\n";
  Printf.printf "══════════════════════════════════════════\n\n";

  (* G-Counter edge cases *)
  test "GCounter: empty counter has value 0" (fun () ->
    assert_eq (GCounter.value (GCounter.create ())) 0 "empty"
  );

  test "GCounter: merge with empty" (fun () ->
    let c = GCounter.create () |> GCounter.increment "A" 5 in
    let m = GCounter.merge c (GCounter.create ()) in
    assert_eq (GCounter.value m) 5 "merge with empty"
  );

  test "GCounter: merge two empties" (fun () ->
    let m = GCounter.merge (GCounter.create ()) (GCounter.create ()) in
    assert_eq (GCounter.value m) 0 "two empties"
  );

  test "GCounter: multiple increments same replica" (fun () ->
    let c = GCounter.create ()
      |> GCounter.increment "A" 3
      |> GCounter.increment "A" 7
    in
    assert_eq (GCounter.value c) 10 "accumulated"
  );

  test "GCounter: increment by 0" (fun () ->
    let c = GCounter.create () |> GCounter.increment "A" 0 in
    assert_eq (GCounter.value c) 0 "zero increment"
  );

  test "GCounter: associativity" (fun () ->
    let a = GCounter.create () |> GCounter.increment "A" 1 in
    let b = GCounter.create () |> GCounter.increment "B" 2 in
    let c = GCounter.create () |> GCounter.increment "C" 3 in
    let ab_c = GCounter.merge (GCounter.merge a b) c in
    let a_bc = GCounter.merge a (GCounter.merge b c) in
    assert_eq (GCounter.value ab_c) (GCounter.value a_bc) "associative"
  );

  (* PN-Counter edge cases *)
  test "PNCounter: empty has value 0" (fun () ->
    assert_eq (PNCounter.value (PNCounter.create ())) 0 "empty"
  );

  test "PNCounter: decrement only" (fun () ->
    let c = PNCounter.create () |> PNCounter.decrement "A" 5 in
    assert_eq (PNCounter.value c) (-5) "decrement only"
  );

  test "PNCounter: many replicas" (fun () ->
    let c = PNCounter.create ()
      |> PNCounter.increment "A" 10
      |> PNCounter.increment "B" 20
      |> PNCounter.increment "C" 30
      |> PNCounter.decrement "D" 5
    in
    assert_eq (PNCounter.value c) 55 "four replicas"
  );

  (* G-Set edge cases *)
  test "GSet: empty set" (fun () ->
    let s = GSet.create () in
    assert_eq (GSet.size s) 0 "empty size";
    assert_true (not (GSet.contains "x" s)) "not contains"
  );

  test "GSet: merge with self" (fun () ->
    let s = GSet.create () |> GSet.add "a" |> GSet.add "b" in
    let m = GSet.merge s s in
    assert_eq (GSet.size m) 2 "self merge"
  );

  test "GSet: associativity" (fun () ->
    let a = GSet.create () |> GSet.add "1" in
    let b = GSet.create () |> GSet.add "2" in
    let c = GSet.create () |> GSet.add "3" in
    let ab_c = GSet.merge (GSet.merge a b) c in
    let a_bc = GSet.merge a (GSet.merge b c) in
    assert_true (GSet.elements ab_c = GSet.elements a_bc) "associative"
  );

  (* OR-Set edge cases *)
  test "ORSet: empty set" (fun () ->
    let s = ORSet.create () in
    assert_eq (ORSet.size s) 0 "empty";
    assert_true (ORSet.elements s = []) "no elements"
  );

  test "ORSet: remove non-existent is no-op" (fun () ->
    let s = ORSet.create ()
      |> ORSet.add "A" "x"
      |> ORSet.remove "y"
    in
    assert_true (ORSet.contains "x" s) "x still present";
    assert_eq (ORSet.size s) 1 "size unchanged"
  );

  test "ORSet: add same element from different replicas" (fun () ->
    let s = ORSet.create ()
      |> ORSet.add "A" "x"
      |> ORSet.add "B" "x"
    in
    assert_eq (ORSet.size s) 1 "deduplicated";
    (* Remove should clear both tags *)
    let s' = ORSet.remove "x" s in
    assert_true (not (ORSet.contains "x" s')) "removed all tags"
  );

  test "ORSet: add-remove-add" (fun () ->
    let s = ORSet.create ()
      |> ORSet.add "A" "x"
      |> ORSet.remove "x"
      |> ORSet.add "A" "x"
    in
    assert_true (ORSet.contains "x" s) "re-added"
  );

  (* LWW-Register edge cases *)
  test "LWWRegister: same replica successive writes" (fun () ->
    let r = LWWRegister.create "a" 1.0 "R1"
      |> LWWRegister.write "b" 2.0 "R1"
      |> LWWRegister.write "c" 3.0 "R1"
    in
    assert_true (LWWRegister.read r = "c") "latest"
  );

  test "LWWRegister: merge is idempotent" (fun () ->
    let r = LWWRegister.create "x" 5.0 "A" in
    let m = LWWRegister.merge r r in
    assert_true (LWWRegister.read m = "x") "idempotent"
  );

  test "LWWRegister: merge is associative" (fun () ->
    let a = LWWRegister.create "a" 1.0 "A" in
    let b = LWWRegister.create "b" 2.0 "B" in
    let c = LWWRegister.create "c" 3.0 "C" in
    let ab_c = LWWRegister.merge (LWWRegister.merge a b) c in
    let a_bc = LWWRegister.merge a (LWWRegister.merge b c) in
    assert_true (LWWRegister.read ab_c = LWWRegister.read a_bc) "associative"
  );

  (* MV-Register edge cases *)
  test "MVRegister: empty after merge of causal chain" (fun () ->
    let r1 = MVRegister.create "v1" "A" in
    let r2 = MVRegister.write "v2" "A" r1 in
    let r3 = MVRegister.write "v3" "A" r2 in
    let m = MVRegister.merge r1 (MVRegister.merge r2 r3) in
    let vals = MVRegister.read m in
    assert_eq (List.length vals) 1 "causal chain → one value";
    assert_true (List.hd vals = "v3") "latest in chain"
  );

  test "MVRegister: merge is idempotent" (fun () ->
    let r = MVRegister.create "x" "A" in
    let m = MVRegister.merge r r in
    assert_eq (List.length (MVRegister.read m)) 1 "idempotent"
  );

  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "  Edge Cases: %d passed, %d failed\n" !passed !failed;
  Printf.printf "══════════════════════════════════════════\n";
  if !failed > 0 then exit 1
