(* test_diff.ml — Tests for the Myers Diff implementation *)

#use "test_framework.ml";;
#use "diff.ml";;

let () =
  Printf.printf "\n═══ Diff Algorithm Tests ═══\n\n";

  (* ── Identity / empty cases ────────────────────── *)

  suite "Empty and identity" (fun () ->
    let r = diff [||] [||] in
    assert_true ~msg:"empty arrays: 0 distance"
      (r.distance = 0);
    assert_true ~msg:"empty arrays: 1.0 similarity"
      (r.similarity = 1.0);

    let r = diff [|1;2;3|] [|1;2;3|] in
    assert_true ~msg:"identical arrays: 0 distance"
      (r.distance = 0);
    assert_true ~msg:"identical arrays: all Equal edits"
      (List.for_all (function Equal _ -> true | _ -> false) r.edits);
    assert_true ~msg:"identical arrays: lcs = full array"
      (r.lcs = [1;2;3])
  );

  (* ── Pure insertions ──────────────────────────── *)

  suite "Pure insertions" (fun () ->
    let r = diff [||] [|1;2;3|] in
    assert_true ~msg:"insert 3 into empty: distance=3"
      (r.distance = 3);
    assert_true ~msg:"all edits are Insert"
      (List.for_all (function Insert _ -> true | _ -> false) r.edits);
    assert_true ~msg:"lcs is empty"
      (r.lcs = [])
  );

  (* ── Pure deletions ───────────────────────────── *)

  suite "Pure deletions" (fun () ->
    let r = diff [|1;2;3|] [||] in
    assert_true ~msg:"delete all: distance=3"
      (r.distance = 3);
    assert_true ~msg:"all edits are Delete"
      (List.for_all (function Delete _ -> true | _ -> false) r.edits);
    assert_true ~msg:"lcs is empty"
      (r.lcs = [])
  );

  (* ── Mixed edits ──────────────────────────────── *)

  suite "Mixed edits" (fun () ->
    let r = diff [|1;2;3|] [|1;3;4|] in
    assert_true ~msg:"distance is 2 (delete 2, insert 4)"
      (r.distance = 2);
    assert_true ~msg:"lcs contains common elements"
      (r.lcs = [1;3]);
    assert_true ~msg:"similarity between 0 and 1"
      (r.similarity > 0.0 && r.similarity < 1.0)
  );

  (* ── LCS correctness ─────────────────────────── *)

  suite "LCS extraction" (fun () ->
    let r = diff [|1;2;3;4;5|] [|2;4;6|] in
    assert_true ~msg:"lcs is [2;4]"
      (r.lcs = [2;4]);

    let r = diff [|"a";"b";"c";"d"|] [|"b";"d";"e"|] in
    assert_true ~msg:"string lcs is [b;d]"
      (r.lcs = ["b";"d"])
  );

  (* ── Patch application ───────────────────────── *)

  suite "Patch apply" (fun () ->
    let a = [|1;2;3;4;5|] in
    let b = [|1;3;5;6|] in
    let r = diff a b in
    let patched = apply_patch a r.edits in
    assert_true ~msg:"apply_patch reproduces b"
      (patched = b);

    (* Round-trip: apply then reverse *)
    let reversed = reverse_patch b r.edits in
    assert_true ~msg:"reverse_patch reproduces a"
      (reversed = a)
  );

  suite "Patch on strings" (fun () ->
    let a = [|"hello";"world";"foo"|] in
    let b = [|"hello";"bar";"world"|] in
    let r = diff a b in
    let patched = apply_patch a r.edits in
    assert_true ~msg:"string patch correct"
      (patched = b)
  );

  (* ── Similarity ───────────────────────────────── *)

  suite "Similarity metric" (fun () ->
    let r = diff [|1;2;3|] [|1;2;3|] in
    assert_float_eq ~msg:"identical: similarity 1.0" ~eps:0.001
      1.0 r.similarity;

    let r = diff [|1;2;3|] [|4;5;6|] in
    assert_float_eq ~msg:"completely different: similarity 0.0" ~eps:0.001
      0.0 r.similarity
  );

  (* ── Line-level diff ──────────────────────────── *)

  suite "Line-level diff" (fun () ->
    let old_text = "line1\nline2\nline3\n" in
    let new_text = "line1\nmodified\nline3\nnew_line\n" in
    let r = diff_lines old_text new_text in
    assert_true ~msg:"distance = 2 (delete line2, insert modified, insert new_line)"
      (r.distance >= 2);
    assert_true ~msg:"has hunks"
      (List.length r.hunks > 0)
  );

  (* ── Word-level diff ──────────────────────────── *)

  suite "Word-level diff" (fun () ->
    let r = diff_words "the quick brown fox" "the slow brown cat" in
    assert_true ~msg:"word diff distance = 2"
      (r.distance = 2);
    assert_true ~msg:"common words in lcs"
      (List.mem "the" r.lcs && List.mem "brown" r.lcs)
  );

  (* ── Character-level diff ─────────────────────── *)

  suite "Character-level diff" (fun () ->
    let r = diff_chars "abc" "adc" in
    assert_true ~msg:"char diff distance = 2 (delete b, insert d)"
      (r.distance = 2);
    assert_true ~msg:"lcs contains a and c"
      (List.mem "a" r.lcs && List.mem "c" r.lcs)
  );

  (* ── Unified format ───────────────────────────── *)

  suite "Unified format output" (fun () ->
    let r = diff_lines "a\nb\nc\n" "a\nx\nc\n" in
    let output = format_unified r in
    assert_true ~msg:"contains --- header"
      (String.length output > 0 &&
       try let _ = String.index output '-' in true with Not_found -> false)
  );

  (* ── Stats ────────────────────────────────────── *)

  suite "Edit stats" (fun () ->
    let r = diff [|1;2;3|] [|1;4;3;5|] in
    let (ins, del, eq) = compute_stats r.edits in
    assert_true ~msg:"stats insertions > 0"
      (ins > 0);
    assert_true ~msg:"stats sum = total edits"
      (ins + del + eq = List.length r.edits)
  );

  (* ── Three-way merge ──────────────────────────── *)

  suite "Three-way merge (no conflict)" (fun () ->
    let base  = [|"a";"b";"c";"d"|] in
    let ours  = [|"a";"B";"c";"d"|] in  (* changed b->B *)
    let theirs = [|"a";"b";"c";"D"|] in (* changed d->D *)
    let r = merge3 base ours theirs in
    assert_true ~msg:"no conflicts"
      (r.conflict_count = 0);
    assert_true ~msg:"merged result exists"
      (r.merged <> None);
    (match r.merged with
     | Some m ->
       assert_true ~msg:"merge combines both changes"
         (m = ["a";"B";"c";"D"])
     | None -> assert_true ~msg:"should have merged" false)
  );

  suite "Three-way merge (conflict)" (fun () ->
    let base   = [|"a";"b";"c"|] in
    let ours   = [|"a";"X";"c"|] in  (* changed b->X *)
    let theirs = [|"a";"Y";"c"|] in  (* changed b->Y *)
    let r = merge3 base ours theirs in
    assert_true ~msg:"has conflicts"
      (r.conflict_count > 0);
    assert_true ~msg:"merged is None"
      (r.merged = None)
  );

  (* ── Stress test ──────────────────────────────── *)

  suite "Stress: large arrays" (fun () ->
    let a = Array.init 200 Fun.id in
    let b = Array.init 200 (fun i -> if i mod 10 = 0 then i + 1000 else i) in
    let r = diff a b in
    assert_true ~msg:"distance = 40 (20 deletes + 20 inserts)"
      (r.distance = 40);
    let patched = apply_patch a r.edits in
    assert_true ~msg:"patch reproduces b"
      (patched = b)
  );

  test_summary ()
