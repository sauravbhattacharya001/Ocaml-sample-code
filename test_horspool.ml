(* test_horspool.ml - Tests for horspool.ml (Boyer-Moore-Horspool)         *)
(*                                                                          *)
(* Style mirrors test_sunday.ml / test_bitap.ml / test_diff.ml: loaded via  *)
(* `#use`, so the demo block in horspool.ml runs first, then we exercise   *)
(* the public API through the `Horspool` module. The Makefile's            *)
(* `test-extended` target auto-discovers this file (it has a `#use`        *)
(* directive, so it's classed as a script test). *)

#use "test_framework.ml";;
#use "horspool.ml";;

let () =
  Printf.printf "\n=== Horspool Tests ===\n\n";

  let module H = Horspool in

  (* -- find_all: basic exact search ------------------------------- *)

  suite "find_all: basic exact search" (fun () ->
    let c = H.compile "abab" in
    let hits = H.find_all c "ababcababababcabab" in
    assert_true ~msg:"abab in ababcababababcabab -> [0;5;7;9;14]"
      (hits = [0; 5; 7; 9; 14]);

    let c = H.compile "aaa" in
    assert_true ~msg:"aaa in aaaaaa -> [0;1;2;3]"
      (H.find_all c "aaaaaa" = [0; 1; 2; 3]);

    let c = H.compile "xyz" in
    assert_true ~msg:"xyz in abcdefg -> []"
      (H.find_all c "abcdefg" = []);

    let c = H.compile "fox" in
    assert_true ~msg:"fox in classic sentence -> [16]"
      (H.find_all c "the quick brown fox jumps over the lazy dog" = [16])
  );

  (* -- find_all: edge alignments ---------------------------------- *)

  suite "find_all: edge alignments" (fun () ->
    let c = H.compile "a" in
    assert_true ~msg:"single-char pattern hits every occurrence"
      (H.find_all c "banana" = [1; 3; 5]);

    let c = H.compile "abc" in
    assert_true ~msg:"match at index 0"
      (H.find_all c "abcdef" = [0]);

    let c = H.compile "def" in
    assert_true ~msg:"match at end of text"
      (H.find_all c "abcdef" = [3]);

    let c = H.compile "abc" in
    assert_true ~msg:"pattern equal to text -> [0]"
      (H.find_all c "abc" = [0]);

    let c = H.compile "abcd" in
    assert_true ~msg:"pattern longer than text -> []"
      (H.find_all c "abc" = [])
  );

  (* -- Empty-pattern semantics (mirrors kmp.ml / bitap.ml / sunday.ml) *)

  suite "empty pattern matches every gap" (fun () ->
    let c = H.compile "" in
    assert_true ~msg:"empty pattern in \"abc\" -> [0;1;2;3]"
      (H.find_all c "abc" = [0; 1; 2; 3]);
    assert_true ~msg:"empty pattern in \"\" -> [0]"
      (H.find_all c "" = [0])
  );

  (* -- Convenience accessors -------------------------------------- *)

  suite "find_first / contains / count" (fun () ->
    let c = H.compile "the" in
    let text = "the quick brown fox jumps over the lazy dog" in
    assert_true ~msg:"find_first returns the leftmost match"
      (H.find_first c text = Some 0);
    assert_true ~msg:"contains returns true when present"
      (H.contains c text);
    assert_true ~msg:"contains returns false when absent"
      (not (H.contains (H.compile "zzz") text));
    assert_true ~msg:"count agrees with List.length (find_all)"
      (H.count c text = 2);
    assert_true ~msg:"find_first on miss -> None"
      (H.find_first (H.compile "missing") text = None)
  );

  (* -- One-shot wrappers ------------------------------------------ *)

  suite "search / occurs / search_all wrappers" (fun () ->
    let text = "the quick brown fox jumps over the lazy dog" in
    assert_true ~msg:"search returns Some leftmost index"
      (H.search ~pattern:"fox" ~text = Some 16);
    assert_true ~msg:"search returns None when absent"
      (H.search ~pattern:"cat" ~text = None);
    assert_true ~msg:"occurs true/false matches search"
      (H.occurs ~pattern:"fox" ~text && not (H.occurs ~pattern:"cat" ~text));
    assert_true ~msg:"search_all in 'aaaaaa' for 'aa' -> [0;1;2;3;4]"
      (H.search_all ~pattern:"aa" ~text:"aaaaaa" = [0; 1; 2; 3; 4])
  );

  (* -- Shift-table sanity ----------------------------------------- *)

  suite "shift_for: bad-char trailing-window table" (fun () ->
    let c = H.compile "abc" in
    (* For pattern "abc" of length m=3, Horspool excludes the last   *)
    (* byte (index m-1) when building the shift table, so:           *)
    (*   shift('a') = m - 1 - rightmost('a' in "ab") = 2 - 0 = 2     *)
    (*   shift('b') = m - 1 - rightmost('b' in "ab") = 2 - 1 = 1     *)
    (*   shift('c') (absent from prefix) = m = 3                     *)
    (*   shift('z') (absent)             = m = 3                     *)
    assert_true ~msg:"shift('a') for 'abc' = 2"
      (H.shift_for c 'a' = 2);
    assert_true ~msg:"shift('b') for 'abc' = 1"
      (H.shift_for c 'b' = 1);
    assert_true ~msg:"shift('c') for 'abc' = m = 3 (last byte excluded)"
      (H.shift_for c 'c' = 3);
    assert_true ~msg:"shift(absent) for 'abc' = m = 3"
      (H.shift_for c 'z' = 3)
  );

  (* -- Shift-table sanity: repeated bytes use rightmost prefix occ - *)

  suite "shift_for: rightmost-in-prefix wins for repeats" (fun () ->
    let c = H.compile "abcabd" in
    (* m = 6, prefix = "abcab", so rightmost 'a' = index 3,          *)
    (* rightmost 'b' = index 4, rightmost 'c' = index 2.              *)
    (*   shift('a') = 5 - 3 = 2                                       *)
    (*   shift('b') = 5 - 4 = 1                                       *)
    (*   shift('c') = 5 - 2 = 3                                       *)
    (*   shift('d') = m = 6 (excluded last byte; appears nowhere      *)
    (*                       else in the prefix)                      *)
    assert_true ~msg:"shift('a') for 'abcabd' = 2"
      (H.shift_for c 'a' = 2);
    assert_true ~msg:"shift('b') for 'abcabd' = 1"
      (H.shift_for c 'b' = 1);
    assert_true ~msg:"shift('c') for 'abcabd' = 3"
      (H.shift_for c 'c' = 3);
    assert_true ~msg:"shift('d') for 'abcabd' = m = 6 (last-byte exclusion)"
      (H.shift_for c 'd' = 6)
  );

  (* -- Positive-shift invariant (no infinite loops) --------------- *)

  suite "shift table is always >= 1 (no zero shifts)" (fun () ->
    let check pattern =
      let c = H.compile pattern in
      let ok = ref true in
      for b = 0 to 255 do
        if H.shift_for c (Char.chr b) < 1 then ok := false
      done;
      assert_true
        ~msg:(Printf.sprintf "all 256 shifts >= 1 for pattern %S" pattern)
        !ok
    in
    List.iter check [ "a"; "ab"; "aaa"; "abc"; "abcabd"; "the quick fox" ]
  );

  (* -- Byte safety: full 0..255 alphabet, NUL bytes --------------- *)

  suite "byte-clean: handles arbitrary bytes incl. NUL" (fun () ->
    let pattern = "\x00\xffA" in
    let text    = "xx\x00\xffA\x00\xffAyy" in
    let hits = H.find_all (H.compile pattern) text in
    assert_true ~msg:"finds first occurrence of NUL/0xFF/'A' run"
      (List.mem 2 hits);
    assert_true ~msg:"finds second occurrence of NUL/0xFF/'A' run at 5"
      (List.mem 5 hits)
  );

  (* -- Cross-check vs a known expected list (same as test_sunday) - *)

  suite "agrees with Kmp/Sunday on the same inputs" (fun () ->
    (* We don't #use kmp.ml / sunday.ml here (would re-run their     *)
    (* demos); instead assert against the same precomputed list as   *)
    (* the Sunday test suite to confirm BMH agreement.               *)
    let text =
      "the rain in spain falls mainly on the plain; in the rain"
    in
    let c = H.compile "ain" in
    (* 'ain' occurs at: rain (5), spain (14), mainly (25), plain (40), rain (53) *)
    let hits = H.find_all c text in
    assert_true ~msg:"Horspool finds all 'ain' occurrences"
      (hits = [5; 14; 25; 40; 53])
  );

  (* -- Iter_matches: early termination via exception --------------- *)

  suite "iter_matches: early termination via raised exception" (fun () ->
    let c = H.compile "ab" in
    let seen = ref [] in
    (try
      H.iter_matches c "ababab" (fun start ->
        seen := start :: !seen;
        if List.length !seen >= 2 then raise Exit)
    with Exit -> ());
    assert_true ~msg:"stopped after exactly 2 matches"
      (List.rev !seen = [0; 2])
  );

  test_summary ()
