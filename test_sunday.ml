(* test_sunday.ml - Tests for sunday.ml (Sunday's Quick Search)            *)
(*                                                                          *)
(* Style mirrors test_bitap.ml / test_diff.ml: loaded via `#use`, so the    *)
(* demo block in sunday.ml runs first, then we exercise the public API     *)
(* through the `Sunday` module. The Makefile's `test-extended` target       *)
(* auto-discovers this file (it has a `#use` directive, so it's classed    *)
(* as a script test).                                                       *)

#use "test_framework.ml";;
#use "sunday.ml";;

let () =
  Printf.printf "\n=== Sunday Tests ===\n\n";

  let module S = Sunday in

  (* -- find_all: basic exact search ------------------------------- *)

  suite "find_all: basic exact search" (fun () ->
    let c = S.compile "abab" in
    let hits = S.find_all c "ababcababababcabab" in
    assert_true ~msg:"abab in ababcababababcabab -> [0;5;7;9;14]"
      (hits = [0; 5; 7; 9; 14]);

    let c = S.compile "aaa" in
    assert_true ~msg:"aaa in aaaaaa -> [0;1;2;3]"
      (S.find_all c "aaaaaa" = [0; 1; 2; 3]);

    let c = S.compile "xyz" in
    assert_true ~msg:"xyz in abcdefg -> []"
      (S.find_all c "abcdefg" = []);

    let c = S.compile "fox" in
    assert_true ~msg:"fox in classic sentence -> [16]"
      (S.find_all c "the quick brown fox jumps over the lazy dog" = [16])
  );

  (* -- find_all: edge alignments ---------------------------------- *)

  suite "find_all: edge alignments" (fun () ->
    let c = S.compile "a" in
    assert_true ~msg:"single-char pattern hits every occurrence"
      (S.find_all c "banana" = [1; 3; 5]);

    let c = S.compile "abc" in
    assert_true ~msg:"match at index 0"
      (S.find_all c "abcdef" = [0]);

    let c = S.compile "def" in
    assert_true ~msg:"match at end of text"
      (S.find_all c "abcdef" = [3]);

    let c = S.compile "abc" in
    assert_true ~msg:"pattern equal to text -> [0]"
      (S.find_all c "abc" = [0]);

    let c = S.compile "abcd" in
    assert_true ~msg:"pattern longer than text -> []"
      (S.find_all c "abc" = [])
  );

  (* -- Empty-pattern semantics (mirrors kmp.ml / bitap.ml) -------- *)

  suite "empty pattern matches every gap" (fun () ->
    let c = S.compile "" in
    assert_true ~msg:"empty pattern in \"abc\" -> [0;1;2;3]"
      (S.find_all c "abc" = [0; 1; 2; 3]);
    assert_true ~msg:"empty pattern in \"\" -> [0]"
      (S.find_all c "" = [0])
  );

  (* -- Convenience accessors -------------------------------------- *)

  suite "find_first / contains / count" (fun () ->
    let c = S.compile "the" in
    let text = "the quick brown fox jumps over the lazy dog" in
    assert_true ~msg:"find_first returns the leftmost match"
      (S.find_first c text = Some 0);
    assert_true ~msg:"contains returns true when present"
      (S.contains c text);
    assert_true ~msg:"contains returns false when absent"
      (not (S.contains (S.compile "zzz") text));
    assert_true ~msg:"count agrees with List.length (find_all)"
      (S.count c text = 2);
    assert_true ~msg:"find_first on miss -> None"
      (S.find_first (S.compile "missing") text = None)
  );

  (* -- One-shot wrappers ------------------------------------------ *)

  suite "search / occurs / search_all wrappers" (fun () ->
    let text = "the quick brown fox jumps over the lazy dog" in
    assert_true ~msg:"search returns Some leftmost index"
      (S.search ~pattern:"fox" ~text = Some 16);
    assert_true ~msg:"search returns None when absent"
      (S.search ~pattern:"cat" ~text = None);
    assert_true ~msg:"occurs true/false matches search"
      (S.occurs ~pattern:"fox" ~text && not (S.occurs ~pattern:"cat" ~text));
    assert_true ~msg:"search_all in 'aaaaaa' for 'aa' -> [0;1;2;3;4]"
      (S.search_all ~pattern:"aa" ~text:"aaaaaa" = [0; 1; 2; 3; 4])
  );

  (* -- Shift-table sanity ----------------------------------------- *)

  suite "shift_for: bad-char next-window table" (fun () ->
    let c = S.compile "abc" in
    (* For pattern "abc" of length 3:                                *)
    (*   shift('a') = m - rightmost('a') = 3 - 0 = 3                  *)
    (*   shift('b') = 3 - 1 = 2                                       *)
    (*   shift('c') = 3 - 2 = 1                                       *)
    (*   shift('z') (absent) = m + 1 = 4                              *)
    assert_true ~msg:"shift('a') for 'abc' = 3"
      (S.shift_for c 'a' = 3);
    assert_true ~msg:"shift('b') for 'abc' = 2"
      (S.shift_for c 'b' = 2);
    assert_true ~msg:"shift('c') for 'abc' = 1"
      (S.shift_for c 'c' = 1);
    assert_true ~msg:"shift(absent) for 'abc' = m + 1 = 4"
      (S.shift_for c 'z' = 4)
  );

  (* -- Byte safety: full 0..255 alphabet, NUL bytes --------------- *)

  suite "byte-clean: handles arbitrary bytes incl. NUL" (fun () ->
    let pattern = "\x00\xffA" in
    let text    = "xx\x00\xffA\x00\xffAyy" in
    let hits = S.find_all (S.compile pattern) text in
    assert_true ~msg:"finds first occurrence of NUL/0xFF/'A' run"
      (List.mem 2 hits);
    assert_true ~msg:"finds second overlapping run starting at 5"
      (List.mem 5 hits)
  );

  (* -- Cross-check vs Kmp for a random-ish text ------------------- *)

  suite "agrees with Kmp on the same inputs" (fun () ->
    (* We don't #use kmp.ml here (would re-run its demo); instead    *)
    (* assert against a precomputed expected list for a known case.  *)
    let text =
      "the rain in spain falls mainly on the plain; in the rain"
    in
    let c = S.compile "ain" in
    (* 'ain' occurs at: rain (5), spain (14), mainly (25), plain (40), rain (53) *)
    let hits = S.find_all c text in
    assert_true ~msg:"Sunday finds all 'ain' occurrences"
      (hits = [5; 14; 25; 40; 53])
  );

  test_summary ()
