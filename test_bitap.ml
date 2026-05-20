(* test_bitap.ml — Tests for bitap.ml (Shift-Or / Wu–Manber bitap)         *)
(*                                                                          *)
(* Style mirrors test_diff.ml: loaded via `#use`, so the demo block in      *)
(* bitap.ml runs first, then we exercise the public API through the         *)
(* `Bitap` module. The Makefile's `test-extended` target auto-discovers     *)
(* this file (it has a `#use` directive, so it's classed as a script test). *)

#use "test_framework.ml";;
#use "bitap.ml";;

let () =
  Printf.printf "\n=== Bitap Tests ===\n\n";

  let module B = Bitap in

  (* ── Exact: find_all leftmost-ascending positions ─────────────── *)

  suite "find_all: basic exact search" (fun () ->
    let c = B.compile "abab" in
    let hits = B.find_all c "ababcababababcabab" in
    (* Text positions:                                                *)
    (*   a b a b c a b a b a b a b c a b a b                          *)
    (*   0 1 2 3 4 5 6 7 8 9 ...                                      *)
    (* Exact "abab" alignments: 0, 5, 7, 9, 14                        *)
    assert_true ~msg:"abab in ababcababababcabab → [0;5;7;9;14]"
      (hits = [0; 5; 7; 9; 14]);

    let c = B.compile "aaa" in
    assert_true ~msg:"aaa in aaaaaa → [0;1;2;3]"
      (B.find_all c "aaaaaa" = [0; 1; 2; 3]);

    let c = B.compile "xyz" in
    assert_true ~msg:"xyz in abcdefg → []"
      (B.find_all c "abcdefg" = []);

    let c = B.compile "fox" in
    assert_true ~msg:"fox in classic sentence → [16]"
      (B.find_all c "the quick brown fox jumps over the lazy dog" = [16])
  );

  (* ── Exact: single-char and edge-of-text matches ──────────────── *)

  suite "find_all: edge alignments" (fun () ->
    let c = B.compile "a" in
    assert_true ~msg:"single-char pattern hits every occurrence"
      (B.find_all c "banana" = [1; 3; 5]);

    let c = B.compile "abc" in
    assert_true ~msg:"match at index 0"
      (B.find_all c "abcdef" = [0]);

    let c = B.compile "def" in
    assert_true ~msg:"match at end of text"
      (B.find_all c "abcdef" = [3]);

    let c = B.compile "abc" in
    assert_true ~msg:"pattern equal to text → [0]"
      (B.find_all c "abc" = [0]);

    let c = B.compile "abcd" in
    assert_true ~msg:"pattern longer than text → []"
      (B.find_all c "abc" = [])
  );

  (* ── Empty-pattern semantics (mirrors kmp.ml) ─────────────────── *)

  suite "empty pattern matches every gap" (fun () ->
    let c = B.compile "" in
    (* find_all returns 0..n inclusive for empty pattern *)
    assert_true ~msg:"empty pattern in \"abc\" → [0;1;2;3]"
      (B.find_all c "abc" = [0; 1; 2; 3]);
    assert_true ~msg:"empty pattern in \"\" → [0]"
      (B.find_all c "" = [0])
  );

  (* ── Convenience accessors ────────────────────────────────────── *)

  suite "find_first / contains / count" (fun () ->
    let c = B.compile "the" in
    let text = "the quick brown fox jumps over the lazy dog" in
    assert_true ~msg:"find_first returns the leftmost match"
      (B.find_first c text = Some 0);
    assert_true ~msg:"contains returns true when present"
      (B.contains c text);
    assert_true ~msg:"contains returns false when absent"
      (not (B.contains (B.compile "zzz") text));
    assert_true ~msg:"count agrees with List.length (find_all …)"
      (B.count c text = 2);
    assert_true ~msg:"find_first on miss → None"
      (B.find_first (B.compile "missing") text = None)
  );

  (* ── One-shot wrappers ────────────────────────────────────────── *)

  suite "search / occurs / search_all wrappers" (fun () ->
    let text = "the quick brown fox jumps over the lazy dog" in
    assert_true ~msg:"search returns Some leftmost index"
      (B.search ~pattern:"fox" ~text = Some 16);
    assert_true ~msg:"search returns None when absent"
      (B.search ~pattern:"cat" ~text = None);
    assert_true ~msg:"occurs true / false matches search"
      (B.occurs ~pattern:"fox" ~text && not (B.occurs ~pattern:"cat" ~text));
    assert_true ~msg:"search_all in 'aaaaaa' for 'aa' → [0;1;2;3;4]"
      (B.search_all ~pattern:"aa" ~text:"aaaaaa" = [0; 1; 2; 3; 4])
  );

  (* ── Approximate matching (Wu–Manber Hamming distance) ────────── *)

  suite "find_all_approx: k = 0 matches exact" (fun () ->
    let pattern = "GATTACA" in
    let text    = "AGATTACACGATTACAGATTAGAGATTACA" in
    (* Exact starts at 1, 9, 23 → end positions = start + 7 - 1.    *)
    let exact = B.find_all_approx ~pattern ~text ~k:0 in
    let starts_from_exact = List.map (fun (e, d) -> assert (d = 0); e - 6) exact in
    assert_true ~msg:"k=0 reproduces exact-search starts"
      (starts_from_exact = B.search_all ~pattern ~text)
  );

  suite "find_all_approx: k > 0 widens the result set" (fun () ->
    let pattern = "fortune" in
    let text    = "the unfortunate fortuneteller had foreknowledge" in
    let n0 = List.length (B.find_all_approx ~pattern ~text ~k:0) in
    let n1 = List.length (B.find_all_approx ~pattern ~text ~k:1) in
    let n2 = List.length (B.find_all_approx ~pattern ~text ~k:2) in
    assert_true ~msg:"k:0 ≤ k:1 ≤ k:2 (monotone in k)"
      (n0 <= n1 && n1 <= n2);
    assert_true ~msg:"k:0 finds at least one exact 'fortune' alignment"
      (n0 >= 1);
    assert_true ~msg:"all reported errors are ≤ k"
      (List.for_all (fun (_, d) -> d <= 2)
         (B.find_all_approx ~pattern ~text ~k:2));
    assert_true ~msg:"end positions are within text bounds"
      (List.for_all
         (fun (e, _) -> e >= 0 && e < String.length text)
         (B.find_all_approx ~pattern ~text ~k:2))
  );

  suite "find_all_approx: single-substitution case" (fun () ->
    (* Pattern "abcd" against "abXd" should match with 1 error at end=3. *)
    let hits = B.find_all_approx ~pattern:"abcd" ~text:"abXd" ~k:1 in
    assert_true ~msg:"finds the 1-sub alignment"
      (List.exists (fun (e, d) -> e = 3 && d = 1) hits)
  );

  suite "find_all_approx: rejects negative k" (fun () ->
    assert_raises ~msg:"k < 0 raises Invalid_argument" (fun () ->
      B.find_all_approx ~pattern:"abc" ~text:"abc" ~k:(-1))
  );

  (* ── Length limit (bitap_max enforcement) ─────────────────────── *)

  suite "compile: pattern length limit" (fun () ->
    assert_true ~msg:"bitap_max is 62 (one bit reserved for accept flag)"
      (B.bitap_max = 62);

    (* At-the-limit pattern compiles and finds itself. *)
    let limit_pat = String.make B.bitap_max 'x' in
    let c = B.compile limit_pat in
    assert_true ~msg:"max-length pattern compiles and self-matches"
      (B.find_all c limit_pat = [0]);

    (* One byte over the limit must raise. *)
    let long_pat = String.make (B.bitap_max + 1) 'x' in
    assert_raises ~msg:"compile rejects over-limit pattern" (fun () ->
      B.compile long_pat)
  );

  (* ── Byte safety: full 0..255 alphabet, NUL bytes ─────────────── *)

  suite "byte-clean: handles arbitrary bytes incl. NUL" (fun () ->
    let pattern = "\x00\xffA" in
    let text    = "xx\x00\xffA\x00\xffAyy" in
    let hits = B.find_all (B.compile pattern) text in
    assert_true ~msg:"finds first occurrence of NUL/0xFF/'A' run"
      (List.mem 2 hits);
    assert_true ~msg:"finds second overlapping run starting at 5"
      (List.mem 5 hits)
  );

  test_summary ()
