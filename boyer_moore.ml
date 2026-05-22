(* boyer_moore.ml — Boyer–Moore String Search                              *)
(*                                                                          *)
(* The classic Boyer–Moore exact-match algorithm scans the pattern          *)
(* right-to-left over each alignment of the text and uses two heuristics    *)
(* to skip ahead on mismatch:                                               *)
(*                                                                          *)
(*   1. Bad-character rule   — align the mismatching text character with    *)
(*                              its rightmost occurrence in the pattern     *)
(*                              (or shift past it entirely if absent).      *)
(*   2. Good-suffix rule     — having matched a suffix t of the pattern,    *)
(*                              shift so the next occurrence of t (or a     *)
(*                              prefix matching a suffix of t) lines up.    *)
(*                                                                          *)
(* The implementation precomputes both tables in O(n+|sigma|) time          *)
(* and then runs in sublinear average time (and O(n+m) worst case).         *)
(*                                                                          *)
(* Sibling to aho_corasick.ml (multi-pattern), z_algorithm.ml (Z-function), *)
(* and manacher.ml (palindromes).                                           *)
(*                                                                          *)
(* Demonstrates: imperative arrays, two-table preprocessing (suffixes +     *)
(* prefix-match), per-byte alphabet table over the full 0..255 range, and   *)
(* "build once, query many" automaton-style design.                          *)

(** Boyer-Moore exact string search.

    Builds the bad-character and good-suffix tables once via
    {!BoyerMoore.compile}, then matches against any number of texts in
    sublinear average time (O(n + m) worst case).

    Sibling to {!module:Kmp} (linear worst case via failure function),
    {!module:AhoCorasick} (multi-pattern), and the Z-algorithm /
    Manacher modules. *)
module BoyerMoore = struct

  (** [build_bad_char_table pattern] returns a 256-entry array where
      entry [b] is the rightmost index in [pattern] at which byte [b]
      occurs, or [-1] if [b] does not occur in [pattern]. O(m + 256). *)
  let build_bad_char_table pattern =
    let m = String.length pattern in
    let tbl = Array.make 256 (-1) in
    for i = 0 to m - 1 do
      tbl.(Char.code pattern.[i]) <- i
    done;
    tbl

  (** [build_good_suffix_table pattern] returns the good-suffix shift
      table (length [m + 1]) used by Boyer-Moore. Encodes both the
      "strong" rule (Case 1: shift to next occurrence of the matched
      suffix in the pattern) and the "weak" rule (Case 2: align the
      longest prefix of the pattern that matches a suffix of the
      matched run). Computed in O(m). *)
  let build_good_suffix_table pattern =
    let m = String.length pattern in
    let border = Array.make (m + 1) 0 in
    let shift  = Array.make (m + 1) 0 in
    (* --- Pass 1: borders / Case 1 ("strong" good-suffix shifts). --- *)
    let i = ref m and j = ref (m + 1) in
    border.(!i) <- !j;
    while !i > 0 do
      while !j <= m
            && (let ii = !i - 1 and jj = !j - 1 in
                ii >= 0 && jj >= 0 && jj < m
                && pattern.[ii] <> pattern.[jj]) do
        if shift.(!j) = 0 then shift.(!j) <- !j - !i;
        j := border.(!j)
      done;
      decr i;
      decr j;
      border.(!i) <- !j
    done;
    (* --- Pass 2: Case 2 ("weak" good-suffix shifts, prefix==suffix). - *)
    let j = ref border.(0) in
    for k = 0 to m do
      if shift.(k) = 0 then shift.(k) <- !j;
      if k = !j then j := border.(!j)
    done;
    shift

  (** Precomputed Boyer-Moore automaton bundling the pattern, its
      length, and both heuristic tables. Reuse across many texts to
      amortise preprocessing cost. *)
  type automaton = {
    pattern    : string;
    m          : int;
    bad_char   : int array;     (* length 256                        *)
    good_suff  : int array;     (* length m+1                        *)
  }

  (** [compile pattern] precomputes the bad-character and good-suffix
      tables. O(m + 256) time and space. *)
  let compile pattern =
    let m = String.length pattern in
    {
      pattern;
      m;
      bad_char  = build_bad_char_table pattern;
      good_suff = build_good_suffix_table pattern;
    }

  (** [scan auto text on_match] streams matches of the compiled
      [auto] over [text] in left-to-right order. The callback receives
      each match start offset and returns [true] to continue scanning
      or [false] to stop early.

      Empty-pattern convention: a single match is reported at offset 0
      and the scan halts. *)
  let scan auto text on_match =
    let m = auto.m and n = String.length text in
    if m = 0 then begin
      (* Empty pattern matches at every position; report once at 0. *)
      ignore (on_match 0)
    end else begin
      let s = ref 0 and stop = ref false in
      while not !stop && !s <= n - m do
        let j = ref (m - 1) in
        while !j >= 0 && auto.pattern.[!j] = text.[!s + !j] do
          decr j
        done;
        if !j < 0 then begin
          if not (on_match !s) then stop := true
          else s := !s + auto.good_suff.(0)
        end else begin
          let bc_shift =
            !j - auto.bad_char.(Char.code text.[!s + !j])
          in
          let gs_shift = auto.good_suff.(!j + 1) in
          s := !s + max 1 (max bc_shift gs_shift)
        end
      done
    end

  (** [find_all auto text] returns the list of every start offset of
      the compiled pattern in [text], in increasing order. *)
  let find_all auto text =
    let acc = ref [] in
    scan auto text (fun i -> acc := i :: !acc; true);
    List.rev !acc

  (** [find_first auto text] returns [Some i] for the first occurrence
      or [None] if the pattern is absent. *)
  let find_first auto text =
    let result = ref None in
    scan auto text (fun i -> result := Some i; false);
    !result

  (** [contains auto text] is an O(n) existence check using
      short-circuit scanning. *)
  let contains auto text =
    find_first auto text <> None

  (** [count auto text] returns the number of (non-overlapping in the
      Boyer-Moore sense after each match shift) occurrences. *)
  let count auto text =
    let n = ref 0 in
    scan auto text (fun _ -> incr n; true);
    !n

  (** [search ~pattern ~text] compiles internally and returns every
      occurrence. Prefer {!compile} + {!find_all} when the pattern is
      reused. *)
  let search ~pattern ~text = find_all (compile pattern) text

  (** [occurs ~pattern ~text] is the one-shot existence check. *)
  let occurs ~pattern ~text = contains (compile pattern) text

end


(* ====================================================================== *)
(* Demo                                                                   *)
(* ====================================================================== *)

let print_matches label pattern text occs =
  Printf.printf "  %s\n" label;
  Printf.printf "    pattern = %S\n" pattern;
  Printf.printf "    text    = %S\n" text;
  if occs = [] then
    print_endline "    (no matches)"
  else begin
    Printf.printf "    matches at: [%s]\n"
      (String.concat "; " (List.map string_of_int occs));
    List.iter (fun i ->
      let prefix = String.sub text 0 i in
      let m      = String.length pattern in
      let suffix =
        String.sub text (i + m) (String.length text - i - m)
      in
      Printf.printf "      %s[%s]%s\n" prefix pattern suffix
    ) occs
  end

let () =
  print_endline "=== Boyer-Moore String Search ===";

  (* Classic textbook examples. *)
  let examples = [
    "abc",          "abcabcabc";
    "GCAGAGAG",     "GCATCGCAGAGAGTATACAGTACG";
    "aaab",         "aaaabaaaab";
    "TTAT",         "GTTATAGCTGATCGCGGCGTAGCGGCGAA";
    "needle",       "find a needle in this haystack of needles";
    "x",            "xxxxx";
    "",             "anything";
    "missing",      "this string has no match";
  ] in
  List.iter (fun (p, t) ->
    let occs = BoyerMoore.search ~pattern:p ~text:t in
    print_matches "case:" p t occs
  ) examples;

  (* Pathological pattern: mismatch-rich periodic strings exercise both
     the bad-character and good-suffix shifts. *)
  print_endline "  periodic stress:";
  let text    = String.make 64 'a' ^ "b" ^ String.make 64 'a' in
  let pattern = String.make 8 'a' ^ "b" ^ String.make 8 'a' in
  let auto = BoyerMoore.compile pattern in
  let n_occ = BoyerMoore.count auto text in
  Printf.printf "    text length=%d, pattern length=%d, matches=%d\n"
    (String.length text) (String.length pattern) n_occ;

  (* contains / find_first short-circuit demonstration. *)
  print_endline "  contains / find_first:";
  let auto = BoyerMoore.compile "lorem" in
  let big  = "the quick brown fox jumps over lorem ipsum dolor sit amet, \
              consectetur lorem adipiscing elit" in
  Printf.printf "    contains? %b\n" (BoyerMoore.contains auto big);
  (match BoyerMoore.find_first auto big with
   | Some i -> Printf.printf "    first match at %d\n" i
   | None   -> print_endline "    no first match");
  Printf.printf "    total matches: %d\n" (BoyerMoore.count auto big);

  print_endline "=== Done ==="
