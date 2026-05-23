(* sunday.ml - Sunday's Quick Search String Matching                        *)
(*                                                                          *)
(* Daniel M. Sunday's "Quick Search" algorithm (CACM, 1990) is a            *)
(* delightful simplification of Boyer-Moore: it keeps only the              *)
(* bad-character heuristic, but consults the character of the text          *)
(* immediately AFTER the current alignment window. On a mismatch (or even   *)
(* after a successful match) we shift by enough to align that "next" byte   *)
(* with its rightmost occurrence in the pattern, or skip past it entirely   *)
(* if it does not occur.                                                    *)
(*                                                                          *)
(* The result is a remarkably short matcher that is competitive with        *)
(* full Boyer-Moore on natural-language text and short patterns, with a     *)
(* tiny 256-entry preprocessing table and no good-suffix bookkeeping.       *)
(*                                                                          *)
(* This file is the "minimalist Boyer-Moore" sibling to:                    *)
(*   - boyer_moore.ml   (full bad-char + good-suffix, sublinear average)    *)
(*   - kmp.ml           (linear worst case via failure function)            *)
(*   - rabin_karp.ml    (rolling hash multi-pattern)                        *)
(*   - aho_corasick.ml  (multi-pattern automaton)                           *)
(*   - z_algorithm.ml   (Z-function based prefix matching)                  *)
(*   - manacher.ml      (linear-time palindrome analysis)                   *)
(*   - bitap.ml         (Shift-Or NFA, k-mismatch variant)                  *)
(*                                                                          *)
(* API mirrors kmp.ml and boyer_moore.ml: compile / iter_matches /          *)
(* find_all / find_first / contains / count + one-shot search / occurs /    *)
(* search_all helpers.                                                      *)
(*                                                                          *)
(* Worst case is O(n * m) (pathological alphabets), average case is         *)
(* sublinear and often beats KMP in practice for short patterns over        *)
(* large alphabets. Pure imperative byte-level preprocessing.               *)

(** Sunday's Quick Search exact string matching.

    Compile a pattern once with {!Sunday.compile} and then match it
    against many texts. Preprocessing is O(m + 256). Matching is
    sublinear on average and O(n * m) in the worst case (no good-suffix
    rule, unlike full Boyer-Moore).

    Sibling to {!module:Kmp}, {!module:BoyerMoore}, {!module:RabinKarp},
    {!module:AhoCorasick}, the Z-algorithm, Manacher, and Bitap modules.

    The key insight is the "next-character" shift table: on each
    alignment attempt the algorithm peeks at [text.\[i + m\]] (the byte
    just past the current window) and shifts the pattern so that byte
    aligns with its rightmost occurrence in the pattern, or jumps the
    pattern fully past it if it does not occur. *)
module Sunday = struct

  (** [build_shift pattern] returns a 256-entry table where entry [b]
      is the shift to apply when the byte just past the current
      alignment window equals [b]. Specifically,
      [shift.(b) = m - rightmost_index_of b in pattern], or [m + 1] if
      [b] does not occur in [pattern]. O(m + 256). *)
  let build_shift pattern =
    let m = String.length pattern in
    let tbl = Array.make 256 (m + 1) in
    for i = 0 to m - 1 do
      tbl.(Char.code pattern.[i]) <- m - i
    done;
    tbl

  (** Compiled-pattern handle. Caches the next-character shift table so
      the same pattern can be matched against many texts without
      redundant preprocessing. *)
  type compiled = {
    pattern : string;
    shift   : int array;
  }

  (** [compile pattern] precomputes the shift table for [pattern] and
      returns a reusable {!compiled} handle. O(m + 256). *)
  let compile pattern = { pattern; shift = build_shift pattern }

  (** [iter_matches compiled text on_match] walks [text], invoking
      [on_match start] for every occurrence of the compiled pattern at
      byte offset [start], in increasing order.

      Streams matches without allocating an intermediate list. Suitable
      for very large texts or for early termination via an exception
      raised from [on_match].

      Empty-pattern convention: the empty pattern matches at every
      position [0..String.length text] inclusive, mirroring KMP /
      Boyer-Moore in this repo. *)
  let iter_matches { pattern; shift } text on_match =
    let m = String.length pattern in
    let n = String.length text in
    if m = 0 then begin
      for i = 0 to n do on_match i done
    end
    else if m <= n then begin
      let i = ref 0 in
      while !i <= n - m do
        (* Try to match pattern against text starting at !i. We scan
           left-to-right; left-to-right is fine because we are not
           using the good-suffix rule. *)
        let j = ref 0 in
        while !j < m && pattern.[!j] = text.[!i + !j] do
          incr j
        done;
        if !j = m then on_match !i;
        (* Whether we matched or not, jump using the byte right after
           the current window. If there is no byte after the window
           (i.e. !i + m = n), we are done. *)
        if !i + m < n then
          i := !i + shift.(Char.code text.[!i + m])
        else
          i := n  (* terminate the outer loop *)
      done
    end

  (** [find_all compiled text] returns all start offsets of the
      compiled pattern in [text], in increasing order. Allocates the
      result list; use {!iter_matches} to stream without allocation. *)
  let find_all compiled text =
    let acc = ref [] in
    iter_matches compiled text (fun start -> acc := start :: !acc);
    List.rev !acc

  (** [find_first compiled text] returns [Some i] where [i] is the
      smallest start offset of the compiled pattern in [text], or
      [None] if the pattern does not occur. Stops scanning at the first
      match. *)
  let find_first compiled text =
    let result = ref None in
    (try
      iter_matches compiled text (fun start ->
        result := Some start;
        raise Exit)
    with Exit -> ());
    !result

  (** [contains compiled text] is [true] iff the compiled pattern
      occurs at least once in [text]. *)
  let contains compiled text =
    match find_first compiled text with
    | Some _ -> true
    | None -> false

  (** [count compiled text] returns the total number of (possibly
      overlapping) occurrences of the compiled pattern in [text]. *)
  let count compiled text =
    let c = ref 0 in
    iter_matches compiled text (fun _ -> incr c);
    !c

  (** [search ~pattern ~text] is a one-shot wrapper that compiles
      [pattern] internally and returns the first occurrence (or
      [None]). Prefer {!compile} + {!find_first} when matching the
      same pattern against multiple texts. *)
  let search ~pattern ~text = find_first (compile pattern) text

  (** [occurs ~pattern ~text] is a one-shot existence check. *)
  let occurs ~pattern ~text = contains (compile pattern) text

  (** [search_all ~pattern ~text] is a one-shot helper returning every
      occurrence of [pattern] in [text]. *)
  let search_all ~pattern ~text = find_all (compile pattern) text

  (** [shift_for compiled b] is the shift Sunday would apply if the
      byte just past the current alignment window equals [b]. Exposed
      for didactic / instrumentation purposes (e.g. printing the table
      while teaching the algorithm). *)
  let shift_for compiled b = compiled.shift.(Char.code b)

end


(* ============================================================== *)
(*                            Demo                                 *)
(* ============================================================== *)

let () =
  let module S = Sunday in

  Printf.printf "Sunday — Quick Search exact string matching\n";
  Printf.printf "===========================================\n\n";

  (* ----------------- 1. Shift-table showcase --------------------- *)
  let show_shifts p =
    let c = S.compile p in
    Printf.printf "  pattern=%S  m=%d\n" p (String.length p);
    Printf.printf "    shift('a')=%d  shift('b')=%d  shift('c')=%d  shift('z')=%d\n"
      (S.shift_for c 'a') (S.shift_for c 'b')
      (S.shift_for c 'c') (S.shift_for c 'z')
  in
  Printf.printf "[1] Next-character shift table\n";
  List.iter show_shifts [ "abc"; "abcabc"; "aaaa"; "z" ];
  print_newline ();

  (* ----------------- 2. find_all / contains / count -------------- *)
  Printf.printf "[2] Multi-occurrence search\n";
  let demo pattern text =
    let c = S.compile pattern in
    let hits = S.find_all c text in
    let first = S.find_first c text in
    Printf.printf "  pattern=%S  text=%S\n" pattern text;
    Printf.printf "    occurrences=%d  first=%s  positions=[%s]\n"
      (S.count c text)
      (match first with Some i -> string_of_int i | None -> "none")
      (String.concat ";" (List.map string_of_int hits))
  in
  demo "abab" "ababcababababcabab";
  demo "aaa"  "aaaaaa";
  demo "xyz"  "abcdefg";
  demo ""     "anything";
  print_newline ();

  (* ----------------- 3. One-shot wrappers ------------------------ *)
  Printf.printf "[3] One-shot helpers\n";
  let text = "the quick brown fox jumps over the lazy dog" in
  Printf.printf "  occurs ~pattern:%S ~text => %b\n"
    "fox" (S.occurs ~pattern:"fox" ~text);
  Printf.printf "  occurs ~pattern:%S ~text => %b\n"
    "cat" (S.occurs ~pattern:"cat" ~text);
  Printf.printf "  search_all ~pattern:%S ~text => [%s]\n"
    "the"
    (String.concat ";"
       (List.map string_of_int (S.search_all ~pattern:"the" ~text)));

  print_newline ();
  Printf.printf "Done.\n"
