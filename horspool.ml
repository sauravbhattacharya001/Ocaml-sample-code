(* horspool.ml - Boyer-Moore-Horspool exact string matching                *)
(*                                                                          *)
(* Nigel Horspool's 1980 simplification of Boyer-Moore (Software:           *)
(* Practice & Experience, 10(6)): keep only the bad-character heuristic,    *)
(* and key the shift on the LAST character of the current alignment        *)
(* window (text.[i + m - 1]) rather than on the mismatching character.      *)
(*                                                                          *)
(* The result is a tiny, fast matcher that in practice is competitive       *)
(* with full Boyer-Moore on natural-language text, with the same 256-entry  *)
(* preprocessing table as Sunday's Quick Search but using the trailing     *)
(* window byte instead of the post-window byte.                             *)
(*                                                                          *)
(* This file is the "BMH" sibling to:                                       *)
(*   - boyer_moore.ml  (full bad-char + good-suffix, sublinear average)     *)
(*   - sunday.ml       (Quick Search, shifts on post-window byte)           *)
(*   - kmp.ml          (linear worst case via failure function)             *)
(*   - rabin_karp.ml   (rolling-hash multi-pattern)                         *)
(*   - aho_corasick.ml (multi-pattern automaton)                            *)
(*   - z_algorithm.ml  (Z-function based prefix matching)                   *)
(*   - manacher.ml     (linear-time palindrome analysis)                    *)
(*   - bitap.ml        (Shift-Or NFA, k-mismatch variant)                   *)
(*                                                                          *)
(* The chief difference from Sunday: the Horspool shift table is built so   *)
(* that the LAST byte of the pattern always maps to [m] (i.e. shift fully   *)
(* past), and earlier byte occurrences map to [m - 1 - i]. On each step     *)
(* we look at text.[i + m - 1] to decide how far to advance.                *)
(*                                                                          *)
(* API mirrors sunday.ml / kmp.ml / boyer_moore.ml: compile / iter_matches  *)
(* / find_all / find_first / contains / count + one-shot search / occurs / *)
(* search_all helpers + shift_for for introspection.                        *)
(*                                                                          *)
(* Worst case is O(n * m) (pathological alphabets); average case is         *)
(* sublinear and famously fast on English text. Pure imperative byte-level  *)
(* preprocessing, no allocations during matching. *)

(** Boyer-Moore-Horspool exact string matching.

    Compile a pattern once with {!Horspool.compile} and then match it
    against many texts. Preprocessing is O(m + 256). Matching is
    sublinear on average and O(n * m) in the worst case (no
    good-suffix rule, unlike full Boyer-Moore).

    Sibling to {!module:Sunday}, {!module:Kmp}, {!module:BoyerMoore},
    {!module:RabinKarp}, {!module:AhoCorasick}, the Z-algorithm,
    Manacher, and Bitap modules.

    The key insight is the "last-character" shift table: on each
    alignment attempt the algorithm peeks at [text.\[i + m - 1\]] (the
    trailing byte of the current window) and shifts the pattern so
    that byte aligns with its rightmost occurrence in
    [pattern.\[0..m-2\]], or jumps the pattern fully past it if it
    does not occur in that prefix. *)
module Horspool = struct

  (** [build_shift pattern] returns a 256-entry table where entry [b]
      is the shift to apply when the trailing byte of the current
      alignment window equals [b]. Specifically,
      [shift.(b) = m - 1 - rightmost_index_of b in pattern.[0..m-2]],
      or [m] if [b] does not occur in that prefix. The last byte of
      the pattern is intentionally excluded so that a successful match
      still advances by a positive amount. O(m + 256). *)
  let build_shift pattern =
    let m = String.length pattern in
    let tbl = Array.make 256 m in
    (* Exclude the last byte (index m-1): the trailing-window byte by
       definition equals pattern.[m-1] on a match, and we still want a
       positive shift. *)
    for i = 0 to m - 2 do
      tbl.(Char.code pattern.[i]) <- m - 1 - i
    done;
    tbl

  (** Compiled-pattern handle. Caches the trailing-character shift
      table so the same pattern can be matched against many texts
      without redundant preprocessing. *)
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
      position [0..String.length text] inclusive, mirroring KMP,
      Boyer-Moore and Sunday in this repo. *)
  let iter_matches { pattern; shift } text on_match =
    let m = String.length pattern in
    let n = String.length text in
    if m = 0 then begin
      for i = 0 to n do on_match i done
    end
    else if m <= n then begin
      let i = ref 0 in
      let last = m - 1 in
      while !i <= n - m do
        (* Compare the trailing pattern byte first, then walk the
           remainder left-to-right. The trailing-byte check is the
           hottest branch in practice. *)
        if pattern.[last] = text.[!i + last] then begin
          let j = ref 0 in
          while !j < last && pattern.[!j] = text.[!i + !j] do
            incr j
          done;
          if !j = last then on_match !i
        end;
        (* Whether we matched or not, shift using the trailing window
           byte. The shift is always >= 1 because the last byte of the
           pattern was excluded from the table. *)
        i := !i + shift.(Char.code text.[!i + last])
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
      [None] if the pattern does not occur. Stops scanning at the
      first match. *)
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

  (** [shift_for compiled b] is the shift Horspool would apply if the
      trailing byte of the current alignment window equals [b]. Exposed
      for didactic / instrumentation purposes (e.g. printing the table
      while teaching the algorithm). *)
  let shift_for compiled b = compiled.shift.(Char.code b)

end


(* ============================================================== *)
(*                            Demo                                 *)
(* ============================================================== *)

let () =
  let module H = Horspool in

  Printf.printf "Horspool - Boyer-Moore-Horspool exact string matching\n";
  Printf.printf "=====================================================\n\n";

  (* ----------------- 1. Shift-table showcase --------------------- *)
  let show_shifts p =
    let c = H.compile p in
    Printf.printf "  pattern=%S  m=%d\n" p (String.length p);
    Printf.printf "    shift('a')=%d  shift('b')=%d  shift('c')=%d  shift('z')=%d\n"
      (H.shift_for c 'a') (H.shift_for c 'b')
      (H.shift_for c 'c') (H.shift_for c 'z')
  in
  Printf.printf "[1] Trailing-character shift table\n";
  List.iter show_shifts [ "abc"; "abcabc"; "aaaa"; "z" ];
  print_newline ();

  (* ----------------- 2. find_all / contains / count -------------- *)
  Printf.printf "[2] Multi-occurrence search\n";
  let demo pattern text =
    let c = H.compile pattern in
    let hits = H.find_all c text in
    let first = H.find_first c text in
    Printf.printf "  pattern=%S  text=%S\n" pattern text;
    Printf.printf "    occurrences=%d  first=%s  positions=[%s]\n"
      (H.count c text)
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
    "fox" (H.occurs ~pattern:"fox" ~text);
  Printf.printf "  occurs ~pattern:%S ~text => %b\n"
    "cat" (H.occurs ~pattern:"cat" ~text);
  Printf.printf "  search_all ~pattern:%S ~text => [%s]\n"
    "the"
    (String.concat ";"
       (List.map string_of_int (H.search_all ~pattern:"the" ~text)));

  print_newline ();
  Printf.printf "Done.\n"
