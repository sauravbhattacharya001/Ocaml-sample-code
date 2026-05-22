(* kmp.ml — Knuth–Morris–Pratt String Search                                *)
(*                                                                          *)
(* The classic KMP algorithm matches a pattern in O(n + m) worst case by    *)
(* precomputing a "failure function" (a.k.a. longest proper                 *)
(* prefix-which-is-also-suffix array, traditionally called pi or lps) so    *)
(* that on a mismatch the pattern can be shifted maximally without ever    *)
(* re-examining characters of the text.                                     *)
(*                                                                          *)
(* This file is the linear-worst-case sibling to:                           *)
(*   - boyer_moore.ml   (sublinear average, two-table right-to-left scan)   *)
(*   - aho_corasick.ml  (multi-pattern automaton)                           *)
(*   - z_algorithm.ml   (Z-function based prefix matching)                  *)
(*   - manacher.ml      (linear-time palindrome analysis)                   *)
(*                                                                          *)
(* API mirrors boyer_moore.ml: compile/find_all/find_first/contains/        *)
(* count + one-shot search/occurs helpers, plus the failure-function        *)
(* itself which is independently useful for periodicity / borders /         *)
(* string-rotation problems.                                                *)
(*                                                                          *)
(* Demonstrates: pure imperative-style array filling with two-pointer       *)
(* invariant maintenance, byte-level indexing, and the standard             *)
(* "build automaton, then drive it across the text" pipeline.               *)

(** Knuth-Morris-Pratt exact string matching.

    Compile a pattern once with {!Kmp.compile} and then match it against
    many texts in O(n + m) worst-case time, where n is the text length
    and m is the pattern length. The compiled handle caches the
    failure / LPS array so per-text work is purely linear in n.

    Also exposes the failure function itself and helpers built on it
    ({!Kmp.period}, {!Kmp.is_periodic}) since the LPS array has uses
    beyond matching (periodicity, borders, string rotations). *)
module Kmp = struct

  (** [failure pattern] returns the KMP failure function (a.k.a. LPS /
      pi array) for [pattern].

      For a pattern [p] of length [m], the returned array [f] of length
      [m] satisfies: [f.(i)] is the length of the longest proper prefix
      of [p.\[0..i\]] that is also a suffix of [p.\[0..i\]].

      Runs in O(m) time. For the empty pattern this returns [\[||\]]. *)
  let failure pattern =
    let m = String.length pattern in
    let f = Array.make (max m 1) 0 in
    if m = 0 then [||]
    else begin
      f.(0) <- 0;
      let k = ref 0 in
      for i = 1 to m - 1 do
        while !k > 0 && pattern.[!k] <> pattern.[i] do
          k := f.(!k - 1)
        done;
        if pattern.[!k] = pattern.[i] then incr k;
        f.(i) <- !k
      done;
      f
    end

  (** Compiled-pattern handle. Caches the failure function so the same
      pattern can be matched against many texts without redundant work. *)
  type compiled = {
    pattern : string;
    failure : int array;
  }

  (** [compile pattern] precomputes the failure function for [pattern]
      and returns a reusable {!compiled} handle. O(m) in the pattern
      length. *)
  let compile pattern = { pattern; failure = failure pattern }

  (** [iter_matches compiled text on_match] walks [text] once, invoking
      [on_match start] for every occurrence of the compiled pattern at
      byte offset [start].

      Streams matches in left-to-right order; suitable when you want to
      avoid allocating an intermediate list (e.g. very large texts or
      early termination via an exception raised from [on_match]).

      Empty-pattern convention: the empty pattern matches at every
      position [0..String.length text] inclusive, mirroring the
      semantics of {!String.contains} / standard substring search. *)
  let iter_matches { pattern; failure = f } text on_match =
    let m = String.length pattern in
    let n = String.length text in
    if m = 0 then begin
      (* Conventionally the empty pattern matches at every position    *)
      (* including the end of text.  Mirrors String.contains semantics. *)
      for i = 0 to n do on_match i done
    end
    else if m <= n then begin
      let q = ref 0 in
      for i = 0 to n - 1 do
        while !q > 0 && pattern.[!q] <> text.[i] do
          q := f.(!q - 1)
        done;
        if pattern.[!q] = text.[i] then incr q;
        if !q = m then begin
          on_match (i - m + 1);
          q := f.(m - 1)
        end
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

  (** [period pattern] returns the smallest period [p] such that
      [pattern.\[i\] = pattern.\[i + p\]] for all valid [i + p], derived
      from the failure function in O(m).

      Examples: [period "abcabcab" = 3], [period "abcdef" = 6],
      [period "" = 0]. *)
  let period pattern =
    let m = String.length pattern in
    if m = 0 then 0
    else
      let f = failure pattern in
      m - f.(m - 1)

  (** [is_periodic pattern] is [true] iff [pattern] is a non-trivial
      power of a shorter string (i.e. its smallest period strictly
      divides its length). [false] for the empty pattern. *)
  let is_periodic pattern =
    let m = String.length pattern in
    if m = 0 then false
    else
      let p = period pattern in
      p < m && m mod p = 0

end


(* ============================================================== *)
(*                            Demo                                 *)
(* ============================================================== *)

let () =
  let module K = Kmp in

  Printf.printf "KMP — Knuth–Morris–Pratt exact string matching\n";
  Printf.printf "==============================================\n\n";

  (* ----------------- 1. Failure function showcase ---------------- *)
  let show_failure p =
    let f = K.failure p in
    Printf.printf "  failure(%S) =" p;
    Array.iter (fun v -> Printf.printf " %d" v) f;
    print_newline ()
  in
  Printf.printf "[1] Failure function (LPS / pi array)\n";
  List.iter show_failure
    [ "abcabcd"
    ; "aabaabaaa"
    ; "abcabcab"
    ; "abcdef"
    ; "aaaaa"
    ];
  print_newline ();

  (* ----------------- 2. find_all / contains / count -------------- *)
  Printf.printf "[2] Multi-occurrence search\n";
  let demo pattern text =
    let c = K.compile pattern in
    let hits = K.find_all c text in
    let first = K.find_first c text in
    Printf.printf "  pattern=%S  text=%S\n" pattern text;
    Printf.printf "    occurrences=%d  first=%s  positions=[%s]\n"
      (K.count c text)
      (match first with Some i -> string_of_int i | None -> "none")
      (String.concat ";" (List.map string_of_int hits))
  in
  demo "abab" "ababcababababcabab";
  demo "aaa"  "aaaaaa";
  demo "xyz"  "abcdefg";
  demo ""     "anything";
  print_newline ();

  (* ----------------- 3. Period detection ------------------------- *)
  Printf.printf "[3] Smallest period (from KMP failure function)\n";
  List.iter
    (fun p ->
       Printf.printf "  period(%S) = %d  periodic=%b\n"
         p (K.period p) (K.is_periodic p))
    [ "abcabcabc"
    ; "abcabcab"
    ; "ababab"
    ; "abcdef"
    ; "aaaa"
    ; ""
    ];
  print_newline ();

  (* ----------------- 4. One-shot wrappers ------------------------ *)
  Printf.printf "[4] One-shot helpers\n";
  let text = "the quick brown fox jumps over the lazy dog" in
  Printf.printf "  occurs ~pattern:%S ~text => %b\n"
    "fox" (K.occurs ~pattern:"fox" ~text);
  Printf.printf "  occurs ~pattern:%S ~text => %b\n"
    "cat" (K.occurs ~pattern:"cat" ~text);
  Printf.printf "  search_all ~pattern:%S ~text => [%s]\n"
    "the"
    (String.concat ";"
       (List.map string_of_int (K.search_all ~pattern:"the" ~text)));

  print_newline ();
  Printf.printf "Done.\n"
