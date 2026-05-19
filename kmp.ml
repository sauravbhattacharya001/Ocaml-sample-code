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

module Kmp = struct

  (* ---------------------------------------------------------------- *)
  (* Failure function (a.k.a. LPS / pi array).                        *)
  (*                                                                  *)
  (* For pattern p of length m, returns an int array f of length m    *)
  (* such that f.(i) is the length of the longest proper prefix of    *)
  (* p.[0..i] which is also a suffix of p.[0..i].                     *)
  (*                                                                  *)
  (* For the empty pattern this returns an empty array.               *)
  (* ---------------------------------------------------------------- *)
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

  (* ---------------------------------------------------------------- *)
  (* Compiled-pattern handle: caches the failure function so the same *)
  (* pattern can be matched against many texts cheaply.               *)
  (* ---------------------------------------------------------------- *)
  type compiled = {
    pattern : string;
    failure : int array;
  }

  let compile pattern = { pattern; failure = failure pattern }

  (* ---------------------------------------------------------------- *)
  (* Core scan driver: walks the text once, threading the longest     *)
  (* prefix-match length through the failure function on mismatch,    *)
  (* invoking [on_match start] whenever a full occurrence is found.   *)
  (* ---------------------------------------------------------------- *)
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

  let find_all compiled text =
    let acc = ref [] in
    iter_matches compiled text (fun start -> acc := start :: !acc);
    List.rev !acc

  let find_first compiled text =
    let result = ref None in
    (try
      iter_matches compiled text (fun start ->
        result := Some start;
        raise Exit)
    with Exit -> ());
    !result

  let contains compiled text =
    match find_first compiled text with
    | Some _ -> true
    | None -> false

  let count compiled text =
    let c = ref 0 in
    iter_matches compiled text (fun _ -> incr c);
    !c

  (* ---------------------------------------------------------------- *)
  (* Convenience one-shot wrappers that compile internally; suitable  *)
  (* when the pattern is used only once.                              *)
  (* ---------------------------------------------------------------- *)
  let search ~pattern ~text = find_first (compile pattern) text
  let occurs ~pattern ~text = contains (compile pattern) text
  let search_all ~pattern ~text = find_all (compile pattern) text

  (* ---------------------------------------------------------------- *)
  (* Bonus: smallest period of [pattern] derivable from the failure   *)
  (* function.  For "abcabcab" returns 3, for "abcdef" returns 6.     *)
  (* Returns 0 for the empty pattern.                                 *)
  (* ---------------------------------------------------------------- *)
  let period pattern =
    let m = String.length pattern in
    if m = 0 then 0
    else
      let f = failure pattern in
      m - f.(m - 1)

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
