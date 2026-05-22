(* bitap.ml — Bitap / Shift-Or string search                                *)
(*                                                                          *)
(* Bitap (a.k.a. Shift-Or / Baeza-Yates–Gonnet) encodes the partial-match   *)
(* NFA of a pattern as an OCaml int bitmask and slides it across the text   *)
(* with a single bitwise step per text character. Worst-case O(n * ceil(m / *)
(* w)) where w is the host word size; for patterns that fit in one machine  *)
(* word (here, up to BITAP_MAX = 62 chars on a 63-bit native int) this is   *)
(* effectively O(n) with extremely tight inner loops.                       *)
(*                                                                          *)
(* This file is the bitwise-NFA sibling to the string-search family:        *)
(*   - kmp.ml          (linear via failure function)                        *)
(*   - boyer_moore.ml  (sublinear average, two-table right-to-left scan)    *)
(*   - rabin_karp.ml   (rolling-hash, multi-pattern friendly)               *)
(*   - aho_corasick.ml (multi-pattern automaton with failure links)         *)
(*   - z_algorithm.ml  (Z-function based prefix matching)                   *)
(*   - manacher.ml     (linear-time palindrome analysis)                    *)
(*                                                                          *)
(* Bitap shines for approximate matching: extending the NFA with an extra   *)
(* row per allowed error gives Wu–Manber's k-mismatch variant essentially   *)
(* for free, which we implement as [find_all_approx ~k].                    *)
(*                                                                          *)
(* API:                                                                     *)
(*   compile : string -> compiled                                           *)
(*   find_all     : compiled -> string -> int list   (exact, leftmost asc)  *)
(*   find_first   : compiled -> string -> int option                        *)
(*   contains     : compiled -> string -> bool                              *)
(*   count        : compiled -> string -> int                               *)
(*   search       : pattern:string -> text:string -> int option   (one-shot)*)
(*   occurs       : pattern:string -> text:string -> bool                   *)
(*   search_all   : pattern:string -> text:string -> int list               *)
(*   find_all_approx : pattern:string -> text:string -> k:int               *)
(*                   -> (int * int) list                                    *)
(*       Returns (end_position, errors) for every alignment whose Hamming   *)
(*       distance to the pattern is at most k. end_position is the index in *)
(*       text of the LAST character of the match (Wu–Manber convention).    *)
(*       Use start = end_position - pattern_length + 1 to recover the start.*)
(*                                                                          *)
(* Limits: patterns above BITAP_MAX are rejected with Invalid_argument.     *)
(* For longer patterns, fall back to kmp.ml / boyer_moore.ml.               *)

(** Bitap / Shift-Or string search (bitwise NFA).

    Encodes a pattern's partial-match NFA as a single OCaml int and
    slides it across the text one bitwise step per character. For
    patterns up to {!Bitap.bitap_max} characters this gives effectively
    O(n) exact matching with extremely tight inner loops.

    Also provides Wu-Manber-style approximate matching via
    {!Bitap.find_all_approx} (Hamming distance, up to [k] mismatches).

    Sibling to {!module:Kmp}, {!module:BoyerMoore}, {!module:Rabin_karp},
    {!module:AhoCorasick}, the Z-algorithm and Manacher modules. *)
module Bitap = struct

  (** Maximum pattern length safely encodable in a single OCaml native
      int. On a 64-bit runtime OCaml native ints are 63 bits and one bit
      is reserved for the high "match" flag, leaving 62 usable bits. *)
  let bitap_max = 62

  (** Compiled-pattern handle. The character mask uses Shift-Or
      convention: bit i of [mask.(c)] is [0] iff character [c] occurs
      at position [i] in the pattern. *)
  type compiled = {
    pattern : string;
    m       : int;
    (* For each byte value 0..255, the bitmask of positions in the pattern  *)
    (* where that byte does NOT occur. Shift-Or convention: 0 bit = match.  *)
    mask    : int array;
    (* The accept bit: 1 lsl (m - 1). After processing a text character,    *)
    (* the state has its accept bit clear iff the last m text characters    *)
    (* spell the pattern exactly.                                           *)
    accept  : int;
  }

  (** [compile pattern] precomputes the per-character mask table.

      @raise Invalid_argument if [String.length pattern > bitap_max]. *)
  let compile pattern =
    let m = String.length pattern in
    if m = 0 then
      { pattern; m = 0; mask = Array.make 256 0; accept = 0 }
    else if m > bitap_max then
      invalid_arg
        (Printf.sprintf "Bitap.compile: pattern length %d exceeds bitap_max=%d"
           m bitap_max)
    else begin
      let all_ones = (1 lsl m) - 1 in
      let mask = Array.make 256 all_ones in
      for i = 0 to m - 1 do
        let c = Char.code pattern.[i] in
        (* clear bit i to mark "char c occurs at position i" *)
        mask.(c) <- mask.(c) land (lnot (1 lsl i))
      done;
      { pattern; m; mask; accept = 1 lsl (m - 1) }
    end

  (** [find_all c text] returns every start offset at which the
      compiled pattern occurs in [text], in increasing order.

      Uses the Shift-Or recurrence:
      {[ state := ((state lsl 1) lor mask.(text.\[j\])) land all_ones ]}
      Bit [i] of [state] is [0] iff [pattern.\[0..i\]] is a suffix of
      the text read so far. *)
  let find_all c text =
    let m = c.m in
    let n = String.length text in
    if m = 0 then begin
      (* Match at every position incl. end-of-text, mirroring kmp.ml. *)
      let rec build i acc = if i < 0 then acc else build (i - 1) (i :: acc) in
      build n []
    end else if m > n then []
    else begin
      let all_ones = (1 lsl m) - 1 in
      let state = ref all_ones in
      let acc = ref [] in
      for j = 0 to n - 1 do
        let cj = Char.code text.[j] in
        (* Shift-Or step: state := ((state << 1) | mask[c]) & all_ones.   *)
        state := (((!state lsl 1) lor c.mask.(cj)) land all_ones);
        if !state land c.accept = 0 then
          acc := (j - m + 1) :: !acc
      done;
      List.rev !acc
    end

  (** [find_first c text] returns the smallest start offset of the
      compiled pattern in [text], or [None] if absent. *)
  let find_first c text =
    match find_all c text with
    | [] -> None
    | x :: _ -> Some x

  (** [contains c text] is the existence-only variant. *)
  let contains c text =
    match find_first c text with Some _ -> true | None -> false

  (** [count c text] returns the total number of (possibly overlapping)
      matches. *)
  let count c text = List.length (find_all c text)

  (** [search ~pattern ~text] one-shot wrapper: compile and return the
      first occurrence. Matches the signature of {!Kmp.search} so
      callers can swap algorithms freely. *)
  let search  ~pattern ~text = find_first (compile pattern) text

  (** [occurs ~pattern ~text] one-shot existence check. *)
  let occurs  ~pattern ~text = contains   (compile pattern) text

  (** [search_all ~pattern ~text] one-shot helper returning every
      occurrence. *)
  let search_all ~pattern ~text = find_all (compile pattern) text

  (** [find_all_approx ~pattern ~text ~k] returns every approximate
      occurrence of [pattern] in [text] allowing up to [k] character
      substitutions (Hamming distance).

      Each result is a [(end_position, errors)] pair where
      [end_position] is the 0-based index of the last matched byte and
      [errors] is the number of substitutions used. Results are in
      ascending [end_position] order and each position appears at most
      once (smallest error count wins on ties).

      Implementation: Wu-Manber [k]-row Shift-Or NFA. When [k = 0] this
      degrades to the exact {!find_all} path.

      @raise Invalid_argument if [k < 0]. *)
  let find_all_approx ~pattern ~text ~k =
    if k < 0 then invalid_arg "Bitap.find_all_approx: k must be >= 0";
    let c = compile pattern in
    let m = c.m in
    let n = String.length text in
    if m = 0 then []
    else if k = 0 then
      List.map (fun s -> (s + m - 1, 0)) (find_all c text)
    else begin
      let all_ones = (1 lsl m) - 1 in
      let r = Array.make (k + 1) all_ones in
      let acc = ref [] in
      for j = 0 to n - 1 do
        let cj = Char.code text.[j] in
        let prev = Array.copy r in
        r.(0) <- ((prev.(0) lsl 1) land all_ones) lor c.mask.(cj);
        for d = 1 to k do
          let exact =
            (((prev.(d) lsl 1) lor c.mask.(cj)) land all_ones)
          in
          let sub =
            (prev.(d - 1) lsl 1) land all_ones
          in
          (* AND in 0=match convention: bit i is 0 only if BOTH lanes had *)
          (* a viable extension at position i (match or single sub).      *)
          r.(d) <- exact land sub
        done;
        (* Best error level reaching accept at j (smallest d wins). *)
        let rec scan d =
          if d > k then ()
          else if r.(d) land c.accept = 0 then
            acc := (j, d) :: !acc
          else scan (d + 1)
        in
        scan 0
      done;
      List.rev !acc
    end
end

(* ====================================================================== *)
(* Demo                                                                   *)
(* ====================================================================== *)

let () =
  let module B = Bitap in
  Printf.printf "=== Bitap / Shift-Or string search ===\n\n";

  (* ----------------- 1. Exact search ---------------------------- *)
  Printf.printf "[1] Exact search (Shift-Or)\n";
  let demo pattern text =
    let c = B.compile pattern in
    let hits = B.find_all c text in
    let first = B.find_first c text in
    Printf.printf "  pattern=%S  text=%S\n" pattern text;
    Printf.printf "    occurrences=%d  first=%s  positions=[%s]\n"
      (B.count c text)
      (match first with Some i -> string_of_int i | None -> "none")
      (String.concat ";" (List.map string_of_int hits))
  in
  demo "abab"  "ababcababababcabab";
  demo "aaa"   "aaaaaa";
  demo "xyz"   "abcdefg";
  demo "fox"   "the quick brown fox jumps over the lazy dog";
  demo ""      "anything";
  print_newline ();

  (* ----------------- 2. One-shot helpers ------------------------ *)
  Printf.printf "[2] One-shot helpers\n";
  let text = "the quick brown fox jumps over the lazy dog" in
  Printf.printf "  occurs ~pattern:%S ~text => %b\n"
    "fox" (B.occurs ~pattern:"fox" ~text);
  Printf.printf "  occurs ~pattern:%S ~text => %b\n"
    "cat" (B.occurs ~pattern:"cat" ~text);
  Printf.printf "  search_all ~pattern:%S ~text => [%s]\n"
    "the"
    (String.concat ";"
       (List.map string_of_int (B.search_all ~pattern:"the" ~text)));
  print_newline ();

  (* ----------------- 3. Approximate (k-mismatch) ---------------- *)
  Printf.printf "[3] Approximate matching (Hamming distance <= k)\n";
  let approx_demo pattern text k =
    let hits = B.find_all_approx ~pattern ~text ~k in
    Printf.printf "  pattern=%S  text=%S  k=%d\n" pattern text k;
    Printf.printf "    matches=%d  (end_pos, errors)=[%s]\n"
      (List.length hits)
      (String.concat "; "
         (List.map
            (fun (e, d) -> Printf.sprintf "(%d,%d)" e d)
            hits))
  in
  (* Classic example: looking for "fortunate" inside a slightly noisy text. *)
  approx_demo "fortune" "the unfortunate fortuneteller had foreknowledge" 0;
  approx_demo "fortune" "the unfortunate fortuneteller had foreknowledge" 1;
  approx_demo "fortune" "the unfortunate fortuneteller had foreknowledge" 2;
  approx_demo "GATTACA" "AGATTACACGATTACAGATTAGAGATTACA" 0;
  approx_demo "GATTACA" "AGATTACACGATTACAGATTAGAGATTACA" 1;
  print_newline ();

  (* ----------------- 4. Length limit ---------------------------- *)
  Printf.printf "[4] Length limit (bitap_max = %d)\n" B.bitap_max;
  let long_pattern = String.make (B.bitap_max + 1) 'x' in
  begin
    try
      let _ = B.compile long_pattern in
      Printf.printf "  unexpected success\n"
    with Invalid_argument msg ->
      Printf.printf "  rejected as expected: %s\n" msg
  end;

  print_newline ();
  Printf.printf "Done.\n"
