(* rabin_karp.ml — Rabin–Karp Rolling-Hash String Search                    *)
(*                                                                          *)
(* Rabin–Karp matches a pattern (or a set of patterns of the same length)   *)
(* against a text by computing a polynomial rolling hash and only doing a   *)
(* full byte-by-byte equality check when the hashes collide.                *)
(*                                                                          *)
(* Average case is O(n + m); worst case is O(n*m) on pathological inputs    *)
(* (essentially a degenerate hash-collision attack), but the rolling-hash   *)
(* design makes it especially well suited to                                *)
(*   - multi-pattern search where every pattern shares a length, and        *)
(*   - duplicate-substring / plagiarism style scans where we need every    *)
(*     length-k substring of a text indexed by hash.                        *)
(*                                                                          *)
(* This file is the rolling-hash sibling to:                                *)
(*   - kmp.ml           (linear, failure function)                          *)
(*   - boyer_moore.ml   (sublinear average, two-table right-to-left scan)   *)
(*   - aho_corasick.ml  (multi-pattern automaton, mixed lengths)            *)
(*   - z_algorithm.ml   (Z-function based prefix matching)                  *)
(*   - manacher.ml      (linear-time palindrome analysis)                   *)
(*                                                                          *)
(* API mirrors kmp.ml: compile / find_all / find_first / contains / count   *)
(* plus one-shot helpers (search / occurs / search_all).  Multi-pattern     *)
(* helpers (compile_multi / find_all_multi) round out the module.           *)
(*                                                                          *)
(* The hash uses a 256-byte alphabet with base = 257 and a large prime      *)
(* modulus that comfortably fits in OCaml's native int on 64-bit hosts      *)
(* (1_000_000_007), so all arithmetic stays in plain int — no extra deps.   *)

module Rabin_karp = struct

  (** Hash base for the polynomial rolling hash (size of the byte
      alphabet plus one). *)
  let base = 257

  (** Hash modulus. A large prime that comfortably fits in OCaml's
      63-bit native int, so all rolling-hash arithmetic stays in plain
      [int] with no external dependencies. *)
  let prime = 1_000_000_007

  (** [hash_slice s lo len] computes the polynomial rolling hash of
      [s.\[lo .. lo + len - 1\]] from scratch:
      {[ sum_{i=0..len-1} byte(s.\[lo+i\]) * base^(len-1-i) mod prime ]}
      O(len). *)
  let hash_slice s lo len =
    let h = ref 0 in
    for i = 0 to len - 1 do
      h := (!h * base + Char.code s.[lo + i]) mod prime
    done;
    !h

  (** [hash s] is the polynomial rolling hash of the entire string [s]. *)
  let hash s = hash_slice s 0 (String.length s)

  (** [high_power len] precomputes [base ^ (len - 1) mod prime], the
      multiplier used to remove the high-order byte when rolling the
      hash window forward by one position. Returns [1] when [len = 0]. *)
  let high_power len =
    let h = ref 1 in
    for _ = 1 to len - 1 do
      h := (!h * base) mod prime
    done;
    !h

  (** Compiled-pattern handle: stores the pattern, its length, its
      precomputed hash and the high-order-byte multiplier used by the
      rolling-hash step. *)
  type compiled = {
    pattern  : string;
    plen     : int;
    phash    : int;
    high_pow : int;   (* base^(plen-1) mod prime *)
  }

  (** [compile pattern] precomputes the rolling-hash state for
      [pattern] so it can be matched against many texts without
      re-hashing. O(m). *)
  let compile pattern =
    let plen = String.length pattern in
    { pattern;
      plen;
      phash = hash_slice pattern 0 plen;
      high_pow = high_power plen;
    }

  (** [slice_equals pattern text start] verifies a candidate match by
      direct byte comparison. Used after every rolling-hash collision
      to rule out false positives. Returns [false] if the candidate
      window does not fit in [text]. *)
  let slice_equals pattern text start =
    let m = String.length pattern in
    let n = String.length text in
    if start < 0 || start + m > n then false
    else
      let rec loop i =
        if i = m then true
        else if pattern.[i] <> text.[start + i] then false
        else loop (i + 1)
      in
      loop 0

  (** [iter_matches compiled text on_match] streams every confirmed
      occurrence of the compiled pattern in [text] in left-to-right
      order, invoking [on_match start] for each match offset.
      Expected O(n + m) with negligible verification overhead under a
      uniform-random hash; worst case O(n * m) on adversarial inputs.

      Empty-pattern convention: the empty pattern matches at every
      position [0..String.length text] inclusive. *)
  let iter_matches { pattern; plen; phash; high_pow } text on_match =
    let n = String.length text in
    if plen = 0 then begin
      (* Conventionally the empty pattern matches at every position    *)
      (* including the end of text.  Mirrors kmp.ml + Aho-Corasick.    *)
      for i = 0 to n do on_match i done
    end
    else if plen <= n then begin
      let window_hash = ref (hash_slice text 0 plen) in
      if !window_hash = phash && slice_equals pattern text 0 then
        on_match 0;
      for i = 1 to n - plen do
        (* Roll: remove text.[i-1] * base^(plen-1), shift left, add new *)
        let leaving = Char.code text.[i - 1] in
        let entering = Char.code text.[i + plen - 1] in
        let next = (!window_hash - leaving * high_pow) mod prime in
        let next = (next * base + entering) mod prime in
        (* OCaml's mod can return a negative result if the lhs is        *)
        (* negative — normalise so the comparison with phash is sound.   *)
        let next = if next < 0 then next + prime else next in
        window_hash := next;
        if !window_hash = phash && slice_equals pattern text i then
          on_match i
      done
    end

  (** [find_all compiled text] returns every start offset of the
      compiled pattern in [text], in increasing order. *)
  let find_all compiled text =
    let acc = ref [] in
    iter_matches compiled text (fun start -> acc := start :: !acc);
    List.rev !acc

  (** [find_first compiled text] returns [Some i] for the first
      occurrence or [None] if absent. Stops scanning at the first
      confirmed match. *)
  let find_first compiled text =
    let result = ref None in
    (try
      iter_matches compiled text (fun start ->
        result := Some start;
        raise Exit)
    with Exit -> ());
    !result

  (** [contains compiled text] is the existence-only variant. *)
  let contains compiled text =
    match find_first compiled text with
    | Some _ -> true
    | None -> false

  (** [count compiled text] returns the total number of confirmed
      occurrences. *)
  let count compiled text =
    let c = ref 0 in
    iter_matches compiled text (fun _ -> incr c);
    !c

  (** [search ~pattern ~text] compiles internally and returns the first
      occurrence. *)
  let search ~pattern ~text = find_first (compile pattern) text

  (** [occurs ~pattern ~text] is the one-shot existence check. *)
  let occurs ~pattern ~text = contains (compile pattern) text

  (** [search_all ~pattern ~text] returns every occurrence. *)
  let search_all ~pattern ~text = find_all (compile pattern) text

  (** Compiled multi-pattern handle for equal-length pattern sets.
      Stores the patterns array, the shared pattern length, and a
      hash-bucket map from hash value to candidate pattern indices. *)
  type multi_compiled = {
    patterns : string array;
    plen_m   : int;
    hashes   : (int, int list) Hashtbl.t;  (* hash -> [pattern index ...] *)
    high_pow_m : int;
  }

  (** [compile_multi patterns] precomputes a shared rolling-hash setup
      for a list of patterns that all have the same length (the
      canonical Rabin-Karp multi-pattern arrangement: one rolling hash
      drives the entire scan).

      @raise Invalid_argument if the patterns do not all share a
      length. The empty pattern list yields an inert handle that
      matches nothing. *)
  let compile_multi patterns =
    match patterns with
    | [] -> { patterns = [||]; plen_m = 0;
              hashes = Hashtbl.create 1; high_pow_m = 1 }
    | first :: _ ->
        let plen = String.length first in
        List.iter (fun p ->
          if String.length p <> plen then
            invalid_arg
              "Rabin_karp.compile_multi: all patterns must share a length")
          patterns;
        let arr = Array.of_list patterns in
        let h = Hashtbl.create (max 16 (Array.length arr)) in
        Array.iteri (fun idx p ->
          let ph = hash_slice p 0 plen in
          let prev = try Hashtbl.find h ph with Not_found -> [] in
          Hashtbl.replace h ph (idx :: prev))
          arr;
        { patterns = arr;
          plen_m = plen;
          hashes = h;
          high_pow_m = high_power plen;
        }

  (** [find_all_multi mc text] runs the compiled multi-pattern handle
      against [text] in a single linear pass.

      Returns an associative list of [(pattern, positions)] in the
      same order as the original patterns. Patterns that do not occur
      get an empty list. *)
  let find_all_multi mc text =
    let n = String.length text in
    let plen = mc.plen_m in
    let np = Array.length mc.patterns in
    (* Result accumulator: positions for each pattern, in reverse order *)
    let acc = Array.make np [] in
    if np = 0 then []
    else if plen = 0 then begin
      let all = ref [] in
      for i = n downto 0 do all := i :: !all done;
      Array.iteri (fun idx _ -> acc.(idx) <- !all) mc.patterns;
      Array.to_list
        (Array.mapi (fun idx p -> (p, acc.(idx))) mc.patterns)
    end
    else if plen > n then
      Array.to_list (Array.map (fun p -> (p, [])) mc.patterns)
    else begin
      let try_match h start =
        match Hashtbl.find_opt mc.hashes h with
        | None -> ()
        | Some idxs ->
            List.iter (fun idx ->
              let p = mc.patterns.(idx) in
              if slice_equals p text start then
                acc.(idx) <- start :: acc.(idx))
              idxs
      in
      let window_hash = ref (hash_slice text 0 plen) in
      try_match !window_hash 0;
      for i = 1 to n - plen do
        let leaving = Char.code text.[i - 1] in
        let entering = Char.code text.[i + plen - 1] in
        let next = (!window_hash - leaving * mc.high_pow_m) mod prime in
        let next = (next * base + entering) mod prime in
        let next = if next < 0 then next + prime else next in
        window_hash := next;
        try_match !window_hash i
      done;
      Array.to_list
        (Array.mapi (fun idx p -> (p, List.rev acc.(idx))) mc.patterns)
    end

  (** [duplicate_substrings ?min_count ~k text] indexes every length-[k]
      substring of [text] by its rolling hash and returns every
      [(hash, positions)] group with at least [min_count] members
      (default [2]).

      Useful for plagiarism / duplicate-substring detection. Note that
      hash collisions are NOT verified by byte comparison — callers
      should disambiguate candidate groups themselves if exact
      duplicates are required. Returns [\[\]] for [k <= 0] or [k > |text|]. *)
  let duplicate_substrings ?(min_count = 2) ~k text =
    let n = String.length text in
    if k <= 0 || k > n then []
    else begin
      let high = high_power k in
      let table = Hashtbl.create 64 in
      let h = ref (hash_slice text 0 k) in
      let push h0 i =
        let prev = try Hashtbl.find table h0 with Not_found -> [] in
        Hashtbl.replace table h0 (i :: prev)
      in
      push !h 0;
      for i = 1 to n - k do
        let leaving = Char.code text.[i - 1] in
        let entering = Char.code text.[i + k - 1] in
        let next = (!h - leaving * high) mod prime in
        let next = (next * base + entering) mod prime in
        let next = if next < 0 then next + prime else next in
        h := next;
        push !h i
      done;
      Hashtbl.fold (fun key positions acc ->
        if List.length positions >= min_count
        then (key, List.rev positions) :: acc
        else acc)
        table []
    end

end


(* ============================================================== *)
(*                            Demo                                 *)
(* ============================================================== *)

let () =
  let module R = Rabin_karp in

  Printf.printf "Rabin–Karp — rolling-hash string matching\n";
  Printf.printf "=========================================\n\n";

  (* ----------------- 1. hash + rolling sanity check -------------- *)
  Printf.printf "[1] Hash sanity\n";
  let show_hash s = Printf.printf "  hash(%S) = %d\n" s (R.hash s) in
  List.iter show_hash [ "abc"; "abd"; ""; "hello"; "world" ];
  print_newline ();

  (* ----------------- 2. single-pattern find_all / count ---------- *)
  Printf.printf "[2] Single-pattern multi-occurrence search\n";
  let demo pattern text =
    let c = R.compile pattern in
    let hits = R.find_all c text in
    let first = R.find_first c text in
    Printf.printf "  pattern=%S  text=%S\n" pattern text;
    Printf.printf "    occurrences=%d  first=%s  positions=[%s]\n"
      (R.count c text)
      (match first with Some i -> string_of_int i | None -> "none")
      (String.concat ";" (List.map string_of_int hits))
  in
  demo "abab" "ababcababababcabab";
  demo "aaa"  "aaaaaa";
  demo "xyz"  "abcdefg";
  demo ""     "anything";
  print_newline ();

  (* ----------------- 3. One-shot helpers ------------------------- *)
  Printf.printf "[3] One-shot helpers\n";
  let text = "the quick brown fox jumps over the lazy dog" in
  Printf.printf "  occurs  ~pattern:%S => %b\n"
    "fox" (R.occurs ~pattern:"fox" ~text);
  Printf.printf "  occurs  ~pattern:%S => %b\n"
    "cat" (R.occurs ~pattern:"cat" ~text);
  Printf.printf "  search_all ~pattern:%S => [%s]\n"
    "the"
    (String.concat ";"
       (List.map string_of_int (R.search_all ~pattern:"the" ~text)));
  print_newline ();

  (* ----------------- 4. Multi-pattern (same length) -------------- *)
  Printf.printf "[4] Multi-pattern same-length search\n";
  let text2 =
    "she sells sea shells by the sea shore and the shells are hers"
  in
  let mc = R.compile_multi [ "she"; "sea"; "the"; "her" ] in
  let results = R.find_all_multi mc text2 in
  Printf.printf "  text = %S\n" text2;
  List.iter
    (fun (p, hits) ->
       Printf.printf "    %S => [%s]\n"
         p (String.concat ";" (List.map string_of_int hits)))
    results;
  print_newline ();

  (* ----------------- 5. Duplicate-substring detection ------------ *)
  Printf.printf "[5] Duplicate length-k substrings (plagiarism-style)\n";
  let plagiarism =
    "the rain in spain falls mainly on the plain and the rain"
  in
  let dups = R.duplicate_substrings ~k:8 ~min_count:2 plagiarism in
  Printf.printf "  text = %S\n" plagiarism;
  Printf.printf "  repeated length-8 substrings (showing up to 5):\n";
  let shown = ref 0 in
  List.iter
    (fun (_h, positions) ->
       if !shown < 5 then begin
         let first = List.hd positions in
         let sub = String.sub plagiarism first 8 in
         Printf.printf "    %S at positions [%s]\n"
           sub (String.concat ";" (List.map string_of_int positions));
         incr shown
       end)
    dups;

  print_newline ();
  Printf.printf "Done.\n"
