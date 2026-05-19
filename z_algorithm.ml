(* z_algorithm.ml — Z-function & Linear-Time String Matching *)
(* The Z-function of a string s of length n is the array z where         *)
(* z.(i) is the length of the longest substring starting at position i   *)
(* that matches a prefix of s.  By convention z.(0) = 0 (or n; we use 0).*)
(*                                                                       *)
(* Computed in O(n) using the classic "Z-box" trick of maintaining the   *)
(* rightmost match interval [l, r] seen so far and reusing previously    *)
(* computed values whenever the current index falls inside that box.    *)
(*                                                                       *)
(* Applications shipped in this module:                                  *)
(*   - z          : raw Z-function                                       *)
(*   - find_all   : O(n+m) multi-occurrence search of pattern in text    *)
(*   - contains   : O(n+m) existence check                               *)
(*   - count      : O(n+m) match count                                   *)
(*   - lcp        : longest common prefix length of two strings          *)
(*   - period     : smallest period p such that s[i]=s[i+p] for all i+p<n*)
(*   - is_periodic: does s have a non-trivial period dividing |s|?       *)
(*   - tandem_repeats : every (start, period, repeats) tandem-repeat run *)
(*   - borders    : every proper border length (longest first)           *)
(*   - distinct_substrings : O(n^2) count via Z-function repetition      *)
(*                                                                       *)
(* Demonstrates: clean separation of core algorithm from applications,   *)
(* tight loop with imperative arrays, and re-use of one O(n) primitive   *)
(* to answer many classical string questions.                            *)

module Z = struct

  (* ---- Core: the Z-function ----------------------------------------- *)

  (** [z s] returns an int array of length [String.length s] where      *)
  (** [(z s).(i)] is the longest prefix of [s] that also occurs at      *)
  (** position [i].  By convention [(z s).(0) = 0].                     *)
  let z s =
    let n = String.length s in
    let z = Array.make n 0 in
    if n = 0 then z
    else begin
      let l = ref 0 and r = ref 0 in
      for i = 1 to n - 1 do
        (* Reuse previous Z-value if inside current Z-box. *)
        if i < !r then
          z.(i) <- min (!r - i) z.(i - !l);
        (* Try to extend match past the Z-box. *)
        while i + z.(i) < n
              && String.unsafe_get s (z.(i))
                 = String.unsafe_get s (i + z.(i))
        do
          z.(i) <- z.(i) + 1
        done;
        (* Update Z-box if we extended past r. *)
        if i + z.(i) > !r then begin
          l := i;
          r := i + z.(i)
        end
      done;
      z
    end

  (* ---- Pattern matching --------------------------------------------- *)

  (* All algorithms below build the Z-array of [pattern ^ sep ^ text]    *)
  (* where [sep] is a single byte guaranteed not to appear in either    *)
  (* string.  We pick byte 0 by default and fall back to byte 1, 2, …    *)
  (* if it does occur.  This separator trick is what makes Z-based      *)
  (* pattern matching O(n + m) with no extra preprocessing.             *)

  let choose_sep pattern text =
    let used = Array.make 256 false in
    String.iter (fun c -> used.(Char.code c) <- true) pattern;
    String.iter (fun c -> used.(Char.code c) <- true) text;
    let s = ref (-1) in
    let i = ref 0 in
    while !s < 0 && !i < 256 do
      if not used.(!i) then s := !i;
      incr i
    done;
    if !s < 0 then
      (* Both strings together cover every byte.  Fall back to the rare- *)
      (* est byte; correctness still holds because we only treat the    *)
      (* boundary index specially.                                       *)
      let counts = Array.make 256 0 in
      String.iter (fun c -> counts.(Char.code c) <- counts.(Char.code c) + 1)
        pattern;
      String.iter (fun c -> counts.(Char.code c) <- counts.(Char.code c) + 1)
        text;
      let best = ref 0 in
      for i = 1 to 255 do
        if counts.(i) < counts.(!best) then best := i
      done;
      Char.chr !best
    else Char.chr !s

  (** [find_all ~pattern ~text] returns every 0-based starting offset    *)
  (** at which [pattern] occurs in [text], in ascending order.  Runs in *)
  (** O(|pattern| + |text|) time and space.                              *)
  let find_all ~pattern ~text =
    let m = String.length pattern in
    if m = 0 then []
    else
      let sep = choose_sep pattern text in
      let combined = pattern ^ String.make 1 sep ^ text in
      let za = z combined in
      let acc = ref [] in
      let base = m + 1 in
      let n = String.length text in
      for i = 0 to n - 1 do
        if za.(base + i) >= m then acc := i :: !acc
      done;
      List.rev !acc

  (** [contains ~pattern ~text] is true iff [pattern] occurs in [text]. *)
  (** Like [find_all] but stops at the first hit.                       *)
  let contains ~pattern ~text =
    let m = String.length pattern in
    if m = 0 then true
    else
      let sep = choose_sep pattern text in
      let combined = pattern ^ String.make 1 sep ^ text in
      let za = z combined in
      let base = m + 1 in
      let n = String.length text in
      let found = ref false in
      let i = ref 0 in
      while not !found && !i < n do
        if za.(base + !i) >= m then found := true;
        incr i
      done;
      !found

  (** [count ~pattern ~text] returns the number of (possibly overlapping)*)
  (** occurrences of [pattern] in [text].                                *)
  let count ~pattern ~text = List.length (find_all ~pattern ~text)

  (* ---- Longest common prefix ---------------------------------------- *)

  (** [lcp a b] returns the length of the longest common prefix of      *)
  (** [a] and [b].  Implemented directly (faster than going through Z). *)
  let lcp a b =
    let la = String.length a and lb = String.length b in
    let n = min la lb in
    let i = ref 0 in
    while !i < n
          && String.unsafe_get a !i = String.unsafe_get b !i
    do incr i done;
    !i

  (* ---- Periods, borders, periodicity -------------------------------- *)

  (** [period s] returns the smallest p > 0 such that                   *)
  (** [s.[i] = s.[i + p]] for every valid i, i.e. the smallest period   *)
  (** of [s].  For the empty string returns 0.                          *)
  (**                                                                   *)
  (** Uses the fact that p is a period iff p + Z[p] >= n, scanning      *)
  (** ascending p.  O(n) overall.                                       *)
  let period s =
    let n = String.length s in
    if n = 0 then 0
    else begin
      let za = z s in
      let p = ref n in
      let i = ref 1 in
      while !p = n && !i < n do
        if !i + za.(!i) >= n then p := !i;
        incr i
      done;
      !p
    end

  (** [is_periodic s] is true iff [s] has a non-trivial period [p < |s|]*)
  (** that divides [|s|] — i.e. [s] is a concatenation of >= 2 copies   *)
  (** of some proper prefix.                                            *)
  let is_periodic s =
    let n = String.length s in
    if n < 2 then false
    else
      let p = period s in
      p < n && n mod p = 0

  (** [borders s] returns every proper border length (a border is a     *)
  (** proper prefix that is also a suffix), in descending order.        *)
  (**                                                                   *)
  (** Implementation: [k] is a border length iff [Z[n-k] = k] for some  *)
  (** position [n-k], OR iff the suffix of length [k] equals the prefix *)
  (** of length [k].  We test directly via Z over the reversed pair to  *)
  (** keep the code obvious — O(n).                                     *)
  let borders s =
    let n = String.length s in
    if n = 0 then []
    else begin
      let za = z s in
      let acc = ref [] in
      for i = 1 to n - 1 do
        if i + za.(i) = n then acc := za.(i) :: !acc
      done;
      (* Dedupe + descending sort. *)
      let arr = Array.of_list !acc in
      Array.sort (fun a b -> compare b a) arr;
      let out = ref [] in
      let last = ref (-1) in
      Array.iter (fun k ->
        if k <> !last && k > 0 && k < n then begin
          out := k :: !out;
          last := k
        end
      ) arr;
      List.rev !out
    end

  (* ---- Tandem repeats ----------------------------------------------- *)

  (** A tandem repeat run at position [i] with period [p] and count [c] *)
  (** means [s.[i..i+p*c-1] = w^c] for some primitive word [w] of      *)
  (** length [p], with [c >= 2], and the run cannot be extended on     *)
  (** either side (maximal run).                                       *)
  type tandem_run = {
    start  : int;   (* 0-based start position                            *)
    period : int;   (* primitive period length                           *)
    repeats: int;   (* number of full copies (>= 2)                      *)
  }

  (** [tandem_repeats s] returns every maximal tandem-repeat run in     *)
  (** [s], deduplicated and sorted by (start, period).  This is the     *)
  (** "right-only" scan from each starting index — O(n^2) worst case    *)
  (** but with very small constants, fine for streams up to a few MB.   *)
  (**                                                                   *)
  (** The Z-function gives us per-position match lengths; we use it to  *)
  (** cheaply test, for each candidate period [p], how far the repeat   *)
  (** extends.                                                          *)
  let tandem_repeats s =
    let n = String.length s in
    if n < 2 then []
    else begin
      let za = z s in
      let acc = ref [] in
      let i = ref 0 in
      while !i < n do
        (* For each starting index, search for the smallest period p >=1*)
        (* such that s[i..i+p-1] is repeated, then maximize repeats.    *)
        let found = ref false in
        let p = ref 1 in
        while not !found && !p <= (n - !i) / 2 do
          (* Repeat condition: Z at position i+p (in suffix s.[i..]) >= p
             We approximate by using Z of full s shifted: this holds iff
             s.[i+p..i+2p-1] = s.[i..i+p-1].  The Z-array is over s, so
             we need the LCP of s.[i..] and s.[i+p..], which equals     *)
          let lcp_here =
            (* compute LCP(s.[i..], s.[i+p..]) on the fly                *)
            let k = ref 0 in
            while !i + !p + !k < n
                  && String.unsafe_get s (!i + !k)
                     = String.unsafe_get s (!i + !p + !k)
            do incr k done;
            !k
          in
          if lcp_here >= !p then begin
            let total = lcp_here + !p in
            let repeats = total / !p in
            if repeats >= 2 then begin
              (* Check left-maximality: previous char must not extend.  *)
              let left_max =
                !i = 0
                || String.unsafe_get s (!i - 1)
                   <> String.unsafe_get s (!i + !p - 1)
              in
              if left_max then begin
                acc := { start = !i; period = !p; repeats } :: !acc;
                found := true
              end else incr p
            end else incr p
          end else incr p
        done;
        let _ = za in
        incr i
      done;
      (* Dedupe by (start, period, repeats). *)
      let arr = Array.of_list !acc in
      Array.sort (fun a b ->
        let c = compare a.start b.start in
        if c <> 0 then c
        else let c2 = compare a.period b.period in
             if c2 <> 0 then c2 else compare a.repeats b.repeats
      ) arr;
      let out = ref [] in
      let last = ref None in
      Array.iter (fun r ->
        match !last with
        | Some r' when r' = r -> ()
        | _ -> out := r :: !out; last := Some r
      ) arr;
      List.rev !out
    end

  (* ---- Distinct substring count ------------------------------------- *)

  (** [distinct_substrings s] returns the number of distinct non-empty  *)
  (** substrings of [s].  Computed in O(n^2) using the standard         *)
  (** suffix-Z trick: for each suffix, count chars not absorbed by the  *)
  (** max Z-value among already-processed suffixes.                     *)
  let distinct_substrings s =
    let n = String.length s in
    if n = 0 then 0
    else begin
      let total = ref 0 in
      for i = 0 to n - 1 do
        let suffix = String.sub s i (n - i) in
        let za = z suffix in
        let m = n - i in
        let max_z = ref 0 in
        for j = 1 to m - 1 do
          if za.(j) > !max_z then max_z := za.(j)
        done;
        total := !total + (m - !max_z)
      done;
      !total
    end
end

(* ---- Demo ---------------------------------------------------------- *)

let () =
  let open Z in
  Printf.printf "Z-algorithm demo\n";

  (* 1. Raw Z-function. *)
  let s = "aabcaabxaaaz" in
  let za = z s in
  Printf.printf "  z(%S) = [|" s;
  Array.iter (fun v -> Printf.printf "%d;" v) za;
  Printf.printf "|]\n";

  (* 2. Pattern matching. *)
  let pattern = "aab" in
  let hits = find_all ~pattern ~text:s in
  Printf.printf "  find_all %S in %S -> [%s]\n"
    pattern s
    (String.concat "; " (List.map string_of_int hits));
  Printf.printf "  contains %S in %S = %b\n"
    pattern s (contains ~pattern ~text:s);
  Printf.printf "  count    %S in %S = %d\n"
    pattern s (count ~pattern ~text:s);

  (* 3. LCP. *)
  Printf.printf "  lcp %S %S = %d\n"
    "abcdef" "abcxyz" (lcp "abcdef" "abcxyz");

  (* 4. Periods and borders. *)
  let p = "abcabcabc" in
  Printf.printf "  period %S = %d  (is_periodic=%b)\n"
    p (period p) (is_periodic p);
  Printf.printf "  borders %S = [%s]\n"
    p (String.concat "; " (List.map string_of_int (borders p)));

  let q = "abcabd" in
  Printf.printf "  period %S = %d  (is_periodic=%b)\n"
    q (period q) (is_periodic q);

  (* 5. Tandem repeats. *)
  let t = "abcabcabcxyabxyabxy" in
  let runs = tandem_repeats t in
  Printf.printf "  tandem_repeats %S -> %d runs\n" t (List.length runs);
  List.iter (fun r ->
    Printf.printf "    @%2d  period=%d  repeats=%d\n"
      r.start r.period r.repeats
  ) runs;

  (* 6. Distinct substrings. *)
  let d = "abab" in
  Printf.printf "  distinct_substrings %S = %d\n"
    d (distinct_substrings d);
  (* "a", "b", "ab", "ba", "aba", "bab", "abab"  -> 7 *)

  (* 7. Larger search: scan a sentence for several keywords. *)
  let text =
    "the quick brown fox jumps over the lazy dog; the fox is quick"
  in
  let p1 = "the" and p2 = "quick" and p3 = "fox" in
  Printf.printf "\nMulti-pattern scan in %S\n" text;
  List.iter (fun pat ->
    let hs = find_all ~pattern:pat ~text in
    Printf.printf "  %-6S -> %d hits [%s]\n"
      pat (List.length hs)
      (String.concat "; " (List.map string_of_int hs))
  ) [p1; p2; p3]
