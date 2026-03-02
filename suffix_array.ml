(* suffix_array.ml — Suffix Array with LCP array *)
(* Demonstrates: string algorithms, sorting, arrays, functional programming *)
(* A suffix array is a sorted array of all suffixes of a string.
   Combined with the LCP (Longest Common Prefix) array, it enables
   efficient string searching, pattern matching, and substring queries.

   Applications:
   - Full-text search (O(m log n) pattern matching)
   - Finding longest repeated substrings
   - Counting distinct substrings
   - Bioinformatics (genome sequence analysis)
   - Data compression (BWT transform)

   This implementation uses:
   - O(n log^2 n) suffix array construction via comparison sort with
     rank pairs
   - O(n) Kasai's algorithm for LCP array computation
   - O(m log n) binary search for pattern matching *)

(* --- Suffix Array Construction --- *)

(* Build a suffix array for the given string.
   Returns an int array where sa.(i) is the starting index of the
   i-th lexicographically smallest suffix. *)
let build text =
  let n = String.length text in
  if n = 0 then [||]
  else begin
    let sa = Array.init n Fun.id in
    let rank = Array.init n (fun i -> Char.code text.[i]) in
    let tmp = Array.make n 0 in
    let k = ref 1 in
    let sorted = ref false in
    while not !sorted && !k < n do
      let kk = !k in
      let cmp a b =
        let c = compare rank.(a) rank.(b) in
        if c <> 0 then c
        else
          let ra = if a + kk < n then rank.(a + kk) else (-1) in
          let rb = if b + kk < n then rank.(b + kk) else (-1) in
          compare ra rb
      in
      Array.sort cmp sa;
      tmp.(sa.(0)) <- 0;
      for i = 1 to n - 1 do
        tmp.(sa.(i)) <-
          tmp.(sa.(i - 1)) + (if cmp sa.(i - 1) sa.(i) <> 0 then 1 else 0)
      done;
      Array.blit tmp 0 rank 0 n;
      if rank.(sa.(n - 1)) = n - 1 then sorted := true;
      k := kk * 2
    done;
    sa
  end

(* --- LCP Array (Kasai's Algorithm) --- *)

(* Compute the LCP (Longest Common Prefix) array.
   lcp.(i) = length of the longest common prefix between
   the i-th and (i-1)-th suffixes in sorted order.
   lcp.(0) is always 0. *)
let build_lcp text sa =
  let n = String.length text in
  if n = 0 then [||]
  else begin
    let lcp = Array.make n 0 in
    let pos = Array.make n 0 in
    Array.iteri (fun i s -> pos.(s) <- i) sa;
    let h = ref 0 in
    for i = 0 to n - 1 do
      if pos.(i) > 0 then begin
        let j = sa.(pos.(i) - 1) in
        while i + !h < n && j + !h < n && text.[i + !h] = text.[j + !h] do
          incr h
        done;
        lcp.(pos.(i)) <- !h;
        if !h > 0 then decr h
      end else
        h := 0
    done;
    lcp
  end

(* --- Pattern Matching --- *)

(* Compare pattern against suffix starting at position s in text.
   Returns negative if pattern < suffix, 0 if suffix starts with
   pattern, positive if pattern > suffix. *)
let compare_suffix text s pattern =
  let plen = String.length pattern in
  let tlen = String.length text in
  let rec loop i =
    if i >= plen then 0
    else if s + i >= tlen then 1
    else
      let c = compare (Char.code pattern.[i]) (Char.code text.[s + i]) in
      if c <> 0 then c
      else loop (i + 1)
  in
  loop 0

(* Find the leftmost position in sa where pattern could match. *)
let lower_bound text sa pattern =
  let n = Array.length sa in
  let lo = ref 0 in
  let hi = ref n in
  while !lo < !hi do
    let mid = !lo + (!hi - !lo) / 2 in
    let c = compare_suffix text sa.(mid) pattern in
    if c > 0 then lo := mid + 1
    else hi := mid
  done;
  !lo

(* Find one past the rightmost position in sa where pattern matches. *)
let upper_bound text sa pattern =
  let n = Array.length sa in
  let lo = ref 0 in
  let hi = ref n in
  while !lo < !hi do
    let mid = !lo + (!hi - !lo) / 2 in
    let c = compare_suffix text sa.(mid) pattern in
    if c > 0 then lo := mid + 1
    else if c < 0 then hi := mid
    else lo := mid + 1
  done;
  !lo

(* Find all occurrences of pattern in text using the suffix array.
   Returns a sorted list of starting positions. O(m log n) *)
let search text sa pattern =
  let plen = String.length pattern in
  let n = Array.length sa in
  if plen = 0 || n = 0 then []
  else begin
    let lo = lower_bound text sa pattern in
    let hi = upper_bound text sa pattern in
    let results = ref [] in
    for i = lo to hi - 1 do
      results := sa.(i) :: !results
    done;
    List.sort compare !results
  end

(* Count occurrences of pattern. O(m log n) *)
let count text sa pattern =
  let plen = String.length pattern in
  let n = Array.length sa in
  if plen = 0 || n = 0 then 0
  else upper_bound text sa pattern - lower_bound text sa pattern

(* Check if pattern exists in text. O(m log n) *)
let contains text sa pattern =
  count text sa pattern > 0

(* --- Substring Queries --- *)

(* Find the longest repeated substring in the text.
   Returns (substring, position, length) or None if no repetition. *)
let longest_repeated_substring text sa lcp =
  let n = Array.length lcp in
  if n <= 1 then None
  else begin
    let max_len = ref 0 in
    let max_pos = ref 0 in
    for i = 1 to n - 1 do
      if lcp.(i) > !max_len then begin
        max_len := lcp.(i);
        max_pos := sa.(i)
      end
    done;
    if !max_len = 0 then None
    else Some (String.sub text !max_pos !max_len, !max_pos, !max_len)
  end

(* Count the number of distinct substrings in the text.
   Uses the formula: n*(n+1)/2 - sum(lcp) *)
let count_distinct_substrings text _sa lcp =
  let n = String.length text in
  if n = 0 then 0
  else begin
    let total = n * (n + 1) / 2 in
    let lcp_sum = Array.fold_left ( + ) 0 lcp in
    total - lcp_sum
  end

(* Find the k-th lexicographically smallest distinct substring.
   Returns None if k is out of range (1-indexed). *)
let kth_substring text sa lcp k =
  let n = Array.length sa in
  if k < 1 || n = 0 then None
  else begin
    let remaining = ref k in
    let result = ref None in
    let i = ref 0 in
    while !i < n && !result = None do
      let suf_len = String.length text - sa.(!i) in
      let new_count = suf_len - lcp.(!i) in
      if !remaining <= new_count then begin
        let len = lcp.(!i) + !remaining in
        result := Some (String.sub text sa.(!i) len)
      end else
        remaining := !remaining - new_count;
      incr i
    done;
    !result
  end

(* --- Burrows-Wheeler Transform --- *)

(* Compute the BWT string from the suffix array.
   bwt[i] = text[(sa[i] - 1 + n) mod n] *)
let bwt text sa =
  let n = String.length text in
  String.init n (fun i ->
    let j = (sa.(i) - 1 + n) mod n in
    text.[j])

(* --- Pretty Printing --- *)

let pp text sa =
  let n = Array.length sa in
  Printf.printf "Suffix Array (%d suffixes):\n" n;
  Printf.printf "  %4s  %4s  %s\n" "Rank" "Pos" "Suffix";
  Printf.printf "  %s\n" (String.make 50 '-');
  for i = 0 to n - 1 do
    let suf = String.sub text sa.(i) (String.length text - sa.(i)) in
    let display = if String.length suf > 40
      then String.sub suf 0 37 ^ "..."
      else suf in
    Printf.printf "  %4d  %4d  %s\n" i sa.(i) display
  done

let pp_with_lcp text sa lcp =
  let n = Array.length sa in
  Printf.printf "Suffix Array with LCP (%d suffixes):\n" n;
  Printf.printf "  %4s  %4s  %4s  %s\n" "Rank" "Pos" "LCP" "Suffix";
  Printf.printf "  %s\n" (String.make 55 '-');
  for i = 0 to n - 1 do
    let suf = String.sub text sa.(i) (String.length text - sa.(i)) in
    let display = if String.length suf > 36
      then String.sub suf 0 33 ^ "..."
      else suf in
    Printf.printf "  %4d  %4d  %4d  %s\n" i sa.(i) lcp.(i) display
  done
