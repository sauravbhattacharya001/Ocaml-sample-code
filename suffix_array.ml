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

(** Suffix array with LCP array, BWT, and generalized multi-string
    queries.

    A suffix array is a sorted array of all suffixes of a string,
    represented as the array of their starting indices. Combined with
    the longest-common-prefix (LCP) array it powers efficient
    full-text search, longest-repeated-substring queries, distinct
    substring counting, longest common substring of K strings, and a
    sentinel-based Burrows-Wheeler transform.

    Complexity summary:
    - {!build}: O(n log^2 n) via comparison sort with rank pairs.
    - {!build_lcp}: O(n) via Kasai's algorithm.
    - Pattern matching ({!search} / {!count} / {!contains}): O(m log n). *)

(* --- Suffix Array Construction --- *)

(** [build text] returns the suffix array of [text]: an int array [sa]
    where [sa.(i)] is the starting index of the i-th
    lexicographically smallest suffix. Returns [\[||\]] for the empty
    string. O(n log^2 n). *)
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

(** [build_lcp text sa] computes the LCP (Longest Common Prefix)
    array, where [lcp.(i)] is the length of the longest common prefix
    between the i-th and (i-1)-th suffixes in sorted order.
    [lcp.(0)] is always 0. O(n) via Kasai's algorithm. *)
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

(** [compare_suffix text s pattern] compares [pattern] against the
    suffix of [text] starting at [s]. Returns a negative integer if
    [pattern] is strictly less than the suffix, [0] if the suffix
    starts with [pattern], and a positive integer otherwise. *)
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

(** [lower_bound text sa pattern] returns the leftmost index in [sa]
    at which [pattern] could match (i.e. the first suffix that is not
    strictly less than [pattern]). O(m log n). *)
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

(** [upper_bound text sa pattern] returns one past the rightmost
    index in [sa] at which [pattern] matches (i.e. the first suffix
    that is strictly greater than [pattern]). O(m log n). *)
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

(** [search text sa pattern] returns every starting position of
    [pattern] in [text] (via the suffix array [sa]), sorted in
    ascending order. O(m log n + occ). Returns [\[\]] for an empty
    pattern or empty text. *)
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

(** [count text sa pattern] returns the number of occurrences of
    [pattern] in [text] using the precomputed suffix array. O(m log n). *)
let count text sa pattern =
  let plen = String.length pattern in
  let n = Array.length sa in
  if plen = 0 || n = 0 then 0
  else upper_bound text sa pattern - lower_bound text sa pattern

(** [contains text sa pattern] is [true] iff [pattern] occurs in
    [text]. O(m log n). *)
let contains text sa pattern =
  count text sa pattern > 0

(* --- Substring Queries --- *)

(** [longest_repeated_substring text sa lcp] returns
    [Some (substring, position, length)] for the longest substring of
    [text] that occurs at least twice, or [None] if no character is
    repeated. The position is one specific occurrence of the
    repeated substring (not necessarily the leftmost). O(n). *)
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

(** [count_distinct_substrings text sa lcp] returns the number of
    distinct non-empty substrings of [text], computed in O(n) as
    [n * (n + 1) / 2 - sum lcp]. *)
let count_distinct_substrings text _sa lcp =
  let n = String.length text in
  if n = 0 then 0
  else begin
    let total = n * (n + 1) / 2 in
    let lcp_sum = Array.fold_left ( + ) 0 lcp in
    total - lcp_sum
  end

(** [kth_substring text sa lcp k] returns [Some s] where [s] is the
    [k]-th lexicographically smallest distinct non-empty substring of
    [text] (1-indexed), or [None] if [k] is out of range. *)
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

(** [bwt text sa] returns the cyclic Burrows-Wheeler transform of
    [text] derived from its suffix array: [bwt.\[i\] = text.\[(sa.(i) - 1 + n) mod n\]].
    Note: this cyclic variant requires the primary index to invert.
    For an exactly invertible BWT see {!bwt_with_sentinel}. *)
let bwt text sa =
  let n = String.length text in
  String.init n (fun i ->
    let j = (sa.(i) - 1 + n) mod n in
    text.[j])

(** [bwt_with_sentinel text] computes the sentinel-based BWT used by
    bzip2-style pipelines and FM-indexes. It appends a byte strictly
    smaller than every byte already in [text] (chosen from the unused
    range [0..254]) and returns [(sentinel, bwt)] where [bwt] is the
    transform over [text ^ sentinel]. The result is exactly
    invertible by {!inverse_bwt} without a primary index.

    @raise Invalid_argument if every byte in [0..254] already appears
    in [text] (no free byte for the sentinel). *)
let bwt_with_sentinel text =
  let n = String.length text in
  if n = 0 then (Char.chr 0, "")
  else begin
    let used = Array.make 256 false in
    String.iter (fun c -> used.(Char.code c) <- true) text;
    let sentinel = ref (-1) in
    (try
       for c = 0 to 254 do
         if not used.(c) then (sentinel := c; raise Exit)
       done
     with Exit -> ());
    if !sentinel < 0 then
      invalid_arg
        "Suffix_array.bwt_with_sentinel: no free byte value for sentinel";
    let sep = Char.chr !sentinel in
    let augmented = text ^ String.make 1 sep in
    let sa = build augmented in
    let m = n + 1 in
    let b = String.init m (fun i ->
      let j = sa.(i) in
      if j = 0 then sep else augmented.[j - 1])
    in
    (sep, b)
  end

(** [inverse_bwt sentinel bwt] inverts a sentinel-tagged BWT produced
    by {!bwt_with_sentinel}. The sentinel byte is stripped before
    returning, so [inverse_bwt sep (snd (bwt_with_sentinel s)) = s]
    for any [s] that has at least one free byte value. O(n + sigma).

    @raise Invalid_argument if [sentinel] does not occur in [bwt]. *)
let inverse_bwt sentinel bwt =
  let n = String.length bwt in
  if n = 0 then ""
  else begin
    let count = Array.make 257 0 in
    for i = 0 to n - 1 do
      count.(Char.code bwt.[i] + 1) <- count.(Char.code bwt.[i] + 1) + 1
    done;
    for i = 1 to 256 do count.(i) <- count.(i) + count.(i - 1) done;
    let lf = Array.make n 0 in
    let cursor = Array.copy count in
    for i = 0 to n - 1 do
      let c = Char.code bwt.[i] in
      lf.(i) <- cursor.(c);
      cursor.(c) <- cursor.(c) + 1
    done;
    (* Start the walk at the unique row whose BWT character is the
       sentinel: that row corresponds to the suffix beginning at position 0
       of the augmented string, so walking backwards reproduces
       [text ^ sentinel] character by character. *)
    let start =
      let rec find i =
        if i >= n then
          invalid_arg "Suffix_array.inverse_bwt: sentinel not found in input"
        else if bwt.[i] = sentinel then i
        else find (i + 1)
      in find 0
    in
    let buf = Bytes.create n in
    let j = ref start in
    for i = n - 1 downto 0 do
      Bytes.set buf i bwt.[!j];
      j := lf.(!j)
    done;
    let raw = Bytes.unsafe_to_string buf in
    (* The construction guarantees the trailing byte is the sentinel. *)
    if n > 0 && raw.[n - 1] = sentinel then String.sub raw 0 (n - 1)
    else raw
  end

(* --- Generalized Suffix Array and Multi-string Queries --- *)

(* Internal: pick a 1-byte separator strictly smaller than every byte in
   [strings]. Raises [Invalid_argument] if every byte 0..254 is used. *)
let pick_separators strings =
  let used = Array.make 256 false in
  List.iter (String.iter (fun c -> used.(Char.code c) <- true)) strings;
  let seps = ref [] in
  let needed = List.length strings in
  let i = ref 0 in
  while List.length !seps < needed && !i < 256 do
    if not used.(!i) then seps := Char.chr !i :: !seps;
    incr i
  done;
  if List.length !seps < needed then
    invalid_arg
      "Suffix_array: no free byte values available to separate inputs; \
       reserve at least N low bytes (e.g. \\001..\\00N) outside your input";
  List.rev !seps

(** [generalized_build strings] builds a generalized suffix array
    over a list of input strings.

    Each input is joined into a single text with a unique low-byte
    separator that does not occur in any input. Returns the tuple:
    - [concat]: the joined text (with separators interleaved);
    - [sa]: the suffix array over [concat];
    - [lcp]: the LCP array over [sa];
    - [owner]: [owner.(p)] is the 0-based index of the source string
      that position [p] in [concat] belongs to, or [-1] for separator
      positions;
    - [offset]: [offset.(p)] is the position within its source
      string, or [-1] for separator positions.

    Empty strings in the input list are filtered out.

    @raise Invalid_argument if there are not enough free byte values
    in [0..255] to assign one unique separator per input. *)
let generalized_build strings =
  let strings = List.filter (fun s -> String.length s > 0) strings in
  match strings with
  | [] ->
    let empty = [||] in ("", empty, empty, empty, empty)
  | _ ->
    let seps = pick_separators strings in
    let buf = Buffer.create 64 in
    List.iter2 (fun s sep ->
      Buffer.add_string buf s;
      Buffer.add_char buf sep
    ) strings seps;
    let concat = Buffer.contents buf in
    let n = String.length concat in
    let owner = Array.make n (-1) in
    let offset = Array.make n (-1) in
    let p = ref 0 in
    List.iteri (fun id s ->
      let len = String.length s in
      for j = 0 to len - 1 do
        owner.(!p + j) <- id;
        offset.(!p + j) <- j
      done;
      p := !p + len + 1 (* skip separator *)
    ) strings;
    let sa = build concat in
    let lcp = build_lcp concat sa in
    (concat, sa, lcp, owner, offset)

(** [longest_common_substring_k strings] returns
    [Some (substring, positions)] where [substring] is a longest
    substring that occurs in every input string and [positions.(i)]
    is its start index inside the i-th input (matching the input
    order). Returns [None] if [strings] is empty, contains an empty
    string, or the inputs share no common substring.

    Runs in O(N) over total input length (modulo the
    suffix-array build, which dominates). *)
let longest_common_substring_k strings =
  let k = List.length strings in
  if k = 0 then None
  else if List.exists (fun s -> String.length s = 0) strings then None
  else if k = 1 then
    let s = List.hd strings in Some (s, [0])
  else begin
    let (concat, sa, lcp, owner, offset) = generalized_build strings in
    let n = Array.length sa in
    (* Sliding window over sa indices, tracking owners covered. *)
    let counts = Array.make k 0 in
    let distinct = ref 0 in
    let window_min = ref [] in (* monotonic deque of (idx, lcp_value) *)
    let best_len = ref 0 in
    let best_sa_idx = ref (-1) in
    let l = ref 0 in
    let add_owner o =
      if o >= 0 then begin
        if counts.(o) = 0 then incr distinct;
        counts.(o) <- counts.(o) + 1
      end
    in
    let remove_owner o =
      if o >= 0 then begin
        counts.(o) <- counts.(o) - 1;
        if counts.(o) = 0 then decr distinct
      end
    in
    (* push lcp.(i) into the monotonic deque covering window (l+1..r) *)
    let push_lcp i v =
      let rec drop = function
        | (_, w) :: rest when w >= v -> drop rest
        | xs -> xs
      in
      window_min := (i, v) :: drop !window_min
    in
    let pop_lcp_before threshold =
      window_min :=
        List.filter (fun (i, _) -> i > threshold) !window_min
    in
    let window_min_value () =
      match List.rev !window_min with
      | [] -> 0
      | (_, v) :: _ -> v
    in
    for r = 0 to n - 1 do
      add_owner owner.(sa.(r));
      if r > 0 then push_lcp r lcp.(r);
      while !distinct = k && !l < r do
        let len = window_min_value () in
        if len > !best_len then begin
          best_len := len;
          best_sa_idx := !l
        end;
        remove_owner owner.(sa.(!l));
        incr l;
        pop_lcp_before !l
      done
    done;
    if !best_len = 0 then None
    else begin
      let start = sa.(!best_sa_idx) in
      let substr = String.sub concat start !best_len in
      (* For each input string, locate the substring. Use the owner/offset
         arrays plus the SA window to find concrete positions. *)
      let positions = Array.make k (-1) in
      for i = 0 to n - 1 do
        let p = sa.(i) in
        let o = owner.(p) in
        if o >= 0 && positions.(o) < 0 then begin
          let s = List.nth strings o in
          let slen = String.length s in
          let off = offset.(p) in
          if off + !best_len <= slen &&
             String.sub concat p !best_len = substr
          then positions.(o) <- off
        end
      done;
      if Array.exists (fun x -> x < 0) positions then None
      else Some (substr, Array.to_list positions)
    end
  end

(** [longest_common_substring a b] returns
    [Some (substring, pos_in_a, pos_in_b)] for a longest common
    substring of [a] and [b], or [None] if they share no character.
    Convenience wrapper over {!longest_common_substring_k}. *)
let longest_common_substring a b =
  match longest_common_substring_k [a; b] with
  | Some (s, [pa; pb]) -> Some (s, pa, pb)
  | _ -> None

(* --- Pretty Printing --- *)

(** [pp text sa] prints the suffix array of [text] in human-readable
    form: rank, position, and a truncated rendering of each suffix. *)
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

(** [pp_with_lcp text sa lcp] prints the suffix array of [text]
    alongside its LCP array. Suffixes are truncated to fit. *)
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
