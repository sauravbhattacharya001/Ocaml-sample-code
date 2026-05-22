(* ============================================================
   Manacher's Algorithm — Linear-time Palindrome Analysis

   Given a string s of length n, Manacher's algorithm finds the
   maximum palindromic radius around every center in O(n) time.
   Centers are taken over a transformed string with a sentinel
   character ('#') inserted between every original character so
   that even-length and odd-length palindromes are handled
   uniformly: position 2*i in the transform corresponds to the
   gap to the left of s.[i], position 2*i+1 corresponds to
   s.[i] itself.

   This module exposes the raw radii array along with a small
   library of palindrome utilities built on top of it:

     - radii            : the per-center radius array (transform)
     - longest          : longest palindromic substring of s
     - all_maximal      : every maximal palindrome (start,length)
     - count            : total number of palindromic substrings
     - count_distinct   : number of distinct palindromic substrings
     - is_palindrome    : O(1) lookup for any (start,length) slice
     - contains_palindrome_at_least : earliest palindrome of len>=k

   All operations after the initial O(n) preprocessing answer in
   O(1) for is_palindrome queries and O(n) for the bulk queries.
   ============================================================ *)

(** Manacher's algorithm: linear-time palindrome analysis.

    Given a string [s], computes the maximum palindromic radius around
    every center of [s] in O(|s|) time, then exposes a small library of
    palindrome utilities built on that radii array.

    The implementation uses the classic transform trick: insert '#'
    between every original character and pad the ends with distinct
    sentinels '^' and '$' so even-length and odd-length palindromes are
    handled uniformly. *)

(* ---- Core algorithm ---- *)

(** [transform s] returns the sentinel-padded transform
    ["^#a#b#c#$"] (for [s = "abc"]) used internally by Manacher. The
    distinct end sentinels ['^'] and ['$'] terminate the expansion
    loop without explicit bounds checks. *)
let transform (s : string) : string =
  let n = String.length s in
  let buf = Buffer.create ((2 * n) + 3) in
  Buffer.add_char buf '^';
  for i = 0 to n - 1 do
    Buffer.add_char buf '#';
    Buffer.add_char buf s.[i]
  done;
  Buffer.add_char buf '#';
  Buffer.add_char buf '$';
  Buffer.contents buf

(** [radii s] runs Manacher's main loop and returns the radii array
    [p] for the {!transform}ed string [t], where [p.(i)] is the
    largest [r] such that [t.\[i - r .. i + r\]] is a palindrome.
    Total cost O(|s|). *)
let radii (s : string) : int array =
  let t = transform s in
  let n = String.length t in
  let p = Array.make n 0 in
  let center = ref 0 in
  let right = ref 0 in
  for i = 1 to n - 2 do
    let mirror = (2 * !center) - i in
    if i < !right then
      p.(i) <- min (!right - i) p.(mirror);
    (* Attempt to expand around i. The sentinels '^' and '$' make
       this loop self-terminating without explicit bounds checks. *)
    while t.[i + p.(i) + 1] = t.[i - p.(i) - 1] do
      p.(i) <- p.(i) + 1
    done;
    if i + p.(i) > !right then begin
      center := i;
      right := i + p.(i)
    end
  done;
  p

(* ---- Derived queries ---- *)

(** [longest s] returns [(start, length)] for the longest palindromic
    substring of [s]. On ties, the leftmost occurrence wins
    (deterministic). Returns [(0, 0)] for the empty string. *)
let longest (s : string) : int * int =
  if String.length s = 0 then (0, 0)
  else begin
    let p = radii s in
    let best_center = ref 0 in
    let best_len = ref 0 in
    for i = 1 to Array.length p - 2 do
      if p.(i) > !best_len then begin
        best_len := p.(i);
        best_center := i
      end
    done;
    (* Map transformed center back to original string. *)
    let start = (!best_center - !best_len) / 2 in
    (start, !best_len)
  end

(** [longest_substring s] returns the longest palindromic substring of
    [s] as a fresh string (the [(start, length)] slice produced by
    {!longest}). *)
let longest_substring (s : string) : string =
  let (start, len) = longest s in
  String.sub s start len

(** [all_maximal s] returns every maximal palindrome in [s] (one that
    cannot be extended on either side while remaining a palindrome) as
    [(start, length)] pairs, sorted by [start] ascending and then by
    [length] descending. Single-character palindromes are included
    only when they are not part of a longer palindrome at the same
    center. *)
let all_maximal (s : string) : (int * int) list =
  if String.length s = 0 then []
  else begin
    let p = radii s in
    let acc = ref [] in
    for i = 1 to Array.length p - 2 do
      if p.(i) > 0 then begin
        let len = p.(i) in
        let start = (i - len) / 2 in
        acc := (start, len) :: !acc
      end
    done;
    List.sort
      (fun (s1, l1) (s2, l2) ->
        if s1 <> s2 then compare s1 s2 else compare l2 l1)
      !acc
  end

(** [count s] returns the total number of palindromic substrings of
    [s] counted with multiplicity (each [(start, length)] occurrence
    counts once, even if the same palindromic string appears at
    multiple positions). Includes single-character palindromes.

    Centers in the transform are weighted [(p.(i) + 1) / 2]: odd
    radii contribute the odd-length palindromes centered on real
    characters, even radii contribute the even-length palindromes
    centered on the gaps between characters. *)
let count (s : string) : int =
  let p = radii s in
  let total = ref 0 in
  for i = 1 to Array.length p - 2 do
    total := !total + ((p.(i) + 1) / 2)
  done;
  !total

(** [count_distinct s] returns the number of {e distinct} palindromic
    substrings of [s]. Uses a [Hashtbl] to stay stdlib-only; an
    Eertree (palindromic tree) would be asymptotically better but
    requires significantly more machinery. *)
let count_distinct (s : string) : int =
  let p = radii s in
  let seen = Hashtbl.create 64 in
  for i = 1 to Array.length p - 2 do
    let r = p.(i) in
    if r > 0 then begin
      (* Enumerate palindromes centered at i with radii r, r-2, r-4, ... *)
      let rr = ref r in
      while !rr > 0 do
        let start = (i - !rr) / 2 in
        let sub = String.sub s start !rr in
        Hashtbl.replace seen sub ();
        rr := !rr - 2
      done
    end
  done;
  Hashtbl.length seen

(** [is_palindrome_at ~radii ~start ~len] is an O(1) lookup that
    returns [true] iff [s.\[start .. start + len - 1\]] is a
    palindrome, where [radii] is the array returned by {!radii} on the
    same original [s]. Returns [false] for out-of-range slices and
    [true] for empty slices.

    Build the [radii] array once and pass it in for repeated queries. *)
let is_palindrome_at ~(radii : int array) ~(start : int) ~(len : int) : bool =
  if len <= 0 then true
  else
    let n_orig = (Array.length radii - 3) / 2 in
    if start < 0 || start + len > n_orig then false
    else
      (* In the transformed string ^#c0#c1#...#cn#$, the center of
         the original slice s[start..start+len) is at index
         2*start + len + 1. The palindrome length in the original
         string equals the transformed radius. *)
      let center = (2 * start) + len + 1 in
      radii.(center) >= len

(** [is_palindrome s] is [true] iff the whole string [s] is a
    palindrome. Strings of length 0 or 1 are trivially palindromic. *)
let is_palindrome (s : string) : bool =
  let n = String.length s in
  if n <= 1 then true
  else
    let r = radii s in
    is_palindrome_at ~radii:r ~start:0 ~len:n

(** [contains_palindrome_at_least s k] returns [Some (start, length)]
    for the leftmost maximal palindrome in [s] whose length is at
    least [k], or [None] if no such palindrome exists. Useful for
    "does this string hide a palindromic run of size k?" detection.
    For [k <= 0] returns [Some (0, 0)]. *)
let contains_palindrome_at_least (s : string) (k : int) : (int * int) option =
  if k <= 0 then Some (0, 0)
  else begin
    let p = radii s in
    let best = ref None in
    let best_start = ref max_int in
    for i = 1 to Array.length p - 2 do
      if p.(i) >= k then begin
        (* Take the full maximal palindrome at this center; its
           start in the original string is the smallest start
           reachable from this center. *)
        let start = (i - p.(i)) / 2 in
        let len = p.(i) in
        if start < !best_start then begin
          best_start := start;
          best := Some (start, len)
        end
      end
    done;
    !best
  end

(* ---- Demo ---- *)

let () =
  let cases = [
    "";
    "a";
    "aa";
    "abc";
    "babad";
    "cbbd";
    "abacdfgdcaba";    (* longest = "aba" (left), not "aba" (right) *)
    "forgeeksskeegfor"; (* longest = "geeksskeeg" *)
    "abacabad";
    "aaaa";
  ] in
  Printf.printf "Manacher's algorithm — palindrome analysis\n";
  Printf.printf "===========================================\n\n";
  List.iter (fun s ->
    let (start, len) = longest s in
    let lp = if len > 0 then String.sub s start len else "" in
    Printf.printf "  %-20S  longest=%S  count=%d  distinct=%d\n"
      s lp (count s) (count_distinct s)
  ) cases;

  Printf.printf "\nMaximal palindromes in %S:\n" "abacabad";
  List.iter (fun (start, len) ->
    Printf.printf "    @%2d len=%d  %S\n" start len
      (String.sub "abacabad" start len)
  ) (all_maximal "abacabad");

  Printf.printf "\nO(1) is_palindrome_at queries on %S:\n" "abacabad";
  let r = radii "abacabad" in
  let queries = [
    (0, 5); (0, 7); (1, 3); (2, 3); (3, 1); (0, 4);
  ] in
  List.iter (fun (start, len) ->
    Printf.printf "    s[%d..%d) (%S) palindrome? %b\n"
      start (start + len)
      (String.sub "abacabad" start len)
      (is_palindrome_at ~radii:r ~start ~len)
  ) queries;

  Printf.printf "\ncontains_palindrome_at_least:\n";
  let scan = "the level of detail in the racecar story was noon" in
  List.iter (fun k ->
    match contains_palindrome_at_least scan k with
    | Some (start, len) ->
      Printf.printf "  k=%d -> @%d len=%d %S\n"
        k start len (String.sub scan start len)
    | None ->
      Printf.printf "  k=%d -> none\n" k
  ) [3; 5; 7; 9; 12]
