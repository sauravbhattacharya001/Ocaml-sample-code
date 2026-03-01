(* rope.ml — Rope Data Structure for Efficient String Operations     *)
(* A rope is a balanced binary tree of strings that provides O(log n) *)
(* concatenation, split, insert, and delete instead of O(n) copies.  *)
(* Used in text editors (e.g., VS Code, Xi editor) for large texts.  *)
(* Supports: concat, index, length, substring, insert, delete,      *)
(* balance, to_string, of_string, split, iter, fold, map, lines,    *)
(* depth, is_balanced, append_char, prepend.                         *)

module Rope = struct

  (** Maximum leaf size before splitting into a tree.
      Smaller = more balanced but more overhead; larger = fewer nodes. *)
  let max_leaf = 512

  (** A rope is either a leaf string or a concatenation of two ropes
      with cached weight (length of left subtree) and total length. *)
  type t =
    | Leaf of string
    | Node of { left: t; right: t; weight: int; len: int; depth: int }

  (* ── Construction ─────────────────────────────────────────────── *)

  (** Empty rope. *)
  let empty = Leaf ""

  (** Create a rope from a string. Splits into a balanced tree if the
      string exceeds [max_leaf]. *)
  let rec of_string s =
    let n = String.length s in
    if n <= max_leaf then Leaf s
    else
      let mid = n / 2 in
      let left = of_string (String.sub s 0 mid) in
      let right = of_string (String.sub s mid (n - mid)) in
      Node { left; right; weight = mid; len = n; depth = 1 + max (depth_of left) (depth_of right) }

  and depth_of = function
    | Leaf _ -> 0
    | Node { depth; _ } -> depth

  (** Length of the rope (total characters). O(1). *)
  let length = function
    | Leaf s -> String.length s
    | Node { len; _ } -> len

  (** Depth of the tree. O(1). *)
  let depth = function
    | Leaf _ -> 0
    | Node { depth; _ } -> depth

  (* ── Concatenation ────────────────────────────────────────────── *)

  (** Concatenate two ropes. O(1). *)
  let concat a b =
    match a, b with
    | Leaf "", r -> r
    | l, Leaf "" -> l
    | _ ->
      let la = length a in
      let lb = length b in
      Node {
        left = a;
        right = b;
        weight = la;
        len = la + lb;
        depth = 1 + max (depth a) (depth b)
      }

  (** Prepend a string to the rope. *)
  let prepend s r = concat (of_string s) r

  (** Append a single character. *)
  let append_char r c = concat r (Leaf (String.make 1 c))

  (* ── Indexing ─────────────────────────────────────────────────── *)

  (** Get the character at position [i]. O(log n).
      @raise Invalid_argument if [i] is out of bounds. *)
  let rec index t i =
    if i < 0 || i >= length t then
      invalid_arg (Printf.sprintf "Rope.index: %d out of bounds (length %d)" i (length t))
    else match t with
    | Leaf s -> s.[i]
    | Node { left; right; weight; _ } ->
      if i < weight then index left i
      else index right (i - weight)

  (* ── Split ────────────────────────────────────────────────────── *)

  (** Split the rope at position [i], returning (left, right) where
      left has [i] characters and right has the rest. O(log n). *)
  let rec split t i =
    if i <= 0 then (empty, t)
    else if i >= length t then (t, empty)
    else match t with
    | Leaf s ->
      (Leaf (String.sub s 0 i), Leaf (String.sub s i (String.length s - i)))
    | Node { left; right; weight; _ } ->
      if i = weight then (left, right)
      else if i < weight then
        let (ll, lr) = split left i in
        (ll, concat lr right)
      else
        let (rl, rr) = split right (i - weight) in
        (concat left rl, rr)

  (* ── Substring ────────────────────────────────────────────────── *)

  (** Extract a substring from position [start] with length [len].
      O(log n) for the splits + O(len) for materialization. *)
  let substring t start len =
    if start < 0 || len < 0 || start + len > length t then
      invalid_arg (Printf.sprintf "Rope.substring: start=%d len=%d out of bounds (length %d)"
        start len (length t))
    else if len = 0 then empty
    else
      let (_, rest) = split t start in
      let (result, _) = split rest len in
      result

  (* ── Insert / Delete ──────────────────────────────────────────── *)

  (** Insert string [s] at position [i]. O(log n). *)
  let insert t i s =
    if i < 0 || i > length t then
      invalid_arg (Printf.sprintf "Rope.insert: %d out of bounds (length %d)" i (length t))
    else
      let (left, right) = split t i in
      concat (concat left (of_string s)) right

  (** Delete [len] characters starting at position [start]. O(log n). *)
  let delete t start len =
    if start < 0 || len < 0 || start + len > length t then
      invalid_arg (Printf.sprintf "Rope.delete: start=%d len=%d out of bounds (length %d)"
        start len (length t))
    else if len = 0 then t
    else
      let (left, rest) = split t start in
      let (_, right) = split rest len in
      concat left right

  (* ── Conversion ───────────────────────────────────────────────── *)

  (** Convert the rope to a flat string. O(n). *)
  let to_string t =
    let buf = Buffer.create (length t) in
    let rec go = function
      | Leaf s -> Buffer.add_string buf s
      | Node { left; right; _ } -> go left; go right
    in
    go t;
    Buffer.contents buf

  (* ── Iteration ────────────────────────────────────────────────── *)

  (** Iterate over each character in order. *)
  let iter f t =
    let rec go = function
      | Leaf s -> String.iter f s
      | Node { left; right; _ } -> go left; go right
    in
    go t

  (** Iterate over each leaf string. More efficient than char iteration. *)
  let iter_leaves f t =
    let rec go = function
      | Leaf s -> if String.length s > 0 then f s
      | Node { left; right; _ } -> go left; go right
    in
    go t

  (** Fold left over characters. *)
  let fold f init t =
    let acc = ref init in
    iter (fun c -> acc := f !acc c) t;
    !acc

  (** Map a function over each character, producing a new rope. *)
  let map f t =
    let rec go = function
      | Leaf s ->
        Leaf (String.init (String.length s) (fun i -> f s.[i]))
      | Node { left; right; _ } ->
        concat (go left) (go right)
    in
    go t

  (* ── Balancing ────────────────────────────────────────────────── *)

  (** Check if the rope is "balanced" — depth is at most 1.5 * log2(leaves). *)
  let is_balanced t =
    let n = length t in
    if n = 0 then true
    else
      let d = float_of_int (depth t) in
      let max_depth = 1.5 *. (log (float_of_int n) /. log 2.0) in
      d <= max_depth +. 1.0

  (** Rebalance the rope by collecting all leaves, then building a
      balanced tree bottom-up. O(n). *)
  let balance t =
    let leaves = ref [] in
    iter_leaves (fun s -> leaves := s :: !leaves) t;
    let leaves = List.rev !leaves in
    let arr = Array.of_list leaves in
    let n = Array.length arr in
    if n = 0 then empty
    else
      let rec build lo hi =
        if lo = hi then of_string arr.(lo)
        else if lo + 1 = hi then
          concat (of_string arr.(lo)) (of_string arr.(hi))
        else
          let mid = (lo + hi) / 2 in
          concat (build lo mid) (build (mid + 1) hi)
      in
      build 0 (n - 1)

  (* ── Line Operations ──────────────────────────────────────────── *)

  (** Split the rope into lines (by '\n'). Returns a list of ropes. *)
  let lines t =
    let s = to_string t in
    let result = ref [] in
    let start = ref 0 in
    let len = String.length s in
    for i = 0 to len - 1 do
      if s.[i] = '\n' then begin
        result := of_string (String.sub s !start (i - !start)) :: !result;
        start := i + 1
      end
    done;
    if !start <= len then
      result := of_string (String.sub s !start (len - !start)) :: !result;
    List.rev !result

  (** Count the number of lines (occurrences of '\n' + 1). *)
  let line_count t =
    1 + fold (fun acc c -> if c = '\n' then acc + 1 else acc) 0 t

  (** Get the text of a specific line (0-indexed). O(n) worst case. *)
  let get_line t n =
    let ls = lines t in
    if n < 0 || n >= List.length ls then
      invalid_arg (Printf.sprintf "Rope.get_line: %d out of bounds (%d lines)" n (List.length ls))
    else List.nth ls n

  (* ── Search ───────────────────────────────────────────────────── *)

  (** Find the first occurrence of character [c] starting at [from].
      Returns [Some pos] or [None]. *)
  let find_char ?(from = 0) c t =
    let result = ref None in
    let pos = ref 0 in
    let stop = ref false in
    iter (fun ch ->
      if not !stop then begin
        if !pos >= from && ch = c then begin
          result := Some !pos;
          stop := true
        end;
        incr pos
      end
    ) t;
    !result

  (** Count occurrences of character [c]. *)
  let count_char c t =
    fold (fun acc ch -> if ch = c then acc + 1 else acc) 0 t

  (* ── Comparison and Equality ──────────────────────────────────── *)

  (** Structural equality based on content (not tree shape). *)
  let equal a b =
    if length a <> length b then false
    else to_string a = to_string b

  (** Lexicographic comparison. *)
  let compare a b =
    String.compare (to_string a) (to_string b)

end


(* ================================================================ *)
(* Interactive demo / main                                           *)
(* ================================================================ *)

let () =
  let open Rope in
  Printf.printf "=== Rope Data Structure Demo ===\n\n";

  (* Basic construction *)
  let r = of_string "Hello, World!" in
  Printf.printf "Original: \"%s\" (length=%d, depth=%d)\n"
    (to_string r) (length r) (depth r);

  (* Concatenation *)
  let r2 = concat r (of_string " How are you?") in
  Printf.printf "After concat: \"%s\" (length=%d)\n"
    (to_string r2) (length r2);

  (* Indexing *)
  Printf.printf "Character at index 7: '%c'\n" (index r2 7);

  (* Insert *)
  let r3 = insert r2 13 " --" in
  Printf.printf "After insert at 13: \"%s\"\n" (to_string r3);

  (* Delete *)
  let r4 = delete r3 13 3 in
  Printf.printf "After delete 3 chars at 13: \"%s\"\n" (to_string r4);

  (* Substring *)
  let sub = substring r2 7 5 in
  Printf.printf "Substring(7,5): \"%s\"\n" (to_string sub);

  (* Split *)
  let (left, right) = split r2 5 in
  Printf.printf "Split at 5: \"%s\" | \"%s\"\n" (to_string left) (to_string right);

  (* Map — uppercase *)
  let upper = map Char.uppercase_ascii r in
  Printf.printf "Uppercase: \"%s\"\n" (to_string upper);

  (* Lines *)
  let multiline = of_string "line 1\nline 2\nline 3" in
  Printf.printf "\nMultiline (%d lines):\n" (line_count multiline);
  List.iteri (fun i l ->
    Printf.printf "  [%d] \"%s\"\n" i (to_string l)
  ) (lines multiline);

  (* Large rope — demonstrate balancing *)
  Printf.printf "\n--- Large Rope ---\n";
  let big = ref empty in
  for _ = 1 to 100 do
    big := concat !big (of_string "abcdefghij")
  done;
  Printf.printf "100 concats: length=%d, depth=%d, balanced=%b\n"
    (length !big) (depth !big) (is_balanced !big);
  let balanced = balance !big in
  Printf.printf "After rebalance: depth=%d, balanced=%b\n"
    (depth balanced) (is_balanced balanced);
  Printf.printf "Content matches: %b\n" (equal !big balanced);

  (* Search *)
  let r5 = of_string "find the needle in the haystack" in
  (match find_char 'n' r5 with
   | Some pos -> Printf.printf "\nFirst 'n' at position %d\n" pos
   | None -> Printf.printf "\n'n' not found\n");
  Printf.printf "Count of 'e': %d\n" (count_char 'e' r5);

  Printf.printf "\nDone.\n"
