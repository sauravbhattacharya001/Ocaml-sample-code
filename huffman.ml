(* Huffman Coding — Lossless Data Compression *)
(* Demonstrates: algebraic data types, priority queues, recursive tree traversal,
   character frequency analysis, variable-length prefix codes, encoding/decoding.

   Huffman coding assigns shorter bit-strings to more frequent characters and
   longer ones to rarer characters, producing an optimal prefix-free code for
   a given character frequency distribution.

   This implementation uses a simple sorted-list priority queue for clarity.
   For production use, replace with a binary heap (see heap.ml).
*)

(* --- Huffman tree --- *)

(* A Huffman tree is either a Leaf carrying a character and its frequency,
   or a Node combining two subtrees with their combined frequency. *)
type tree =
  | Leaf of char * int
  | Node of tree * tree * int

(* Extract the frequency (weight) of a tree node *)
let freq = function
  | Leaf (_, f) -> f
  | Node (_, _, f) -> f

(* --- Priority queue (sorted list) --- *)
(* Insert a tree into a list sorted by ascending frequency.
   Ties are broken by insertion order (stable). *)
let rec pq_insert t = function
  | [] -> [t]
  | h :: rest as lst ->
    if freq t <= freq h then t :: lst
    else h :: pq_insert t rest

(* Build the initial priority queue from a list of trees *)
let pq_of_list trees =
  List.fold_left (fun pq t -> pq_insert t pq) [] trees

(* --- Frequency analysis --- *)

(* Count character frequencies in a string. Returns an association list
   sorted by (frequency ascending, char ascending) for deterministic output. *)
let char_frequencies s =
  let tbl = Hashtbl.create 128 in
  String.iter (fun c ->
    let count = try Hashtbl.find tbl c with Not_found -> 0 in
    Hashtbl.replace tbl c (count + 1)
  ) s;
  let pairs = Hashtbl.fold (fun c f acc -> (c, f) :: acc) tbl [] in
  List.sort (fun (c1, f1) (c2, f2) ->
    let cmp = compare f1 f2 in
    if cmp <> 0 then cmp else compare c1 c2
  ) pairs

(* --- Build Huffman tree --- *)

(* Build a Huffman tree from character frequencies.
   Algorithm:
   1. Create a leaf for each character
   2. Repeatedly merge the two lowest-frequency nodes
   3. Stop when one node remains — that's the root

   Returns None for empty input. *)
let build_tree freqs =
  match freqs with
  | [] -> None
  | [(c, f)] ->
    (* Single character: wrap in a node so the code table has a "0" entry *)
    Some (Node (Leaf (c, f), Leaf (c, f), f * 2))
  | _ ->
    let leaves = List.map (fun (c, f) -> Leaf (c, f)) freqs in
    let pq = pq_of_list leaves in
    let rec merge = function
      | [] -> None
      | [t] -> Some t
      | a :: b :: rest ->
        let combined = Node (a, b, freq a + freq b) in
        merge (pq_insert combined rest)
    in
    merge pq

(* Build a tree directly from a string *)
let build_tree_from_string s =
  build_tree (char_frequencies s)

(* --- Code table: char -> bit string --- *)

(* Traverse the tree to produce a mapping from characters to their
   Huffman codes (strings of '0' and '1').
   Left child = '0', right child = '1'. *)
let build_code_table tree =
  let tbl = Hashtbl.create 64 in
  let rec walk prefix = function
    | Leaf (c, _) ->
      Hashtbl.replace tbl c prefix
    | Node (left, right, _) ->
      walk (prefix ^ "0") left;
      walk (prefix ^ "1") right
  in
  walk "" tree;
  tbl

(* Get the code for a character, raising Not_found if absent *)
let lookup_code tbl c =
  try Hashtbl.find tbl c
  with Not_found ->
    failwith (Printf.sprintf "Huffman: character '%c' not in code table" c)

(* Return the code table as a sorted association list *)
let code_table_to_list tbl =
  let pairs = Hashtbl.fold (fun c code acc -> (c, code) :: acc) tbl [] in
  List.sort (fun (c1, _) (c2, _) -> compare c1 c2) pairs

(* --- Encoding --- *)

(* Encode a string into a bit-string using the given code table.
   Returns a string of '0' and '1' characters. *)
let encode tbl s =
  let buf = Buffer.create (String.length s * 4) in
  String.iter (fun c ->
    Buffer.add_string buf (lookup_code tbl c)
  ) s;
  Buffer.contents buf

(* Encode directly from a string (builds tree + table internally) *)
let encode_string s =
  match build_tree_from_string s with
  | None -> ("", None)
  | Some tree ->
    let tbl = build_code_table tree in
    let bits = encode tbl s in
    (bits, Some tree)

(* --- Decoding --- *)

(* Decode a bit-string back to characters using the Huffman tree.
   Walks the tree from root: '0' goes left, '1' goes right.
   When a leaf is reached, emit the character and restart from root. *)
let decode tree bits =
  let buf = Buffer.create (String.length bits / 4) in
  let len = String.length bits in
  let rec walk node i =
    if i >= len then
      (* If we're at a leaf, emit it; otherwise the bits are exhausted mid-symbol *)
      (match node with
       | Leaf (c, _) -> Buffer.add_char buf c
       | Node _ -> ())
    else
      match node with
      | Leaf (c, _) ->
        Buffer.add_char buf c;
        walk tree i  (* restart from root *)
      | Node (left, right, _) ->
        if bits.[i] = '0' then walk left (i + 1)
        else walk right (i + 1)
  in
  walk tree 0;
  Buffer.contents buf

(* --- Compression statistics --- *)

type stats = {
  original_bits: int;    (* 8 bits per character *)
  encoded_bits: int;     (* length of the bit-string *)
  ratio: float;          (* encoded / original *)
  savings_pct: float;    (* percentage saved *)
  unique_chars: int;     (* distinct characters *)
  avg_code_length: float;(* weighted average code length *)
}

let compression_stats s encoded_bits code_table =
  let original_bits = String.length s * 8 in
  let ratio = if original_bits > 0
    then float_of_int encoded_bits /. float_of_int original_bits
    else 0.0 in
  let savings = if original_bits > 0
    then (1.0 -. ratio) *. 100.0
    else 0.0 in
  let freqs = char_frequencies s in
  let total_chars = String.length s in
  let avg_code_len =
    if total_chars > 0 then
      List.fold_left (fun acc (c, f) ->
        let code = try Hashtbl.find code_table c with Not_found -> "" in
        acc +. (float_of_int (String.length code) *. float_of_int f)
      ) 0.0 freqs /. float_of_int total_chars
    else 0.0
  in
  {
    original_bits;
    encoded_bits;
    ratio;
    savings_pct = savings;
    unique_chars = List.length freqs;
    avg_code_length = avg_code_len;
  }

(* --- Serialization: tree to/from string --- *)
(* A simple serialization for the Huffman tree so it can be transmitted
   alongside the encoded data. Format:
   'L' <char-byte>  for a Leaf
   'N'              for a Node (left and right follow recursively)
*)

let serialize_tree tree =
  let buf = Buffer.create 256 in
  let rec ser = function
    | Leaf (c, _) ->
      Buffer.add_char buf 'L';
      Buffer.add_char buf c
    | Node (left, right, _) ->
      Buffer.add_char buf 'N';
      ser left;
      ser right
  in
  ser tree;
  Buffer.contents buf

let deserialize_tree s =
  let len = String.length s in
  let rec deser i =
    if i >= len then failwith "Huffman: unexpected end of serialized tree"
    else match s.[i] with
    | 'L' ->
      if i + 1 >= len then failwith "Huffman: truncated leaf";
      (Leaf (s.[i + 1], 0), i + 2)
    | 'N' ->
      let (left, i2) = deser (i + 1) in
      let (right, i3) = deser i2 in
      (Node (left, right, 0), i3)
    | c -> failwith (Printf.sprintf "Huffman: invalid tag '%c'" c)
  in
  let (tree, _) = deser 0 in
  tree

(* --- Pretty printing --- *)

let print_tree tree =
  let rec pp indent = function
    | Leaf (c, f) ->
      let ch_str = match c with
        | ' ' -> "SPACE"
        | '\n' -> "NEWLINE"
        | '\t' -> "TAB"
        | c -> String.make 1 c
      in
      Printf.printf "%s[%s: %d]\n" indent ch_str f
    | Node (left, right, f) ->
      Printf.printf "%s(%d)\n" indent f;
      pp (indent ^ "  ") left;
      pp (indent ^ "  ") right
  in
  pp "" tree

let print_code_table tbl =
  let sorted = code_table_to_list tbl in
  List.iter (fun (c, code) ->
    let ch_str = match c with
      | ' ' -> "SPACE"
      | '\n' -> "NEWLINE"
      | '\t' -> "TAB"
      | c -> String.make 1 c
    in
    Printf.printf "  '%s' -> %s\n" ch_str code
  ) sorted

let print_stats stats =
  Printf.printf "  Original:   %d bits (%d bytes)\n" stats.original_bits (stats.original_bits / 8);
  Printf.printf "  Encoded:    %d bits\n" stats.encoded_bits;
  Printf.printf "  Ratio:      %.1f%%\n" (stats.ratio *. 100.0);
  Printf.printf "  Savings:    %.1f%%\n" stats.savings_pct;
  Printf.printf "  Unique:     %d characters\n" stats.unique_chars;
  Printf.printf "  Avg code:   %.2f bits/char\n" stats.avg_code_length

(* --- Verify round-trip --- *)

let verify_roundtrip s =
  match build_tree_from_string s with
  | None -> true  (* empty string trivially round-trips *)
  | Some tree ->
    let tbl = build_code_table tree in
    let bits = encode tbl s in
    let decoded = decode tree bits in
    s = decoded

(* === Example usage === *)

let () =
  print_endline "=== Huffman Coding ===\n";

  (* Example 1: Simple text *)
  let text1 = "hello world" in
  Printf.printf "Text: \"%s\"\n\n" text1;

  let freqs = char_frequencies text1 in
  Printf.printf "Character frequencies:\n";
  List.iter (fun (c, f) ->
    let ch = match c with ' ' -> "SPACE" | c -> String.make 1 c in
    Printf.printf "  '%s': %d\n" ch f
  ) freqs;
  print_newline ();

  (match build_tree_from_string text1 with
   | None -> print_endline "Empty input"
   | Some tree ->
     print_endline "Huffman tree:";
     print_tree tree;
     print_newline ();

     let tbl = build_code_table tree in
     print_endline "Code table:";
     print_code_table tbl;
     print_newline ();

     let bits = encode tbl text1 in
     Printf.printf "Encoded: %s\n" bits;
     Printf.printf "Encoded length: %d bits\n\n" (String.length bits);

     let decoded = decode tree bits in
     Printf.printf "Decoded: \"%s\"\n" decoded;
     Printf.printf "Round-trip OK: %b\n\n" (text1 = decoded);

     let stats = compression_stats text1 (String.length bits) tbl in
     print_endline "Compression stats:";
     print_stats stats;
     print_newline ());

  (* Example 2: Repeated characters (high compression) *)
  let text2 = "aaaaabbbcc" in
  Printf.printf "Text: \"%s\"\n" text2;
  (match build_tree_from_string text2 with
   | None -> ()
   | Some tree ->
     let tbl = build_code_table tree in
     let bits = encode tbl text2 in
     let stats = compression_stats text2 (String.length bits) tbl in
     Printf.printf "  Savings: %.1f%% (%d bits -> %d bits)\n"
       stats.savings_pct stats.original_bits stats.encoded_bits;
     Printf.printf "  Round-trip: %b\n\n" (verify_roundtrip text2));

  (* Example 3: Serialization round-trip *)
  print_endline "=== Tree Serialization ===";
  (match build_tree_from_string text1 with
   | None -> ()
   | Some tree ->
     let serialized = serialize_tree tree in
     Printf.printf "Serialized tree: %d bytes\n" (String.length serialized);
     let tree2 = deserialize_tree serialized in
     let tbl2 = build_code_table tree2 in
     let bits = encode tbl2 text1 in
     let decoded = decode tree2 bits in
     Printf.printf "Deserialized decode OK: %b\n\n" (text1 = decoded));

  (* Example 4: Single character *)
  let text4 = "aaaa" in
  Printf.printf "Single-char text: \"%s\"\n" text4;
  Printf.printf "  Round-trip: %b\n" (verify_roundtrip text4);
  print_newline ();

  print_endline "=== All examples complete ==="
