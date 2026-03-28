(* Radix Tree (Patricia Trie) — compressed prefix tree for efficient string storage *)
(* Demonstrates: algebraic data types, string slicing, pattern matching,          *)
(* recursive data structures, option types, accumulator patterns, persistence     *)

(* A radix tree compresses chains of single-child nodes into one node with a      *)
(* multi-character edge label. This gives better space efficiency than a plain     *)
(* trie while preserving O(m) lookup where m = key length.                        *)

type t =
  | Leaf
  | Node of {
      prefix: string;       (* edge label from parent *)
      is_word: bool;        (* does a word end here? *)
      children: t list;     (* child subtrees *)
    }

let empty = Leaf

(* ---------- helpers ---------- *)

(* Length of common prefix between two strings *)
let common_prefix_len a b =
  let len = min (String.length a) (String.length b) in
  let rec go i =
    if i >= len then i
    else if a.[i] = b.[i] then go (i + 1)
    else i
  in
  go 0

(* Safe substring — returns "" when out of range *)
let safe_sub s start len =
  if start >= String.length s || len <= 0 then ""
  else String.sub s start (min len (String.length s - start))

(* Get the prefix of a node (Leaf has empty prefix) *)
let node_prefix = function
  | Leaf -> ""
  | Node n -> n.prefix

(* ---------- insert ---------- *)

let rec insert key t =
  match t with
  | Leaf ->
    Node { prefix = key; is_word = true; children = [] }
  | Node n ->
    let cp = common_prefix_len key n.prefix in
    let klen = String.length key in
    let plen = String.length n.prefix in
    if cp = plen && cp = klen then
      (* exact match — mark this node as word *)
      Node { n with is_word = true }
    else if cp = plen then
      (* key extends beyond this node's prefix — recurse into children *)
      let rest = safe_sub key cp (klen - cp) in
      let inserted = insert_into_children rest n.children in
      Node { n with children = inserted }
    else if cp = klen then
      (* key is a prefix of this node — split node *)
      let child_suffix = safe_sub n.prefix cp (plen - cp) in
      let child = Node { n with prefix = child_suffix } in
      Node { prefix = key; is_word = true; children = [child] }
    else
      (* partial match — split at divergence point *)
      let shared = safe_sub key 0 cp in
      let key_rest = safe_sub key cp (klen - cp) in
      let node_rest = safe_sub n.prefix cp (plen - cp) in
      let old_child = Node { n with prefix = node_rest } in
      let new_child = Node { prefix = key_rest; is_word = true; children = [] } in
      Node { prefix = shared; is_word = false; children = [old_child; new_child] }

and insert_into_children key children =
  match children with
  | [] ->
    [Node { prefix = key; is_word = true; children = [] }]
  | (Node n as child) :: rest when String.length n.prefix > 0 && String.length key > 0 && key.[0] = n.prefix.[0] ->
    (* found matching first char — recurse into this child *)
    (insert key child) :: rest
  | child :: rest ->
    child :: (insert_into_children key rest)

(* ---------- member ---------- *)

let rec member key = function
  | Leaf -> false
  | Node n ->
    let cp = common_prefix_len key n.prefix in
    let klen = String.length key in
    let plen = String.length n.prefix in
    if cp = plen && cp = klen then
      n.is_word
    else if cp = plen then
      let rest = safe_sub key cp (klen - cp) in
      find_in_children rest n.children
    else
      false

and find_in_children key = function
  | [] -> false
  | child :: rest ->
    if member key child then true
    else find_in_children key rest

(* ---------- all_words ---------- *)

(* Collect all words stored in the tree *)
let all_words t =
  let rec aux prefix acc = function
    | Leaf -> acc
    | Node n ->
      let full = prefix ^ n.prefix in
      let acc = if n.is_word then full :: acc else acc in
      List.fold_left (fun a c -> aux full a c) acc n.children
  in
  List.rev (aux "" [] t)

(* ---------- words_with_prefix ---------- *)

(* Find all words that start with the given prefix *)
let words_with_prefix pfx t =
  let rec descend key = function
    | Leaf -> []
    | Node n ->
      let cp = common_prefix_len key n.prefix in
      let klen = String.length key in
      let plen = String.length n.prefix in
      if cp = klen && cp = plen then
        (* exact node match — collect everything below *)
        let full = pfx in
        let acc = if n.is_word then [full] else [] in
        let rest_words = List.fold_left (fun a c -> a @ collect (pfx) c) [] n.children in
        acc @ rest_words
      else if cp = klen then
        (* prefix consumed within this node's label — everything below matches *)
        collect (safe_sub pfx 0 (String.length pfx - klen + plen)) (Node n)
      else if cp = plen then
        let rest = safe_sub key cp (klen - cp) in
        find_prefix_child rest n.children
      else
        []
  and find_prefix_child key = function
    | [] -> []
    | child :: rest ->
      (match descend key child with
       | [] -> find_prefix_child key rest
       | found -> found)
  and collect prefix = function
    | Leaf -> []
    | Node n ->
      let full = prefix ^ n.prefix in
      let acc = if n.is_word then [full] else [] in
      List.fold_left (fun a c -> a @ collect full c) acc n.children
  in
  descend pfx t

(* ---------- remove ---------- *)

let rec remove key = function
  | Leaf -> Leaf
  | Node n ->
    let cp = common_prefix_len key n.prefix in
    let klen = String.length key in
    let plen = String.length n.prefix in
    if cp = plen && cp = klen then
      (* exact match — unmark word *)
      if n.children = [] then Leaf
      else
        match n.children with
        | [Node c] when not n.is_word ->
          (* merge with single child *)
          Node { c with prefix = n.prefix ^ c.prefix }
        | _ ->
          Node { n with is_word = false }
    else if cp = plen then
      let rest = safe_sub key cp (klen - cp) in
      let new_children = remove_from_children rest n.children in
      (* compress if only one non-word child remains *)
      (match new_children with
       | [Node c] when not n.is_word ->
         Node { c with prefix = n.prefix ^ c.prefix }
       | [] when not n.is_word -> Leaf
       | _ -> Node { n with children = new_children })
    else
      Node n  (* key not found *)

and remove_from_children key = function
  | [] -> []
  | child :: rest ->
    let child' = remove key child in
    (match child' with
     | Leaf -> rest
     | _ -> child' :: rest)

(* ---------- size ---------- *)

let rec size = function
  | Leaf -> 0
  | Node n ->
    let base = if n.is_word then 1 else 0 in
    List.fold_left (fun acc c -> acc + size c) base n.children

(* ---------- demo ---------- *)

let () =
  Printf.printf "=== Radix Tree (Patricia Trie) Demo ===\n\n";

  (* Build a tree with related words *)
  let words = ["romane"; "romanus"; "romulus"; "rubens"; "ruber"; "rubicon"; "rubicundus"] in
  let tree = List.fold_left (fun t w -> insert w t) empty words in

  Printf.printf "Inserted %d words: %s\n" (List.length words) (String.concat ", " words);
  Printf.printf "Tree size: %d\n\n" (size tree);

  (* Membership tests *)
  Printf.printf "--- Membership ---\n";
  List.iter (fun w ->
    Printf.printf "  member \"%s\" = %b\n" w (member w tree)
  ) ["romane"; "roman"; "romanus"; "xyz"; "rub"; "rubicon"];

  (* Prefix search *)
  Printf.printf "\n--- Prefix Search ---\n";
  let prefixes = ["ro"; "rub"; "rom"; "x"] in
  List.iter (fun p ->
    let results = words_with_prefix p tree in
    Printf.printf "  prefix \"%s\" -> [%s]\n" p (String.concat "; " results)
  ) prefixes;

  (* All words *)
  Printf.printf "\n--- All Words ---\n";
  let all = all_words tree in
  Printf.printf "  [%s]\n" (String.concat "; " all);

  (* Removal *)
  Printf.printf "\n--- Removal ---\n";
  let tree2 = remove "romanus" tree in
  Printf.printf "  After removing \"romanus\": size=%d, member=\"romanus\"=%b\n"
    (size tree2) (member "romanus" tree2);
  let tree3 = remove "rubicon" tree2 in
  Printf.printf "  After removing \"rubicon\": size=%d\n" (size tree3);
  Printf.printf "  Remaining: [%s]\n" (String.concat "; " (all_words tree3));

  (* Additional insertions *)
  Printf.printf "\n--- Additional Insertions ---\n";
  let tree4 = insert "roman" (insert "rub" tree) in
  Printf.printf "  After adding \"roman\" and \"rub\": size=%d\n" (size tree4);
  Printf.printf "  All: [%s]\n" (String.concat "; " (all_words tree4));

  Printf.printf "\nDone.\n"
