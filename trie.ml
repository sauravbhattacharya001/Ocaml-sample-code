(* Trie (prefix tree) — efficient string storage and prefix-based retrieval *)
(* Demonstrates: Map module functor, recursive data types, option types, *)
(* higher-order functions, accumulators, tail recursion, string manipulation *)

module CharMap = Map.Make(Char)

(* A trie node: each node may mark the end of a word and has *)
(* children indexed by character. This is a purely functional *)
(* persistent data structure — all operations return new tries. *)
type trie = {
  is_word: bool;          (* does a word end at this node? *)
  children: trie CharMap.t;  (* child nodes keyed by character *)
}

(* The empty trie — no words stored *)
let empty = { is_word = false; children = CharMap.empty }

(* Convert a string to a list of characters for recursive processing *)
let chars_of_string s =
  List.init (String.length s) (String.get s)

(* Convert a character list back to a string — O(n) via Buffer *)
let string_of_chars chars =
  let buf = Buffer.create (List.length chars) in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

(* Insert a word into the trie — O(m) where m = word length *)
let insert word trie =
  let chars = chars_of_string word in
  let rec aux chars node =
    match chars with
    | [] -> { node with is_word = true }
    | c :: rest ->
      let child = match CharMap.find_opt c node.children with
        | Some t -> t
        | None -> empty
      in
      let updated_child = aux rest child in
      { node with children = CharMap.add c updated_child node.children }
  in
  aux chars trie

(** Navigate to the subtrie at a given path — O(m).
    Returns [Some node] if the path exists, [None] otherwise.
    This is the shared traversal logic used by [member],
    [has_prefix], and [find_subtrie]. *)
let walk path trie =
  let chars = chars_of_string path in
  let rec aux chars node =
    match chars with
    | [] -> Some node
    | c :: rest ->
      match CharMap.find_opt c node.children with
      | None -> None
      | Some child -> aux rest child
  in
  aux chars trie

(** Check if a word exists in the trie — O(m) *)
let member word trie =
  match walk word trie with
  | Some node -> node.is_word
  | None -> false

(** Check if any word in the trie starts with the given prefix — O(m) *)
let has_prefix prefix trie =
  Option.is_some (walk prefix trie)

(** Navigate to the subtrie at a given prefix — O(m) *)
let find_subtrie prefix trie =
  walk prefix trie

(* Collect all words in a trie with a given prefix *)
(* Uses an accumulator for efficient list building *)
let words_with_prefix prefix trie =
  match find_subtrie prefix trie with
  | None -> []
  | Some subtrie ->
    let prefix_chars = chars_of_string prefix in
    let rec collect acc path node =
      let acc = if node.is_word then (string_of_chars (List.rev path)) :: acc else acc in
      CharMap.fold (fun c child acc ->
        collect acc (c :: path) child
      ) node.children acc
    in
    List.rev (collect [] (List.rev prefix_chars) subtrie)

(* List all words in the trie — sorted lexicographically *)
(* (CharMap maintains sorted order by character) *)
let all_words trie = words_with_prefix "" trie

(* Count the number of words in the trie *)
let word_count trie =
  let rec aux node =
    let count = if node.is_word then 1 else 0 in
    CharMap.fold (fun _ child acc -> acc + aux child) node.children count
  in
  aux trie

(* Count the total number of nodes in the trie *)
let node_count trie =
  let rec aux node =
    1 + CharMap.fold (fun _ child acc -> acc + aux child) node.children 0
  in
  aux trie

(* Delete a word from the trie — O(m) *)
(* Returns a pruned trie: removes nodes that are no longer needed *)
let delete word trie =
  let chars = chars_of_string word in
  let rec aux chars node =
    match chars with
    | [] ->
      if not node.is_word then node  (* word not present, no change *)
      else { node with is_word = false }
    | c :: rest ->
      match CharMap.find_opt c node.children with
      | None -> node  (* word not present, no change *)
      | Some child ->
        let updated_child = aux rest child in
        (* Prune: if child has no words and no children, remove it *)
        if not updated_child.is_word && CharMap.is_empty updated_child.children then
          { node with children = CharMap.remove c node.children }
        else
          { node with children = CharMap.add c updated_child node.children }
  in
  aux chars trie

(* Find the longest common prefix of all words in the trie *)
let longest_common_prefix trie =
  let rec aux node =
    if node.is_word && not (CharMap.is_empty node.children) then ""
    else if node.is_word then ""
    else
      match CharMap.bindings node.children with
      | [(c, child)] -> String.make 1 c ^ aux child
      | _ -> ""  (* zero or multiple children: LCP ends here *)
  in
  if CharMap.is_empty trie.children then ""
  else aux trie

(* Build a trie from a list of words *)
let of_list words =
  List.fold_left (fun t w -> insert w t) empty words

(* ASCII visualization of the trie structure *)
(* Shows the tree with indentation and markers *)
let to_string trie =
  let buf = Buffer.create 256 in
  let rec aux indent last node bindings =
    match bindings with
    | [] -> ()
    | [(c, child)] ->
      let connector = if last then "└── " else "├── " in
      let next_indent = if last then indent ^ "    " else indent ^ "│   " in
      Buffer.add_string buf indent;
      Buffer.add_string buf connector;
      Buffer.add_char buf c;
      if child.is_word then Buffer.add_string buf " *";
      Buffer.add_char buf '\n';
      aux next_indent true child (CharMap.bindings child.children)
    | (c, child) :: rest ->
      let next_indent = indent ^ "│   " in
      Buffer.add_string buf indent;
      Buffer.add_string buf "├── ";
      Buffer.add_char buf c;
      if child.is_word then Buffer.add_string buf " *";
      Buffer.add_char buf '\n';
      aux next_indent false child (CharMap.bindings child.children);
      aux indent last node rest
  in
  Buffer.add_string buf "(root)";
  if trie.is_word then Buffer.add_string buf " *";
  Buffer.add_char buf '\n';
  aux "" true trie (CharMap.bindings trie.children);
  Buffer.contents buf

(* =============================================================== *)
(*                       EXAMPLE USAGE                             *)
(* =============================================================== *)

let () =
  print_endline "=== Trie (Prefix Tree) ===\n";

  (* Build a trie with some words *)
  let words = ["apple"; "app"; "application"; "apply"; "apt";
                "bat"; "bath"; "batch"; "bad";
                "car"; "card"; "care"; "careful"; "cart"] in
  let t = of_list words in
  Printf.printf "Inserted %d words\n\n" (List.length words);

  (* Membership queries *)
  print_endline "--- Membership ---";
  Printf.printf "member \"apple\":  %b\n" (member "apple" t);
  Printf.printf "member \"app\":    %b\n" (member "app" t);
  Printf.printf "member \"ap\":     %b\n" (member "ap" t);
  Printf.printf "member \"bat\":    %b\n" (member "bat" t);
  Printf.printf "member \"batman\": %b\n" (member "batman" t);
  print_newline ();

  (* Prefix queries *)
  print_endline "--- Prefix Search ---";
  Printf.printf "has_prefix \"app\": %b\n" (has_prefix "app" t);
  Printf.printf "has_prefix \"xyz\": %b\n" (has_prefix "xyz" t);
  print_newline ();

  (* Auto-complete *)
  print_endline "--- Auto-complete ---";
  let show_words prefix =
    let results = words_with_prefix prefix t in
    Printf.printf "  \"%s\" -> [%s]\n" prefix (String.concat "; " results)
  in
  show_words "app";
  show_words "car";
  show_words "bat";
  show_words "ba";
  show_words "z";
  print_newline ();

  (* Statistics *)
  print_endline "--- Statistics ---";
  Printf.printf "Word count: %d\n" (word_count t);
  Printf.printf "Node count: %d\n" (node_count t);
  Printf.printf "All words: [%s]\n" (String.concat "; " (all_words t));
  print_newline ();

  (* Longest common prefix *)
  let lcp_trie = of_list ["flower"; "flow"; "flight"] in
  Printf.printf "LCP of [flower; flow; flight]: \"%s\"\n" (longest_common_prefix lcp_trie);
  let lcp_trie2 = of_list ["test"; "testing"; "tested"; "tester"] in
  Printf.printf "LCP of [test; testing; tested; tester]: \"%s\"\n" (longest_common_prefix lcp_trie2);
  print_newline ();

  (* Deletion *)
  print_endline "--- Deletion ---";
  let t2 = delete "apple" t in
  Printf.printf "After deleting \"apple\":\n";
  Printf.printf "  member \"apple\": %b\n" (member "apple" t2);
  Printf.printf "  member \"app\":   %b\n" (member "app" t2);
  Printf.printf "  word count: %d\n" (word_count t2);
  let t3 = delete "app" t2 in
  Printf.printf "After also deleting \"app\":\n";
  Printf.printf "  member \"app\":          %b\n" (member "app" t3);
  Printf.printf "  member \"application\":  %b\n" (member "application" t3);
  Printf.printf "  word count: %d\n" (word_count t3);
  print_newline ();

  (* Persistence — original trie is unchanged *)
  print_endline "--- Persistence ---";
  Printf.printf "Original still has \"apple\": %b\n" (member "apple" t);
  Printf.printf "Original word count: %d\n" (word_count t);
  print_newline ();

  (* ASCII visualization *)
  print_endline "--- Trie Structure ---";
  let small_trie = of_list ["an"; "ant"; "and"; "be"; "bee"; "been"] in
  print_string (to_string small_trie);
  print_newline ();

  (* --- walk (internal traversal primitive) --- *)
  print_endline "\n--- walk: internal traversal ---";
  (match walk "app" t with
   | Some node ->
     Printf.printf "walk \"app\": found subtrie (is_word=%b)\n" node.is_word
   | None -> print_endline "walk \"app\": not found");
  (match walk "xyz" t with
   | Some _ -> print_endline "walk \"xyz\": found"
   | None -> print_endline "walk \"xyz\": not found");
  print_newline ();

  (* Build from empty *)
  print_endline "--- Edge Cases ---";
  Printf.printf "Empty trie word count: %d\n" (word_count empty);
  Printf.printf "Empty trie member \"a\": %b\n" (member "a" empty);
  Printf.printf "Empty trie all_words: [%s]\n" (String.concat "; " (all_words empty));
  let single = insert "hello" empty in
  Printf.printf "Single word trie: [%s]\n" (String.concat "; " (all_words single));
  (* Empty string as word *)
  let with_empty = insert "" empty in
  Printf.printf "Trie with empty string word count: %d\n" (word_count with_empty);
  Printf.printf "Empty string member: %b\n" (member "" with_empty)
