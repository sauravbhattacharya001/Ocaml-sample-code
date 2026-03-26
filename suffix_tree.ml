(* Suffix Tree — Ukkonen-inspired suffix tree for string analysis *)
(* Demonstrates: algebraic data types, mutable records, imperative OCaml, *)
(* string slicing, recursive traversal, pattern matching, hash tables *)

(* ================================================================== *)
(* A suffix tree stores all suffixes of a string in a compressed trie. *)
(* It enables O(m) substring search, longest repeated substring,       *)
(* suffix counting, and more. This implementation uses an explicit     *)
(* construction (insert each suffix) for clarity.                      *)
(* ================================================================== *)

(* Edge label represented as a slice of the original string *)
type edge_label = {
  text: string;   (* the full source string *)
  start: int;     (* start index of the edge label *)
  len: int;       (* length of the edge label *)
}

(* Suffix tree node *)
type node = {
  mutable children: (char * edge * node) list;
  mutable is_leaf: bool;
  mutable suffix_index: int;  (* -1 for internal nodes *)
}

and edge = edge_label

(* Get the i-th character of an edge label *)
let edge_char e i = e.text.[e.start + i]

(* Get the full string of an edge label *)
let edge_string e = String.sub e.text e.start e.len

(* Create a new internal node *)
let make_node () = { children = []; is_leaf = false; suffix_index = -1 }

(* Create a leaf node with suffix index *)
let make_leaf idx = { children = []; is_leaf = true; suffix_index = idx }

(* Find a child edge starting with character c *)
let find_child node c =
  List.find_opt (fun (ch, _, _) -> ch = c) node.children

(* Remove a child by character *)
let remove_child node c =
  node.children <- List.filter (fun (ch, _, _) -> ch <> c) node.children

(* Add a child *)
let add_child node c edge child =
  node.children <- (c, edge, child) :: node.children

(* ------------------------------------------------------------------ *)
(* Construction: naive O(n²) method — insert each suffix explicitly.  *)
(* Clear and correct; Ukkonen's O(n) is complex but this suffices     *)
(* for learning and moderate-sized strings.                           *)
(* ------------------------------------------------------------------ *)

let build str =
  (* Append sentinel character to ensure all suffixes end at leaves *)
  let s = str ^ "$" in
  let n = String.length s in
  let root = make_node () in

  for i = 0 to n - 1 do
    (* Insert suffix starting at position i *)
    let rec insert_at node pos =
      if pos >= n then
        (* Reached end — mark as leaf *)
        (node.is_leaf <- true; node.suffix_index <- i)
      else
        let c = s.[pos] in
        match find_child node c with
        | None ->
          (* No edge with this char — create a new leaf *)
          let leaf = make_leaf i in
          let edge = { text = s; start = pos; len = n - pos } in
          add_child node c edge leaf
        | Some (_, edge, child) ->
          (* Walk along the edge, comparing characters *)
          let rec walk j =
            if j >= edge.len then
              (* Exhausted the edge — continue at child *)
              insert_at child (pos + j)
            else if pos + j >= n then
              (* Suffix ended mid-edge — split *)
              split node c edge child j i
            else if s.[pos + j] <> edge_char edge j then
              (* Mismatch at position j — split the edge *)
              split_at_mismatch node c edge child j (pos + j) i
            else
              walk (j + 1)
          in
          walk 0
    and split _parent _c _edge _child _j _idx = ()
    and split_at_mismatch parent c edge child j mismatch_pos suffix_idx =
      (* Create a new internal node at the split point *)
      let internal = make_node () in
      (* Edge from parent to internal: first j chars of original edge *)
      let edge_to_internal = { text = edge.text; start = edge.start; len = j } in
      (* Edge from internal to old child: remaining chars *)
      let edge_to_old = { text = edge.text; start = edge.start + j; len = edge.len - j } in
      (* Edge from internal to new leaf: remaining suffix *)
      let n_len = String.length edge.text in
      let new_leaf = make_leaf suffix_idx in
      let edge_to_new = { text = edge.text; start = mismatch_pos; len = n_len - mismatch_pos } in
      (* Rewire *)
      remove_child parent c;
      add_child parent (edge_char edge_to_internal 0) edge_to_internal internal;
      add_child internal (edge_char edge_to_old 0) edge_to_old child;
      add_child internal (edge_char edge_to_new 0) edge_to_new new_leaf
    in
    insert_at root i
  done;
  (root, s)

(* ------------------------------------------------------------------ *)
(* Search: check if pattern exists as a substring — O(m)              *)
(* ------------------------------------------------------------------ *)

let search (root, s) pattern =
  let m = String.length pattern in
  if m = 0 then true
  else
    let rec walk node pos =
      if pos >= m then true
      else
        match find_child node pattern.[pos] with
        | None -> false
        | Some (_, edge, child) ->
          let rec match_edge j =
            if pos + j >= m then true  (* pattern exhausted — found *)
            else if j >= edge.len then walk child (pos + j)  (* edge exhausted *)
            else if pattern.[pos + j] = edge_char edge j then match_edge (j + 1)
            else false  (* mismatch *)
          in
          match_edge 0
    in
    walk root 0

(* ------------------------------------------------------------------ *)
(* Count leaves below a node — gives number of occurrences            *)
(* ------------------------------------------------------------------ *)

let rec count_leaves node =
  if node.children = [] then 1
  else List.fold_left (fun acc (_, _, child) -> acc + count_leaves child) 0 node.children

(* Count occurrences of a pattern *)
let count_occurrences (root, _s) pattern =
  let m = String.length pattern in
  if m = 0 then 0
  else
    let rec walk node pos =
      if pos >= m then Some node
      else
        match find_child node pattern.[pos] with
        | None -> None
        | Some (_, edge, child) ->
          let rec match_edge j =
            if pos + j >= m then Some (if j >= edge.len then child else child)
            else if j >= edge.len then walk child (pos + j)
            else if pattern.[pos + j] = edge_char edge j then match_edge (j + 1)
            else None
          in
          match_edge 0
    in
    match walk root 0 with
    | None -> 0
    | Some node -> count_leaves node

(* ------------------------------------------------------------------ *)
(* Collect all suffix indices below a node                            *)
(* ------------------------------------------------------------------ *)

let rec collect_indices node =
  if node.children = [] then [node.suffix_index]
  else List.concat_map (fun (_, _, child) -> collect_indices child) node.children

(* Find all positions where pattern occurs *)
let find_all (root, _s) pattern =
  let m = String.length pattern in
  if m = 0 then []
  else
    let rec walk node pos =
      if pos >= m then Some node
      else
        match find_child node pattern.[pos] with
        | None -> None
        | Some (_, edge, child) ->
          let rec match_edge j =
            if pos + j >= m then Some (if j >= edge.len then child else child)
            else if j >= edge.len then walk child (pos + j)
            else if pattern.[pos + j] = edge_char edge j then match_edge (j + 1)
            else None
          in
          match_edge 0
    in
    match walk root 0 with
    | None -> []
    | Some node -> List.sort compare (collect_indices node)

(* ------------------------------------------------------------------ *)
(* Longest Repeated Substring                                         *)
(* Find the deepest internal node (non-leaf with >1 child paths)      *)
(* ------------------------------------------------------------------ *)

let longest_repeated_substring (root, s) =
  let best = ref "" in
  let rec dfs node depth acc =
    (* Internal node with children = repeated substring *)
    if node.children <> [] && depth > 0 then begin
      let candidate = String.concat "" (List.rev acc) in
      if String.length candidate > String.length !best then
        best := candidate
    end;
    List.iter (fun (_, edge, child) ->
      let label = edge_string edge in
      (* Don't follow edges that include the sentinel *)
      if not (String.contains label '$') then
        dfs child (depth + edge.len) (label :: acc)
      else begin
        (* Partial label up to $ *)
        let dollar_pos = String.index label '$' in
        if dollar_pos > 0 then begin
          let partial = String.sub label 0 dollar_pos in
          let candidate = String.concat "" (List.rev (partial :: acc)) in
          if String.length candidate > String.length !best then
            best := candidate
        end
      end
    ) node.children
  in
  dfs root 0 [];
  !best

(* ------------------------------------------------------------------ *)
(* Pretty-print the suffix tree for debugging                        *)
(* ------------------------------------------------------------------ *)

let print_tree (root, _s) =
  let rec pp indent node =
    List.iter (fun (_, edge, child) ->
      let label = edge_string edge in
      Printf.printf "%s├── \"%s\"" indent label;
      if child.children = [] then
        Printf.printf " [suffix %d]" child.suffix_index;
      Printf.printf "\n";
      pp (indent ^ "│   ") child
    ) (List.sort (fun (a,_,_) (b,_,_) -> Char.compare a b) node.children)
  in
  Printf.printf "(root)\n";
  pp "" root

(* ================================================================== *)
(* Demo / main                                                        *)
(* ================================================================== *)

let () =
  Printf.printf "=== Suffix Tree Demo ===\n\n";

  (* Build a suffix tree for "banana" *)
  let tree = build "banana" in

  Printf.printf "String: \"banana\"\n\n";
  Printf.printf "Tree structure:\n";
  print_tree tree;
  Printf.printf "\n";

  (* Search tests *)
  let patterns = ["ban"; "ana"; "nan"; "xyz"; "a"; "banana"; "nana"; ""] in
  Printf.printf "Substring search:\n";
  List.iter (fun p ->
    Printf.printf "  \"%s\" -> %s\n" p (if search tree p then "found" else "not found")
  ) patterns;
  Printf.printf "\n";

  (* Count occurrences *)
  Printf.printf "Occurrence counts:\n";
  List.iter (fun p ->
    Printf.printf "  \"%s\" -> %d times\n" p (count_occurrences tree p)
  ) ["an"; "a"; "na"; "ban"; "x"];
  Printf.printf "\n";

  (* Find all positions *)
  Printf.printf "All positions of \"an\": %s\n"
    (String.concat ", " (List.map string_of_int (find_all tree "an")));
  Printf.printf "All positions of \"a\": %s\n"
    (String.concat ", " (List.map string_of_int (find_all tree "a")));
  Printf.printf "\n";

  (* Longest repeated substring *)
  Printf.printf "Longest repeated substring: \"%s\"\n\n"
    (longest_repeated_substring tree);

  (* Another example *)
  let tree2 = build "mississippi" in
  Printf.printf "String: \"mississippi\"\n";
  Printf.printf "Longest repeated substring: \"%s\"\n"
    (longest_repeated_substring tree2);
  Printf.printf "Occurrences of \"issi\": %d\n"
    (count_occurrences tree2 "issi");
  Printf.printf "Positions of \"ss\": %s\n"
    (String.concat ", " (List.map string_of_int (find_all tree2 "ss")));
  Printf.printf "\n";

  Printf.printf "=== Done ===\n"
