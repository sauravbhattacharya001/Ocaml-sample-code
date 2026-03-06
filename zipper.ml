(*
 *  zipper.ml
 *  OCaml Sample Code
 *
 *  Zipper — functional cursor for navigating and editing immutable
 *  data structures in O(1) per step.  The core idea: decompose a
 *  data structure into a *focus* (the element we're looking at) and
 *  a *context* (everything else, stored as a stack of "one-hole"
 *  frames so we can reconstruct the whole thing).
 *
 *  Three zippers are implemented:
 *
 *    1. **List zipper** — cursor inside a list with O(1) left/right
 *       movement, insert, delete, and replace.
 *
 *    2. **Binary tree zipper** — Huet's original zipper for binary
 *       trees.  Navigate up/left/right, edit the focused subtree,
 *       insert children, prune branches — all purely functional.
 *
 *    3. **Filesystem zipper** — zipper over a rose tree (n-ary tree
 *       with named edges), modeling a directory hierarchy with
 *       cd / ls / mkdir / touch / pwd operations.
 *
 *  Concepts: algebraic data types, one-hole contexts, purely
 *  functional editing, pattern matching, modules, recursive types.
 *)

(* ================================================================
   1. LIST ZIPPER
   ================================================================ *)

module ListZipper = struct

  (** A zipper over a list ['a].
      [left]  — elements to the left of the cursor, nearest first.
      [focus] — the element under the cursor.
      [right] — elements to the right of the cursor. *)
  type 'a t = {
    left  : 'a list;
    focus : 'a;
    right : 'a list;
  }

  (** Create a zipper focused on the first element of a non-empty list.
      Returns [None] for the empty list. *)
  let of_list = function
    | []     -> None
    | x :: r -> Some { left = []; focus = x; right = r }

  (** Reconstruct the full list from the zipper. *)
  let to_list z =
    List.rev_append z.left (z.focus :: z.right)

  (** The element currently under the cursor. *)
  let focus z = z.focus

  (** Move the cursor one step to the right.
      Returns [None] if already at the rightmost element. *)
  let move_right z =
    match z.right with
    | []     -> None
    | r :: rs -> Some { left = z.focus :: z.left; focus = r; right = rs }

  (** Move the cursor one step to the left.
      Returns [None] if already at the leftmost element. *)
  let move_left z =
    match z.left with
    | []     -> None
    | l :: ls -> Some { left = ls; focus = l; right = z.focus :: z.right }

  (** Replace the focused element. *)
  let replace x z = { z with focus = x }

  (** Apply a function to the focused element. *)
  let modify f z = { z with focus = f z.focus }

  (** Insert an element to the left of the cursor (cursor stays). *)
  let insert_left x z = { z with left = x :: z.left }

  (** Insert an element to the right of the cursor (cursor stays). *)
  let insert_right x z = { z with right = x :: z.right }

  (** Delete the focused element, moving cursor right if possible,
      otherwise left.  Returns [None] if the zipper has only one element. *)
  let delete z =
    match z.right, z.left with
    | r :: rs, _      -> Some { left = z.left; focus = r; right = rs }
    | [], l :: ls      -> Some { left = ls; focus = l; right = [] }
    | [], []           -> None

  (** Move the cursor to the leftmost position. *)
  let rec rewind z =
    match move_left z with
    | None   -> z
    | Some z' -> rewind z'

  (** Move the cursor to the rightmost position. *)
  let rec fast_forward z =
    match move_right z with
    | None   -> z
    | Some z' -> fast_forward z'

  (** Number of elements in the zipper. *)
  let length z =
    List.length z.left + 1 + List.length z.right

  (** Zero-based index of the cursor from the left. *)
  let index z = List.length z.left

  (** Move the cursor to a specific zero-based index.
      Returns [None] if the index is out of bounds. *)
  let goto n z =
    let z = rewind z in
    let rec step i z =
      if i = n then Some z
      else match move_right z with
        | None   -> None
        | Some z' -> step (i + 1) z'
    in
    if n < 0 then None else step 0 z

  (** Map a function over every element, preserving cursor position. *)
  let map f z = {
    left  = List.map f z.left;
    focus = f z.focus;
    right = List.map f z.right;
  }

  (** Fold left over all elements in list order (not cursor order). *)
  let fold_left f acc z =
    let acc = List.fold_right (fun x a -> f a x) z.left acc in
    let acc = f acc z.focus in
    List.fold_left f acc z.right

  (** Find the first element matching [pred], moving cursor there.
      Searches right from current position first, then from the start. *)
  let find pred z =
    let rec search_right z =
      if pred z.focus then Some z
      else match move_right z with
        | None   -> None
        | Some z' -> search_right z'
    in
    match search_right z with
    | Some _ as found -> found
    | None -> search_right (rewind z)

  (** Pretty-print the zipper, marking the focused element with []. *)
  let to_string show z =
    let items = List.rev_map show z.left in
    let items = items @ ["[" ^ show z.focus ^ "]"] in
    let items = items @ List.map show z.right in
    String.concat " " items
end


(* ================================================================
   2. BINARY TREE ZIPPER (Huet's Zipper)
   ================================================================ *)

module TreeZipper = struct

  (** A binary tree. *)
  type 'a tree =
    | Leaf
    | Node of 'a tree * 'a * 'a tree

  (** A single step in the path from focus to root.
      [Left (x, right)]  — we came from the left child;
                            parent value is [x], right sibling is [right].
      [Right (left, x)]  — we came from the right child;
                            parent value is [x], left sibling is [left]. *)
  type 'a crumb =
    | Left  of 'a * 'a tree
    | Right of 'a tree * 'a

  (** A zipper = focused subtree + path of crumbs back to root. *)
  type 'a t = {
    focus  : 'a tree;
    crumbs : 'a crumb list;
  }

  (** Create a zipper focused on the root of a tree. *)
  let of_tree t = { focus = t; crumbs = [] }

  (** Reconstruct the full tree by walking back to the root. *)
  let rec to_tree z =
    match z.crumbs with
    | [] -> z.focus
    | Left (x, r)  :: cs -> to_tree { focus = Node (z.focus, x, r); crumbs = cs }
    | Right (l, x) :: cs -> to_tree { focus = Node (l, x, z.focus); crumbs = cs }

  (** The focused subtree. *)
  let focus z = z.focus

  (** Move focus to the left child.  Returns [None] on a Leaf. *)
  let go_left z =
    match z.focus with
    | Leaf -> None
    | Node (l, x, r) ->
      Some { focus = l; crumbs = Left (x, r) :: z.crumbs }

  (** Move focus to the right child.  Returns [None] on a Leaf. *)
  let go_right z =
    match z.focus with
    | Leaf -> None
    | Node (l, x, r) ->
      Some { focus = r; crumbs = Right (l, x) :: z.crumbs }

  (** Move focus to the parent.  Returns [None] at the root. *)
  let go_up z =
    match z.crumbs with
    | [] -> None
    | Left (x, r)  :: cs -> Some { focus = Node (z.focus, x, r); crumbs = cs }
    | Right (l, x) :: cs -> Some { focus = Node (l, x, z.focus); crumbs = cs }

  (** Move to the root (top) of the tree. *)
  let rec top z =
    match go_up z with
    | None   -> z
    | Some z' -> top z'

  (** Are we at the root? *)
  let is_root z = z.crumbs = []

  (** Is the focused node a Leaf? *)
  let is_leaf z = z.focus = Leaf

  (** Depth of the focus from the root. *)
  let depth z = List.length z.crumbs

  (** Replace the focused subtree. *)
  let replace t z = { z with focus = t }

  (** Apply a function to the root value of the focused subtree.
      Returns [None] if focused on a Leaf. *)
  let modify f z =
    match z.focus with
    | Leaf -> None
    | Node (l, x, r) -> Some { z with focus = Node (l, f x, r) }

  (** Get the value at the focused node.  [None] for Leaf. *)
  let value z =
    match z.focus with
    | Leaf -> None
    | Node (_, x, _) -> Some x

  (** Insert a value as a new left child, pushing the old left child
      down as the new node's left subtree. *)
  let insert_left v z =
    match z.focus with
    | Leaf -> { z with focus = Node (Leaf, v, Leaf) }
    | Node (l, x, r) ->
      { z with focus = Node (Node (l, v, Leaf), x, r) }

  (** Insert a value as a new right child, pushing the old right child
      down as the new node's right subtree. *)
  let insert_right v z =
    match z.focus with
    | Leaf -> { z with focus = Node (Leaf, v, Leaf) }
    | Node (l, x, r) ->
      { z with focus = Node (l, x, Node (Leaf, v, r)) }

  (** Prune the focused subtree, replacing it with Leaf. *)
  let prune z = { z with focus = Leaf }

  (** Size (number of nodes) of the focused subtree. *)
  let rec subtree_size = function
    | Leaf -> 0
    | Node (l, _, r) -> 1 + subtree_size l + subtree_size r

  (** Height of the focused subtree. *)
  let rec subtree_height = function
    | Leaf -> 0
    | Node (l, _, r) -> 1 + max (subtree_height l) (subtree_height r)

  (** Navigate to the leftmost node (leaf-level). *)
  let rec leftmost z =
    match go_left z with
    | None   -> z
    | Some z' -> leftmost z'

  (** Navigate to the rightmost node (leaf-level). *)
  let rec rightmost z =
    match go_right z with
    | None   -> z
    | Some z' -> rightmost z'

  (** In-order traversal collecting values. *)
  let rec inorder = function
    | Leaf -> []
    | Node (l, x, r) -> inorder l @ [x] @ inorder r

  (** Pretty-print a tree. *)
  let rec tree_to_string show = function
    | Leaf -> "."
    | Node (l, x, r) ->
      Printf.sprintf "(%s %s %s)"
        (tree_to_string show l) (show x) (tree_to_string show r)

  (** Pretty-print a zipper, showing the focus path. *)
  let to_string show z =
    let tree_str = tree_to_string show (to_tree z) in
    let focus_str = tree_to_string show z.focus in
    Printf.sprintf "Tree: %s\nFocus: %s\nDepth: %d"
      tree_str focus_str (depth z)
end


(* ================================================================
   3. FILESYSTEM ZIPPER (Rose Tree)
   ================================================================ *)

module FSZipper = struct

  (** A filesystem entry: either a file with content or a directory
      with named children. *)
  type entry =
    | File of string         (* file content *)
    | Dir  of (string * entry) list  (* named children *)

  (** A crumb for the filesystem zipper.
      [parent_name] — name of the directory we came from (for pwd).
      [lefts]       — siblings to the left.
      [rights]      — siblings to the right. *)
  type crumb = {
    parent_name : string;
    lefts       : (string * entry) list;
    rights      : (string * entry) list;
  }

  (** A zipper = (current_name, current_entry) + path of crumbs. *)
  type t = {
    name   : string;
    entry  : entry;
    crumbs : crumb list;
  }

  (** Create a zipper at the root of a filesystem tree. *)
  let of_entry ?(name="/") e = { name; entry = e; crumbs = [] }

  (** Reconstruct the full tree by going up to root. *)
  let rec to_entry z =
    match z.crumbs with
    | [] -> (z.name, z.entry)
    | c :: cs ->
      let children =
        List.rev_append c.lefts ((z.name, z.entry) :: c.rights)
      in
      to_entry { name = c.parent_name; entry = Dir children; crumbs = cs }

  (** Navigate into a child directory or file by name.
      Returns [None] if not found or current entry is a File. *)
  let cd child_name z =
    match z.entry with
    | File _ -> None
    | Dir children ->
      let rec split_at name acc = function
        | [] -> None
        | (n, e) :: rest when n = name ->
          Some (List.rev acc, (n, e), rest)
        | x :: rest -> split_at name (x :: acc) rest
      in
      match split_at child_name [] children with
      | None -> None
      | Some (lefts, (n, e), rights) ->
        Some {
          name   = n;
          entry  = e;
          crumbs = { parent_name = z.name; lefts; rights } :: z.crumbs;
        }

  (** Navigate up to the parent directory.
      Returns [None] if already at root. *)
  let cd_up z =
    match z.crumbs with
    | [] -> None
    | c :: cs ->
      let children =
        List.rev_append c.lefts ((z.name, z.entry) :: c.rights)
      in
      Some { name = c.parent_name; entry = Dir children; crumbs = cs }

  (** Navigate to the root. *)
  let rec cd_root z =
    match cd_up z with
    | None   -> z
    | Some z' -> cd_root z'

  (** Current working directory path. *)
  let pwd z =
    let parts = List.rev_map (fun c -> c.parent_name) z.crumbs in
    let parts = parts @ [z.name] in
    match parts with
    | ["/"] -> "/"
    | "/" :: rest -> "/" ^ String.concat "/" rest
    | _ -> String.concat "/" parts

  (** List children of the current directory.
      Returns [None] if current entry is a file. *)
  let ls z =
    match z.entry with
    | File _ -> None
    | Dir children -> Some (List.map fst children)

  (** Create a new empty subdirectory.
      Returns [None] if current entry is a file, or name already exists. *)
  let mkdir name z =
    match z.entry with
    | File _ -> None
    | Dir children ->
      if List.exists (fun (n, _) -> n = name) children then None
      else Some { z with entry = Dir (children @ [(name, Dir [])]) }

  (** Create a new file (or overwrite if it exists).
      Returns [None] if current entry is a file. *)
  let touch name content z =
    match z.entry with
    | File _ -> None
    | Dir children ->
      let replaced = ref false in
      let children' = List.map (fun (n, e) ->
        if n = name then (replaced := true; (n, File content))
        else (n, e)
      ) children in
      let children' =
        if !replaced then children'
        else children' @ [(name, File content)]
      in
      Some { z with entry = Dir children' }

  (** Remove a child entry by name.
      Returns [None] if current is a file or name not found. *)
  let rm name z =
    match z.entry with
    | File _ -> None
    | Dir children ->
      if not (List.exists (fun (n, _) -> n = name) children) then None
      else
        let children' = List.filter (fun (n, _) -> n <> name) children in
        Some { z with entry = Dir children' }

  (** Rename the current entry (the focused node). *)
  let rename new_name z = { z with name = new_name }

  (** Is the current entry a file? *)
  let is_file z = match z.entry with File _ -> true | Dir _ -> false

  (** Is the current entry a directory? *)
  let is_dir z = match z.entry with Dir _ -> true | File _ -> false

  (** Get file content.  [None] if current entry is a Dir. *)
  let read_file z =
    match z.entry with
    | File s -> Some s
    | Dir _  -> None

  (** Count all entries (files + dirs) in the focused subtree. *)
  let rec count_entries = function
    | File _ -> 1
    | Dir children ->
      1 + List.fold_left (fun acc (_, e) -> acc + count_entries e) 0 children

  (** Pretty-print the filesystem tree from the current node. *)
  let rec tree_string indent (name, entry) =
    match entry with
    | File content ->
      Printf.sprintf "%s%s (%d bytes)" indent name (String.length content)
    | Dir children ->
      let header = Printf.sprintf "%s%s/" indent name in
      let child_strs = List.map (tree_string (indent ^ "  ")) children in
      String.concat "\n" (header :: child_strs)

  let to_string z = tree_string "" (z.name, z.entry)
end


(* ================================================================
   TESTS
   ================================================================ *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_equal name expected actual =
  if expected = actual then
    incr tests_passed
  else begin
    Printf.printf "FAIL: %s\n  expected: %s\n  actual:   %s\n"
      name (expected) (actual);
    incr tests_failed
  end

let assert_true name b =
  if b then incr tests_passed
  else begin
    Printf.printf "FAIL: %s (expected true)\n" name;
    incr tests_failed
  end

let assert_false name b =
  if not b then incr tests_passed
  else begin
    Printf.printf "FAIL: %s (expected false)\n" name;
    incr tests_failed
  end

let assert_none name = function
  | None -> incr tests_passed
  | Some _ ->
    Printf.printf "FAIL: %s (expected None)\n" name;
    incr tests_failed

let assert_some name = function
  | Some _ -> incr tests_passed
  | None ->
    Printf.printf "FAIL: %s (expected Some)\n" name;
    incr tests_failed

let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

let string_of_string_list lst =
  "[" ^ String.concat "; " (List.map (Printf.sprintf "%S") lst) ^ "]"

let () =
  Printf.printf "=== Zipper Tests ===\n\n";

  (* -------- List Zipper -------- *)
  Printf.printf "--- List Zipper ---\n";

  (* of_list / to_list *)
  assert_none "of_list empty" (ListZipper.of_list []);
  let z = match ListZipper.of_list [1; 2; 3; 4; 5] with
    | Some z -> z | None -> failwith "unexpected" in
  assert_equal "to_list" "[1; 2; 3; 4; 5]"
    (string_of_int_list (ListZipper.to_list z));
  assert_equal "focus" "1" (string_of_int (ListZipper.focus z));

  (* movement *)
  let z1 = match ListZipper.move_right z with Some z -> z | None -> failwith "r" in
  assert_equal "move_right focus" "2" (string_of_int (ListZipper.focus z1));
  let z2 = match ListZipper.move_right z1 with Some z -> z | None -> failwith "r" in
  assert_equal "move_right 2" "3" (string_of_int (ListZipper.focus z2));
  let z3 = match ListZipper.move_left z2 with Some z -> z | None -> failwith "l" in
  assert_equal "move_left" "2" (string_of_int (ListZipper.focus z3));
  assert_none "move_left at start" (ListZipper.move_left z);
  let zend = ListZipper.fast_forward z in
  assert_equal "fast_forward" "5" (string_of_int (ListZipper.focus zend));
  assert_none "move_right at end" (ListZipper.move_right zend);
  let zstart = ListZipper.rewind zend in
  assert_equal "rewind" "1" (string_of_int (ListZipper.focus zstart));

  (* to_list preserves order after moves *)
  assert_equal "to_list after moves" "[1; 2; 3; 4; 5]"
    (string_of_int_list (ListZipper.to_list z2));

  (* replace / modify *)
  let z_rep = ListZipper.replace 99 z2 in
  assert_equal "replace" "[1; 2; 99; 4; 5]"
    (string_of_int_list (ListZipper.to_list z_rep));
  let z_mod = ListZipper.modify (fun x -> x * 10) z2 in
  assert_equal "modify" "[1; 2; 30; 4; 5]"
    (string_of_int_list (ListZipper.to_list z_mod));

  (* insert left/right *)
  let z_il = ListZipper.insert_left 42 z2 in
  assert_equal "insert_left" "[1; 2; 42; 3; 4; 5]"
    (string_of_int_list (ListZipper.to_list z_il));
  assert_equal "insert_left focus unchanged" "3"
    (string_of_int (ListZipper.focus z_il));
  let z_ir = ListZipper.insert_right 42 z2 in
  assert_equal "insert_right" "[1; 2; 3; 42; 4; 5]"
    (string_of_int_list (ListZipper.to_list z_ir));

  (* delete *)
  let z_del = match ListZipper.delete z2 with Some z -> z | None -> failwith "d" in
  assert_equal "delete" "[1; 2; 4; 5]"
    (string_of_int_list (ListZipper.to_list z_del));
  assert_equal "delete moves right" "4"
    (string_of_int (ListZipper.focus z_del));
  let z_single = match ListZipper.of_list [42] with Some z -> z | None -> failwith "s" in
  assert_none "delete single" (ListZipper.delete z_single);
  (* delete at end moves left *)
  let z_end_del = match ListZipper.delete zend with Some z -> z | None -> failwith "d" in
  assert_equal "delete at end" "4" (string_of_int (ListZipper.focus z_end_del));

  (* length / index *)
  assert_equal "length" "5" (string_of_int (ListZipper.length z));
  assert_equal "index at start" "0" (string_of_int (ListZipper.index z));
  assert_equal "index at 2" "2" (string_of_int (ListZipper.index z2));

  (* goto *)
  let z_g = match ListZipper.goto 3 z with Some z -> z | None -> failwith "g" in
  assert_equal "goto 3" "4" (string_of_int (ListZipper.focus z_g));
  assert_none "goto negative" (ListZipper.goto (-1) z);
  assert_none "goto out of bounds" (ListZipper.goto 5 z);
  let z_g0 = match ListZipper.goto 0 z2 with Some z -> z | None -> failwith "g" in
  assert_equal "goto 0 from middle" "1" (string_of_int (ListZipper.focus z_g0));

  (* map *)
  let z_map = ListZipper.map (fun x -> x + 10) z2 in
  assert_equal "map" "[11; 12; 13; 14; 15]"
    (string_of_int_list (ListZipper.to_list z_map));
  assert_equal "map focus" "13" (string_of_int (ListZipper.focus z_map));

  (* fold_left *)
  let sum = ListZipper.fold_left ( + ) 0 z2 in
  assert_equal "fold_left sum" "15" (string_of_int sum);

  (* find *)
  let z_find = match ListZipper.find (fun x -> x = 4) z with
    | Some z -> z | None -> failwith "find" in
  assert_equal "find" "4" (string_of_int (ListZipper.focus z_find));
  assert_none "find missing" (ListZipper.find (fun x -> x = 99) z);

  (* to_string *)
  assert_equal "to_string" "[1] 2 3 4 5"
    (ListZipper.to_string string_of_int z);
  assert_equal "to_string mid" "1 2 [3] 4 5"
    (ListZipper.to_string string_of_int z2);

  Printf.printf "\n";

  (* -------- Tree Zipper -------- *)
  Printf.printf "--- Tree Zipper ---\n";

  let open TreeZipper in
  (*       1
         /   \
        2     3
       / \     \
      4   5     6   *)
  let tree =
    Node (
      Node (Node (Leaf, 4, Leaf), 2, Node (Leaf, 5, Leaf)),
      1,
      Node (Leaf, 3, Node (Leaf, 6, Leaf))
    ) in
  let z = of_tree tree in
  assert_true "is_root" (is_root z);
  assert_false "is_leaf at root" (is_leaf z);
  assert_equal "depth at root" "0" (string_of_int (depth z));
  assert_equal "root value" "1"
    (match value z with Some v -> string_of_int v | None -> "none");

  (* navigation *)
  let z_l = match go_left z with Some z -> z | None -> failwith "l" in
  assert_equal "go_left value" "2"
    (match value z_l with Some v -> string_of_int v | None -> "none");
  assert_equal "depth after left" "1" (string_of_int (depth z_l));
  assert_false "not root after left" (is_root z_l);

  let z_ll = match go_left z_l with Some z -> z | None -> failwith "ll" in
  assert_equal "go_left_left value" "4"
    (match value z_ll with Some v -> string_of_int v | None -> "none");
  assert_equal "depth 2" "2" (string_of_int (depth z_ll));

  (* leaf children *)
  assert_none "go_left from leaf" (go_left z_ll);
  assert_none "go_right from leaf's children"
    (match go_left z_ll with Some z -> go_left z | None -> None);

  let z_lr = match go_right z_l with Some z -> z | None -> failwith "lr" in
  assert_equal "go_right from 2" "5"
    (match value z_lr with Some v -> string_of_int v | None -> "none");

  (* go_up reconstructs correctly *)
  let z_back = match go_up z_lr with Some z -> z | None -> failwith "up" in
  assert_equal "go_up back to 2" "2"
    (match value z_back with Some v -> string_of_int v | None -> "none");
  assert_none "go_up from root" (go_up z);

  (* top returns to root *)
  let z_top = top z_ll in
  assert_true "top is_root" (is_root z_top);
  assert_equal "to_tree preserves" (tree_to_string string_of_int tree)
    (tree_to_string string_of_int (to_tree z_top));

  (* to_tree from anywhere *)
  assert_equal "to_tree from depth 2" (tree_to_string string_of_int tree)
    (tree_to_string string_of_int (to_tree z_ll));

  (* modify *)
  let z_mod = match modify (fun x -> x * 100) z_l with
    | Some z -> z | None -> failwith "mod" in
  assert_equal "modify" "200"
    (match value z_mod with Some v -> string_of_int v | None -> "none");
  (* original unaffected by modify (functional) *)
  assert_equal "original unchanged" "2"
    (match value z_l with Some v -> string_of_int v | None -> "none");
  assert_none "modify leaf" (modify (fun x -> x) (of_tree Leaf));

  (* replace *)
  let z_repl = replace (Node (Leaf, 99, Leaf)) z_l in
  assert_equal "replace subtree" "99"
    (match value z_repl with Some v -> string_of_int v | None -> "none");

  (* prune *)
  let z_pruned = prune z_l in
  assert_true "prune makes leaf" (is_leaf z_pruned);
  let pruned_tree = to_tree z_pruned in
  assert_equal "pruned tree" "(. 1 (. 3 (. 6 .)))"
    (tree_to_string string_of_int pruned_tree);

  (* insert_left / insert_right *)
  let z_il = insert_left 10 z in
  assert_equal "insert_left tree"
    "(((. 4 .) 2 (. 5 .)) 10 .)"
    (match focus z_il with
     | Node (l, _, _) -> tree_to_string string_of_int l
     | Leaf -> "leaf");
  (* Actually check the whole focus *)
  let z_ir = insert_right 20 z in
  let right_tree = match focus z_ir with
    | Node (_, _, r) -> tree_to_string string_of_int r
    | Leaf -> "leaf" in
  assert_equal "insert_right tree" "(. 20 (. 3 (. 6 .)))" right_tree;

  (* subtree_size / subtree_height *)
  assert_equal "subtree_size full" "6"
    (string_of_int (subtree_size tree));
  assert_equal "subtree_size left" "3"
    (string_of_int (subtree_size (focus z_l)));
  assert_equal "subtree_height" "3"
    (string_of_int (subtree_height tree));

  (* leftmost / rightmost *)
  let z_lm = leftmost z in
  assert_true "leftmost is leaf" (is_leaf z_lm);
  assert_equal "leftmost depth" "3" (string_of_int (depth z_lm));
  let z_rm = rightmost z in
  assert_true "rightmost is leaf" (is_leaf z_rm);

  (* inorder *)
  assert_equal "inorder" "[4; 2; 5; 1; 3; 6]"
    (string_of_int_list (inorder tree));

  Printf.printf "\n";

  (* -------- Filesystem Zipper -------- *)
  Printf.printf "--- Filesystem Zipper ---\n";

  let open FSZipper in
  let fs = Dir [
    ("bin", Dir [
      ("ls", File "#!/bin/ls");
      ("cat", File "#!/bin/cat");
    ]);
    ("home", Dir [
      ("user", Dir [
        ("notes.txt", File "Hello, World!");
        ("code", Dir [
          ("main.ml", File "let () = print_endline \"hi\"");
        ]);
      ]);
    ]);
    ("tmp", Dir []);
  ] in
  let z = of_entry fs in

  (* pwd at root *)
  assert_equal "pwd root" "/" (pwd z);

  (* ls at root *)
  (match ls z with
   | Some names ->
     assert_equal "ls root" "[\"bin\"; \"home\"; \"tmp\"]"
       (string_of_string_list names)
   | None -> assert_true "ls root failed" false);

  (* cd into nested dirs *)
  let z_home = match cd "home" z with Some z -> z | None -> failwith "cd home" in
  assert_equal "pwd home" "/home" (pwd z_home);
  let z_user = match cd "user" z_home with Some z -> z | None -> failwith "cd user" in
  assert_equal "pwd user" "/home/user" (pwd z_user);
  let z_code = match cd "code" z_user with Some z -> z | None -> failwith "cd code" in
  assert_equal "pwd code" "/home/user/code" (pwd z_code);

  (* cd into file *)
  let z_file = match cd "main.ml" z_code with Some z -> z | None -> failwith "cd file" in
  assert_equal "pwd file" "/home/user/code/main.ml" (pwd z_file);
  assert_true "is_file" (is_file z_file);
  assert_false "not is_dir" (is_dir z_file);
  assert_equal "read_file" "let () = print_endline \"hi\""
    (match read_file z_file with Some s -> s | None -> "none");

  (* cd_up *)
  let z_up = match cd_up z_file with Some z -> z | None -> failwith "cd_up" in
  assert_equal "cd_up pwd" "/home/user/code" (pwd z_up);
  assert_true "cd_up is_dir" (is_dir z_up);

  (* cd_root *)
  let z_root = cd_root z_code in
  assert_equal "cd_root pwd" "/" (pwd z_root);

  (* cd non-existent *)
  assert_none "cd non-existent" (cd "bogus" z);

  (* cd from file *)
  assert_none "cd from file" (cd "sub" z_file);

  (* cd_up from root *)
  assert_none "cd_up from root" (cd_up z);

  (* mkdir *)
  let z_mkdir = match mkdir "new_dir" z_user with
    | Some z -> z | None -> failwith "mkdir" in
  (match ls z_mkdir with
   | Some names ->
     assert_true "mkdir added" (List.mem "new_dir" names)
   | None -> assert_true "mkdir ls failed" false);
  (* mkdir duplicate *)
  assert_none "mkdir duplicate" (mkdir "code" z_user);
  (* mkdir on file *)
  assert_none "mkdir on file" (mkdir "x" z_file);

  (* touch - new file *)
  let z_touch = match touch "readme.md" "# Hello" z_user with
    | Some z -> z | None -> failwith "touch" in
  let z_readme = match cd "readme.md" z_touch with
    | Some z -> z | None -> failwith "cd readme" in
  assert_equal "touch content" "# Hello"
    (match read_file z_readme with Some s -> s | None -> "none");

  (* touch - overwrite *)
  let z_overwrite = match touch "notes.txt" "Updated!" z_user with
    | Some z -> z | None -> failwith "touch overwrite" in
  let z_notes = match cd "notes.txt" z_overwrite with
    | Some z -> z | None -> failwith "cd notes" in
  assert_equal "touch overwrite" "Updated!"
    (match read_file z_notes with Some s -> s | None -> "none");

  (* touch on file *)
  assert_none "touch on file" (touch "x" "y" z_file);

  (* rm *)
  let z_rm = match rm "tmp" z with Some z -> z | None -> failwith "rm" in
  (match ls z_rm with
   | Some names ->
     assert_false "rm removed" (List.mem "tmp" names)
   | None -> assert_true "rm ls failed" false);
  assert_none "rm non-existent" (rm "bogus" z);
  assert_none "rm from file" (rm "x" z_file);

  (* rename *)
  let z_renamed = rename "documents" z_user in
  assert_equal "rename pwd" "/home/documents" (pwd z_renamed);

  (* count_entries *)
  let count = count_entries fs in
  assert_equal "count_entries" "10" (string_of_int count);

  (* ls on file *)
  assert_none "ls on file" (ls z_file);

  (* read_file on dir *)
  assert_none "read_file on dir" (read_file z);

  (* roundtrip: modify and reconstruct *)
  let z_modified = match touch "new.txt" "data" z_user with
    | Some z -> z | None -> failwith "m" in
  let (root_name, _root_entry) = to_entry (cd_root z_modified) in
  assert_equal "roundtrip root name" "/" root_name;

  Printf.printf "\n";

  (* -------- Summary -------- *)
  Printf.printf "=== Results: %d passed, %d failed ===\n"
    !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1


(* ================================================================
   DEMO
   ================================================================ *)

let () =
  Printf.printf "\n=== Zipper Demos ===\n\n";

  (* List Zipper demo *)
  Printf.printf "--- List Zipper ---\n";
  let z = match ListZipper.of_list [1; 2; 3; 4; 5] with
    | Some z -> z | None -> failwith "empty" in
  Printf.printf "Initial:   %s\n" (ListZipper.to_string string_of_int z);
  let z = match ListZipper.move_right z with Some z -> z | None -> z in
  let z = match ListZipper.move_right z with Some z -> z | None -> z in
  Printf.printf "After >>:  %s\n" (ListZipper.to_string string_of_int z);
  let z = ListZipper.replace 99 z in
  Printf.printf "Replace 3: %s\n" (ListZipper.to_string string_of_int z);
  let z = ListZipper.insert_left 42 z in
  Printf.printf "Insert 42: %s\n" (ListZipper.to_string string_of_int z);
  let z = match ListZipper.delete z with Some z -> z | None -> z in
  Printf.printf "Delete:    %s\n" (ListZipper.to_string string_of_int z);
  Printf.printf "List:      %s\n"
    (String.concat ", " (List.map string_of_int (ListZipper.to_list z)));
  Printf.printf "\n";

  (* Tree Zipper demo *)
  Printf.printf "--- Tree Zipper ---\n";
  let open TreeZipper in
  let tree = Node (
    Node (Node (Leaf, 4, Leaf), 2, Node (Leaf, 5, Leaf)),
    1,
    Node (Leaf, 3, Node (Leaf, 6, Leaf))
  ) in
  Printf.printf "Tree:    %s\n" (tree_to_string string_of_int tree);
  Printf.printf "Inorder: %s\n"
    (String.concat ", " (List.map string_of_int (inorder tree)));
  let z = of_tree tree in
  let z = match go_left z with Some z -> z | None -> z in
  Printf.printf "Go left: focused on %s\n"
    (match value z with Some v -> string_of_int v | None -> "leaf");
  let z = match modify (fun x -> x * 100) z with Some z -> z | None -> z in
  Printf.printf "Modify:  focused on %s\n"
    (match value z with Some v -> string_of_int v | None -> "leaf");
  let result = to_tree (top z) in
  Printf.printf "Result:  %s\n" (tree_to_string string_of_int result);
  Printf.printf "Inorder: %s\n"
    (String.concat ", " (List.map string_of_int (inorder result)));
  Printf.printf "\n";

  (* Filesystem Zipper demo *)
  Printf.printf "--- Filesystem Zipper ---\n";
  let open FSZipper in
  let fs = Dir [
    ("src", Dir [
      ("main.ml", File "let () = print_endline \"hello\"");
      ("utils.ml", File "let id x = x");
    ]);
    ("docs", Dir [
      ("README.md", File "# My Project");
    ]);
    ("Makefile", File "all: main");
  ] in
  let z = of_entry fs in
  Printf.printf "%s\n\n" (to_string z);
  Printf.printf "pwd: %s\n" (pwd z);
  Printf.printf "ls:  %s\n"
    (match ls z with
     | Some names -> String.concat ", " names
     | None -> "(not a directory)");
  let z = match cd "src" z with Some z -> z | None -> z in
  Printf.printf "\ncd src -> pwd: %s\n" (pwd z);
  let z = match mkdir "tests" z with Some z -> z | None -> z in
  Printf.printf "mkdir tests -> ls: %s\n"
    (match ls z with
     | Some names -> String.concat ", " names
     | None -> "(not a directory)");
  let z = match touch "lib.ml" "let version = 1" z with Some z -> z | None -> z in
  Printf.printf "touch lib.ml -> ls: %s\n"
    (match ls z with
     | Some names -> String.concat ", " names
     | None -> "(not a directory)");
  let z = cd_root z in
  Printf.printf "\nFull tree after edits:\n%s\n" (to_string z)
