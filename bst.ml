(** Binary Search Tree — Algebraic Data Types & Pattern Matching

    A purely functional binary search tree implementation demonstrating
    OCaml's algebraic data types, pattern matching, and recursion.

    All operations preserve the BST invariant: for every [Node (l, v, r)],
    all values in [l] are strictly less than [v] and all values in [r]
    are strictly greater.

    Duplicates are silently ignored on insertion. *)

(** {1 Types} *)

(** A polymorphic binary tree. ['a] must support structural comparison. *)
type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

(** {1 Core Operations} *)

(** [insert x t] returns a new BST with [x] added.
    If [x] already exists in [t], the tree is returned unchanged.
    @param x the value to insert
    @param t the tree to insert into
    @return a new tree containing [x] *)
let rec insert x = function
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (left, v, right) ->
    if x < v then Node (insert x left, v, right)
    else if x > v then Node (left, v, insert x right)
    else Node (left, v, right)

(** [member x t] tests whether [x] is present in tree [t].
    Runs in O(h) where h is the height of the tree.
    @return [true] if [x] is found, [false] otherwise *)
let rec member x = function
  | Leaf -> false
  | Node (left, v, right) ->
    if x = v then true
    else if x < v then member x left
    else member x right

(** {1 Traversal} *)

(** [inorder t] returns the elements of [t] in sorted (ascending) order.

    Uses an accumulator to avoid O(n) list concatenation at each node,
    giving O(n) overall instead of O(n²) with a naive approach. *)
let inorder tree =
  let rec aux acc = function
    | Leaf -> acc
    | Node (left, v, right) -> aux (v :: aux acc right) left
  in
  aux [] tree

(** {1 Queries} *)

(** [min_elem t] returns the smallest element in [t], or [None] if empty.
    Follows the leftmost spine of the tree. *)
let rec min_elem = function
  | Leaf -> None
  | Node (Leaf, v, _) -> Some v
  | Node (left, _, _) -> min_elem left

(** [max_elem t] returns the largest element in [t], or [None] if empty.
    Follows the rightmost spine of the tree. *)
let rec max_elem = function
  | Leaf -> None
  | Node (_, v, Leaf) -> Some v
  | Node (_, _, right) -> max_elem right

(** [size t] returns the number of nodes in [t]. O(n). *)
let rec size = function
  | Leaf -> 0
  | Node (left, _, right) -> 1 + size left + size right

(** [depth t] returns the height of [t] (longest root-to-leaf path).
    An empty tree ([Leaf]) has depth 0. *)
let rec depth = function
  | Leaf -> 0
  | Node (left, _, right) -> 1 + max (depth left) (depth right)

(** {1 Deletion} *)

(** [delete x t] removes [x] from [t].
    If [x] is not present, the tree is returned unchanged.

    When deleting a node with two children, the in-order successor
    (minimum of the right subtree) replaces the deleted node. *)
let rec delete x = function
  | Leaf -> Leaf
  | Node (left, v, right) ->
    if x < v then Node (delete x left, v, right)
    else if x > v then Node (left, v, delete x right)
    else
      match left, right with
      | Leaf, _ -> right
      | _, Leaf -> left
      | _ ->
        (match min_elem right with
         | None -> Leaf
         | Some successor -> Node (left, successor, delete successor right))

(** {1 Construction} *)

(** [tree_of_list lst] builds a BST by folding [insert] over [lst].
    The resulting tree shape depends on insertion order. *)
let tree_of_list lst =
  List.fold_left (fun acc x -> insert x acc) Leaf lst

(** {1 Example} *)

let () =
  let t = tree_of_list [5; 3; 7; 1; 4; 6; 8] in
  Printf.printf "In-order: ";
  List.iter (Printf.printf "%d ") (inorder t);
  print_newline ();
  Printf.printf "Contains 4: %b\n" (member 4 t);
  Printf.printf "Contains 9: %b\n" (member 9 t);
  Printf.printf "Depth: %d\n" (depth t);
  Printf.printf "Size: %d\n" (size t);
  (match min_elem t with
  | None -> print_endline "Empty tree"
  | Some m -> Printf.printf "Minimum: %d\n" m);
  (match max_elem t with
  | None -> ()
  | Some m -> Printf.printf "Maximum: %d\n" m);
  let t2 = delete 3 t in
  Printf.printf "After deleting 3: ";
  List.iter (Printf.printf "%d ") (inorder t2);
  print_newline ();
  Printf.printf "Contains 3 after delete: %b\n" (member 3 t2)
