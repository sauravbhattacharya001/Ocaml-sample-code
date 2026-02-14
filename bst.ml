(* Binary search tree operations using algebraic data types *)
(* Demonstrates: variants, pattern matching, recursion *)

type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

(* Insert a value into a BST *)
let rec insert x = function
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (left, v, right) ->
    if x < v then Node (insert x left, v, right)
    else if x > v then Node (left, v, insert x right)
    else Node (left, v, right)  (* duplicate: no change *)

(* Check if a value exists in the tree *)
let rec member x = function
  | Leaf -> false
  | Node (left, v, right) ->
    if x = v then true
    else if x < v then member x left
    else member x right

(* In-order traversal returns a sorted list *)
(* Uses an accumulator to avoid O(n) list concatenation at each node,
   giving O(n) overall instead of O(n²) with naive @ approach *)
let inorder tree =
  let rec aux acc = function
    | Leaf -> acc
    | Node (left, v, right) -> aux (v :: aux acc right) left
  in
  aux [] tree

(* Find the minimum element *)
let rec min_elem = function
  | Leaf -> None
  | Node (Leaf, v, _) -> Some v
  | Node (left, _, _) -> min_elem left

(* Find the maximum element *)
let rec max_elem = function
  | Leaf -> None
  | Node (_, v, Leaf) -> Some v
  | Node (_, _, right) -> max_elem right

(* Count the number of nodes *)
let rec size = function
  | Leaf -> 0
  | Node (left, _, right) -> 1 + size left + size right

(* Tree depth *)
let rec depth = function
  | Leaf -> 0
  | Node (left, _, right) -> 1 + max (depth left) (depth right)

(* Delete a value from the BST *)
let rec delete x = function
  | Leaf -> Leaf
  | Node (left, v, right) ->
    if x < v then Node (delete x left, v, right)
    else if x > v then Node (left, v, delete x right)
    else
      (* Found the node to delete *)
      match left, right with
      | Leaf, _ -> right           (* no left child *)
      | _, Leaf -> left            (* no right child *)
      | _ ->                       (* two children: replace with in-order successor *)
        (match min_elem right with
         | None -> Leaf  (* unreachable since right <> Leaf *)
         | Some successor -> Node (left, successor, delete successor right))

(* Build a tree from a list *)
let tree_of_list lst =
  List.fold_left (fun acc x -> insert x acc) Leaf lst;;

(* Example usage *)
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
  Printf.printf "Contains 3 after delete: %b\n" (member 3 t2);;
