(* AA Tree - A balanced binary search tree (Arne Andersson, 1993)
   
   AA trees are a simplified variant of red-black trees where:
   - Red nodes can only appear as right children
   - This eliminates half the restructuring cases
   - Uses a "level" instead of color
   
   Invariants:
   1. Leaf nodes have level 1
   2. Left children have level = parent level - 1
   3. Right children have level = parent level or parent level - 1
   4. Right grandchildren have level < grandparent level
   5. Every node with level > 1 has two children
   
   All operations are O(log n). The beauty is that balancing needs only
   two simple operations: skew (right rotation) and split (left rotation).
*)

type 'a tree =
  | Leaf
  | Node of { level: int; left: 'a tree; value: 'a; right: 'a tree }

let level = function
  | Leaf -> 0
  | Node n -> n.level

(* Skew: fix left horizontal link (left child at same level)
   
       T           L
      / \         / \
     L   R  =>  A    T
    / \              / \
   A   B            B   R
   
   When L.level = T.level, rotate right *)
let skew = function
  | Node ({ left = Node l; _ } as t) when l.level = t.level ->
    Node { l with right = Node { t with left = l.right } }
  | t -> t

(* Split: fix consecutive right horizontal links
   
     T               R
    / \             /   \
   A   R    =>     T     X
      / \         / \
     B   X       A   B
   
   When T.level = X.level (right-right same level), rotate left and bump level *)
let split = function
  | Node ({ right = Node ({ right = Node rr; _ } as r); _ } as t)
    when t.level = rr.level ->
    Node { r with level = r.level + 1;
                  left = Node { t with right = r.left } }
  | t -> t

(* Insert a value into the AA tree *)
let rec insert x = function
  | Leaf -> Node { level = 1; left = Leaf; value = x; right = Leaf }
  | Node n ->
    let node =
      if x < n.value then Node { n with left = insert x n.left }
      else if x > n.value then Node { n with right = insert x n.right }
      else Node n  (* duplicate: no-op *)
    in
    node |> skew |> split

(* Check membership *)
let rec mem x = function
  | Leaf -> false
  | Node n ->
    if x < n.value then mem x n.left
    else if x > n.value then mem x n.right
    else true

(* Find minimum value *)
let rec min_value = function
  | Leaf -> failwith "min_value: empty tree"
  | Node { left = Leaf; value; _ } -> value
  | Node { left; _ } -> min_value left

(* Find maximum value *)
let rec max_value = function
  | Leaf -> failwith "max_value: empty tree"
  | Node { right = Leaf; value; _ } -> value
  | Node { right; _ } -> max_value right

(* Decrease the level of a node if needed after deletion *)
let decrease_level = function
  | Node n ->
    let should_be = min (level n.left) (level n.right) + 1 in
    if should_be < n.level then
      let right' = match n.right with
        | Node r when should_be < r.level ->
          Node { r with level = should_be }
        | r -> r
      in
      Node { n with level = should_be; right = right' }
  | t -> t

(* Delete a value from the AA tree *)
let rec delete x = function
  | Leaf -> Leaf
  | Node n ->
    let node =
      if x < n.value then Node { n with left = delete x n.left }
      else if x > n.value then Node { n with right = delete x n.right }
      else
        (* Found the node to delete *)
        match n.left, n.right with
        | Leaf, Leaf -> Leaf
        | Leaf, _ ->
          let successor = min_value n.right in
          Node { n with value = successor; right = delete successor n.right }
        | _, _ ->
          let predecessor = max_value n.left in
          Node { n with value = predecessor; left = delete predecessor n.left }
    in
    (* Rebalance after deletion *)
    node
    |> decrease_level
    |> skew
    |> (function
      | Node n -> Node { n with right = skew n.right } |> (function
        | Node n -> Node { n with right = match n.right with
            | Node r -> Node { r with right = skew r.right }
            | t -> t }
        | t -> t)
      | t -> t)
    |> split
    |> (function
      | Node n -> Node { n with right = split n.right }
      | t -> t)

(* Convert tree to sorted list (in-order traversal) *)
let rec to_list = function
  | Leaf -> []
  | Node n -> to_list n.left @ [n.value] @ to_list n.right

(* Build tree from a list *)
let of_list xs = List.fold_left (fun t x -> insert x t) Leaf xs

(* Count nodes *)
let rec size = function
  | Leaf -> 0
  | Node n -> 1 + size n.left + size n.right

(* Height of tree *)
let rec height = function
  | Leaf -> 0
  | Node n -> 1 + max (height n.left) (height n.right)

(* Check if tree is empty *)
let is_empty = function
  | Leaf -> true
  | Node _ -> false

(* Fold over tree in order *)
let rec fold_inorder f acc = function
  | Leaf -> acc
  | Node n ->
    let acc = fold_inorder f acc n.left in
    let acc = f acc n.value in
    fold_inorder f acc n.right

(* Iterator: find successor of a value *)
let rec successor x = function
  | Leaf -> None
  | Node n ->
    if x < n.value then
      match successor x n.left with
      | Some _ as result -> result
      | None -> Some n.value
    else successor x n.right

(* Iterator: find predecessor of a value *)
let rec predecessor x = function
  | Leaf -> None
  | Node n ->
    if x > n.value then
      match predecessor x n.right with
      | Some _ as result -> result
      | None -> Some n.value
    else predecessor x n.left

(* Range query: find all values in [lo, hi] *)
let rec range lo hi = function
  | Leaf -> []
  | Node n ->
    let left_part = if n.value > lo then range lo hi n.left else [] in
    let self = if n.value >= lo && n.value <= hi then [n.value] else [] in
    let right_part = if n.value < hi then range lo hi n.right else [] in
    left_part @ self @ right_part

(* Validate AA tree invariants *)
let rec validate = function
  | Leaf -> true
  | Node n ->
    (* Left child level must be exactly one less *)
    let left_ok = level n.left = n.level - 1 in
    (* Right child level must be parent or parent - 1 *)
    let right_ok = level n.right = n.level || level n.right = n.level - 1 in
    (* Right grandchild level must be strictly less *)
    let rgc_ok = match n.right with
      | Node r -> level r.right < n.level
      | Leaf -> true
    in
    left_ok && right_ok && rgc_ok && validate n.left && validate n.right

(* Pretty-print the tree structure *)
let rec pp_tree indent = function
  | Leaf -> ()
  | Node n ->
    pp_tree (indent ^ "  ") n.right;
    Printf.printf "%s[%d] %d\n" indent n.level n.value;
    pp_tree (indent ^ "  ") n.left

(* ===== Demo ===== *)
let () =
  Printf.printf "=== AA Tree Demo ===\n\n";
  
  (* Build a tree *)
  let values = [5; 3; 7; 1; 4; 6; 8; 2; 9; 0] in
  Printf.printf "Inserting: ";
  List.iter (Printf.printf "%d ") values;
  Printf.printf "\n\n";
  
  let tree = of_list values in
  
  Printf.printf "Tree structure (level shown in brackets):\n";
  pp_tree "" tree;
  Printf.printf "\n";
  
  Printf.printf "Sorted: ";
  List.iter (Printf.printf "%d ") (to_list tree);
  Printf.printf "\n";
  
  Printf.printf "Size: %d\n" (size tree);
  Printf.printf "Height: %d\n" (height tree);
  Printf.printf "Valid AA tree: %b\n\n" (validate tree);
  
  (* Membership *)
  Printf.printf "Contains 4: %b\n" (mem 4 tree);
  Printf.printf "Contains 11: %b\n" (mem 11 tree);
  Printf.printf "Min: %d, Max: %d\n" (min_value tree) (max_value tree);
  
  (* Successor/predecessor *)
  Printf.printf "Successor of 4: %s\n"
    (match successor 4 tree with Some v -> string_of_int v | None -> "none");
  Printf.printf "Predecessor of 4: %s\n\n"
    (match predecessor 4 tree with Some v -> string_of_int v | None -> "none");
  
  (* Range query *)
  Printf.printf "Values in [3, 7]: ";
  List.iter (Printf.printf "%d ") (range 3 7 tree);
  Printf.printf "\n\n";
  
  (* Deletion *)
  Printf.printf "Deleting 3, 7, 0:\n";
  let tree = tree |> delete 3 |> delete 7 |> delete 0 in
  Printf.printf "Sorted after deletion: ";
  List.iter (Printf.printf "%d ") (to_list tree);
  Printf.printf "\n";
  Printf.printf "Still valid: %b\n\n" (validate tree);
  
  (* Fold *)
  let sum = fold_inorder (fun acc x -> acc + x) 0 tree in
  Printf.printf "Sum of all values: %d\n" sum;
  
  Printf.printf "\n=== AA Tree: Simple yet perfectly balanced! ===\n"
