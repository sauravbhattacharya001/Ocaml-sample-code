(** AA Tree — a balanced binary search tree (Arne Andersson, 1993).

    AA trees are a simplified variant of red–black trees where:
    - red nodes can only appear as right children, which eliminates half
      the restructuring cases;
    - balance is tracked via a per-node {!level} rather than a colour.

    {1 Invariants}
    + Leaf nodes have level [1].
    + Left children have level = parent level − 1.
    + Right children have level = parent level or parent level − 1.
    + Right grand-children have level < grand-parent level.
    + Every node with level > 1 has two children.

    All operations are O(log n). Balancing needs only two simple
    rotations: {!skew} (right rotation) and {!split} (left rotation).
*)

(** The AA tree itself. [Leaf] is the empty tree; [Node] carries an
    AA-balance [level], its [left] / [right] subtrees, and a [value]. *)
type 'a tree =
  | Leaf
  | Node of { level: int; left: 'a tree; value: 'a; right: 'a tree }

(** [level t] is the AA balance level of [t] (0 for [Leaf]). *)
let level = function
  | Leaf -> 0
  | Node n -> n.level

(** [skew t] fixes a left horizontal link (left child at the same level
    as its parent) by rotating right. Idempotent on already-balanced
    trees. O(1).
{v
      T           L
     / \         / \
    L   R  =>  A   T
   / \            / \
  A   B          B   R
v} *)
let skew = function
  | Node ({ left = Node l; _ } as t) when l.level = t.level ->
    Node { l with right = Node { t with left = l.right } }
  | t -> t

(** [split t] fixes two consecutive right horizontal links by rotating
    left and bumping the new root's level. Idempotent on already-balanced
    trees. O(1).
{v
    T               R
   / \             / \
  A   R    =>     T   X
     / \         / \
    B   X       A   B
v} *)
let split = function
  | Node ({ right = Node ({ right = Node rr; _ } as r); _ } as t)
    when t.level = rr.level ->
    Node { r with level = r.level + 1;
                  left = Node { t with right = r.left } }
  | t -> t

(** [insert x t] returns a new tree containing [x]. Duplicates are
    silently ignored (the tree behaves as a set). O(log n). *)
let rec insert x = function
  | Leaf -> Node { level = 1; left = Leaf; value = x; right = Leaf }
  | Node n ->
    let node =
      if x < n.value then Node { n with left = insert x n.left }
      else if x > n.value then Node { n with right = insert x n.right }
      else Node n  (* duplicate: no-op *)
    in
    node |> skew |> split

(** [mem x t] is [true] iff [x] occurs in [t]. O(log n). *)
let rec mem x = function
  | Leaf -> false
  | Node n ->
    if x < n.value then mem x n.left
    else if x > n.value then mem x n.right
    else true

(** [min_value t] is the smallest element of [t].
    @raise Failure if [t] is empty. O(log n). *)
let rec min_value = function
  | Leaf -> failwith "min_value: empty tree"
  | Node { left = Leaf; value; _ } -> value
  | Node { left; _ } -> min_value left

(** [max_value t] is the largest element of [t].
    @raise Failure if [t] is empty. O(log n). *)
let rec max_value = function
  | Leaf -> failwith "max_value: empty tree"
  | Node { right = Leaf; value; _ } -> value
  | Node { right; _ } -> max_value right

(** [decrease_level t] lowers the level of [t] (and the level of its
    right child if necessary) so that the AA invariants still hold after
    a {!delete}. Internal helper. O(1). *)
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

(** [delete x t] removes [x] from [t]. If [x] is absent the tree is
    returned unchanged. O(log n). *)
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

(** [to_list t] is an in-order traversal of [t], producing the elements
    in ascending order. O(n). *)
let rec to_list = function
  | Leaf -> []
  | Node n -> to_list n.left @ [n.value] @ to_list n.right

(** [of_list xs] inserts every element of [xs] into the empty tree,
    left-to-right. O(n log n). *)
let of_list xs = List.fold_left (fun t x -> insert x t) Leaf xs

(** [size t] is the number of elements stored in [t]. O(n). *)
let rec size = function
  | Leaf -> 0
  | Node n -> 1 + size n.left + size n.right

(** [height t] is the length of the longest root-to-leaf path in [t].
    For an AA tree of size [n] this is bounded by 2·log₂(n+1). O(n). *)
let rec height = function
  | Leaf -> 0
  | Node n -> 1 + max (height n.left) (height n.right)

(** [is_empty t] is [true] iff [t] contains no elements. O(1). *)
let is_empty = function
  | Leaf -> true
  | Node _ -> false

(** [fold_inorder f acc t] folds [f] over the elements of [t] in
    ascending order: [f (... (f (f acc x1) x2) ...) xn]. O(n). *)
let rec fold_inorder f acc = function
  | Leaf -> acc
  | Node n ->
    let acc = fold_inorder f acc n.left in
    let acc = f acc n.value in
    fold_inorder f acc n.right

(** [successor x t] is the smallest element of [t] strictly greater than
    [x], or [None] if [x] is at or above the maximum. O(log n).
    [x] need not be present in [t]. *)
let rec successor x = function
  | Leaf -> None
  | Node n ->
    if x < n.value then
      match successor x n.left with
      | Some _ as result -> result
      | None -> Some n.value
    else successor x n.right

(** [predecessor x t] is the largest element of [t] strictly less than
    [x], or [None] if [x] is at or below the minimum. O(log n).
    [x] need not be present in [t]. *)
let rec predecessor x = function
  | Leaf -> None
  | Node n ->
    if x > n.value then
      match predecessor x n.right with
      | Some _ as result -> result
      | None -> Some n.value
    else predecessor x n.left

(** [range lo hi t] returns, in ascending order, every element [v] of
    [t] with [lo <= v <= hi]. O(log n + k) where [k] is the size of the
    output. *)
let rec range lo hi = function
  | Leaf -> []
  | Node n ->
    let left_part = if n.value > lo then range lo hi n.left else [] in
    let self = if n.value >= lo && n.value <= hi then [n.value] else [] in
    let right_part = if n.value < hi then range lo hi n.right else [] in
    left_part @ self @ right_part

(** [validate t] is [true] iff [t] satisfies all AA-tree invariants
    (used for testing / property checks). O(n). *)
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

(** [pp_tree indent t] prints [t] sideways to [stdout] with [indent]
    as the leading whitespace for the root. Useful for debugging. *)
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
