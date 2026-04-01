(* weight_balanced_tree.ml - Weight-Balanced Tree (BB[α] Tree)
 *
 * A weight-balanced tree (also called a BB[α] tree or Adams tree)
 * is a self-balancing binary search tree where each node maintains
 * a size field, and balance is enforced by keeping the ratio of
 * left/right subtree sizes within a constant factor.
 *
 * The balance invariant: for every node with left subtree of size l
 * and right subtree of size r, both l and r are at most
 * delta * (l + r + 1), where delta is typically 3.
 *
 * When rebalancing is needed, single or double rotations are used,
 * chosen based on the gamma ratio (typically 2).
 *
 * Features:
 *   - Insert, delete, member lookup
 *   - Kth smallest / rank queries
 *   - Split and join operations
 *   - Set operations (union, intersection, difference)
 *   - Range queries [lo, hi]
 *   - Fold, map, to_list, of_list
 *   - Pretty printing
 *
 * All operations are O(log n) worst-case.
 *
 * This is the balancing scheme used by Haskell's Data.Set and Data.Map.
 *)

(* ── Types ───────────────────────────────────────────── *)

type 'a tree =
  | Leaf
  | Node of { left: 'a tree; value: 'a; right: 'a tree; size: int }

(* ── Balance parameters ──────────────────────────────── *)

(* delta: max ratio between sibling subtree sizes *)
let delta = 3

(* gamma: determines single vs double rotation *)
let gamma = 2

(* ── Size ────────────────────────────────────────────── *)

let size = function
  | Leaf -> 0
  | Node n -> n.size

let node left value right =
  Node { left; value; right; size = size left + size right + 1 }

(* ── Rotations ───────────────────────────────────────── *)

let single_left = function
  | Node { left = a; value = x; right = Node { left = b; value = y; right = c; _ }; _ } ->
    node (node a x b) y c
  | t -> t

let single_right = function
  | Node { left = Node { left = a; value = x; right = b; _ }; value = y; right = c; _ } ->
    node a x (node b y c)
  | t -> t

let double_left = function
  | Node { left = a; value = x;
           right = Node { left = Node { left = b1; value = y; right = b2; _ };
                          value = z; right = c; _ }; _ } ->
    node (node a x b1) y (node b2 z c)
  | t -> t

let double_right = function
  | Node { left = Node { left = a; value = x;
                          right = Node { left = b1; value = y; right = b2; _ }; _ };
           value = z; right = c; _ } ->
    node (node a x b1) y (node b2 z c)
  | t -> t

(* ── Balancing ───────────────────────────────────────── *)

let balance_left left value right =
  let ln = size left and rn = size right in
  if rn > delta * (ln + 1) then begin
    (* right is too heavy *)
    match right with
    | Node { left = rl; _ } when size rl < gamma * (size right - size rl - 1) ->
      single_left (node left value right)
    | _ ->
      double_left (node left value right)
  end
  else node left value right

let balance_right left value right =
  let ln = size left and rn = size right in
  if ln > delta * (rn + 1) then begin
    (* left is too heavy *)
    match left with
    | Node { right = lr; _ } when size lr < gamma * (size left - size lr - 1) ->
      single_right (node left value right)
    | _ ->
      double_right (node left value right)
  end
  else node left value right

let balance left value right =
  let ln = size left and rn = size right in
  if rn > delta * (ln + 1) then
    balance_left left value right
  else if ln > delta * (rn + 1) then
    balance_right left value right
  else
    node left value right

(* ── Insert ──────────────────────────────────────────── *)

let rec insert x = function
  | Leaf -> node Leaf x Leaf
  | Node n ->
    if x < n.value then
      balance (insert x n.left) n.value n.right
    else if x > n.value then
      balance n.left n.value (insert x n.right)
    else
      Node n  (* already present *)

(* ── Min / Max ───────────────────────────────────────── *)

let rec min_elt = function
  | Leaf -> failwith "min_elt: empty tree"
  | Node { left = Leaf; value; _ } -> value
  | Node { left; _ } -> min_elt left

let rec max_elt = function
  | Leaf -> failwith "max_elt: empty tree"
  | Node { right = Leaf; value; _ } -> value
  | Node { right; _ } -> max_elt right

let rec remove_min = function
  | Leaf -> failwith "remove_min: empty tree"
  | Node { left = Leaf; right; _ } -> right
  | Node { left; value; right; _ } ->
    balance (remove_min left) value right

(* ── Delete ──────────────────────────────────────────── *)

let rec delete x = function
  | Leaf -> Leaf
  | Node n ->
    if x < n.value then
      balance (delete x n.left) n.value n.right
    else if x > n.value then
      balance n.left n.value (delete x n.right)
    else begin
      (* found it *)
      match n.left, n.right with
      | Leaf, r -> r
      | l, Leaf -> l
      | _, r ->
        let successor = min_elt r in
        balance n.left successor (remove_min r)
    end

(* ── Membership ──────────────────────────────────────── *)

let rec member x = function
  | Leaf -> false
  | Node n ->
    if x < n.value then member x n.left
    else if x > n.value then member x n.right
    else true

(* ── Kth smallest (1-indexed) ────────────────────────── *)

let rec kth k = function
  | Leaf -> failwith "kth: index out of range"
  | Node n ->
    let left_size = size n.left in
    if k <= left_size then kth k n.left
    else if k = left_size + 1 then n.value
    else kth (k - left_size - 1) n.right

(* ── Rank (number of elements < x) ──────────────────── *)

let rec rank x = function
  | Leaf -> 0
  | Node n ->
    if x < n.value then rank x n.left
    else if x > n.value then size n.left + 1 + rank x n.right
    else size n.left

(* ── Range query [lo, hi] ────────────────────────────── *)

let rec range_query lo hi acc = function
  | Leaf -> acc
  | Node n ->
    let acc =
      if n.value > lo then range_query lo hi acc n.left
      else acc
    in
    let acc =
      if lo <= n.value && n.value <= hi then n.value :: acc
      else acc
    in
    if n.value < hi then range_query lo hi acc n.right
    else acc

let range lo hi t = List.rev (range_query lo hi [] t)

(* ── Split ───────────────────────────────────────────── *)

let rec split x = function
  | Leaf -> (Leaf, false, Leaf)
  | Node n ->
    if x < n.value then
      let (ll, present, lr) = split x n.left in
      (ll, present, balance lr n.value n.right)
    else if x > n.value then
      let (rl, present, rr) = split x n.right in
      (balance n.left n.value rl, present, rr)
    else
      (n.left, true, n.right)

(* ── Join ────────────────────────────────────────────── *)

let rec join left value right =
  match left, right with
  | Leaf, _ -> insert value right
  | _, Leaf -> insert value left
  | Node ln, Node rn ->
    if delta * (ln.size + 1) < rn.size then
      balance (join left value rn.left) rn.value rn.right
    else if delta * (rn.size + 1) < ln.size then
      balance ln.left ln.value (join ln.right value right)
    else
      node left value right

(* ── Set operations ──────────────────────────────────── *)

let rec union t1 t2 =
  match t1, t2 with
  | Leaf, t | t, Leaf -> t
  | _, Node n2 ->
    let (l1, _, r1) = split n2.value t1 in
    let new_left = union l1 n2.left in
    let new_right = union r1 n2.right in
    join new_left n2.value new_right

let rec intersection t1 t2 =
  match t1, t2 with
  | Leaf, _ | _, Leaf -> Leaf
  | _, Node n2 ->
    let (l1, found, r1) = split n2.value t1 in
    let new_left = intersection l1 n2.left in
    let new_right = intersection r1 n2.right in
    if found then join new_left n2.value new_right
    else begin
      match new_left, new_right with
      | Leaf, t | t, Leaf -> t
      | _ ->
        let m = min_elt new_right in
        join new_left m (remove_min new_right)
    end

let rec difference t1 t2 =
  match t1, t2 with
  | Leaf, _ -> Leaf
  | t, Leaf -> t
  | _, Node n2 ->
    let (l1, _, r1) = split n2.value t1 in
    let new_left = difference l1 n2.left in
    let new_right = difference r1 n2.right in
    match new_left, new_right with
    | Leaf, t | t, Leaf -> t
    | _ ->
      let m = min_elt new_right in
      join new_left m (remove_min new_right)

(* ── Fold / Map / Traversal ──────────────────────────── *)

let rec fold_left f acc = function
  | Leaf -> acc
  | Node n ->
    let acc = fold_left f acc n.left in
    let acc = f acc n.value in
    fold_left f acc n.right

let rec fold_right f t acc =
  match t with
  | Leaf -> acc
  | Node n ->
    let acc = fold_right f n.right acc in
    let acc = f n.value acc in
    fold_right f n.left acc

let to_list t = fold_right (fun x acc -> x :: acc) t []

let rec map f = function
  | Leaf -> Leaf
  | Node n ->
    (* Note: map may break BST invariant if f is not monotonic *)
    node (map f n.left) (f n.value) (map f n.right)

let of_list lst =
  List.fold_left (fun t x -> insert x t) Leaf lst

let is_empty = function
  | Leaf -> true
  | Node _ -> false

let cardinal = size

(* ── Pretty printing ─────────────────────────────────── *)

let rec pp_tree indent = function
  | Leaf -> ()
  | Node n ->
    pp_tree (indent ^ "  ") n.right;
    Printf.printf "%s%d (size=%d)\n" indent n.value n.size;
    pp_tree (indent ^ "  ") n.left

let print_tree t =
  Printf.printf "Weight-Balanced Tree (size=%d):\n" (size t);
  pp_tree "  " t

(* ── Validation ──────────────────────────────────────── *)

let rec is_balanced = function
  | Leaf -> true
  | Node n ->
    let ln = size n.left and rn = size n.right in
    ln <= delta * (rn + 1) &&
    rn <= delta * (ln + 1) &&
    n.size = ln + rn + 1 &&
    is_balanced n.left &&
    is_balanced n.right

let rec is_bst_between lo hi = function
  | Leaf -> true
  | Node n ->
    (match lo with None -> true | Some l -> n.value > l) &&
    (match hi with None -> true | Some h -> n.value < h) &&
    is_bst_between lo (Some n.value) n.left &&
    is_bst_between (Some n.value) hi n.right

let is_valid t = is_balanced t && is_bst_between None None t

(* ── Demo ────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Weight-Balanced Tree (BB[α] Tree) Demo ===\n\n";

  (* Build a tree from a list *)
  let values = [8; 3; 10; 1; 6; 14; 4; 7; 13] in
  Printf.printf "Inserting: ";
  List.iter (Printf.printf "%d ") values;
  Printf.printf "\n\n";

  let t = of_list values in
  print_tree t;
  Printf.printf "\nValid: %b\n\n" (is_valid t);

  (* Membership *)
  Printf.printf "member 6 = %b\n" (member 6 t);
  Printf.printf "member 5 = %b\n" (member 5 t);

  (* Kth smallest *)
  Printf.printf "\n1st smallest = %d\n" (kth 1 t);
  Printf.printf "5th smallest = %d\n" (kth 5 t);
  Printf.printf "9th smallest = %d\n" (kth 9 t);

  (* Rank *)
  Printf.printf "\nrank(6) = %d elements less than 6\n" (rank 6 t);
  Printf.printf "rank(10) = %d elements less than 10\n" (rank 10 t);

  (* Range query *)
  Printf.printf "\nrange [4, 10]: ";
  List.iter (Printf.printf "%d ") (range 4 10 t);
  Printf.printf "\n";

  (* Delete *)
  let t2 = delete 6 t in
  Printf.printf "\nAfter deleting 6:\n";
  Printf.printf "Sorted: ";
  List.iter (Printf.printf "%d ") (to_list t2);
  Printf.printf "\nValid: %b\n" (is_valid t2);

  (* Set operations *)
  let s1 = of_list [1; 2; 3; 4; 5] in
  let s2 = of_list [3; 4; 5; 6; 7] in

  Printf.printf "\n--- Set Operations ---\n";
  Printf.printf "S1: "; List.iter (Printf.printf "%d ") (to_list s1); Printf.printf "\n";
  Printf.printf "S2: "; List.iter (Printf.printf "%d ") (to_list s2); Printf.printf "\n";

  Printf.printf "Union:        "; List.iter (Printf.printf "%d ") (to_list (union s1 s2)); Printf.printf "\n";
  Printf.printf "Intersection: "; List.iter (Printf.printf "%d ") (to_list (intersection s1 s2)); Printf.printf "\n";
  Printf.printf "Difference:   "; List.iter (Printf.printf "%d ") (to_list (difference s1 s2)); Printf.printf "\n";

  (* Stress test for balance *)
  Printf.printf "\n--- Stress test: inserting 1..100 sequentially ---\n";
  let big = List.init 100 (fun i -> i + 1) in
  let t3 = of_list big in
  Printf.printf "Size: %d, Valid: %b\n" (cardinal t3) (is_valid t3);
  Printf.printf "50th element: %d\n" (kth 50 t3);

  (* Delete half and check *)
  let t4 = List.fold_left (fun t i -> delete (2 * i) t) t3 (List.init 50 (fun i -> i + 1)) in
  Printf.printf "After deleting all evens: size=%d, valid=%b\n" (cardinal t4) (is_valid t4);

  Printf.printf "\nDone!\n"
