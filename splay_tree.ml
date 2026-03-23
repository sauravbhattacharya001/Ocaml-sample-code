(* Splay Tree — self-adjusting binary search tree *)
(* Implements Sleator & Tarjan's splay tree with amortized O(log n) ops *)
(* Key property: recently accessed elements are near the root            *)
(* Great for workloads with temporal locality                            *)

(* ── Types ─────────────────────────────────────────────────────────── *)

type 'a splay_tree =
  | Leaf
  | Node of 'a splay_tree * 'a * 'a splay_tree

(* ── Splay operation ───────────────────────────────────────────────── *)

(* Splay brings target element (or nearest) to the root via rotations.
   Uses top-down splaying for efficiency. *)

let rec splay x = function
  | Leaf -> Leaf
  (* Zig: target is root's child *)
  | Node (Leaf, v, right) when x < v ->
    Node (Leaf, v, right)  (* can't go further left *)
  | Node (left, v, Leaf) when x > v ->
    Node (left, v, Leaf)   (* can't go further right *)
  (* Zig-Zig: target is in left-left *)
  | Node (Node (ll, lv, lr), v, right) when x < v && x < lv ->
    let ll' = splay x ll in
    (* rotate right twice *)
    (match ll' with
     | Leaf -> Node (Leaf, lv, Node (lr, v, right))
     | Node (a, w, b) ->
       Node (a, w, Node (b, lv, Node (lr, v, right))))
  (* Zig-Zag: target is in left-right *)
  | Node (Node (ll, lv, lr), v, right) when x < v && x > lv ->
    let lr' = splay x lr in
    (match lr' with
     | Leaf -> Node (ll, lv, Node (Leaf, v, right))
     | Node (a, w, b) ->
       Node (Node (ll, lv, a), w, Node (b, v, right)))
  (* Zig-Zag: target is in right-left *)
  | Node (left, v, Node (rl, rv, rr)) when x > v && x < rv ->
    let rl' = splay x rl in
    (match rl' with
     | Leaf -> Node (left, v, Node (Leaf, rv, rr))
     | Node (a, w, b) ->
       Node (Node (left, v, a), w, Node (b, rv, rr)))
  (* Zig-Zig: target is in right-right *)
  | Node (left, v, Node (rl, rv, rr)) when x > v && x > rv ->
    let rr' = splay x rr in
    (match rr' with
     | Leaf -> Node (Node (left, v, rl), rv, Leaf)
     | Node (a, w, b) ->
       Node (Node (Node (left, v, rl), rv, a), w, b))
  (* Zig left *)
  | Node (left, v, right) when x < v ->
    let left' = splay x left in
    (match left' with
     | Leaf -> Node (Leaf, v, right)
     | Node (a, w, b) -> Node (a, w, Node (b, v, right)))
  (* Zig right *)
  | Node (left, v, right) when x > v ->
    let right' = splay x right in
    (match right' with
     | Leaf -> Node (left, v, Leaf)
     | Node (a, w, b) -> Node (Node (left, v, a), w, b))
  (* Found *)
  | t -> t

(* ── Core operations ───────────────────────────────────────────────── *)

let empty = Leaf

let is_empty = function Leaf -> true | _ -> false

let member x t =
  match splay x t with
  | Node (_, v, _) when v = x -> true
  | _ -> false

(* find returns (value option, splayed tree) *)
let find x t =
  let t' = splay x t in
  match t' with
  | Node (_, v, _) when v = x -> (Some v, t')
  | _ -> (None, t')

let insert x t =
  match splay x t with
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (left, v, right) when x < v ->
    Node (left, x, Node (Leaf, v, right))
  | Node (left, v, right) when x > v ->
    Node (Node (left, v, Leaf), x, right)
  | t' -> t'  (* already present *)

(* Find max in tree (helper for delete) *)
let rec find_max = function
  | Leaf -> failwith "find_max: empty tree"
  | Node (_, v, Leaf) -> v
  | Node (_, _, right) -> find_max right

let delete x t =
  match splay x t with
  | Node (left, v, right) when v = x ->
    (match left with
     | Leaf -> right
     | _ ->
       let max_left = find_max left in
       let left' = splay max_left left in
       (match left' with
        | Node (ll, lv, _) -> Node (ll, lv, right)
        | Leaf -> right))
  | t' -> t'  (* not found, return splayed tree *)

(* ── Traversal ─────────────────────────────────────────────────────── *)

let rec to_list_acc acc = function
  | Leaf -> acc
  | Node (left, v, right) ->
    to_list_acc (v :: to_list_acc acc right) left

let to_sorted_list t = to_list_acc [] t

let rec size = function
  | Leaf -> 0
  | Node (left, _, right) -> 1 + size left + size right

let rec height = function
  | Leaf -> 0
  | Node (left, _, right) -> 1 + max (height left) (height right)

(* ── Min / Max ─────────────────────────────────────────────────────── *)

let rec min_element = function
  | Leaf -> None
  | Node (Leaf, v, _) -> Some v
  | Node (left, _, _) -> min_element left

let rec max_element = function
  | Leaf -> None
  | Node (_, v, Leaf) -> Some v
  | Node (_, _, right) -> max_element right

(* ── Fold ──────────────────────────────────────────────────────────── *)

let rec fold_inorder f acc = function
  | Leaf -> acc
  | Node (left, v, right) ->
    let acc' = fold_inorder f acc left in
    let acc'' = f acc' v in
    fold_inorder f acc'' right

(* ── From list ─────────────────────────────────────────────────────── *)

let of_list lst =
  List.fold_left (fun t x -> insert x t) empty lst

(* ── Split: partition tree around a pivot ──────────────────────────── *)

let split x t =
  match splay x t with
  | Leaf -> (Leaf, false, Leaf)
  | Node (left, v, right) when v = x -> (left, true, right)
  | Node (left, v, right) when v < x -> (Node (left, v, Leaf), false, right)
  | Node (left, v, right) -> (left, false, Node (Leaf, v, right))

(* ── Merge: join two trees where all keys in t1 < all keys in t2 ──── *)

let merge t1 t2 =
  match t1 with
  | Leaf -> t2
  | _ ->
    let m = find_max t1 in
    let t1' = splay m t1 in
    (match t1' with
     | Node (left, v, _) -> Node (left, v, t2)
     | Leaf -> t2)

(* ── Range query: all elements in [lo, hi] ─────────────────────────── *)

let range_query lo hi t =
  let rec collect acc = function
    | Leaf -> acc
    | Node (left, v, right) ->
      let acc' = if v >= lo then collect acc left else acc in
      let acc'' = if v >= lo && v <= hi then v :: acc' else acc' in
      if v <= hi then collect acc'' right else acc''
  in
  List.rev (collect [] t)

(* ── Rank: number of elements less than x ──────────────────────────── *)

let rank x t =
  let rec count = function
    | Leaf -> 0
    | Node (left, v, right) ->
      if x <= v then count left
      else 1 + size left + count right
  in
  count t

(* ── Pretty-print ─────────────────────────────────────────────────── *)

let rec pp_tree indent = function
  | Leaf -> Printf.printf "%s·\n" indent
  | Node (left, v, right) ->
    Printf.printf "%s%d\n" indent v;
    pp_tree (indent ^ "  ├─") left;
    pp_tree (indent ^ "  └─") right

let print_tree t = pp_tree "" t

(* ── Demo ──────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Splay Tree Demo ===\n\n";

  (* Build a tree *)
  let t = of_list [5; 3; 8; 1; 4; 7; 9; 2; 6; 10] in
  Printf.printf "Tree from [5;3;8;1;4;7;9;2;6;10]:\n";
  Printf.printf "  Size: %d\n" (size t);
  Printf.printf "  Height: %d\n" (height t);
  Printf.printf "  Sorted: [%s]\n\n"
    (String.concat "; " (List.map string_of_int (to_sorted_list t)));

  (* Membership *)
  Printf.printf "Member 4: %b\n" (member 4 t);
  Printf.printf "Member 11: %b\n\n" (member 11 t);

  (* Min/Max *)
  (match min_element t with
   | Some v -> Printf.printf "Min: %d\n" v
   | None -> Printf.printf "Min: (empty)\n");
  (match max_element t with
   | Some v -> Printf.printf "Max: %d\n" v
   | None -> Printf.printf "Max: (empty)\n");
  Printf.printf "\n";

  (* Range query *)
  let range = range_query 3 7 t in
  Printf.printf "Range [3, 7]: [%s]\n\n"
    (String.concat "; " (List.map string_of_int range));

  (* Rank *)
  Printf.printf "Rank of 5: %d (elements less than 5)\n" (rank 5 t);
  Printf.printf "Rank of 8: %d (elements less than 8)\n\n" (rank 8 t);

  (* Delete *)
  let t2 = delete 5 t in
  Printf.printf "After deleting 5:\n";
  Printf.printf "  Size: %d\n" (size t2);
  Printf.printf "  Sorted: [%s]\n\n"
    (String.concat "; " (List.map string_of_int (to_sorted_list t2)));

  (* Split & Merge *)
  let (left, found, right) = split 6 t in
  Printf.printf "Split at 6: found=%b\n" found;
  Printf.printf "  Left:  [%s]\n"
    (String.concat "; " (List.map string_of_int (to_sorted_list left)));
  Printf.printf "  Right: [%s]\n\n"
    (String.concat "; " (List.map string_of_int (to_sorted_list right)));
  let merged = merge left (insert 6 right) in
  Printf.printf "Merged back: [%s]\n\n"
    (String.concat "; " (List.map string_of_int (to_sorted_list merged)));

  (* Fold — sum all elements *)
  let total = fold_inorder (fun acc x -> acc + x) 0 t in
  Printf.printf "Sum of all elements: %d\n\n" total;

  (* Demonstrate splay property: repeated access is fast *)
  Printf.printf "=== Splay Property Demo ===\n";
  Printf.printf "After accessing 3, it becomes the root:\n";
  let t3 = splay 3 t in
  (match t3 with
   | Node (_, v, _) -> Printf.printf "  Root is now: %d\n" v
   | Leaf -> Printf.printf "  (empty)\n");

  Printf.printf "\nDone!\n"
