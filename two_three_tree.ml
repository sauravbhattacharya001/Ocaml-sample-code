(* two_three_tree.ml - 2-3 Tree: A Balanced Search Tree
 *
 * A 2-3 tree is a perfectly balanced search tree where:
 * - Every internal node has either 2 or 3 children
 * - All leaves are at the same depth
 * - 2-nodes store one key/value, 3-nodes store two keys/values
 *
 * Operations: insert, find, delete, fold, to_list, min, max, range query
 * All operations are O(log n) due to perfect balance.
 *
 * This is an educational implementation demonstrating how 2-3 trees
 * maintain balance through node splitting and merging.
 *)

(* ============================================================ *)
(* Core Types                                                    *)
(* ============================================================ *)

type ('k, 'v) tree =
  | Empty
  | Leaf2 of 'k * 'v                           (* 2-node leaf: one key *)
  | Leaf3 of 'k * 'v * 'k * 'v                 (* 3-node leaf: two keys *)
  | Node2 of ('k, 'v) tree * 'k * 'v * ('k, 'v) tree
      (* left, key, value, right *)
  | Node3 of ('k, 'v) tree * 'k * 'v * ('k, 'v) tree * 'k * 'v * ('k, 'v) tree
      (* left, key1, val1, mid, key2, val2, right *)

(* Intermediate type used during insertion when a node splits *)
type ('k, 'v) insert_result =
  | Done of ('k, 'v) tree
  | Split of ('k, 'v) tree * 'k * 'v * ('k, 'v) tree
      (* left subtree, promoted key/value, right subtree *)

(* Intermediate type used during deletion when a node shrinks *)
type ('k, 'v) delete_result =
  | Shrunk of ('k, 'v) tree   (* tree height decreased *)
  | Same of ('k, 'v) tree     (* tree height unchanged *)

(* ============================================================ *)
(* Creation                                                      *)
(* ============================================================ *)

let empty = Empty

let singleton k v = Leaf2 (k, v)

(* ============================================================ *)
(* Query                                                         *)
(* ============================================================ *)

let is_empty = function
  | Empty -> true
  | _ -> false

let rec find k = function
  | Empty -> None
  | Leaf2 (k1, v1) ->
    if k = k1 then Some v1 else None
  | Leaf3 (k1, v1, k2, v2) ->
    if k = k1 then Some v1
    else if k = k2 then Some v2
    else None
  | Node2 (left, k1, v1, right) ->
    if k = k1 then Some v1
    else if k < k1 then find k left
    else find k right
  | Node3 (left, k1, v1, mid, k2, v2, right) ->
    if k = k1 then Some v1
    else if k = k2 then Some v2
    else if k < k1 then find k left
    else if k < k2 then find k mid
    else find k right

let mem k t = find k t <> None

let rec min_binding = function
  | Empty -> None
  | Leaf2 (k, v) -> Some (k, v)
  | Leaf3 (k, v, _, _) -> Some (k, v)
  | Node2 (left, k, v, _) ->
    (match min_binding left with Some r -> Some r | None -> Some (k, v))
  | Node3 (left, k, v, _, _, _, _) ->
    (match min_binding left with Some r -> Some r | None -> Some (k, v))

let rec max_binding = function
  | Empty -> None
  | Leaf2 (k, v) -> Some (k, v)
  | Leaf3 (_, _, k, v) -> Some (k, v)
  | Node2 (_, k, v, right) ->
    (match max_binding right with Some r -> Some r | None -> Some (k, v))
  | Node3 (_, _, _, _, k, v, right) ->
    (match max_binding right with Some r -> Some r | None -> Some (k, v))

(* ============================================================ *)
(* Insertion                                                     *)
(* ============================================================ *)

(* Insert into a leaf, potentially splitting *)
let insert_leaf k v = function
  | Empty -> Done (Leaf2 (k, v))
  | Leaf2 (k1, v1) ->
    if k = k1 then Done (Leaf2 (k, v))  (* update *)
    else if k < k1 then Done (Leaf3 (k, v, k1, v1))
    else Done (Leaf3 (k1, v1, k, v))
  | Leaf3 (k1, v1, k2, v2) ->
    if k = k1 then Done (Leaf3 (k, v, k2, v2))
    else if k = k2 then Done (Leaf3 (k1, v1, k, v))
    else if k < k1 then
      Split (Leaf2 (k, v), k1, v1, Leaf2 (k2, v2))
    else if k < k2 then
      Split (Leaf2 (k1, v1), k, v, Leaf2 (k2, v2))
    else
      Split (Leaf2 (k1, v1), k2, v2, Leaf2 (k, v))
  | _ -> failwith "insert_leaf called on non-leaf"

let rec insert_aux k v = function
  | Empty -> Done (Leaf2 (k, v))
  | Leaf2 _ | Leaf3 _ as leaf -> insert_leaf k v leaf
  | Node2 (left, k1, v1, right) ->
    if k = k1 then Done (Node2 (left, k, v, right))
    else if k < k1 then
      match insert_aux k v left with
      | Done new_left -> Done (Node2 (new_left, k1, v1, right))
      | Split (sl, sk, sv, sr) ->
        Done (Node3 (sl, sk, sv, sr, k1, v1, right))
    else
      match insert_aux k v right with
      | Done new_right -> Done (Node2 (left, k1, v1, new_right))
      | Split (sl, sk, sv, sr) ->
        Done (Node3 (left, k1, v1, sl, sk, sv, sr))
  | Node3 (left, k1, v1, mid, k2, v2, right) ->
    if k = k1 then Done (Node3 (left, k, v, mid, k2, v2, right))
    else if k = k2 then Done (Node3 (left, k1, v1, mid, k, v, right))
    else if k < k1 then
      match insert_aux k v left with
      | Done new_left -> Done (Node3 (new_left, k1, v1, mid, k2, v2, right))
      | Split (sl, sk, sv, sr) ->
        Split (Node2 (sl, sk, sv, sr), k1, v1, Node2 (mid, k2, v2, right))
    else if k < k2 then
      match insert_aux k v mid with
      | Done new_mid -> Done (Node3 (left, k1, v1, new_mid, k2, v2, right))
      | Split (sl, sk, sv, sr) ->
        Split (Node2 (left, k1, v1, sl), sk, sv, Node2 (sr, k2, v2, right))
    else
      match insert_aux k v right with
      | Done new_right -> Done (Node3 (left, k1, v1, mid, k2, v2, new_right))
      | Split (sl, sk, sv, sr) ->
        Split (Node2 (left, k1, v1, mid), k2, v2, Node2 (sl, sk, sv, sr))

let insert k v t =
  match insert_aux k v t with
  | Done t' -> t'
  | Split (l, k', v', r) -> Node2 (l, k', v', r)

(* ============================================================ *)
(* Deletion                                                      *)
(* ============================================================ *)

(* Remove the minimum element, returning it and the shrunk tree *)
let rec remove_min = function
  | Empty -> failwith "remove_min: empty"
  | Leaf2 (k, v) -> (k, v, Shrunk Empty)
  | Leaf3 (k1, v1, k2, v2) -> (k1, v1, Same (Leaf2 (k2, v2)))
  | Node2 (left, k1, v1, right) ->
    let (mk, mv, result) = remove_min left in
    (match result with
     | Same new_left -> (mk, mv, Same (Node2 (new_left, k1, v1, right)))
     | Shrunk new_left ->
       (* Borrow or merge with right sibling *)
       match right with
       | Node2 (rl, rk, rv, rr) ->
         (mk, mv, Shrunk (Node3 (new_left, k1, v1, rl, rk, rv, rr)))
       | Node3 (rl, rk1, rv1, rm, rk2, rv2, rr) ->
         (mk, mv, Same (Node2 (Node2 (new_left, k1, v1, rl), rk1, rv1,
                                Node2 (rm, rk2, rv2, rr))))
       | Leaf2 (rk, rv) ->
         (mk, mv, Shrunk (Leaf3 (k1, v1, rk, rv)))
       | Leaf3 (rk1, rv1, rk2, rv2) ->
         (mk, mv, Same (Node2 (Leaf2 (k1, v1), rk1, rv1, Leaf2 (rk2, rv2))))
       | Empty ->
         (mk, mv, Shrunk (Leaf2 (k1, v1)))
    )
  | Node3 (left, k1, v1, mid, k2, v2, right) ->
    let (mk, mv, result) = remove_min left in
    (match result with
     | Same new_left -> (mk, mv, Same (Node3 (new_left, k1, v1, mid, k2, v2, right)))
     | Shrunk new_left ->
       match mid with
       | Node2 (ml, mk1, mv1, mr) ->
         (mk, mv, Same (Node2 (Node3 (new_left, k1, v1, ml, mk1, mv1, mr), k2, v2, right)))
       | Node3 (ml, mk1, mv1, mm, mk2, mv2, mr) ->
         (mk, mv, Same (Node3 (Node2 (new_left, k1, v1, ml), mk1, mv1,
                                Node2 (mm, mk2, mv2, mr), k2, v2, right)))
       | Leaf2 (mk1, mv1) ->
         (mk, mv, Same (Node2 (Leaf3 (k1, v1, mk1, mv1), k2, v2, right)))
       | Leaf3 (mk1, mv1, mk2, mv2) ->
         (mk, mv, Same (Node3 (Leaf2 (k1, v1), mk1, mv1, Leaf2 (mk2, mv2), k2, v2, right)))
       | Empty ->
         (mk, mv, Same (Node2 (Leaf2 (k1, v1), k2, v2, right)))
    )

let rec delete_aux k = function
  | Empty -> Same Empty
  | Leaf2 (k1, v1) ->
    if k = k1 then Shrunk Empty else Same (Leaf2 (k1, v1))
  | Leaf3 (k1, v1, k2, v2) ->
    if k = k1 then Same (Leaf2 (k2, v2))
    else if k = k2 then Same (Leaf2 (k1, v1))
    else Same (Leaf3 (k1, v1, k2, v2))
  | Node2 (left, k1, v1, right) ->
    if k = k1 then
      (* Replace with successor *)
      if right = Empty then
        (* k1 is at a leaf-level node *)
        Shrunk left
      else
        let (sk, sv, result) = remove_min right in
        (match result with
         | Same new_right -> Same (Node2 (left, sk, sv, new_right))
         | Shrunk new_right ->
           match left with
           | Node2 (ll, lk, lv, lr) ->
             Shrunk (Node3 (ll, lk, lv, lr, sk, sv, new_right))
           | Node3 (ll, lk1, lv1, lm, lk2, lv2, lr) ->
             Same (Node2 (Node2 (ll, lk1, lv1, lm), lk2, lv2,
                          Node2 (lr, sk, sv, new_right)))
           | Leaf2 (lk, lv) ->
             Shrunk (Leaf3 (lk, lv, sk, sv))
           | Leaf3 (lk1, lv1, lk2, lv2) ->
             Same (Node2 (Leaf2 (lk1, lv1), lk2, lv2, Leaf2 (sk, sv)))
           | Empty -> Shrunk (Leaf2 (sk, sv))
        )
    else if k < k1 then
      (match delete_aux k left with
       | Same new_left -> Same (Node2 (new_left, k1, v1, right))
       | Shrunk new_left ->
         match right with
         | Node2 (rl, rk, rv, rr) ->
           Shrunk (Node3 (new_left, k1, v1, rl, rk, rv, rr))
         | Node3 (rl, rk1, rv1, rm, rk2, rv2, rr) ->
           Same (Node2 (Node2 (new_left, k1, v1, rl), rk1, rv1,
                        Node2 (rm, rk2, rv2, rr)))
         | Leaf2 (rk, rv) ->
           Shrunk (Leaf3 (k1, v1, rk, rv))
         | Leaf3 (rk1, rv1, rk2, rv2) ->
           Same (Node2 (Leaf2 (k1, v1), rk1, rv1, Leaf2 (rk2, rv2)))
         | Empty -> Shrunk (Leaf2 (k1, v1))
      )
    else
      (match delete_aux k right with
       | Same new_right -> Same (Node2 (left, k1, v1, new_right))
       | Shrunk new_right ->
         match left with
         | Node2 (ll, lk, lv, lr) ->
           Shrunk (Node3 (ll, lk, lv, lr, k1, v1, new_right))
         | Node3 (ll, lk1, lv1, lm, lk2, lv2, lr) ->
           Same (Node2 (Node2 (ll, lk1, lv1, lm), lk2, lv2,
                        Node2 (lr, k1, v1, new_right)))
         | Leaf2 (lk, lv) ->
           Shrunk (Leaf3 (lk, lv, k1, v1))
         | Leaf3 (lk1, lv1, lk2, lv2) ->
           Same (Node2 (Leaf2 (lk1, lv1), lk2, lv2, Leaf2 (k1, v1)))
         | Empty -> Shrunk (Leaf2 (k1, v1))
      )
  | Node3 (left, k1, v1, mid, k2, v2, right) ->
    if k = k1 then
      if mid = Empty then
        (* Leaf-level 3-node, remove k1 *)
        Same (Node2 (left, k2, v2, right))
      else
        let (sk, sv, result) = remove_min mid in
        (match result with
         | Same new_mid -> Same (Node3 (left, sk, sv, new_mid, k2, v2, right))
         | Shrunk new_mid ->
           (* Rebalance: borrow from left or right *)
           match left with
           | Node3 (ll, lk1, lv1, lm, lk2, lv2, lr) ->
             Same (Node3 (Node2 (ll, lk1, lv1, lm), lk2, lv2,
                          Node2 (lr, sk, sv, new_mid), k2, v2, right))
           | _ ->
             match right with
             | Node3 (rl, rk1, rv1, rm, rk2, rv2, rr) ->
               Same (Node3 (left, sk, sv,
                            Node2 (new_mid, k2, v2, rl), rk1, rv1,
                            Node2 (rm, rk2, rv2, rr)))
             | _ ->
               (* Merge new_mid into left or create 2-node *)
               Same (Node2 (left, sk, sv, Node2 (new_mid, k2, v2, right)))
        )
    else if k = k2 then
      if right = Empty then
        Same (Node2 (left, k1, v1, mid))
      else
        let (sk, sv, result) = remove_min right in
        (match result with
         | Same new_right -> Same (Node3 (left, k1, v1, mid, sk, sv, new_right))
         | Shrunk new_right ->
           match mid with
           | Node3 (ml, mk1, mv1, mm, mk2, mv2, mr) ->
             Same (Node3 (left, k1, v1,
                          Node2 (ml, mk1, mv1, mm), mk2, mv2,
                          Node2 (mr, sk, sv, new_right)))
           | _ ->
             Same (Node2 (left, k1, v1, Node2 (mid, sk, sv, new_right)))
        )
    else if k < k1 then
      (match delete_aux k left with
       | Same new_left -> Same (Node3 (new_left, k1, v1, mid, k2, v2, right))
       | Shrunk new_left ->
         match mid with
         | Node2 (ml, mk, mv, mr) ->
           Same (Node2 (Node3 (new_left, k1, v1, ml, mk, mv, mr), k2, v2, right))
         | Node3 (ml, mk1, mv1, mm, mk2, mv2, mr) ->
           Same (Node3 (Node2 (new_left, k1, v1, ml), mk1, mv1,
                        Node2 (mm, mk2, mv2, mr), k2, v2, right))
         | Leaf2 (mk, mv) ->
           Same (Node2 (Leaf3 (k1, v1, mk, mv), k2, v2, right))
         | Leaf3 (mk1, mv1, mk2, mv2) ->
           Same (Node3 (Leaf2 (k1, v1), mk1, mv1, Leaf2 (mk2, mv2), k2, v2, right))
         | Empty ->
           Same (Node2 (Leaf2 (k1, v1), k2, v2, right))
      )
    else if k < k2 then
      (match delete_aux k mid with
       | Same new_mid -> Same (Node3 (left, k1, v1, new_mid, k2, v2, right))
       | Shrunk new_mid ->
         match left with
         | Node3 (ll, lk1, lv1, lm, lk2, lv2, lr) ->
           Same (Node3 (Node2 (ll, lk1, lv1, lm), lk2, lv2,
                        Node2 (lr, k1, v1, new_mid), k2, v2, right))
         | _ ->
           match right with
           | Node3 (rl, rk1, rv1, rm, rk2, rv2, rr) ->
             Same (Node3 (left, k1, v1,
                          Node2 (new_mid, k2, v2, rl), rk1, rv1,
                          Node2 (rm, rk2, rv2, rr)))
           | _ ->
             Same (Node2 (left, k1, v1, Node2 (new_mid, k2, v2, right)))
      )
    else
      (match delete_aux k right with
       | Same new_right -> Same (Node3 (left, k1, v1, mid, k2, v2, new_right))
       | Shrunk new_right ->
         match mid with
         | Node3 (ml, mk1, mv1, mm, mk2, mv2, mr) ->
           Same (Node3 (left, k1, v1,
                        Node2 (ml, mk1, mv1, mm), mk2, mv2,
                        Node2 (mr, k2, v2, new_right)))
         | _ ->
           Same (Node2 (left, k1, v1, Node2 (mid, k2, v2, new_right)))
      )

let delete k t =
  match delete_aux k t with
  | Same t' | Shrunk t' -> t'

(* ============================================================ *)
(* Traversal & Conversion                                        *)
(* ============================================================ *)

let rec fold f acc = function
  | Empty -> acc
  | Leaf2 (k, v) -> f acc k v
  | Leaf3 (k1, v1, k2, v2) -> f (f acc k1 v1) k2 v2
  | Node2 (left, k, v, right) ->
    let acc = fold f acc left in
    let acc = f acc k v in
    fold f acc right
  | Node3 (left, k1, v1, mid, k2, v2, right) ->
    let acc = fold f acc left in
    let acc = f acc k1 v1 in
    let acc = fold f acc mid in
    let acc = f acc k2 v2 in
    fold f acc right

let to_list t =
  fold (fun acc k v -> (k, v) :: acc) [] t |> List.rev

let of_list pairs =
  List.fold_left (fun t (k, v) -> insert k v t) empty pairs

let rec size = function
  | Empty -> 0
  | Leaf2 _ -> 1
  | Leaf3 _ -> 2
  | Node2 (l, _, _, r) -> size l + 1 + size r
  | Node3 (l, _, _, m, _, _, r) -> size l + 1 + size m + 1 + size r

let rec height = function
  | Empty -> 0
  | Leaf2 _ | Leaf3 _ -> 1
  | Node2 (l, _, _, _) -> 1 + height l
  | Node3 (l, _, _, _, _, _, _) -> 1 + height l

(* ============================================================ *)
(* Range Query                                                   *)
(* ============================================================ *)

let range_query lo hi t =
  fold (fun acc k v ->
    if k >= lo && k <= hi then (k, v) :: acc else acc
  ) [] t |> List.rev

(* ============================================================ *)
(* Iteration                                                     *)
(* ============================================================ *)

let iter f t =
  fold (fun () k v -> f k v) () t

let map f t =
  fold (fun acc k v -> insert k (f v) acc) empty t

(* ============================================================ *)
(* Pretty Printing                                               *)
(* ============================================================ *)

let rec to_string_aux indent key_to_string = function
  | Empty -> indent ^ "(empty)\n"
  | Leaf2 (k, _) ->
    Printf.sprintf "%s[%s]\n" indent (key_to_string k)
  | Leaf3 (k1, _, k2, _) ->
    Printf.sprintf "%s[%s | %s]\n" indent (key_to_string k1) (key_to_string k2)
  | Node2 (left, k, _, right) ->
    let next = indent ^ "  " in
    to_string_aux next key_to_string left ^
    Printf.sprintf "%s(%s)\n" indent (key_to_string k) ^
    to_string_aux next key_to_string right
  | Node3 (left, k1, _, mid, k2, _, right) ->
    let next = indent ^ "  " in
    to_string_aux next key_to_string left ^
    Printf.sprintf "%s(%s)\n" indent (key_to_string k1) ^
    to_string_aux next key_to_string mid ^
    Printf.sprintf "%s(%s)\n" indent (key_to_string k2) ^
    to_string_aux next key_to_string right

let to_string key_to_string t =
  to_string_aux "" key_to_string t

(* ============================================================ *)
(* Demo                                                          *)
(* ============================================================ *)

let () =
  Printf.printf "=== 2-3 Tree Demo ===\n\n";

  (* Build a tree *)
  let t = empty in
  let keys = [5; 3; 8; 1; 4; 7; 9; 2; 6; 10] in
  let t = List.fold_left (fun t k -> insert k (k * 10) t) t keys in

  Printf.printf "Tree structure:\n%s\n" (to_string string_of_int t);
  Printf.printf "Size: %d, Height: %d\n\n" (size t) (height t);

  (* Lookups *)
  Printf.printf "Find 5: %s\n"
    (match find 5 t with Some v -> string_of_int v | None -> "not found");
  Printf.printf "Find 11: %s\n"
    (match find 11 t with Some v -> string_of_int v | None -> "not found");

  (* Min/Max *)
  Printf.printf "Min: %s\n"
    (match min_binding t with Some (k,v) -> Printf.sprintf "(%d,%d)" k v | None -> "empty");
  Printf.printf "Max: %s\n\n"
    (match max_binding t with Some (k,v) -> Printf.sprintf "(%d,%d)" k v | None -> "empty");

  (* Range query *)
  Printf.printf "Range [3..7]: ";
  List.iter (fun (k,v) -> Printf.printf "(%d,%d) " k v) (range_query 3 7 t);
  Printf.printf "\n\n";

  (* In-order traversal *)
  Printf.printf "In-order: ";
  List.iter (fun (k, v) -> Printf.printf "(%d,%d) " k v) (to_list t);
  Printf.printf "\n\n";

  (* Deletion *)
  let t2 = delete 5 t in
  Printf.printf "After deleting 5:\n";
  List.iter (fun (k, v) -> Printf.printf "(%d,%d) " k v) (to_list t2);
  Printf.printf "\n";
  Printf.printf "Size: %d\n\n" (size t2);

  (* Build from list *)
  let t3 = of_list [("apple", 1); ("banana", 2); ("cherry", 3); ("date", 4)] in
  Printf.printf "String tree in-order: ";
  List.iter (fun (k, v) -> Printf.printf "(%s,%d) " k v) (to_list t3);
  Printf.printf "\n\n";

  (* Map *)
  let t4 = map (fun v -> v * 2) t in
  Printf.printf "After doubling values: ";
  List.iter (fun (k, v) -> Printf.printf "(%d,%d) " k v) (to_list t4);
  Printf.printf "\n";

  Printf.printf "\n=== All operations completed successfully! ===\n"
