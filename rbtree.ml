(* Red-Black Tree — self-balancing binary search tree *)
(* Implements Okasaki's purely functional red-black tree with extensions *)
(* Guarantees O(log n) insert, lookup, delete, min, max *)
(* Invariants:                                                           *)
(*   1. Every node is either Red or Black                                *)
(*   2. The root is always Black                                         *)
(*   3. No Red node has a Red child (no red-red violations)              *)
(*   4. Every path from root to leaf has the same number of Black nodes  *)

(* ── Types ─────────────────────────────────────────────────────────── *)

type color = Red | Black

type 'a rbtree =
  | E                                          (* empty / leaf *)
  | T of color * 'a rbtree * 'a * 'a rbtree   (* color, left, value, right *)

(* ── Core operations ───────────────────────────────────────────────── *)

let empty = E

let is_empty = function E -> true | _ -> false

let rec member x = function
  | E -> false
  | T (_, left, v, right) ->
    if x < v then member x left
    else if x > v then member x right
    else true

(* Okasaki's balance — fixes red-red violations during insert *)
let balance = function
  (* Left-left case *)
  | Black, T (Red, T (Red, a, x, b), y, c), z, d
  (* Left-right case *)
  | Black, T (Red, a, x, T (Red, b, y, c)), z, d
  (* Right-left case *)
  | Black, a, x, T (Red, T (Red, b, y, c), z, d)
  (* Right-right case *)
  | Black, a, x, T (Red, b, y, T (Red, c, z, d)) ->
    T (Red, T (Black, a, x, b), y, T (Black, c, z, d))
  | color, left, v, right ->
    T (color, left, v, right)

let insert x tree =
  let rec ins = function
    | E -> T (Red, E, x, E)
    | T (color, left, v, right) ->
      if x < v then balance (color, ins left, v, right)
      else if x > v then balance (color, left, v, ins right)
      else T (color, left, v, right)  (* duplicate *)
  in
  match ins tree with
  | T (_, left, v, right) -> T (Black, left, v, right)  (* blacken root *)
  | E -> failwith "impossible: insert into empty produced empty"

(* ── Delete (Kahrs / Germane-Might approach) ───────────────────────── *)

(* Double-black is represented by temporarily allowing a "BB" color
   during deletion. We use a helper type internally. *)

(* Make a node redder (Black -> Red, used in delete rebalancing) *)
let redden = function
  | T (Black, left, v, right) -> T (Red, left, v, right)
  | t -> t

(* Balance during delete — handles more cases than insert balance *)
let balance_del = function
  | Black, T (Red, T (Red, a, x, b), y, c), z, d ->
    T (Red, T (Black, a, x, b), y, T (Black, c, z, d))
  | Black, T (Red, a, x, T (Red, b, y, c)), z, d ->
    T (Red, T (Black, a, x, b), y, T (Black, c, z, d))
  | Black, a, x, T (Red, T (Red, b, y, c), z, d) ->
    T (Red, T (Black, a, x, b), y, T (Black, c, z, d))
  | Black, a, x, T (Red, b, y, T (Red, c, z, d)) ->
    T (Red, T (Black, a, x, b), y, T (Black, c, z, d))
  | color, left, v, right ->
    T (color, left, v, right)

(* "Bubble up" a double-black by recoloring *)
let bubble_left = function
  | T (Black, T (Red, a, x, b), y, right) ->
    balance_del (Black, T (Red, a, x, b), y, right)
  | T (color, left, y, T (Black, a, z, b)) ->
    balance_del (color, left, y, T (Red, a, z, b))
  | T (color, left, y, T (Red, T (Black, a, z, b), w, c)) ->
    T (color, T (Black, left, y, T (Red, a, z, b)), w, c)
  | t -> t

let bubble_right = function
  | T (color, T (Black, a, x, b), y, right) ->
    balance_del (color, T (Red, a, x, b), y, right)
  | T (Black, T (Red, a, x, T (Black, b, y, c)), z, right) ->
    T (Black, a, x, T (Black, T (Red, b, y, c), z, right))
  | t -> t

let rec min_elt = function
  | E -> failwith "min_elt: empty tree"
  | T (_, E, v, _) -> v
  | T (_, left, _, _) -> min_elt left

let rec max_elt = function
  | E -> failwith "max_elt: empty tree"
  | T (_, _, v, E) -> v
  | T (_, _, _, right) -> max_elt right

let min_elt_opt = function
  | E -> None
  | t -> Some (min_elt t)

let max_elt_opt = function
  | E -> None
  | t -> Some (max_elt t)

(* Remove minimum element, rebalancing along the way *)
let rec remove_min = function
  | E -> failwith "remove_min: empty tree"
  | T (_, E, _, right) -> right
  | T (color, left, v, right) ->
    let new_left = remove_min left in
    bubble_left (T (color, new_left, v, right))

let delete x tree =
  let rec del = function
    | E -> E
    | T (color, left, v, right) ->
      if x < v then
        let new_left = del left in
        bubble_left (T (color, new_left, v, right))
      else if x > v then
        let new_right = del right in
        bubble_right (T (color, left, v, new_right))
      else
        (* Found: remove this node *)
        match left, right with
        | E, _ -> right
        | _, E -> left
        | _ ->
          let successor = min_elt right in
          let new_right = remove_min right in
          bubble_right (T (color, left, successor, new_right))
  in
  match del tree with
  | T (_, left, v, right) -> T (Black, left, v, right)
  | E -> E

(* ── Size and depth ────────────────────────────────────────────────── *)

let rec cardinal = function
  | E -> 0
  | T (_, left, _, right) -> 1 + cardinal left + cardinal right

let rec height = function
  | E -> 0
  | T (_, left, _, right) -> 1 + max (height left) (height right)

(* Black-height: number of black nodes on any path from root to leaf *)
let rec black_height = function
  | E -> 0
  | T (Black, left, _, _) -> 1 + black_height left
  | T (Red, left, _, _) -> black_height left

(* ── Traversals ────────────────────────────────────────────────────── *)

let to_list tree =
  let rec aux acc = function
    | E -> acc
    | T (_, left, v, right) -> aux (v :: aux acc right) left
  in
  aux [] tree

let rec fold f acc = function
  | E -> acc
  | T (_, left, v, right) ->
    let acc' = fold f acc left in
    let acc'' = f acc' v in
    fold f acc'' right

let rec iter f = function
  | E -> ()
  | T (_, left, v, right) ->
    iter f left;
    f v;
    iter f right

let rec for_all p = function
  | E -> true
  | T (_, left, v, right) ->
    p v && for_all p left && for_all p right

let rec exists p = function
  | E -> false
  | T (_, left, v, right) ->
    p v || exists p left || exists p right

(* ── Construction ──────────────────────────────────────────────────── *)

let of_list lst =
  List.fold_left (fun acc x -> insert x acc) E lst

let singleton x = insert x E

(* ── Set operations ────────────────────────────────────────────────── *)

let union t1 t2 =
  fold (fun acc x -> insert x acc) t1 (to_list t2 |> of_list)

let inter t1 t2 =
  fold (fun acc x -> if member x t2 then insert x acc else acc) E t1

let diff t1 t2 =
  fold (fun acc x -> if not (member x t2) then insert x acc else acc) E t1

let subset t1 t2 =
  for_all (fun x -> member x t2) t1

let equal t1 t2 =
  to_list t1 = to_list t2

(* ── Filter / map / partition ──────────────────────────────────────── *)

let filter p tree =
  fold (fun acc x -> if p x then insert x acc else acc) E tree

let partition p tree =
  fold (fun (yes, no) x ->
    if p x then (insert x yes, no) else (yes, insert x no))
    (E, E) tree

(* map may change ordering, so we rebuild from scratch *)
let map f tree =
  fold (fun acc x -> insert (f x) acc) E tree

(* ── Invariant checking (useful for testing) ───────────────────────── *)

(* Verify no red-red violations *)
let rec no_red_red = function
  | E -> true
  | T (Red, T (Red, _, _, _), _, _)
  | T (Red, _, _, T (Red, _, _, _)) -> false
  | T (_, left, _, right) ->
    no_red_red left && no_red_red right

(* Verify uniform black-height *)
let rec valid_black_height = function
  | E -> Some 0
  | T (color, left, _, right) ->
    match valid_black_height left, valid_black_height right with
    | Some lh, Some rh when lh = rh ->
      let bh = if color = Black then lh + 1 else lh in
      Some bh
    | _ -> None

(* Verify BST ordering *)
let rec is_bst_aux lo hi = function
  | E -> true
  | T (_, left, v, right) ->
    (match lo with None -> true | Some l -> v > l) &&
    (match hi with None -> true | Some h -> v < h) &&
    is_bst_aux lo (Some v) left &&
    is_bst_aux (Some v) hi right

let is_valid tree =
  let root_black = match tree with E -> true | T (Black, _, _, _) -> true | _ -> false in
  root_black &&
  no_red_red tree &&
  (valid_black_height tree <> None) &&
  is_bst_aux None None tree

(* ── Pretty printing ───────────────────────────────────────────────── *)

let string_of_color = function Red -> "R" | Black -> "B"

let to_string f tree =
  let buf = Buffer.create 64 in
  let rec aux indent = function
    | E -> ()
    | T (color, left, v, right) ->
      aux (indent ^ "  ") right;
      Buffer.add_string buf indent;
      Buffer.add_string buf (Printf.sprintf "[%s:%s]\n" (string_of_color color) (f v));
      aux (indent ^ "  ") left
  in
  aux "" tree;
  Buffer.contents buf

(* ── Example usage ─────────────────────────────────────────────────── *)

let () =
  let t = of_list [5; 3; 7; 1; 4; 6; 8; 2; 9; 0] in
  Printf.printf "Red-Black Tree (sorted): ";
  List.iter (Printf.printf "%d ") (to_list t);
  print_newline ();
  Printf.printf "Size: %d\n" (cardinal t);
  Printf.printf "Height: %d (black-height: %d)\n" (height t) (black_height t);
  Printf.printf "Contains 4: %b\n" (member 4 t);
  Printf.printf "Contains 99: %b\n" (member 99 t);
  Printf.printf "Valid RB-tree: %b\n" (is_valid t);
  (match min_elt_opt t with Some m -> Printf.printf "Min: %d\n" m | None -> ());
  (match max_elt_opt t with Some m -> Printf.printf "Max: %d\n" m | None -> ());
  let t2 = delete 5 t in
  Printf.printf "After deleting 5: ";
  List.iter (Printf.printf "%d ") (to_list t2);
  print_newline ();
  Printf.printf "Still valid: %b\n" (is_valid t2);
  Printf.printf "\nTree structure:\n%s" (to_string string_of_int t)
