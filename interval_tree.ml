(* Interval Tree — augmented AVL tree for efficient interval queries *)
(* Stores intervals [lo, hi] in a balanced BST keyed by lo, augmented *)
(* with the maximum hi in each subtree for O(log n) overlap queries.  *)
(* Uses AVL balancing (height-based) for variety vs the repo's RB tree. *)

(* ── Types ─────────────────────────────────────────────────────────── *)

type interval = { lo: int; hi: int }

type t =
  | E
  | N of t * interval * t * int * int
  (* left, interval, right, height, max_hi *)

(* ── Helpers ───────────────────────────────────────────────────────── *)

let intervals_equal a b = a.lo = b.lo && a.hi = b.hi

let interval_to_string iv =
  Printf.sprintf "[%d, %d]" iv.lo iv.hi

let compare_interval a b =
  let c = compare a.lo b.lo in
  if c <> 0 then c else compare a.hi b.hi

let height = function E -> 0 | N (_, _, _, h, _) -> h

let max_hi = function E -> min_int | N (_, _, _, _, m) -> m

let node l iv r =
  let h = 1 + max (height l) (height r) in
  let m = max iv.hi (max (max_hi l) (max_hi r)) in
  N (l, iv, r, h, m)

let balance_factor = function
  | E -> 0
  | N (l, _, r, _, _) -> height l - height r

(* ── AVL rotations ─────────────────────────────────────────────────── *)

let rotate_right = function
  | N (N (ll, lv, lr, _, _), v, r, _, _) ->
    node ll lv (node lr v r)
  | t -> t

let rotate_left = function
  | N (l, v, N (rl, rv, rr, _, _), _, _) ->
    node (node l v rl) rv rr
  | t -> t

let rebalance t =
  match t with
  | E -> E
  | N (l, v, r, _, _) ->
    let bf = balance_factor t in
    if bf > 1 then begin
      if balance_factor l < 0 then
        rotate_right (node (rotate_left l) v r)
      else
        rotate_right t
    end else if bf < -1 then begin
      if balance_factor r > 0 then
        rotate_left (node l v (rotate_right r))
      else
        rotate_left t
    end else
      node l v r

(* ── Core operations ───────────────────────────────────────────────── *)

let empty = E

let is_empty = function E -> true | _ -> false

let rec insert iv = function
  | E -> node E iv E
  | N (l, v, r, _, _) ->
    if compare_interval iv v <= 0 then
      rebalance (node (insert iv l) v r)
    else
      rebalance (node l v (insert iv r))

let rec min_elt = function
  | E -> failwith "IntervalTree.min_elt: empty tree"
  | N (E, v, _, _, _) -> v
  | N (l, _, _, _, _) -> min_elt l

let rec max_elt = function
  | E -> failwith "IntervalTree.max_elt: empty tree"
  | N (_, v, E, _, _) -> v
  | N (_, _, r, _, _) -> max_elt r

let rec remove_min = function
  | E -> failwith "IntervalTree.remove_min: empty"
  | N (E, _, r, _, _) -> r
  | N (l, v, r, _, _) -> rebalance (node (remove_min l) v r)

let rec remove iv = function
  | E -> E
  | N (l, v, r, _, _) ->
    let c = compare_interval iv v in
    if c < 0 then rebalance (node (remove iv l) v r)
    else if c > 0 then rebalance (node l v (remove iv r))
    else
      (* Found it *)
      match l, r with
      | E, _ -> r
      | _, E -> l
      | _, _ ->
        let successor = min_elt r in
        rebalance (node l successor (remove_min r))

let rec mem iv = function
  | E -> false
  | N (l, v, r, _, _) ->
    let c = compare_interval iv v in
    if c = 0 then true
    else if c < 0 then mem iv l
    else mem iv r

let rec cardinal = function
  | E -> 0
  | N (l, _, r, _, _) -> 1 + cardinal l + cardinal r

(* ── Query operations ──────────────────────────────────────────────── *)

(* Two intervals overlap iff a.lo <= b.hi && b.lo <= a.hi *)
let intervals_overlap a b = a.lo <= b.hi && b.lo <= a.hi

let overlaps query t =
  let acc = ref [] in
  let rec go = function
    | E -> ()
    | N (l, v, r, _, m) ->
      if query.lo > m then ()  (* prune: no interval in subtree can overlap *)
      else begin
        go l;
        if intervals_overlap query v then acc := v :: !acc;
        if query.hi >= v.lo then go r
      end
  in
  go t;
  List.rev !acc

let any_overlap query t =
  let rec go = function
    | E -> false
    | N (l, v, r, _, m) ->
      if query.lo > m then false
      else if intervals_overlap query v then true
      else if go l then true
      else query.hi >= v.lo && go r
  in
  go t

let find_containing point t =
  overlaps { lo = point; hi = point } t

let find_intersecting = overlaps

let find_min t = min_elt t

let find_max t =
  (* max by hi: we need to search. But spec says "largest hi". *)
  (* We can use the augmented max to guide search. *)
  let rec go best = function
    | E -> best
    | N (l, v, r, _, m) ->
      let best = if v.hi > best.hi then v else best in
      (* The max_hi tells us which subtree might have the largest hi *)
      if max_hi r >= max_hi l then
        go best r
      else
        go best l
  in
  match t with
  | E -> failwith "IntervalTree.find_max: empty tree"
  | N (_, v, _, _, _) -> go v t

let span = function
  | E -> None
  | t ->
    let lo = (min_elt t).lo in
    let hi = max_hi t in
    Some { lo; hi }

(* ── Higher-order ──────────────────────────────────────────────────── *)

let rec fold f acc = function
  | E -> acc
  | N (l, v, r, _, _) ->
    let acc = fold f acc l in
    let acc = f acc v in
    fold f acc r

let rec iter f = function
  | E -> ()
  | N (l, v, r, _, _) ->
    iter f l; f v; iter f r

let map f t =
  let lst = fold (fun acc iv -> f iv :: acc) [] t in
  List.fold_left (fun t iv -> insert iv t) empty lst

let filter pred t =
  fold (fun acc iv -> if pred iv then insert iv acc else acc) empty t

let rec for_all pred = function
  | E -> true
  | N (l, v, r, _, _) ->
    pred v && for_all pred l && for_all pred r

let rec exists pred = function
  | E -> false
  | N (l, v, r, _, _) ->
    pred v || exists pred l || exists pred r

let partition pred t =
  fold (fun (yes, no) iv ->
    if pred iv then (insert iv yes, no)
    else (yes, insert iv no)
  ) (empty, empty) t

(* ── Set operations ────────────────────────────────────────────────── *)

let union a b = fold (fun t iv -> insert iv t) a b

let inter a b =
  fold (fun acc iv -> if mem iv b then insert iv acc else acc) empty a

let diff a b =
  fold (fun acc iv -> if not (mem iv b) then insert iv acc else acc) empty a

(* ── Utilities ─────────────────────────────────────────────────────── *)

let to_list t = fold (fun acc iv -> iv :: acc) [] t |> List.rev

let of_list lst = List.fold_left (fun t iv -> insert iv t) empty lst

let to_string t =
  let ivs = to_list t in
  "{" ^ String.concat ", " (List.map interval_to_string ivs) ^ "}"

let rec validate = function
  | E -> true
  | N (l, v, r, h, m) ->
    (* Check height *)
    let correct_h = 1 + max (height l) (height r) = h in
    (* Check max *)
    let correct_m = max v.hi (max (max_hi l) (max_hi r)) = m in
    (* Check balance *)
    let balanced = abs (height l - height r) <= 1 in
    (* Check BST ordering *)
    let left_ok = match l with
      | E -> true
      | N (_, lv, _, _, _) -> compare_interval lv v <= 0
    in
    let right_ok = match r with
      | E -> true
      | N (_, rv, _, _, _) -> compare_interval v rv <= 0
    in
    correct_h && correct_m && balanced && left_ok && right_ok
    && validate l && validate r
