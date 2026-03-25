(* Scapegoat Tree — a weight-balanced binary search tree.
   
   Unlike AVL or red-black trees, scapegoat trees store NO balance metadata
   per node. Instead, they detect imbalance by comparing subtree sizes after
   insertion and rebuild the offending subtree from scratch when the balance
   invariant (controlled by alpha, typically 0.5 < alpha < 1.0) is violated.

   Operations:
   - insert: O(log n) amortized, O(n) worst-case (due to rebuilding)
   - search: O(log n) worst-case
   - delete: O(log n) amortized (lazy — triggers global rebuild when needed)
   - size, height, to_list, of_list, min, max, successor, predecessor

   The alpha parameter controls the trade-off:
   - alpha close to 0.5 → more balanced, more rebuilds
   - alpha close to 1.0 → less balanced, fewer rebuilds

   Reference: Galperin & Rivest, "Scapegoat Trees" (1993)
*)

module ScapegoatTree : sig
  type 'a t

  val empty : ?alpha:float -> unit -> 'a t
  val insert : 'a -> 'a t -> 'a t
  val member : 'a -> 'a t -> bool
  val delete : 'a -> 'a t -> 'a t
  val size : 'a t -> int
  val height : 'a t -> int
  val min_elt : 'a t -> 'a option
  val max_elt : 'a t -> 'a option
  val successor : 'a -> 'a t -> 'a option
  val predecessor : 'a -> 'a t -> 'a option
  val to_sorted_list : 'a t -> 'a list
  val of_list : ?alpha:float -> 'a list -> 'a t
  val fold : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
  val iter : ('a -> unit) -> 'a t -> unit
  val is_empty : 'a t -> bool
  val balanced : 'a t -> bool  (* check if currently within balance invariant *)
end = struct
  type 'a node =
    | Leaf
    | Node of { value: 'a; left: 'a node; right: 'a node; sz: int }

  type 'a t = {
    root: 'a node;
    alpha: float;     (* balance parameter, 0.5 < alpha < 1.0 *)
    max_size: int;    (* max size since last full rebuild — for lazy deletion *)
    cur_size: int;
  }

  let node_size = function
    | Leaf -> 0
    | Node { sz; _ } -> sz

  let make_node v l r =
    Node { value = v; left = l; right = r; sz = 1 + node_size l + node_size r }

  let empty ?(alpha=0.6) () =
    if alpha <= 0.5 || alpha >= 1.0 then
      invalid_arg "ScapegoatTree: alpha must be in (0.5, 1.0)";
    { root = Leaf; alpha; max_size = 0; cur_size = 0 }

  let size t = t.cur_size

  let is_empty t = t.cur_size = 0

  let rec node_height = function
    | Leaf -> 0
    | Node { left; right; _ } -> 1 + max (node_height left) (node_height right)

  let height t = node_height t.root

  (* Flatten tree to sorted list *)
  let rec flatten_node acc = function
    | Leaf -> acc
    | Node { value; left; right; _ } ->
      flatten_node (value :: flatten_node acc right) left

  let to_sorted_list t = flatten_node [] t.root

  (* Build a perfectly balanced tree from a sorted array *)
  let build_from_sorted arr lo hi =
    let rec build lo hi =
      if lo > hi then Leaf
      else
        let mid = lo + (hi - lo) / 2 in
        let left = build lo (mid - 1) in
        let right = build (mid + 1) hi in
        make_node arr.(mid) left right
    in
    build lo hi

  let rebuild_node node =
    let elems = flatten_node [] node in
    let arr = Array.of_list elems in
    let n = Array.length arr in
    if n = 0 then Leaf
    else build_from_sorted arr 0 (n - 1)

  (* h_alpha: max allowed height for n nodes *)
  let h_alpha alpha n =
    if n <= 1 then 0
    else int_of_float (Float.ceil (Float.log (float_of_int n) /. Float.log (1.0 /. alpha)))

  let rec member_node x = function
    | Leaf -> false
    | Node { value; left; right; _ } ->
      if x = value then true
      else if x < value then member_node x left
      else member_node x right

  let member x t = member_node x t.root

  (* Insert and return (new_node, depth). If depth > h_alpha, find scapegoat. *)
  let insert x t =
    if member x t then t  (* no duplicates *)
    else begin
      let needs_rebuild = ref false in
      let rec ins depth = function
        | Leaf ->
          if depth > h_alpha t.alpha (t.cur_size + 1) then
            needs_rebuild := true;
          (make_node x Leaf Leaf, depth)
        | Node { value; left; right; _ } as _node ->
          if x < value then
            let (new_left, d) = ins (depth + 1) left in
            let new_node = make_node value new_left right in
            (* Check if this node is the scapegoat *)
            if !needs_rebuild then begin
              let sz = node_size new_node in
              let lsz = node_size new_left in
              if float_of_int lsz > t.alpha *. float_of_int sz then begin
                needs_rebuild := false;
                (rebuild_node new_node, d)
              end else
                (new_node, d)
            end else
              (new_node, d)
          else
            let (new_right, d) = ins (depth + 1) right in
            let new_node = make_node value left new_right in
            if !needs_rebuild then begin
              let sz = node_size new_node in
              let rsz = node_size new_right in
              if float_of_int rsz > t.alpha *. float_of_int sz then begin
                needs_rebuild := false;
                (rebuild_node new_node, d)
              end else
                (new_node, d)
            end else
              (new_node, d)
      in
      let (new_root, _depth) = ins 0 t.root in
      (* If we still need rebuild after reaching root, rebuild root *)
      let final_root = if !needs_rebuild then rebuild_node new_root else new_root in
      let new_size = t.cur_size + 1 in
      { t with root = final_root; cur_size = new_size; max_size = max t.max_size new_size }
    end

  (* Lazy deletion: remove node, rebuild entire tree if size < alpha * max_size *)
  let delete x t =
    if not (member x t) then t
    else begin
      let rec del = function
        | Leaf -> Leaf
        | Node { value; left; right; _ } ->
          if x < value then make_node value (del left) right
          else if x > value then make_node value left (del right)
          else
            (* Found: replace with in-order successor or predecessor *)
            match left, right with
            | Leaf, Leaf -> Leaf
            | _, Leaf -> left
            | Leaf, _ -> right
            | _ ->
              (* Find min of right subtree *)
              let rec find_min = function
                | Leaf -> failwith "impossible"
                | Node { value; left = Leaf; _ } -> value
                | Node { left; _ } -> find_min left
              in
              let succ = find_min right in
              let rec remove_min = function
                | Leaf -> Leaf
                | Node { left = Leaf; right; _ } -> right
                | Node { value; left; right; _ } -> make_node value (remove_min left) right
              in
              make_node succ left (remove_min right)
      in
      let new_root = del t.root in
      let new_size = t.cur_size - 1 in
      (* If tree is too sparse, rebuild *)
      if new_size > 0 && float_of_int new_size < t.alpha *. float_of_int t.max_size then
        { t with root = rebuild_node new_root; cur_size = new_size; max_size = new_size }
      else
        { t with root = new_root; cur_size = new_size }
    end

  let rec min_elt_node = function
    | Leaf -> None
    | Node { value; left = Leaf; _ } -> Some value
    | Node { left; _ } -> min_elt_node left

  let min_elt t = min_elt_node t.root

  let rec max_elt_node = function
    | Leaf -> None
    | Node { value; right = Leaf; _ } -> Some value
    | Node { right; _ } -> max_elt_node right

  let max_elt t = max_elt_node t.root

  let successor x t =
    let result = ref None in
    let rec search = function
      | Leaf -> ()
      | Node { value; left; right; _ } ->
        if x < value then begin
          result := Some value;
          search left
        end else
          search right
    in
    search t.root;
    !result

  let predecessor x t =
    let result = ref None in
    let rec search = function
      | Leaf -> ()
      | Node { value; left; right; _ } ->
        if x >= value then begin
          (if x > value then result := Some value);
          search right
        end else
          search left
    in
    search t.root;
    !result

  let rec fold_node f acc = function
    | Leaf -> acc
    | Node { value; left; right; _ } ->
      let acc = fold_node f acc left in
      let acc = f acc value in
      fold_node f acc right

  let fold f acc t = fold_node f acc t.root

  let rec iter_node f = function
    | Leaf -> ()
    | Node { value; left; right; _ } ->
      iter_node f left;
      f value;
      iter_node f right

  let iter f t = iter_node f t.root

  let of_list ?(alpha=0.6) lst =
    let sorted = List.sort_uniq compare lst in
    let arr = Array.of_list sorted in
    let n = Array.length arr in
    let root = if n = 0 then Leaf else build_from_sorted arr 0 (n - 1) in
    { root; alpha; max_size = n; cur_size = n }

  (* Check if tree is currently within balance invariant *)
  let rec balanced_node alpha = function
    | Leaf -> true
    | Node { left; right; sz; _ } ->
      let lsz = node_size left in
      let rsz = node_size right in
      float_of_int lsz <= alpha *. float_of_int sz
      && float_of_int rsz <= alpha *. float_of_int sz
      && balanced_node alpha left
      && balanced_node alpha right

  let balanced t = balanced_node t.alpha t.root
end

(* ==================== Demo ==================== *)

let () =
  let open ScapegoatTree in
  Printf.printf "=== Scapegoat Tree Demo ===\n\n";

  (* Build from sequential inserts *)
  let t = ref (empty ()) in
  let values = [50; 30; 70; 20; 40; 60; 80; 10; 25; 35; 45; 55; 65; 75; 90] in
  List.iter (fun v ->
    t := insert v !t;
    Printf.printf "Inserted %d (size=%d, height=%d, balanced=%b)\n"
      v (size !t) (height !t) (balanced !t)
  ) values;

  Printf.printf "\nSorted elements: [%s]\n"
    (String.concat "; " (List.map string_of_int (to_sorted_list !t)));

  Printf.printf "\nMin: %s, Max: %s\n"
    (match min_elt !t with Some v -> string_of_int v | None -> "none")
    (match max_elt !t with Some v -> string_of_int v | None -> "none");

  Printf.printf "Successor of 40: %s\n"
    (match successor 40 !t with Some v -> string_of_int v | None -> "none");
  Printf.printf "Predecessor of 60: %s\n"
    (match predecessor 60 !t with Some v -> string_of_int v | None -> "none");

  (* Delete some elements *)
  Printf.printf "\nDeleting 30, 70, 50...\n";
  t := delete 30 !t;
  t := delete 70 !t;
  t := delete 50 !t;
  Printf.printf "After deletions: size=%d, height=%d, balanced=%b\n"
    (size !t) (height !t) (balanced !t);
  Printf.printf "Sorted: [%s]\n"
    (String.concat "; " (List.map string_of_int (to_sorted_list !t)));

  (* Build from list *)
  Printf.printf "\n--- Build from list [1..20] ---\n";
  let t2 = of_list (List.init 20 (fun i -> i + 1)) in
  Printf.printf "Size: %d, Height: %d, Balanced: %b\n"
    (size t2) (height t2) (balanced t2);

  (* Fold: sum *)
  let sum = fold (fun acc x -> acc + x) 0 t2 in
  Printf.printf "Sum of 1..20: %d\n" sum;

  (* Worst-case insertion order — all ascending *)
  Printf.printf "\n--- Worst-case: 1000 ascending inserts ---\n";
  let t3 = ref (empty ~alpha:0.65 ()) in
  for i = 1 to 1000 do
    t3 := insert i !t3
  done;
  Printf.printf "Size: %d, Height: %d (ideal ~10), Balanced: %b\n"
    (size !t3) (height !t3) (balanced !t3);

  (* Membership test *)
  Printf.printf "\nMember 500: %b, Member 1001: %b\n"
    (member 500 !t3) (member 1001 !t3);

  (* Mass deletion *)
  Printf.printf "\n--- Deleting odd numbers 1..999 ---\n";
  for i = 0 to 499 do
    t3 := delete (2 * i + 1) !t3
  done;
  Printf.printf "Size: %d, Height: %d, Balanced: %b\n"
    (size !t3) (height !t3) (balanced !t3);

  Printf.printf "\n=== Scapegoat Tree Demo Complete ===\n"
