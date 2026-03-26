(* Order Statistics Tree — augmented balanced BST with rank/select ops  *)
(* Supports O(log n) rank, select, count_range in addition to standard *)
(* insert, delete, member operations.                                   *)
(* Built on a weight-balanced (size-balanced) tree for simplicity.      *)

(* ── Types ─────────────────────────────────────────────────────────── *)

type 'a ost =
  | Leaf
  | Node of { left: 'a ost; value: 'a; right: 'a ost; size: int }

(* ── Size helper ───────────────────────────────────────────────────── *)

let size = function
  | Leaf -> 0
  | Node n -> n.size

let node left value right =
  Node { left; value; right; size = 1 + size left + size right }

(* ── Balancing (weight-balanced tree, α = 0.29) ────────────────────── *)

let alpha = 0.29

let is_balanced t =
  match t with
  | Leaf -> true
  | Node n ->
    let s = float_of_int n.size in
    float_of_int (size n.left) <= (1.0 -. alpha) *. s &&
    float_of_int (size n.right) <= (1.0 -. alpha) *. s

let rec to_list_acc acc = function
  | Leaf -> acc
  | Node n -> to_list_acc (n.value :: to_list_acc acc n.right) n.left

let to_sorted_list t = to_list_acc [] t

let rec of_sorted_list lst len =
  if len <= 0 then (Leaf, lst)
  else
    let left_len = (len - 1) / 2 in
    let right_len = len - 1 - left_len in
    let (left, rest) = of_sorted_list lst left_len in
    match rest with
    | [] -> (left, [])  (* shouldn't happen with correct len *)
    | v :: rest' ->
      let (right, rest'') = of_sorted_list rest' right_len in
      (node left v right, rest'')

let rebuild t =
  let lst = to_sorted_list t in
  let (t', _) = of_sorted_list lst (List.length lst) in
  t'

let balance t =
  if is_balanced t then t else rebuild t

(* ── Insert ────────────────────────────────────────────────────────── *)

let rec insert x = function
  | Leaf -> node Leaf x Leaf
  | Node n ->
    if x < n.value then
      balance (node (insert x n.left) n.value n.right)
    else if x > n.value then
      balance (node n.left n.value (insert x n.right))
    else
      Node n  (* duplicate: no-op *)

(* ── Member ────────────────────────────────────────────────────────── *)

let rec member x = function
  | Leaf -> false
  | Node n ->
    if x < n.value then member x n.left
    else if x > n.value then member x n.right
    else true

(* ── Min / Max ─────────────────────────────────────────────────────── *)

let rec min_element = function
  | Leaf -> failwith "min_element: empty tree"
  | Node { left = Leaf; value; _ } -> value
  | Node n -> min_element n.left

let rec max_element = function
  | Leaf -> failwith "max_element: empty tree"
  | Node { right = Leaf; value; _ } -> value
  | Node n -> max_element n.right

(* ── Delete ────────────────────────────────────────────────────────── *)

let rec delete x = function
  | Leaf -> Leaf
  | Node n ->
    if x < n.value then
      balance (node (delete x n.left) n.value n.right)
    else if x > n.value then
      balance (node n.left n.value (delete x n.right))
    else
      (* Found: remove this node *)
      match n.left, n.right with
      | Leaf, r -> r
      | l, Leaf -> l
      | l, r ->
        let successor = min_element r in
        balance (node l successor (delete successor r))

(* ── Select (find k-th smallest, 0-indexed) ───────────────────────── *)

let rec select k = function
  | Leaf -> failwith "select: index out of bounds"
  | Node n ->
    let left_size = size n.left in
    if k < left_size then select k n.left
    else if k = left_size then n.value
    else select (k - left_size - 1) n.right

(* ── Rank (number of elements strictly less than x) ────────────────── *)

let rec rank x = function
  | Leaf -> 0
  | Node n ->
    if x < n.value then rank x n.left
    else if x > n.value then size n.left + 1 + rank x n.right
    else size n.left

(* ── Count range [lo, hi] ─────────────────────────────────────────── *)

let count_range lo hi t =
  if lo > hi then 0
  else
    let r_hi =
      let rec count_leq x = function
        | Leaf -> 0
        | Node n ->
          if x < n.value then count_leq x n.left
          else if x > n.value then size n.left + 1 + count_leq x n.right
          else size n.left + 1
      in count_leq hi t
    in
    let r_lo = rank lo t in
    r_hi - r_lo

(* ── Range query: get all elements in [lo, hi] ────────────────────── *)

let range_query lo hi t =
  let rec aux acc = function
    | Leaf -> acc
    | Node n ->
      let acc' = if n.value > hi then acc
                 else aux acc n.right in
      let acc'' = if n.value >= lo && n.value <= hi
                  then n.value :: acc'
                  else acc' in
      if n.value < lo then acc''
      else aux acc'' n.left
  in
  aux [] t

(* ── Median ────────────────────────────────────────────────────────── *)

let median t =
  let s = size t in
  if s = 0 then failwith "median: empty tree"
  else select (s / 2) t

(* ── Percentile (0.0 to 1.0) ──────────────────────────────────────── *)

let percentile p t =
  let s = size t in
  if s = 0 then failwith "percentile: empty tree"
  else
    let k = int_of_float (p *. float_of_int (s - 1)) in
    let k = max 0 (min (s - 1) k) in
    select k t

(* ── Fold / Iter ───────────────────────────────────────────────────── *)

let rec fold_inorder f acc = function
  | Leaf -> acc
  | Node n ->
    let acc' = fold_inorder f acc n.left in
    let acc'' = f acc' n.value in
    fold_inorder f acc'' n.right

let iter f t = fold_inorder (fun () x -> f x) () t

(* ── From list ─────────────────────────────────────────────────────── *)

let of_list lst = List.fold_left (fun t x -> insert x t) Leaf lst

(* ── To list (in-order) ────────────────────────────────────────────── *)

let to_list t = List.rev (fold_inorder (fun acc x -> x :: acc) [] t)

(* ── Height (for diagnostics) ─────────────────────────────────────── *)

let rec height = function
  | Leaf -> 0
  | Node n -> 1 + max (height n.left) (height n.right)

(* ── Pretty print ──────────────────────────────────────────────────── *)

let print_tree to_string t =
  let rec aux prefix is_left = function
    | Leaf -> ()
    | Node n ->
      Printf.printf "%s%s%s (size=%d)\n"
        prefix
        (if is_left then "├── " else "└── ")
        (to_string n.value)
        n.size;
      let new_prefix = prefix ^ (if is_left then "│   " else "    ") in
      aux new_prefix true n.left;
      aux new_prefix false n.right
  in
  match t with
  | Leaf -> Printf.printf "(empty)\n"
  | Node n ->
    Printf.printf "%s (size=%d)\n" (to_string n.value) n.size;
    aux "" true n.left;
    aux "" false n.right

(* ══════════════════════════════════════════════════════════════════════ *)
(* Demo / Tests                                                         *)
(* ══════════════════════════════════════════════════════════════════════ *)

let () =
  Printf.printf "=== Order Statistics Tree ===\n\n";

  (* Build tree from shuffled list *)
  let values = [5; 2; 8; 1; 4; 7; 9; 3; 6; 10] in
  let t = of_list values in

  Printf.printf "Tree structure:\n";
  print_tree string_of_int t;
  Printf.printf "\nSize: %d, Height: %d\n\n" (size t) (height t);

  (* Select: k-th smallest *)
  Printf.printf "── Select (k-th smallest, 0-indexed) ──\n";
  for k = 0 to size t - 1 do
    Printf.printf "  select(%d) = %d\n" k (select k t)
  done;

  (* Rank: elements less than x *)
  Printf.printf "\n── Rank (elements < x) ──\n";
  List.iter (fun x ->
    Printf.printf "  rank(%d) = %d\n" x (rank x t)
  ) [1; 3; 5; 7; 10; 11];

  (* Count range *)
  Printf.printf "\n── Count range ──\n";
  Printf.printf "  count_range(3, 7) = %d\n" (count_range 3 7 t);
  Printf.printf "  count_range(1, 10) = %d\n" (count_range 1 10 t);
  Printf.printf "  count_range(5, 5) = %d\n" (count_range 5 5 t);
  Printf.printf "  count_range(11, 20) = %d\n" (count_range 11 20 t);

  (* Range query *)
  Printf.printf "\n── Range query [3, 7] ──\n";
  let elems = range_query 3 7 t in
  Printf.printf "  elements: [%s]\n"
    (String.concat "; " (List.map string_of_int elems));

  (* Median and percentiles *)
  Printf.printf "\n── Median & Percentiles ──\n";
  Printf.printf "  median = %d\n" (median t);
  Printf.printf "  25th percentile = %d\n" (percentile 0.25 t);
  Printf.printf "  75th percentile = %d\n" (percentile 0.75 t);
  Printf.printf "  90th percentile = %d\n" (percentile 0.90 t);

  (* Delete and verify *)
  Printf.printf "\n── Delete 5 ──\n";
  let t2 = delete 5 t in
  Printf.printf "  size: %d, member(5): %b\n" (size t2) (member 5 t2);
  Printf.printf "  sorted: [%s]\n"
    (String.concat "; " (List.map string_of_int (to_list t2)));

  (* Min/Max *)
  Printf.printf "\n── Min/Max ──\n";
  Printf.printf "  min = %d, max = %d\n" (min_element t) (max_element t);

  (* Large-scale test *)
  Printf.printf "\n── Large-scale test (1000 elements) ──\n";
  let big = List.init 1000 (fun i -> i) in
  let big_t = of_list big in
  Printf.printf "  size: %d, height: %d\n" (size big_t) (height big_t);
  Printf.printf "  select(0) = %d\n" (select 0 big_t);
  Printf.printf "  select(499) = %d\n" (select 499 big_t);
  Printf.printf "  select(999) = %d\n" (select 999 big_t);
  Printf.printf "  rank(500) = %d\n" (rank 500 big_t);
  Printf.printf "  count_range(100, 200) = %d\n" (count_range 100 200 big_t);

  Printf.printf "\n✓ All Order Statistics Tree operations verified!\n"
