(* zip_tree.ml - Zip Tree Data Structure
 *
 * A zip tree is a form of randomized binary search tree introduced by
 * Tarjan, Levy, and Timmel (2019). It achieves the same expected O(log n)
 * performance as treaps but with a simpler mechanism:
 *
 *   - Each node is assigned a random "rank" drawn from a geometric
 *     distribution (i.e., the number of consecutive heads in fair coin flips).
 *   - The tree maintains a max-heap property on ranks (parent rank >= child rank).
 *   - Nodes with equal rank are ordered so that left children have strictly
 *     lower rank (making the tree a "zip" of two paths during insert/delete).
 *
 * The key insight: insertion "unzips" a path, and deletion "zips" two paths
 * together — hence the name. This is conceptually simpler than treap rotations.
 *
 * Features:
 *   - Insert, delete, search, membership
 *   - Min, max, floor, ceiling
 *   - Kth smallest, rank of element
 *   - Range query (all elements in [lo, hi])
 *   - In-order traversal, fold, map
 *   - Size, height, pretty-print
 *   - Bulk construction from sorted list
 *
 * Usage:
 *   let t = empty |> insert 5 |> insert 3 |> insert 7 |> insert 1
 *   let () = pretty_print string_of_int t
 *   let found = search 3 t       (* Some 3 *)
 *   let k2 = kth 2 t             (* Some 3 — 0-indexed *)
 *   let r = range 2 6 t          (* [3; 5] *)
 *)

(* ── Simple PRNG ─────────────────────────────────────── *)
let prng_state = ref 73  (* different seed from treap *)

let next_random () =
  let s = !prng_state in
  let s = s lxor (s lsl 13) in
  let s = s lxor (s asr 17) in
  let s = s lxor (s lsl 5) in
  prng_state := s;
  abs s

(* Geometric distribution: count trailing 1-bits of a random number.
   This gives P(rank = k) = 1/2^(k+1), matching the original paper. *)
let random_rank () =
  let r = next_random () in
  let rec count_bits n acc =
    if n land 1 = 1 then count_bits (n asr 1) (acc + 1)
    else acc
  in
  count_bits r 0

(* ── Core Types ──────────────────────────────────────── *)
type 'a node = {
  key: 'a;
  rank: int;
  size: int;          (* subtree size for order-statistics *)
  left: 'a zip_tree;
  right: 'a zip_tree;
}
and 'a zip_tree = 'a node option

(* ── Helpers ─────────────────────────────────────────── *)
let empty : 'a zip_tree = None

let is_empty (t : 'a zip_tree) = t = None

let size (t : 'a zip_tree) =
  match t with None -> 0 | Some n -> n.size

let node key rank left right =
  Some { key; rank; size = 1 + size left + size right; left; right }

let height (t : 'a zip_tree) =
  let rec go = function
    | None -> 0
    | Some n -> 1 + max (go n.left) (go n.right)
  in go t

(* ── Search ──────────────────────────────────────────── *)
let rec search x (t : 'a zip_tree) =
  match t with
  | None -> None
  | Some n ->
    if x = n.key then Some n.key
    else if x < n.key then search x n.left
    else search x n.right

let mem x t = search x t <> None

(* ── Insert (Unzip) ──────────────────────────────────── *)
(* Insert splits the path where the new node belongs into
   a left subtree (keys < x) and right subtree (keys > x),
   which become the children of the new node. *)
let insert x (t : 'a zip_tree) =
  let r = random_rank () in
  let rec unzip x r = function
    | None -> node x r None None
    | Some n ->
      if x = n.key then Some n  (* already exists *)
      else if x < n.key then
        if r >= n.rank then
          (* new node should be ancestor of n; unzip n's left *)
          let rec split_left = function
            | None -> (None, None)
            | Some m ->
              if x < m.key then
                let (ll, lr) = split_left m.left in
                (ll, Some { m with left = lr; size = 1 + size lr + size m.right })
              else if x > m.key then
                let (rl, rr) = split_left m.right in
                (Some { m with right = rl; size = 1 + size m.left + size rl }, rr)
              else (m.left, m.right)  (* duplicate *)
          in
          let (l, mid) = split_left n.left in
          node x r l (Some { n with left = mid; size = 1 + size mid + size n.right })
        else
          Some { n with left = unzip x r n.left;
                        size = 1 + size (unzip x r n.left) + size n.right }
      else (* x > n.key *)
        if r > n.rank then
          (* new node should be ancestor of n; unzip n's right *)
          let rec split_right = function
            | None -> (None, None)
            | Some m ->
              if x < m.key then
                let (ll, lr) = split_right m.left in
                (ll, Some { m with left = lr; size = 1 + size lr + size m.right })
              else if x > m.key then
                let (rl, rr) = split_right m.right in
                (Some { m with right = rl; size = 1 + size m.left + size rl }, rr)
              else (m.left, m.right)
          in
          let (mid, r_tree) = split_right n.right in
          node x r (Some { n with right = mid; size = 1 + size n.left + size mid }) r_tree
        else
          Some { n with right = unzip x r n.right;
                        size = 1 + size n.left + size (unzip x r n.right) }
  in
  unzip x r t

(* Simpler insert using split/merge approach *)
let rec split x (t : 'a zip_tree) : 'a zip_tree * 'a zip_tree =
  match t with
  | None -> (None, None)
  | Some n ->
    if x <= n.key then
      let (l, r) = split x n.left in
      (l, Some { n with left = r; size = 1 + size r + size n.right })
    else
      let (l, r) = split x n.right in
      (Some { n with right = l; size = 1 + size n.left + size l }, r)

let rec merge (t1 : 'a zip_tree) (t2 : 'a zip_tree) : 'a zip_tree =
  match t1, t2 with
  | None, t | t, None -> t
  | Some n1, Some n2 ->
    if n1.rank >= n2.rank then
      let merged = merge n1.right t2 in
      Some { n1 with right = merged; size = 1 + size n1.left + size merged }
    else
      let merged = merge t1 n2.left in
      Some { n2 with left = merged; size = 1 + size merged + size n2.right }

let insert_via_merge x (t : 'a zip_tree) =
  if mem x t then t
  else
    let r = random_rank () in
    let (l, r_tree) = split x t in
    merge (merge l (node x r None None)) r_tree

(* ── Delete (Zip) ────────────────────────────────────── *)
(* Delete finds the node and "zips" its two children together *)
let rec delete x (t : 'a zip_tree) : 'a zip_tree =
  match t with
  | None -> None
  | Some n ->
    if x = n.key then merge n.left n.right
    else if x < n.key then
      let new_left = delete x n.left in
      Some { n with left = new_left; size = 1 + size new_left + size n.right }
    else
      let new_right = delete x n.right in
      Some { n with right = new_right; size = 1 + size n.left + size new_right }

(* ── Min / Max ───────────────────────────────────────── *)
let rec min_elt (t : 'a zip_tree) =
  match t with
  | None -> None
  | Some { left = None; key; _ } -> Some key
  | Some n -> min_elt n.left

let rec max_elt (t : 'a zip_tree) =
  match t with
  | None -> None
  | Some { right = None; key; _ } -> Some key
  | Some n -> max_elt n.right

(* ── Floor / Ceiling ─────────────────────────────────── *)
let rec floor x (t : 'a zip_tree) =
  match t with
  | None -> None
  | Some n ->
    if x = n.key then Some n.key
    else if x < n.key then floor x n.left
    else
      match floor x n.right with
      | Some _ as result -> result
      | None -> Some n.key

let rec ceiling x (t : 'a zip_tree) =
  match t with
  | None -> None
  | Some n ->
    if x = n.key then Some n.key
    else if x > n.key then ceiling x n.right
    else
      match ceiling x n.left with
      | Some _ as result -> result
      | None -> Some n.key

(* ── Order Statistics ────────────────────────────────── *)
(* kth smallest, 0-indexed *)
let rec kth k (t : 'a zip_tree) =
  match t with
  | None -> None
  | Some n ->
    let left_size = size n.left in
    if k < left_size then kth k n.left
    else if k = left_size then Some n.key
    else kth (k - left_size - 1) n.right

(* Rank of element (0-indexed position in sorted order) *)
let rec rank_of x (t : 'a zip_tree) =
  match t with
  | None -> None
  | Some n ->
    if x = n.key then Some (size n.left)
    else if x < n.key then rank_of x n.left
    else
      match rank_of x n.right with
      | Some r -> Some (size n.left + 1 + r)
      | None -> None

(* ── Range Query ─────────────────────────────────────── *)
let range lo hi (t : 'a zip_tree) =
  let acc = ref [] in
  let rec go = function
    | None -> ()
    | Some n ->
      if n.key > lo then go n.left;
      if n.key >= lo && n.key <= hi then acc := n.key :: !acc;
      if n.key < hi then go n.right
  in
  go t;
  List.rev !acc

(* ── Traversal ───────────────────────────────────────── *)
let to_list (t : 'a zip_tree) =
  let acc = ref [] in
  let rec go = function
    | None -> ()
    | Some n -> go n.right; acc := n.key :: !acc; go n.left
  in
  go t; !acc

let rec fold f acc (t : 'a zip_tree) =
  match t with
  | None -> acc
  | Some n ->
    let acc = fold f acc n.left in
    let acc = f acc n.key in
    fold f acc n.right

let iter f (t : 'a zip_tree) =
  fold (fun () x -> f x) () t

(* ── Bulk Construction ───────────────────────────────── *)
let of_list lst =
  List.fold_left (fun t x -> insert_via_merge x t) empty lst

(* ── Pretty Print ────────────────────────────────────── *)
let pretty_print to_string (t : 'a zip_tree) =
  let rec go prefix is_left = function
    | None -> ()
    | Some n ->
      Printf.printf "%s%s[%s r=%d]\n"
        prefix
        (if is_left then "├── " else "└── ")
        (to_string n.key) n.rank;
      let new_prefix = prefix ^ (if is_left then "│   " else "    ") in
      go new_prefix true n.left;
      go new_prefix false n.right
  in
  match t with
  | None -> Printf.printf "(empty)\n"
  | Some n ->
    Printf.printf "[%s r=%d]\n" (to_string n.key) n.rank;
    go "" true n.left;
    go "" false n.right

(* ── Validation ──────────────────────────────────────── *)
(* Check BST property and rank-heap property *)
let validate (t : 'a zip_tree) =
  let rec go lo hi parent_rank = function
    | None -> true
    | Some n ->
      let key_ok = (match lo with None -> true | Some l -> n.key > l) in
      let key_ok2 = (match hi with None -> true | Some h -> n.key < h) in
      let rank_ok = n.rank <= parent_rank in
      let size_ok = n.size = 1 + size n.left + size n.right in
      key_ok && key_ok2 && rank_ok && size_ok
      && go lo (Some n.key) n.rank n.left
      && go (Some n.key) hi n.rank n.right
  in
  match t with
  | None -> true
  | Some n -> go None None max_int (Some n)

(* ── Demo ────────────────────────────────────────────── *)
let () =
  Printf.printf "=== Zip Tree Demo ===\n\n";

  (* Build a tree *)
  let values = [42; 17; 8; 31; 56; 23; 4; 99; 12; 67; 50; 35; 71; 2; 88] in
  let t = of_list values in

  Printf.printf "Tree structure (key [rank]):\n";
  pretty_print string_of_int t;

  Printf.printf "\nSize: %d, Height: %d\n" (size t) (height t);
  Printf.printf "Valid: %b\n" (validate t);

  Printf.printf "\nSorted: [%s]\n"
    (String.concat "; " (List.map string_of_int (to_list t)));

  (* Search *)
  Printf.printf "\nSearch 31: %s\n"
    (match search 31 t with Some v -> string_of_int v | None -> "not found");
  Printf.printf "Search 100: %s\n"
    (match search 100 t with Some _ -> "found" | None -> "not found");

  (* Min/Max *)
  Printf.printf "\nMin: %s\n"
    (match min_elt t with Some v -> string_of_int v | None -> "empty");
  Printf.printf "Max: %s\n"
    (match max_elt t with Some v -> string_of_int v | None -> "empty");

  (* Floor/Ceiling *)
  Printf.printf "\nFloor(30): %s\n"
    (match floor 30 t with Some v -> string_of_int v | None -> "none");
  Printf.printf "Ceiling(30): %s\n"
    (match ceiling 30 t with Some v -> string_of_int v | None -> "none");

  (* Order statistics *)
  Printf.printf "\n3rd smallest (0-indexed): %s\n"
    (match kth 3 t with Some v -> string_of_int v | None -> "none");
  Printf.printf "Rank of 42: %s\n"
    (match rank_of 42 t with Some r -> string_of_int r | None -> "not found");

  (* Range query *)
  let r = range 20 60 t in
  Printf.printf "\nRange [20, 60]: [%s]\n"
    (String.concat "; " (List.map string_of_int r));

  (* Delete *)
  let t2 = delete 42 t in
  Printf.printf "\nAfter deleting 42:\n";
  Printf.printf "Contains 42: %b\n" (mem 42 t2);
  Printf.printf "Size: %d\n" (size t2);
  Printf.printf "Still valid: %b\n" (validate t2);

  Printf.printf "\n=== Done ===\n"
