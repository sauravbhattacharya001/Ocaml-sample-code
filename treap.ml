(* treap.ml - Treap (Tree + Heap) Data Structure
 *
 * A treap is a balanced binary search tree where each node has:
 *   - A key (BST property on keys)
 *   - A random priority (heap property on priorities)
 *
 * This combination gives expected O(log n) operations without
 * complex rebalancing logic like red-black or AVL trees.
 *
 * Features:
 *   - Insert, delete, search
 *   - Split and merge (fundamental treap operations)
 *   - Kth smallest element
 *   - Range queries
 *   - Set operations (union, intersection, difference)
 *   - Iterator / in-order traversal
 *   - Pretty printing
 *)

(* ── Simple PRNG ─────────────────────────────────────── *)
let prng_state = ref 42

let next_priority () =
  (* xorshift32 *)
  let s = !prng_state in
  let s = s lxor (s lsl 13) in
  let s = s lxor (s asr 17) in
  let s = s lxor (s lsl 5) in
  prng_state := s;
  abs s

(* ── Core Types ──────────────────────────────────────── *)
type 'a node = {
  key: 'a;
  priority: int;
  size: int;          (* subtree size for order-statistics *)
  left: 'a treap;
  right: 'a treap;
}
and 'a treap = 'a node option

(* ── Helpers ─────────────────────────────────────────── *)
let size = function
  | None -> 0
  | Some n -> n.size

let make_node key priority left right =
  Some { key; priority; size = 1 + size left + size right; left; right }

(* ── Split: treap → (< key, >= key) ─────────────────── *)
let rec split key = function
  | None -> (None, None)
  | Some n ->
    if n.key < key then
      let (l, r) = split key n.right in
      (make_node n.key n.priority n.left l, r)
    else
      let (l, r) = split key n.left in
      (l, make_node n.key n.priority r n.right)

(* ── Merge: assumes all keys in l < all keys in r ───── *)
let rec merge l r =
  match l, r with
  | None, t | t, None -> t
  | Some ln, Some rn ->
    if ln.priority >= rn.priority then
      make_node ln.key ln.priority ln.left (merge ln.right r)
    else
      make_node rn.key rn.priority (merge l rn.left) rn.right

(* ── Insert ──────────────────────────────────────────── *)
let insert key t =
  let p = next_priority () in
  let rec ins = function
    | None -> make_node key p None None
    | Some n ->
      if key = n.key then Some n  (* no duplicates *)
      else if key < n.key then
        let new_left = ins n.left in
        let node = make_node n.key n.priority new_left n.right in
        (* rotate right if heap property violated *)
        match node with
        | Some nd -> (
          match nd.left with
          | Some ln when ln.priority > nd.priority ->
            make_node ln.key ln.priority ln.left
              (make_node nd.key nd.priority ln.right nd.right)
          | _ -> node)
        | None -> node
      else
        let new_right = ins n.right in
        let node = make_node n.key n.priority n.left new_right in
        match node with
        | Some nd -> (
          match nd.right with
          | Some rn when rn.priority > nd.priority ->
            make_node rn.key rn.priority
              (make_node nd.key nd.priority nd.left rn.left) rn.right
          | _ -> node)
        | None -> node
  in
  ins t

(* ── Delete (split-merge approach) ───────────────────── *)
let delete key t =
  let rec del = function
    | None -> None
    | Some n ->
      if key = n.key then merge n.left n.right
      else if key < n.key then
        make_node n.key n.priority (del n.left) n.right
      else
        make_node n.key n.priority n.left (del n.right)
  in
  del t

(* ── Search ──────────────────────────────────────────── *)
let rec mem key = function
  | None -> false
  | Some n ->
    if key = n.key then true
    else if key < n.key then mem key n.left
    else mem key n.right

(* ── Kth smallest (1-indexed) ────────────────────────── *)
let rec kth k = function
  | None -> None
  | Some n ->
    let left_size = size n.left in
    if k <= left_size then kth k n.left
    else if k = left_size + 1 then Some n.key
    else kth (k - left_size - 1) n.right

(* ── Min / Max ───────────────────────────────────────── *)
let rec min_elt = function
  | None -> None
  | Some n -> (match n.left with None -> Some n.key | l -> min_elt l)

let rec max_elt = function
  | None -> None
  | Some n -> (match n.right with None -> Some n.key | r -> max_elt r)

(* ── Range collect [lo, hi] ──────────────────────────── *)
let range lo hi t =
  let acc = ref [] in
  let rec walk = function
    | None -> ()
    | Some n ->
      if n.key > lo then walk n.left;
      if n.key >= lo && n.key <= hi then acc := n.key :: !acc;
      if n.key < hi then walk n.right
  in
  walk t;
  List.rev !acc

(* ── Count in range [lo, hi] ────────────────────────── *)
let count_range lo hi t =
  let c = ref 0 in
  let rec walk = function
    | None -> ()
    | Some n ->
      if n.key > lo then walk n.left;
      if n.key >= lo && n.key <= hi then incr c;
      if n.key < hi then walk n.right
  in
  walk t;
  !c

(* ── Set operations ──────────────────────────────────── *)
let rec union a b =
  match a, b with
  | None, t | t, None -> t
  | Some an, _ ->
    let (bl, br) = split an.key b in
    let left = union an.left bl in
    let right = union an.right br in
    make_node an.key an.priority left right

let intersection a b =
  let acc = ref [] in
  let rec walk = function
    | None -> ()
    | Some n ->
      walk n.left;
      if mem n.key b then acc := n.key :: !acc;
      walk n.right
  in
  walk a;
  List.fold_left (fun t k -> insert k t) None !acc

let difference a b =
  let acc = ref [] in
  let rec walk = function
    | None -> ()
    | Some n ->
      walk n.left;
      if not (mem n.key b) then acc := n.key :: !acc;
      walk n.right
  in
  walk a;
  List.fold_left (fun t k -> insert k t) None !acc

(* ── To sorted list ──────────────────────────────────── *)
let to_list t =
  let acc = ref [] in
  let rec walk = function
    | None -> ()
    | Some n ->
      walk n.right;
      acc := n.key :: !acc;
      walk n.left
  in
  walk t;
  !acc

(* ── From list ───────────────────────────────────────── *)
let of_list lst =
  List.fold_left (fun t k -> insert k t) None lst

(* ── Height (for analysis) ───────────────────────────── *)
let rec height = function
  | None -> 0
  | Some n -> 1 + max (height n.left) (height n.right)

(* ── Pretty print ────────────────────────────────────── *)
let pretty_print to_string t =
  let buf = Buffer.create 256 in
  let rec pp prefix is_left = function
    | None -> ()
    | Some n ->
      Buffer.add_string buf prefix;
      Buffer.add_string buf (if is_left then "├── " else "└── ");
      Buffer.add_string buf (Printf.sprintf "%s (p=%d, sz=%d)\n"
        (to_string n.key) n.priority n.size);
      let new_prefix = prefix ^ (if is_left then "│   " else "    ") in
      pp new_prefix true n.left;
      pp new_prefix false n.right
  in
  (match t with
   | None -> Buffer.add_string buf "(empty treap)\n"
   | Some n ->
     Buffer.add_string buf (Printf.sprintf "%s (p=%d, sz=%d)\n"
       (to_string n.key) n.priority n.size);
     pp "" true n.left;
     pp "" false n.right);
  Buffer.contents buf

(* ── Verify invariants ───────────────────────────────── *)
let verify t =
  let rec check lo hi = function
    | None -> true
    | Some n ->
      let key_ok = (match lo with None -> true | Some l -> n.key > l) &&
                   (match hi with None -> true | Some h -> n.key < h) in
      let heap_ok =
        (match n.left with None -> true | Some l -> n.priority >= l.priority) &&
        (match n.right with None -> true | Some r -> n.priority >= r.priority) in
      let size_ok = n.size = 1 + size n.left + size n.right in
      key_ok && heap_ok && size_ok &&
      check lo (Some n.key) n.left &&
      check (Some n.key) hi n.right
  in
  check None None t


(* ══════════════════════════════════════════════════════
   Demo / Examples
   ══════════════════════════════════════════════════════ *)
let () =
  print_endline "=== Treap (Tree + Heap) Data Structure ===\n";

  (* Build a treap *)
  let values = [5; 3; 8; 1; 4; 7; 9; 2; 6; 10] in
  let t = of_list values in

  Printf.printf "Inserted: %s\n"
    (String.concat ", " (List.map string_of_int values));
  Printf.printf "Size: %d\n" (size t);
  Printf.printf "Height: %d (expected ~%.1f for balanced)\n"
    (height t) (log (float_of_int (size t)) /. log 2.0);
  Printf.printf "Invariants valid: %b\n\n" (verify t);

  (* Sorted output *)
  Printf.printf "Sorted: %s\n"
    (String.concat ", " (List.map string_of_int (to_list t)));

  (* Search *)
  Printf.printf "\nSearch 4: %b\n" (mem 4 t);
  Printf.printf "Search 11: %b\n" (mem 11 t);

  (* Order statistics *)
  Printf.printf "\n1st smallest: %s\n"
    (match kth 1 t with Some k -> string_of_int k | None -> "N/A");
  Printf.printf "5th smallest: %s\n"
    (match kth 5 t with Some k -> string_of_int k | None -> "N/A");
  Printf.printf "Min: %s\n"
    (match min_elt t with Some k -> string_of_int k | None -> "N/A");
  Printf.printf "Max: %s\n"
    (match max_elt t with Some k -> string_of_int k | None -> "N/A");

  (* Range query *)
  let r = range 3 7 t in
  Printf.printf "\nRange [3,7]: %s\n"
    (String.concat ", " (List.map string_of_int r));
  Printf.printf "Count in [3,7]: %d\n" (count_range 3 7 t);

  (* Delete *)
  let t2 = delete 5 t in
  Printf.printf "\nAfter deleting 5: %s\n"
    (String.concat ", " (List.map string_of_int (to_list t2)));
  Printf.printf "Size: %d, Valid: %b\n" (size t2) (verify t2);

  (* Set operations *)
  let a = of_list [1; 3; 5; 7; 9] in
  let b = of_list [2; 3; 5; 8; 9] in
  Printf.printf "\nSet A: %s\n"
    (String.concat ", " (List.map string_of_int (to_list a)));
  Printf.printf "Set B: %s\n"
    (String.concat ", " (List.map string_of_int (to_list b)));
  Printf.printf "Union:        %s\n"
    (String.concat ", " (List.map string_of_int (to_list (union a b))));
  Printf.printf "Intersection: %s\n"
    (String.concat ", " (List.map string_of_int (to_list (intersection a b))));
  Printf.printf "Difference:   %s\n"
    (String.concat ", " (List.map string_of_int (to_list (difference a b))));

  (* Pretty print *)
  print_endline "\nTree structure:";
  print_string (pretty_print string_of_int t);

  (* Split demo *)
  let (left, right) = split 6 t in
  Printf.printf "\nSplit at 6:\n";
  Printf.printf "  Left  (< 6): %s\n"
    (String.concat ", " (List.map string_of_int (to_list left)));
  Printf.printf "  Right (>= 6): %s\n"
    (String.concat ", " (List.map string_of_int (to_list right)));

  (* Merge them back *)
  let merged = merge left right in
  Printf.printf "  Merged back: %s (valid: %b)\n"
    (String.concat ", " (List.map string_of_int (to_list merged)))
    (verify merged);

  print_endline "\n=== Done ==="
