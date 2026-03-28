(* Binomial Heap — Purely Functional Mergeable Priority Queue *)
(* Demonstrates: recursive algebraic types, list-based forest representation,
   carry-propagation analogous to binary arithmetic, functor-based ordering *)

(* A binomial heap is a forest of heap-ordered binomial trees.
   Each tree of rank k has exactly 2^k nodes. The forest maintains
   at most one tree of each rank — analogous to binary number representation.
   
   Key operations:
   - insert:      O(1) amortised, O(log n) worst-case
   - find_min:    O(log n)
   - delete_min:  O(log n)
   - merge:       O(log n)
   
   This makes binomial heaps ideal when frequent merges are needed. *)

(* --- Binomial tree representation --- *)
(* A binomial tree of rank k:
   - rank 0: a single node
   - rank k: formed by linking two rank-(k-1) trees;
             one becomes the leftmost child of the other's root *)

type 'a tree = {
  rank : int;
  root : 'a;
  children : 'a tree list;  (* children stored in decreasing rank order *)
}

(* A binomial heap is a list of trees in increasing rank order,
   with no two trees of the same rank *)
type 'a heap = 'a tree list

(* --- Helper: link two trees of equal rank --- *)
(* The tree with the smaller root becomes the parent.
   This preserves heap order. O(1). *)

let link t1 t2 =
  assert (t1.rank = t2.rank);
  if t1.root <= t2.root then
    { rank = t1.rank + 1; root = t1.root; children = t2 :: t1.children }
  else
    { rank = t2.rank + 1; root = t2.root; children = t1 :: t2.children }

(* --- Insert a single tree into a forest --- *)
(* Like adding 1 to a binary number: carry propagation *)

let rec insert_tree t = function
  | [] -> [t]
  | t' :: rest as ts ->
    if t.rank < t'.rank then t :: ts
    else insert_tree (link t t') rest

(* --- Insert an element --- *)

let insert x heap =
  insert_tree { rank = 0; root = x; children = [] } heap

(* --- Merge two heaps --- *)
(* Like binary addition of two numbers *)

let rec merge h1 h2 =
  match h1, h2 with
  | [], h | h, [] -> h
  | t1 :: rest1, t2 :: rest2 ->
    if t1.rank < t2.rank then
      t1 :: merge rest1 h2
    else if t2.rank < t1.rank then
      t2 :: merge h1 rest2
    else
      insert_tree (link t1 t2) (merge rest1 rest2)

(* --- Find minimum element --- *)
(* Scan all roots — there are at most O(log n) trees *)

let find_min = function
  | [] -> failwith "find_min: empty heap"
  | trees ->
    List.fold_left
      (fun acc t -> if t.root < acc then t.root else acc)
      (List.hd trees).root
      (List.tl trees)

(* --- Remove minimum element --- *)
(* 1. Find the tree with the minimum root
   2. Remove it from the forest
   3. Reverse its children (they form a valid binomial heap)
   4. Merge the reversed children back into the remaining forest *)

let delete_min = function
  | [] -> failwith "delete_min: empty heap"
  | trees ->
    (* Find the tree with minimum root *)
    let min_tree =
      List.fold_left
        (fun acc t -> if t.root < acc.root then t else acc)
        (List.hd trees) (List.tl trees)
    in
    (* Remove min_tree from the forest *)
    let rest = List.filter (fun t -> t != min_tree) trees in
    (* Reverse children to get increasing-rank order, then merge *)
    merge rest (List.rev min_tree.children)

(* --- Construct from list --- *)

let of_list lst =
  List.fold_left (fun h x -> insert x h) [] lst

(* --- Convert to sorted list --- *)

let rec to_sorted_list heap =
  match heap with
  | [] -> []
  | _ ->
    let m = find_min heap in
    m :: to_sorted_list (delete_min heap)

(* --- Size: count total elements --- *)

let size heap =
  let rec tree_size t =
    1 + List.fold_left (fun acc c -> acc + tree_size c) 0 t.children
  in
  List.fold_left (fun acc t -> acc + tree_size t) 0 heap

(* --- Is empty --- *)

let is_empty heap = heap = []

(* --- Peek at all tree ranks (useful for understanding structure) --- *)

let ranks heap = List.map (fun t -> t.rank) heap

(* ================================================================ *)
(*                       DEMONSTRATIONS                              *)
(* ================================================================ *)

let () =
  Printf.printf "=== Binomial Heap Demo ===\n\n";

  (* Build a heap by inserting elements *)
  let h = of_list [5; 3; 8; 1; 9; 2; 7; 4; 6; 10] in
  Printf.printf "Heap size: %d\n" (size h);
  Printf.printf "Minimum: %d\n" (find_min h);
  Printf.printf "Tree ranks: [%s]\n"
    (String.concat "; " (List.map string_of_int (ranks h)));

  (* Extract sorted *)
  Printf.printf "Sorted extraction: ";
  let sorted = to_sorted_list h in
  List.iter (fun x -> Printf.printf "%d " x) sorted;
  Printf.printf "\n\n";

  (* Demonstrate merge *)
  Printf.printf "--- Merge Demo ---\n";
  let h1 = of_list [10; 20; 30] in
  let h2 = of_list [5; 15; 25] in
  let merged = merge h1 h2 in
  Printf.printf "Heap1 min: %d, Heap2 min: %d\n" (find_min h1) (find_min h2);
  Printf.printf "Merged min: %d, merged size: %d\n" (find_min merged) (size merged);
  Printf.printf "Merged sorted: ";
  List.iter (fun x -> Printf.printf "%d " x) (to_sorted_list merged);
  Printf.printf "\n\n";

  (* Demonstrate persistence *)
  Printf.printf "--- Persistence Demo ---\n";
  let original = of_list [3; 1; 4; 1; 5] in
  let after_delete = delete_min original in
  Printf.printf "Original min: %d (size %d)\n" (find_min original) (size original);
  Printf.printf "After delete_min: min = %d (size %d)\n"
    (find_min after_delete) (size after_delete);
  Printf.printf "Original still intact: min = %d (size %d)\n"
    (find_min original) (size original);

  (* Binary number analogy *)
  Printf.printf "\n--- Binary Number Analogy ---\n";
  Printf.printf "A binomial heap with n elements has trees whose ranks\n";
  Printf.printf "correspond to the set bits in n's binary representation.\n\n";
  for n = 1 to 10 do
    let h = of_list (List.init n (fun i -> i)) in
    Printf.printf "n=%2d (binary: %s) -> ranks: [%s]\n"
      n
      (let rec bits x = if x = 0 then "" else bits (x / 2) ^ string_of_int (x mod 2) in
       let s = bits n in if s = "" then "0" else s)
      (String.concat ", " (List.map string_of_int (ranks h)))
  done;

  Printf.printf "\n--- Heapsort via Binomial Heap ---\n";
  let data = [42; 17; 93; 5; 28; 61; 3; 84; 50; 12] in
  Printf.printf "Input:  ";
  List.iter (fun x -> Printf.printf "%d " x) data;
  Printf.printf "\n";
  let sorted = to_sorted_list (of_list data) in
  Printf.printf "Sorted: ";
  List.iter (fun x -> Printf.printf "%d " x) sorted;
  Printf.printf "\n";

  Printf.printf "\nAll demos complete.\n"
