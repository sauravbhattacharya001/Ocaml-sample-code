(* Priority Queue / Heap — Leftist Min-Heap *)
(* Demonstrates: algebraic data types with annotations, persistent data structures,
   functors for generic ordering, purely functional merge-based design *)

(* A leftist heap is a purely functional priority queue. Every operation
   creates a new heap — the original is preserved (persistence).
   The "leftist" property ensures merge runs in O(log n) by always
   merging into the shorter (right) spine. *)

(* --- Heap representation --- *)
(* Each node stores its "rank" = length of the rightmost path to a leaf.
   The leftist property guarantees: rank(left) >= rank(right).
   This keeps the right spine short — at most O(log n) nodes. *)

type 'a heap =
  | Empty
  | Node of int * 'a * 'a heap * 'a heap
  (* Node (rank, value, left_child, right_child) *)

(* --- Core operations --- *)

(* Get the rank of a heap node *)
let rank = function
  | Empty -> 0
  | Node (r, _, _, _) -> r

(* Create a node that maintains the leftist property:
   the child with the larger rank goes on the left *)
let make_node x a b =
  if rank a >= rank b then Node (rank b + 1, x, a, b)
  else Node (rank a + 1, x, b, a)

(* Create an empty heap *)
let empty = Empty

(* Check if the heap is empty *)
let is_empty = function
  | Empty -> true
  | Node _ -> false

(* Merge two heaps — the fundamental operation.
   All other operations are defined in terms of merge.
   Time complexity: O(log n) where n = total elements *)
let rec merge cmp h1 h2 =
  match h1, h2 with
  | Empty, h | h, Empty -> h
  | Node (_, x, a1, b1), Node (_, y, _, _) ->
    if cmp x y <= 0 then
      (* x is smaller: keep x as root, merge b1 with h2 *)
      make_node x a1 (merge cmp b1 h2)
    else
      (* y is smaller: swap and merge *)
      merge cmp h2 h1

(* Insert a value — merge with a singleton heap. O(log n) *)
let insert cmp x h =
  merge cmp (Node (1, x, Empty, Empty)) h

(* Find the minimum element. O(1) *)
let find_min = function
  | Empty -> None
  | Node (_, x, _, _) -> Some x

(* Remove the minimum element — merge the two children. O(log n) *)
let delete_min cmp = function
  | Empty -> Empty
  | Node (_, _, left, right) -> merge cmp left right

(* --- Derived operations --- *)

(* Number of elements in the heap. O(n) *)
let rec size = function
  | Empty -> 0
  | Node (_, _, left, right) -> 1 + size left + size right

(* Depth of the heap. O(n) *)
let rec depth = function
  | Empty -> 0
  | Node (_, _, left, right) -> 1 + max (depth left) (depth right)

(* Build a heap from a list — repeated insertion. O(n log n)
   Could be O(n) with pairwise merging, which we also provide. *)
let from_list cmp lst =
  List.fold_left (fun h x -> insert cmp x h) Empty lst

(* Build a heap from a list using bottom-up pairwise merging. O(n) *)
let from_list_fast cmp lst =
  let singletons = List.map (fun x -> Node (1, x, Empty, Empty)) lst in
  let rec merge_pairs = function
    | [] -> Empty
    | [h] -> h
    | h1 :: h2 :: rest -> merge cmp (merge cmp h1 h2) (merge_pairs rest)
  in
  match singletons with
  | [] -> Empty
  | _ ->
    let rec until_one heaps =
      match heaps with
      | [] -> Empty
      | [h] -> h
      | _ -> until_one (merge_pairs_list heaps)
    and merge_pairs_list = function
      | [] -> []
      | [h] -> [h]
      | h1 :: h2 :: rest -> merge cmp h1 h2 :: merge_pairs_list rest
    in
    until_one singletons

(* Extract all elements in sorted order. O(n log n) *)
let to_sorted_list cmp h =
  let rec aux acc h =
    match find_min h with
    | None -> List.rev acc
    | Some x -> aux (x :: acc) (delete_min cmp h)
  in
  aux [] h

(* Heap sort: build a heap, then extract in order. O(n log n) *)
let heap_sort cmp lst =
  to_sorted_list cmp (from_list_fast cmp lst)

(* Convert heap to a list (not necessarily sorted — structure order) *)
let to_list h =
  let rec aux acc = function
    | Empty -> acc
    | Node (_, x, left, right) -> aux (aux (x :: acc) right) left
  in
  aux [] h

(* Peek at the top k smallest elements without destroying the heap *)
let take_min cmp k h =
  let rec aux acc n h =
    if n = 0 then List.rev acc
    else match find_min h with
      | None -> List.rev acc
      | Some x -> aux (x :: acc) (n - 1) (delete_min cmp h)
  in
  aux [] k h

(* --- Validation --- *)

(* Check that the leftist property holds: rank(left) >= rank(right) *)
let rec is_leftist = function
  | Empty -> true
  | Node (_, _, left, right) ->
    rank left >= rank right && is_leftist left && is_leftist right

(* Check that the min-heap property holds: parent <= children *)
let rec is_min_heap cmp = function
  | Empty -> true
  | Node (_, x, left, right) ->
    let left_ok = match left with
      | Empty -> true
      | Node (_, y, _, _) -> cmp x y <= 0 && is_min_heap cmp left
    in
    let right_ok = match right with
      | Empty -> true
      | Node (_, y, _, _) -> cmp x y <= 0 && is_min_heap cmp right
    in
    left_ok && right_ok

(* --- Pretty printing --- *)

let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

let string_of_option f = function
  | None -> "None"
  | Some x -> "Some " ^ f x

(* ASCII tree visualization *)
let print_heap to_string h =
  let rec aux prefix is_left = function
    | Empty ->
      Printf.printf "%s%s(empty)\n" prefix (if is_left then "├── " else "└── ")
    | Node (r, x, Empty, Empty) ->
      Printf.printf "%s%s%s [rank=%d]\n" prefix
        (if is_left then "├── " else "└── ") (to_string x) r
    | Node (r, x, left, right) ->
      Printf.printf "%s%s%s [rank=%d]\n" prefix
        (if is_left then "├── " else "└── ") (to_string x) r;
      let new_prefix = prefix ^ (if is_left then "│   " else "    ") in
      aux new_prefix true left;
      aux new_prefix false right
  in
  match h with
  | Empty -> print_endline "(empty heap)"
  | Node (r, x, left, right) ->
    Printf.printf "%s [rank=%d]\n" (to_string x) r;
    (match left, right with
     | Empty, Empty -> ()
     | _ ->
       aux "" true left;
       aux "" false right)

(* === Example usage === *)

let () =
  print_endline "=== Leftist Min-Heap ===";
  print_endline "A purely functional priority queue\n";

  (* Build a heap by inserting elements one at a time *)
  print_endline "--- Building a heap ---";
  let data = [5; 3; 8; 1; 7; 2; 6; 4] in
  Printf.printf "Input: %s\n\n" (string_of_int_list data);

  let h = from_list compare data in
  print_endline "Heap structure (insert one-by-one):";
  print_heap string_of_int h;
  print_newline ();

  Printf.printf "Size: %d\n" (size h);
  Printf.printf "Depth: %d\n" (depth h);
  Printf.printf "Minimum: %s\n" (string_of_option string_of_int (find_min h));
  Printf.printf "Is leftist: %b\n" (is_leftist h);
  Printf.printf "Is min-heap: %b\n" (is_min_heap compare h);
  print_newline ();

  (* Extract elements in sorted order *)
  print_endline "--- Sorted extraction ---";
  Printf.printf "Sorted: %s\n" (string_of_int_list (to_sorted_list compare h));
  print_newline ();

  (* Demonstrate persistence — original heap is unchanged *)
  print_endline "--- Persistence (functional data structure) ---";
  let h2 = insert compare 0 h in
  let h3 = delete_min compare h in
  Printf.printf "Original min:       %s\n"
    (string_of_option string_of_int (find_min h));
  Printf.printf "After insert 0 min: %s\n"
    (string_of_option string_of_int (find_min h2));
  Printf.printf "After delete min:   %s\n"
    (string_of_option string_of_int (find_min h3));
  Printf.printf "Original unchanged: %s\n"
    (string_of_int_list (to_sorted_list compare h));
  print_newline ();

  (* Merge two heaps *)
  print_endline "--- Merging heaps ---";
  let ha = from_list compare [10; 20; 30] in
  let hb = from_list compare [15; 25; 5] in
  let hc = merge compare ha hb in
  Printf.printf "Heap A sorted: %s\n" (string_of_int_list (to_sorted_list compare ha));
  Printf.printf "Heap B sorted: %s\n" (string_of_int_list (to_sorted_list compare hb));
  Printf.printf "Merged sorted: %s\n" (string_of_int_list (to_sorted_list compare hc));
  Printf.printf "Merged size: %d\n" (size hc);
  print_newline ();

  (* Heap sort *)
  print_endline "--- Heap sort ---";
  let unsorted = [42; 17; 93; 5; 28; 61; 3; 84; 50; 12] in
  Printf.printf "Input:       %s\n" (string_of_int_list unsorted);
  Printf.printf "Sorted asc:  %s\n"
    (string_of_int_list (heap_sort compare unsorted));
  Printf.printf "Sorted desc: %s\n"
    (string_of_int_list (heap_sort (fun a b -> compare b a) unsorted));
  print_newline ();

  (* Top-k elements *)
  print_endline "--- Top-K smallest ---";
  let big_list = [99; 44; 7; 88; 12; 55; 3; 67; 21; 36] in
  let big_heap = from_list_fast compare big_list in
  Printf.printf "Data: %s\n" (string_of_int_list big_list);
  Printf.printf "Top 3 smallest: %s\n"
    (string_of_int_list (take_min compare 3 big_heap));
  Printf.printf "Top 5 smallest: %s\n"
    (string_of_int_list (take_min compare 5 big_heap));
  print_newline ();

  (* Bottom-up construction is faster for bulk data *)
  print_endline "--- Bottom-up construction (O(n) vs O(n log n)) ---";
  let bulk = List.init 15 (fun i -> 15 - i) in  (* [15; 14; 13; ... 1] *)
  let h_slow = from_list compare bulk in
  let h_fast = from_list_fast compare bulk in
  Printf.printf "Input: %s\n" (string_of_int_list bulk);
  Printf.printf "from_list sorted:      %s\n"
    (string_of_int_list (to_sorted_list compare h_slow));
  Printf.printf "from_list_fast sorted: %s\n"
    (string_of_int_list (to_sorted_list compare h_fast));
  Printf.printf "Both valid heaps: leftist=%b,%b  min-heap=%b,%b\n"
    (is_leftist h_slow) (is_leftist h_fast)
    (is_min_heap compare h_slow) (is_min_heap compare h_fast);
  print_newline ();

  (* Custom comparator: max-heap behavior *)
  print_endline "--- Max-heap via custom comparator ---";
  let max_cmp a b = compare b a in
  let max_h = from_list max_cmp [5; 3; 8; 1; 7] in
  Printf.printf "Max-heap top: %s\n"
    (string_of_option string_of_int (find_min max_h));
  Printf.printf "Descending:   %s\n"
    (string_of_int_list (to_sorted_list max_cmp max_h));
  print_newline ();

  (* String priority queue *)
  print_endline "--- String priority queue ---";
  let words = ["banana"; "apple"; "cherry"; "date"; "elderberry"] in
  let word_heap = from_list String.compare words in
  Printf.printf "Words input: [%s]\n" (String.concat "; " words);
  Printf.printf "Alphabetical: [%s]\n"
    (String.concat "; " (to_sorted_list String.compare word_heap));
  Printf.printf "First word: %s\n"
    (string_of_option (fun s -> s) (find_min word_heap));
  print_newline ();

  (* Visualize the final heap structure *)
  print_endline "--- Heap structure visualization ---";
  let viz_h = from_list compare [4; 2; 6; 1; 3; 5; 7] in
  print_heap string_of_int viz_h;
  print_newline ();

  (* Edge cases *)
  print_endline "--- Edge cases ---";
  Printf.printf "Empty heap min: %s\n"
    (string_of_option string_of_int (find_min Empty));
  Printf.printf "Empty heap size: %d\n" (size Empty);
  Printf.printf "Empty heap is_empty: %b\n" (is_empty Empty);
  let singleton = insert compare 42 Empty in
  Printf.printf "Singleton min: %s\n"
    (string_of_option string_of_int (find_min singleton));
  Printf.printf "Singleton after delete: is_empty=%b\n"
    (is_empty (delete_min compare singleton));
  Printf.printf "Delete from empty: is_empty=%b\n"
    (is_empty (delete_min compare Empty))
