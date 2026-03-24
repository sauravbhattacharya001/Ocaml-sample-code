(* leftist_heap.ml — Leftist Heap (weight-biased mergeable priority queue)
 *
 * A leftist heap is a heap-ordered binary tree where the "rank" (length of
 * the rightmost path) of the left child is always >= the right child.
 * This guarantees O(log n) merge, insert, and delete-min.
 *
 * Usage:
 *   let h = LeftistHeap.empty |> LeftistHeap.insert 5 |> LeftistHeap.insert 3
 *   let min_val = LeftistHeap.find_min h    (* Some 3 *)
 *   let h' = LeftistHeap.delete_min h       (* heap without 3 *)
 *)

module LeftistHeap : sig
  type 'a t

  val empty : 'a t
  val is_empty : 'a t -> bool
  val insert : 'a -> 'a t -> 'a t
  val merge : 'a t -> 'a t -> 'a t
  val find_min : 'a t -> 'a option
  val delete_min : 'a t -> 'a t
  val of_list : 'a list -> 'a t
  val to_sorted_list : 'a t -> 'a list
  val size : 'a t -> int
  val to_string : ('a -> string) -> 'a t -> string
end = struct
  type 'a t =
    | Leaf
    | Node of int * 'a * 'a t * 'a t  (* rank, value, left, right *)

  let empty = Leaf

  let is_empty = function Leaf -> true | _ -> false

  let rank = function Leaf -> 0 | Node (r, _, _, _) -> r

  let make_node x left right =
    if rank left >= rank right then
      Node (rank right + 1, x, left, right)
    else
      Node (rank left + 1, x, right, left)

  let rec merge h1 h2 =
    match h1, h2 with
    | Leaf, h | h, Leaf -> h
    | Node (_, x, l1, r1), Node (_, y, l2, r2) ->
      if x <= y then
        make_node x l1 (merge r1 h2)
      else
        make_node y l2 (merge h1 r2)

  let insert x h = merge (Node (1, x, Leaf, Leaf)) h

  let find_min = function
    | Leaf -> None
    | Node (_, x, _, _) -> Some x

  let delete_min = function
    | Leaf -> Leaf
    | Node (_, _, l, r) -> merge l r

  let of_list lst = List.fold_left (fun h x -> insert x h) empty lst

  let to_sorted_list h =
    let rec aux acc h =
      match find_min h with
      | None -> List.rev acc
      | Some x -> aux (x :: acc) (delete_min h)
    in
    aux [] h

  let rec size = function
    | Leaf -> 0
    | Node (_, _, l, r) -> 1 + size l + size r

  let to_string f h =
    let items = to_sorted_list h in
    let inner = String.concat ", " (List.map f items) in
    Printf.sprintf "LeftistHeap[%s]" inner
end

(* --- Demo --- *)
let () =
  let open LeftistHeap in
  Printf.printf "=== Leftist Heap Demo ===\n\n";

  (* Build from list *)
  let data = [42; 7; 23; 1; 15; 99; 3; 50; 8; 12] in
  Printf.printf "Input: [%s]\n"
    (String.concat "; " (List.map string_of_int data));

  let h = of_list data in
  Printf.printf "Heap: %s\n" (to_string string_of_int h);
  Printf.printf "Size: %d\n\n" (size h);

  (* Extract min *)
  (match find_min h with
   | Some x -> Printf.printf "Min: %d\n" x
   | None -> Printf.printf "Empty heap\n");

  (* Pop elements in order *)
  Printf.printf "\nExtracting in sorted order: ";
  let sorted = to_sorted_list h in
  Printf.printf "%s\n"
    (String.concat " " (List.map string_of_int sorted));

  (* Merge two heaps *)
  Printf.printf "\n--- Merge Demo ---\n";
  let h1 = of_list [10; 20; 30] in
  let h2 = of_list [5; 25; 35] in
  Printf.printf "Heap A: %s\n" (to_string string_of_int h1);
  Printf.printf "Heap B: %s\n" (to_string string_of_int h2);
  let merged = merge h1 h2 in
  Printf.printf "Merged: %s\n" (to_string string_of_int merged);
  Printf.printf "Merged size: %d\n\n" (size merged);

  (* Incremental insert + delete *)
  Printf.printf "--- Insert/Delete cycle ---\n";
  let h3 = empty |> insert 100 |> insert 50 |> insert 75 in
  Printf.printf "After inserts: %s\n" (to_string string_of_int h3);
  let h4 = delete_min h3 in
  Printf.printf "After delete_min: %s\n" (to_string string_of_int h4);
  let h5 = delete_min h4 in
  Printf.printf "After delete_min: %s\n" (to_string string_of_int h5);
  Printf.printf "\nDone!\n"
