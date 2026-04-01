(* Pairing Heap — Purely Functional Min-Heap *)
(* Demonstrates: algebraic data types, recursive data structures,
   amortised complexity analysis, persistent heaps, two-pass merging *)

(* A pairing heap is one of the simplest self-adjusting heap structures.
   Unlike leftist or binomial heaps it keeps almost no structural invariant —
   a node simply holds a value and a list of sub-heaps. Despite the simplicity,
   pairing heaps have excellent practical performance:

     insert      — O(1)
     find_min    — O(1)
     merge       — O(1)
     delete_min  — O(log n) amortised

   The key insight is that delete_min uses a two-pass pairing strategy:
   first pair adjacent siblings left-to-right, then merge the resulting
   heaps right-to-left. This gives the amortised O(log n) bound. *)

(* ────────────────────────────────────────────────────────── *)
(*  Core data type                                            *)
(* ────────────────────────────────────────────────────────── *)

type 'a heap =
  | Empty
  | Node of 'a * 'a heap list
(** A pairing heap is either [Empty] or a [Node(root, children)] where
    [root] is the minimum element and [children] is a list of sub-heaps
    whose roots are all >= [root]. *)

(* ────────────────────────────────────────────────────────── *)
(*  Functor for custom ordering                               *)
(* ────────────────────────────────────────────────────────── *)

module type ORDERED = sig
  type t
  val compare : t -> t -> int
end

module Make (Ord : ORDERED) : sig
  type t

  val empty      : t
  val is_empty   : t -> bool
  val insert     : Ord.t -> t -> t
  val find_min   : t -> Ord.t option
  val find_min_exn : t -> Ord.t
  val delete_min : t -> t
  val merge      : t -> t -> t
  val of_list    : Ord.t list -> t
  val to_sorted_list : t -> Ord.t list
  val size       : t -> int
  val fold       : ('a -> Ord.t -> 'a) -> 'a -> t -> 'a
end = struct
  type t = Ord.t heap

  let empty = Empty

  let is_empty = function Empty -> true | _ -> false

  (** Merge two heaps in O(1) by comparing roots. *)
  let merge h1 h2 =
    match h1, h2 with
    | Empty, h | h, Empty -> h
    | Node (x, xs), Node (y, ys) ->
      if Ord.compare x y <= 0
      then Node (x, h2 :: xs)
      else Node (y, h1 :: ys)

  let insert x h = merge (Node (x, [])) h

  let find_min = function
    | Empty -> None
    | Node (x, _) -> Some x

  let find_min_exn = function
    | Empty -> failwith "PairingHeap.find_min_exn: empty heap"
    | Node (x, _) -> x

  (** Two-pass pairing: pair adjacent siblings, then merge right-to-left. *)
  let rec merge_pairs = function
    | [] -> Empty
    | [h] -> h
    | h1 :: h2 :: rest -> merge (merge h1 h2) (merge_pairs rest)

  let delete_min = function
    | Empty -> Empty
    | Node (_, children) -> merge_pairs children

  let of_list xs = List.fold_left (fun h x -> insert x h) empty xs

  let to_sorted_list h =
    let rec aux acc = function
      | Empty -> List.rev acc
      | h ->
        let x = find_min_exn h in
        aux (x :: acc) (delete_min h)
    in
    aux [] h

  let rec size = function
    | Empty -> 0
    | Node (_, children) ->
      1 + List.fold_left (fun acc c -> acc + size c) 0 children

  let fold f init h =
    let rec aux acc = function
      | Empty -> acc
      | h ->
        let x = find_min_exn h in
        aux (f acc x) (delete_min h)
    in
    aux init h
end

(* ────────────────────────────────────────────────────────── *)
(*  Default: integer pairing heap                             *)
(* ────────────────────────────────────────────────────────── *)

module IntHeap = Make (struct
  type t = int
  let compare = compare
end)

(* ────────────────────────────────────────────────────────── *)
(*  Demo / interactive runner                                 *)
(* ────────────────────────────────────────────────────────── *)

let () =
  print_endline "=== Pairing Heap Demo ===\n";

  (* Build a heap from a shuffled list *)
  let values = [42; 17; 3; 99; 1; 28; 55; 8; 12; 71] in
  Printf.printf "Inserting: %s\n"
    (String.concat ", " (List.map string_of_int values));

  let h = IntHeap.of_list values in
  Printf.printf "Heap size: %d\n" (IntHeap.size h);

  (match IntHeap.find_min h with
   | Some x -> Printf.printf "Minimum: %d\n" x
   | None -> print_endline "Heap is empty");

  (* Extract all elements in sorted order *)
  let sorted = IntHeap.to_sorted_list h in
  Printf.printf "Sorted extraction: %s\n"
    (String.concat ", " (List.map string_of_int sorted));

  (* Demonstrate merge *)
  print_endline "\n--- Merge Demo ---";
  let h1 = IntHeap.of_list [10; 20; 30] in
  let h2 = IntHeap.of_list [5; 15; 25] in
  let merged = IntHeap.merge h1 h2 in
  Printf.printf "Merged heap sorted: %s\n"
    (String.concat ", " (List.map string_of_int (IntHeap.to_sorted_list merged)));

  (* Demonstrate persistence — original heaps unchanged *)
  print_endline "\n--- Persistence Demo ---";
  Printf.printf "h1 min after merge: %d (unchanged)\n" (IntHeap.find_min_exn h1);
  Printf.printf "h2 min after merge: %d (unchanged)\n" (IntHeap.find_min_exn h2);

  (* Demonstrate fold — sum all elements *)
  let total = IntHeap.fold ( + ) 0 h in
  Printf.printf "\nSum via fold: %d\n" total;

  (* Demonstrate delete_min sequence *)
  print_endline "\n--- Sequential Delete-Min ---";
  let rec drain h =
    if IntHeap.is_empty h then print_endline "(empty)"
    else begin
      Printf.printf "%d " (IntHeap.find_min_exn h);
      drain (IntHeap.delete_min h)
    end
  in
  drain (IntHeap.of_list [7; 2; 9; 4; 1; 6]);
  print_newline ()
