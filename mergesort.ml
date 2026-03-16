(* Merge sort on lists *)
(* Demonstrates: higher-order functions, tuple destructuring, recursion *)

(** [split lst] divides [lst] into two roughly equal halves by alternating
    elements. Returns [(left, right)] where [|left| - |right|] <= 1.
    Tail-recursive. *)
let split lst =
  let rec aux left right = function
    | [] -> (List.rev left, List.rev right)
    | [x] -> (List.rev (x :: left), List.rev right)
    | x :: y :: rest -> aux (x :: left) (y :: right) rest
  in
  aux [] [] lst

(** [merge cmp l1 l2] merges two sorted lists into a single sorted list
    using comparison function [cmp]. Tail-recursive to avoid stack overflow
    on large inputs. Stable: preserves relative order of equal elements. *)
let merge cmp l1 l2 =
  let rec aux acc l1 l2 =
    match l1, l2 with
    | [], l | l, [] -> List.rev_append acc l
    | h1 :: t1, h2 :: t2 ->
      if cmp h1 h2 <= 0 then aux (h1 :: acc) t1 l2
      else aux (h2 :: acc) l1 t2
  in
  aux [] l1 l2

(** [mergesort cmp lst] sorts [lst] using the merge sort algorithm with
    comparison function [cmp]. Stable sort with O(n log n) time complexity.
    Returns a new sorted list. *)
let rec mergesort cmp = function
  | ([] | [_]) as l -> l  (* base case: 0 or 1 elements *)
  | lst ->
    let (left, right) = split lst in
    merge cmp (mergesort cmp left) (mergesort cmp right)

(** [string_of_int_list lst] formats an integer list as a bracketed,
    semicolon-separated string. *)
let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

(* Example usage *)
let () =
  let data = [38; 27; 43; 3; 9; 82; 10] in
  Printf.printf "Original:    %s\n" (string_of_int_list data);
  Printf.printf "Sorted asc:  %s\n" (string_of_int_list (mergesort compare data));
  Printf.printf "Sorted desc: %s\n"
    (string_of_int_list (mergesort (fun a b -> compare b a) data));

  let words = ["banana"; "apple"; "cherry"; "date"] in
  Printf.printf "Words sorted: [%s]\n"
    (String.concat "; " (mergesort String.compare words))
