(* Merge sort on lists *)
(* Demonstrates: higher-order functions, tuple destructuring, recursion *)

(* Split a list into two roughly equal halves *)
let rec split = function
  | [] -> ([], [])
  | [x] -> ([x], [])
  | x :: y :: rest ->
    let (left, right) = split rest in
    (x :: left, y :: right)

(* Merge two sorted lists into one sorted list *)
let rec merge cmp l1 l2 =
  match l1, l2 with
  | [], l | l, [] -> l
  | h1 :: t1, h2 :: t2 ->
    if cmp h1 h2 <= 0 then h1 :: merge cmp t1 l2
    else h2 :: merge cmp l1 t2

(* Merge sort: split, recurse, merge *)
let rec mergesort cmp = function
  | ([] | [_]) as l -> l  (* base case: 0 or 1 elements *)
  | lst ->
    let (left, right) = split lst in
    merge cmp (mergesort cmp left) (mergesort cmp right)

(* Pretty-print a list of integers *)
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
