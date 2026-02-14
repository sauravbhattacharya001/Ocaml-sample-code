(* Prime factorization using recursive trial division *)
(* Demonstrates: recursion, pattern matching, input validation *)

(* Recall that d divides n iff [n mod d = 0] *)
let factors n =
  if n < 2 then invalid_arg "factors: input must be >= 2"
  else
    let rec aux d n =
      if n = 1 then []
      else if d * d > n then [n]  (* n is prime; no divisor up to sqrt(n) *)
      else if n mod d = 0 then d :: aux d (n / d)
      else aux (d + 1) n
    in
    aux 2 n;;

(* Pretty-print a list of integers *)
let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]";;

(* Example usage *)
let () =
  let test_values = [2; 12; 30; 97; 360] in
  List.iter (fun n ->
    Printf.printf "factors %d = %s\n" n (string_of_int_list (factors n))
  ) test_values;;
