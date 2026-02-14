(* Prime factorization using recursive trial division *)
(* Demonstrates: recursion, pattern matching, input validation *)

(* Optimized: after extracting all factors of 2, only check odd divisors.
   This nearly halves the number of trial divisions for large inputs. *)
let factors n =
  if n < 2 then invalid_arg "factors: input must be >= 2"
  else
    let rec extract_twos n =
      if n mod 2 = 0 then 2 :: extract_twos (n / 2)
      else odd_factors 3 n
    and odd_factors d n =
      if n = 1 then []
      else if d * d > n then [n]  (* n is prime; no divisor up to sqrt(n) *)
      else if n mod d = 0 then d :: odd_factors d (n / d)
      else odd_factors (d + 2) n  (* skip even candidates *)
    in
    extract_twos n

(* Pretty-print a list of integers *)
let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

(* Example usage *)
let () =
  let test_values = [2; 12; 30; 97; 360] in
  List.iter (fun n ->
    Printf.printf "factors %d = %s\n" n (string_of_int_list (factors n))
  ) test_values
