(* Prime factorization using recursive trial division *)
(* Demonstrates: recursion, pattern matching, input validation *)

(** [factors n] returns the prime factorization of [n] as a list of prime
    factors in non-decreasing order.
    @param n integer >= 2
    @raise Invalid_argument if [n < 2]

    Optimized: after extracting all factors of 2, only checks odd divisors.
    This nearly halves the number of trial divisions for large inputs.
    Complexity: O(sqrt(n)) trial divisions in the worst case. *)
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

(** [string_of_int_list lst] formats an integer list as a bracketed,
    semicolon-separated string, e.g. ["[2; 3; 5]"]. *)
let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

(* Example usage *)
let () =
  let test_values = [2; 12; 30; 97; 360] in
  List.iter (fun n ->
    Printf.printf "factors %d = %s\n" n (string_of_int_list (factors n))
  ) test_values
