(* Find the last element of a list using pattern matching *)
(* Demonstrates: option types, pattern matching, recursion *)

let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t;;

(* Example usage *)
let () =
  let print_result name = function
    | None -> Printf.printf "last %s = None\n" name
    | Some x -> Printf.printf "last %s = Some %d\n" name x
  in
  print_result "[1; 2; 3]" (last [1; 2; 3]);
  print_result "[42]" (last [42]);
  print_result "[]" (last []);;
