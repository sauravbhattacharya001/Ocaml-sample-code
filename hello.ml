(* Basic OCaml — variables, types, string formatting, and expressions *)
(* Demonstrates: let bindings, type inference, Printf, string operations *)

(* OCaml infers types — no annotations needed *)
let greeting = "Hello"
let name = "OCaml"
let version = 5

(* String concatenation and formatting *)
let full_greeting = greeting ^ ", " ^ name ^ "!"

(* Let expressions: local bindings scoped to an expression *)
let area_of_circle r =
  let pi = Float.pi in
  pi *. r *. r

(* Pattern matching on tuples — multiple return values *)
let min_max lst =
  match lst with
  | [] -> None
  | x :: rest ->
    let rec aux lo hi = function
      | [] -> (lo, hi)
      | x :: xs -> aux (min lo x) (max hi x) xs
    in
    Some (aux x x rest)

(* Pipe operator for readable data pipelines *)
let result =
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
  |> List.filter (fun x -> x mod 2 = 0)
  |> List.map (fun x -> x * x)
  |> List.fold_left (+) 0

let () =
  Printf.printf "%s\n" full_greeting;
  Printf.printf "%s version %d\n" name version;
  Printf.printf "Area of circle (r=3.0): %.4f\n" (area_of_circle 3.0);
  Printf.printf "Sum of squares of evens 1..10: %d\n" result;
  match min_max [7; 2; 9; 1; 5; 8; 3] with
  | None -> print_endline "Empty list"
  | Some (lo, hi) -> Printf.printf "Min: %d, Max: %d\n" lo hi
