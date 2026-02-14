(* Fibonacci with memoization using a hash table *)
(* Demonstrates: Hash tables, closures, imperative features in OCaml,
   comparison of naive vs memoized approaches *)

(* Naive recursive Fibonacci — exponential time O(2^n) *)
let rec fib_naive = function
  | 0 -> 0
  | 1 -> 1
  | n -> fib_naive (n - 1) + fib_naive (n - 2)

(* Memoized Fibonacci using a closure over a hash table — O(n) time *)
let fib_memo =
  let cache = Hashtbl.create 64 in
  let rec fib n =
    match Hashtbl.find_opt cache n with
    | Some v -> v
    | None ->
      let v = match n with
        | 0 -> 0
        | 1 -> 1
        | _ -> fib (n - 1) + fib (n - 2)
      in
      Hashtbl.replace cache n v;
      v
  in
  fib

(* Tail-recursive iterative Fibonacci — O(n) time, O(1) space *)
let fib_iter n =
  if n <= 0 then 0
  else
    let rec aux a b i =
      if i = n then b
      else aux b (a + b) (i + 1)
    in
    aux 0 1 1

(* Generate first n Fibonacci numbers as a list *)
let fib_sequence n =
  List.init n fib_iter

(* Timing helper — returns (result, elapsed_seconds) *)
let time f x =
  let t0 = Sys.time () in
  let result = f x in
  let t1 = Sys.time () in
  (result, t1 -. t0)

(* Pretty-print a list of integers *)
let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

let () =
  (* Show the first 15 Fibonacci numbers *)
  Printf.printf "First 15 Fibonacci numbers:\n  %s\n\n"
    (string_of_int_list (fib_sequence 15));

  (* Compare performance: naive vs memoized for fib(35) *)
  let n = 35 in
  let (r1, t1) = time fib_naive n in
  Printf.printf "fib_naive(%d) = %d  (%.4fs)\n" n r1 t1;

  let (r2, t2) = time fib_memo n in
  Printf.printf "fib_memo(%d)  = %d  (%.6fs)\n" n r2 t2;

  let (r3, t3) = time fib_iter n in
  Printf.printf "fib_iter(%d)  = %d  (%.6fs)\n" n r3 t3;

  Printf.printf "\nSpeedup (memo vs naive): %.0fx\n"
    (if t2 > 0.0 then t1 /. t2 else infinity);

  (* Large value only possible with efficient implementations *)
  Printf.printf "fib_iter(50) = %d\n" (fib_iter 50)
