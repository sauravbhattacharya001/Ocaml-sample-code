(* test_memoize.ml — Tests for memoization combinators *)


#use "test_framework.ml";;

let assert_float ~msg ~eps expected actual =
  incr tests_run;
  if Float.abs (expected -. actual) < eps then (
    incr tests_passed;
    Printf.printf "  ✓ %s\n" msg
  ) else
    Printf.printf "  ✗ %s (expected %.4f, got %.4f)\n" msg expected actual

(* We inline the module for testing since OCaml doesn't have a module
   import path without dune/build. Copy key functions. *)

(* ── Basic memoize ── *)
let memoize f =
  let cache = Hashtbl.create 16 in
  fun x ->
    match Hashtbl.find_opt cache x with
    | Some y -> y
    | None -> let y = f x in Hashtbl.replace cache x y; y

(* ── Recursive memoize ── *)
let memoize_rec f =
  let cache = Hashtbl.create 16 in
  let rec go x =
    match Hashtbl.find_opt cache x with
    | Some y -> y
    | None -> let y = f go x in Hashtbl.replace cache x y; y
  in go

(* ── Memoize with stats ── *)
type stats = { mutable hits : int; mutable misses : int }

let memoize_stats f =
  let cache = Hashtbl.create 16 in
  let s = { hits = 0; misses = 0 } in
  let memo x =
    match Hashtbl.find_opt cache x with
    | Some y -> s.hits <- s.hits + 1; y
    | None -> s.misses <- s.misses + 1;
      let y = f x in Hashtbl.replace cache x y; y
  in (memo, s)

(* ── Two-arg memoize ── *)
let memoize2 f =
  let cache = Hashtbl.create 16 in
  fun a b ->
    let key = (a, b) in
    match Hashtbl.find_opt cache key with
    | Some y -> y
    | None -> let y = f a b in Hashtbl.replace cache key y; y

(* ── Clearable ── *)
let memoize_clearable f =
  let cache = Hashtbl.create 16 in
  let memo x =
    match Hashtbl.find_opt cache x with
    | Some y -> y
    | None -> let y = f x in Hashtbl.replace cache x y; y
  in
  let clear () = Hashtbl.clear cache in
  (memo, clear)

(* ═══════════════ Tests ═══════════════ *)

let test_basic_memoize () =
  Printf.printf "\n-- Basic memoize --\n";
  let call_count = ref 0 in
  let f = memoize (fun x -> incr call_count; x * x) in
  assert_equal ~msg:"first call computes" 25 (f 5);
  assert_equal ~msg:"call count after first" 1 !call_count;
  assert_equal ~msg:"second call cached" 25 (f 5);
  assert_equal ~msg:"call count unchanged" 1 !call_count;
  assert_equal ~msg:"different arg computes" 9 (f 3);
  assert_equal ~msg:"call count incremented" 2 !call_count

let test_recursive_memoize () =
  Printf.printf "\n-- Recursive memoize (fibonacci) --\n";
  let fib = memoize_rec (fun self n ->
    if n <= 1 then n else self (n-1) + self (n-2)) in
  assert_equal ~msg:"fib(0)=0" 0 (fib 0);
  assert_equal ~msg:"fib(1)=1" 1 (fib 1);
  assert_equal ~msg:"fib(5)=5" 5 (fib 5);
  assert_equal ~msg:"fib(10)=55" 55 (fib 10);
  assert_equal ~msg:"fib(20)=6765" 6765 (fib 20);
  (* Verify it can handle large n without stack overflow *)
  let _ = fib 50 in
  assert_true ~msg:"fib(50) computes without overflow" true

let test_stats () =
  Printf.printf "\n-- Stats memoize --\n";
  let (f, s) = memoize_stats (fun x -> x + 1) in
  ignore (f 1); ignore (f 2); ignore (f 1); ignore (f 3); ignore (f 1);
  assert_equal ~msg:"3 unique = 3 misses" 3 s.misses;
  assert_equal ~msg:"2 repeats = 2 hits" 2 s.hits;
  ignore (f 2); ignore (f 2);
  assert_equal ~msg:"4 hits after more repeats" 4 s.hits;
  assert_equal ~msg:"misses unchanged" 3 s.misses

let test_memoize2 () =
  Printf.printf "\n-- Two-arg memoize --\n";
  let call_count = ref 0 in
  let add = memoize2 (fun a b -> incr call_count; a + b) in
  assert_equal ~msg:"add(2,3)=5" 5 (add 2 3);
  assert_equal ~msg:"add(2,3) cached" 5 (add 2 3);
  assert_equal ~msg:"only 1 computation" 1 !call_count;
  assert_equal ~msg:"add(3,2)=5 (different key)" 5 (add 3 2);
  assert_equal ~msg:"2 computations" 2 !call_count

let test_clearable () =
  Printf.printf "\n-- Clearable memoize --\n";
  let call_count = ref 0 in
  let (f, clear) = memoize_clearable (fun x -> incr call_count; x * 2) in
  assert_equal ~msg:"first call" 10 (f 5);
  assert_equal ~msg:"cached call" 10 (f 5);
  assert_equal ~msg:"1 computation" 1 !call_count;
  clear ();
  assert_equal ~msg:"after clear, recomputes" 10 (f 5);
  assert_equal ~msg:"2 computations" 2 !call_count

let test_collatz () =
  Printf.printf "\n-- Collatz (recursive memoize) --\n";
  let collatz = memoize_rec (fun self n ->
    if n = 1 then 0
    else if n mod 2 = 0 then 1 + self (n / 2)
    else 1 + self (3 * n + 1)) in
  assert_equal ~msg:"collatz(1)=0" 0 (collatz 1);
  assert_equal ~msg:"collatz(2)=1" 1 (collatz 2);
  assert_equal ~msg:"collatz(7)=16" 16 (collatz 7);
  assert_equal ~msg:"collatz(27)=111" 111 (collatz 27)

let test_hit_rate () =
  Printf.printf "\n-- Hit rate --\n";
  let (f, s) = memoize_stats (fun x -> x) in
  let rate () =
    let total = s.hits + s.misses in
    if total = 0 then 0.0 else float s.hits /. float total
  in
  assert_float ~msg:"empty cache = 0%%" ~eps:0.001 0.0 (rate ());
  ignore (f 1); ignore (f 1); ignore (f 1);
  (* 1 miss + 2 hits = 66.7% *)
  assert_float ~msg:"2/3 hits = 66.7%%" ~eps:0.01 0.667 (rate ())

let () =
  Printf.printf "=== Memoization Tests ===\n";
  test_basic_memoize ();
  test_recursive_memoize ();
  test_stats ();
  test_memoize2 ();
  test_clearable ();
  test_collatz ();
  test_hit_rate ();
  test_summary ()
