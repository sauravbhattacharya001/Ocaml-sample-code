(* delimited_cont.ml — Delimited Continuations (shift/reset)
 *
 * Demonstrates one of the most powerful control-flow abstractions in
 * functional programming: delimited continuations with shift and reset.
 *
 * Unlike regular continuations (call/cc) which capture the *entire* rest of
 * the computation, delimited continuations capture only up to a *delimiter*
 * (the nearest enclosing reset). This makes them composable and practical.
 *
 * Concepts demonstrated:
 *   - CPS (Continuation-Passing Style) transformation
 *   - Delimited continuations via shift/reset
 *   - Non-deterministic choice (amb operator)
 *   - Coroutines / cooperative threading
 *   - Exception handling as a continuation pattern
 *   - State as a continuation pattern
 *   - Generators / iterators via yield
 *   - Backtracking search
 *
 * Each section builds on the previous, showing how a single mechanism
 * (delimited continuations) can express many different control patterns.
 *
 * References:
 *   - Filinski, "Representing Monads" (1994)
 *   - Danvy & Filinski, "Abstracting Control" (1990)
 *   - Kiselyov, "Delimited Control in OCaml, Abstractly and Concretely" (2010)
 *)

(* ══════════════════════════════════════════════════════════════════════════
   1. CPS TRANSFORMATION — The Foundation
   ══════════════════════════════════════════════════════════════════════════

   Before diving into delimited continuations, we need to understand CPS.
   In CPS, every function takes an extra argument: its continuation, which
   represents "what to do next" with the result.

   Direct style:  let x = f a in g x
   CPS:           f_cps a (fun x -> g_cps x k)  *)

module CPS = struct
  (* A CPS-transformed identity function *)
  let id_cps x k = k x

  (* CPS addition *)
  let add_cps a b k = k (a + b)

  (* CPS multiplication *)
  let mul_cps a b k = k (a * b)

  (* CPS factorial — notice how recursion becomes tail-recursive in CPS! *)
  let rec factorial_cps n k =
    if n <= 1 then k 1
    else factorial_cps (n - 1) (fun r -> k (n * r))

  (* CPS fibonacci *)
  let rec fibonacci_cps n k =
    if n <= 1 then k n
    else fibonacci_cps (n - 1) (fun a ->
         fibonacci_cps (n - 2) (fun b ->
         k (a + b)))

  (* CPS map over a list *)
  let rec map_cps f lst k =
    match lst with
    | [] -> k []
    | x :: xs -> f x (fun y -> map_cps f xs (fun ys -> k (y :: ys)))

  (* CPS fold *)
  let rec fold_cps f acc lst k =
    match lst with
    | [] -> k acc
    | x :: xs -> f acc x (fun acc' -> fold_cps f acc' xs k)

  (* Run a CPS computation by passing the identity continuation *)
  let run f = f (fun x -> x)

  (* Demo *)
  let demo () =
    Printf.printf "=== CPS Transformation ===\n";
    Printf.printf "id 42 = %d\n" (run (id_cps 42));
    Printf.printf "3 + 4 = %d\n" (run (add_cps 3 4));
    Printf.printf "3 * 4 = %d\n" (run (mul_cps 3 4));
    Printf.printf "5! = %d\n" (run (factorial_cps 5));
    Printf.printf "fib(10) = %d\n" (run (fibonacci_cps 10));
    let double x k = k (x * 2) in
    run (map_cps double [1;2;3;4;5]) |> List.iter (Printf.printf " %d");
    Printf.printf "\n";
    let add_cps2 a b k = k (a + b) in
    Printf.printf "sum [1..5] = %d\n"
      (run (fold_cps add_cps2 0 [1;2;3;4;5]));
    Printf.printf "\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   2. DELIMITED CONTINUATIONS — shift/reset
   ══════════════════════════════════════════════════════════════════════════

   The key insight: `reset` sets a delimiter (a boundary), and `shift`
   captures the continuation up to that delimiter.

   reset (fun () -> 1 + shift (fun k -> k 10))
   => 1 + 10 = 11

   Here, `shift` captures `fun x -> 1 + x` (the context up to reset)
   and passes it as `k`. We call `k 10`, so the result is `1 + 10 = 11`.

   The power comes from the fact that `k` is a regular function — you can
   call it zero, one, or multiple times! *)

module Delimited = struct
  (* ── Practical shift/reset via CPS ── *)

  (* This is the standard, correct implementation.
     We implement shift/reset using a CPS-based encoding.
     This avoids mutable state while being fully composable. *)

  (* A computation in CPS *)
  type 'a cps = ('a -> int) -> int

  (* return/pure: inject a value into CPS *)
  let pure (x : 'a) : 'a cps = fun k -> k x

  (* bind: sequence two CPS computations *)
  let bind (m : 'a cps) (f : 'a -> 'b cps) : 'b cps =
    fun k -> m (fun a -> f a k)

  (* reset: run a CPS computation with the identity continuation.
     This establishes the delimiter — shift will capture up to here. *)
  let reset (m : int cps) : int cps =
    fun k -> k (m (fun x -> x))

  (* shift: capture the current continuation up to reset.
     The captured continuation is passed to the handler as a function. *)
  let shift (f : (int -> int cps) -> int cps) : int cps =
    fun k ->
      let captured v = pure (k v) in
      f captured (fun x -> x)

  (* run: extract the final value *)
  let run (m : int cps) : int = m (fun x -> x)

  let ( let* ) = bind

  (* Demo *)
  let demo () =
    Printf.printf "=== Delimited Continuations (shift/reset) ===\n";

    (* Example 1: Simple shift/reset *)
    (* reset (1 + shift (fun k -> k 10)) = 11 *)
    let ex1 = run (reset (
      let* v = shift (fun k -> k 10) in
      pure (1 + v)
    )) in
    Printf.printf "reset (1 + shift (k -> k 10)) = %d\n" ex1;

    (* Example 2: Calling continuation twice *)
    (* reset (1 + shift (fun k -> k 10 + k 20)) = 11 + 21 = 32 *)
    let ex2 = run (reset (
      let* v = shift (fun k ->
        let* a = k 10 in
        let* b = k 20 in
        pure (a + b)
      ) in
      pure (1 + v)
    )) in
    Printf.printf "reset (1 + shift (k -> k 10 + k 20)) = %d\n" ex2;

    (* Example 3: Discarding the continuation *)
    (* reset (1 + shift (fun _k -> pure 42)) = 42 *)
    let ex3 = run (reset (
      let* _ = shift (fun _k -> pure 42) in
      pure 999  (* never reached *)
    )) in
    Printf.printf "reset (1 + shift (_ -> 42)) = %d\n" ex3;

    (* Example 4: Nested arithmetic *)
    (* reset (2 * (1 + shift (fun k -> k 3))) = 2 * (1 + 3) = 8 *)
    let ex4 = run (reset (
      let* v = shift (fun k -> k 3) in
      pure (2 * (1 + v))
    )) in
    Printf.printf "reset (2 * (1 + shift (k -> k 3))) = %d\n" ex4;

    Printf.printf "\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   3. NON-DETERMINISM — The amb Operator
   ══════════════════════════════════════════════════════════════════════════

   One of the most elegant applications of delimited continuations:
   implementing non-deterministic choice (the "amb" operator from Scheme).

   amb [1; 2; 3] returns each value in turn by capturing and replaying
   the continuation for each alternative. *)

module NonDet = struct
  (* We collect all results using shift/reset *)

  (* A non-deterministic computation *)
  type 'a nd = ('a -> int list) -> int list

  let pure x : int nd = fun k -> k x

  let bind (m : int nd) (f : int -> int nd) : int nd =
    fun k -> m (fun a -> f a k)

  (* amb: non-deterministic choice from a list *)
  let amb (choices : int list) : int nd =
    fun k ->
      List.concat_map k choices

  (* fail: no valid choice *)
  let fail : int nd = fun _k -> []

  (* guard: filter based on a condition *)
  let guard (cond : bool) : int nd =
    if cond then pure 0  (* dummy value, like unit *)
    else fail

  (* run: collect all results *)
  let run (m : int nd) : int list = m (fun x -> [x])

  let ( let* ) = bind

  (* Demo: find all Pythagorean triples up to n *)
  let pythagorean_triples n =
    run (
      let* a = amb (List.init n (fun i -> i + 1)) in
      let* b = amb (List.init (n - a + 1) (fun i -> i + a)) in
      let* c = amb (List.init (n - b + 1) (fun i -> i + b)) in
      let* _ = guard (a * a + b * b = c * c) in
      pure (a * 1000000 + b * 1000 + c)  (* encode triple as single int *)
    )

  (* Demo: solve SEND + MORE = MONEY *)
  let send_more_money () =
    let digits = List.init 10 (fun i -> i) in
    let remove d ds = List.filter (fun x -> x <> d) ds in
    run (
      let* s = amb (List.filter (fun d -> d > 0) digits) in
      let* e = amb (remove s digits) in
      let* n = amb (remove e (remove s digits)) in
      let* d = amb (remove n (remove e (remove s digits))) in
      let send = s * 1000 + e * 100 + n * 10 + d in
      let remaining = remove d (remove n (remove e (remove s digits))) in
      let* m = amb (List.filter (fun d -> d > 0) remaining) in
      let remaining2 = remove m remaining in
      let* o = amb remaining2 in
      let* r = amb (remove o remaining2) in
      let* y = amb (remove r (remove o remaining2)) in
      let more = m * 1000 + o * 100 + r * 10 + e in
      let money = m * 10000 + o * 1000 + n * 100 + e * 10 + y in
      let* _ = guard (send + more = money) in
      pure (send * 100000 + more)
    )

  let demo () =
    Printf.printf "=== Non-Determinism (amb) ===\n";
    let triples = pythagorean_triples 20 in
    Printf.printf "Pythagorean triples up to 20:\n";
    List.iter (fun encoded ->
      let a = encoded / 1000000 in
      let b = (encoded / 1000) mod 1000 in
      let c = encoded mod 1000 in
      Printf.printf "  (%d, %d, %d)\n" a b c
    ) triples;

    Printf.printf "\nSEND + MORE = MONEY solutions:\n";
    let solutions = send_more_money () in
    List.iter (fun encoded ->
      let send = encoded / 100000 in
      let more = encoded mod 100000 in
      Printf.printf "  %d + %d = %d\n" send more (send + more)
    ) solutions;
    Printf.printf "\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   4. COROUTINES — Cooperative Multitasking
   ══════════════════════════════════════════════════════════════════════════

   Delimited continuations give us coroutines for free.
   A coroutine can yield a value, suspending its execution.
   The scheduler resumes coroutines round-robin. *)

module Coroutine = struct
  (* A coroutine is either done or yielding a value with a resumption *)
  type 'a status =
    | Done of 'a
    | Yielded of int * (unit -> 'a status)

  (* A coroutine computation *)
  type 'a co = ('a -> 'a status) -> 'a status

  let pure x : 'a co = fun k -> k x

  let bind (m : 'a co) (f : 'a -> 'b co) : 'b co =
    fun k -> m (fun a -> f a k)

  let ( let* ) = bind

  (* yield: suspend the coroutine, producing a value *)
  let yield_ (v : int) : unit co =
    fun k -> Yielded (v, fun () -> k ())

  (* run a coroutine to completion *)
  let run_one (m : 'a co) : 'a status = m (fun x -> Done x)

  (* Round-robin scheduler *)
  let schedule (coroutines : (unit -> int status) list) : int list =
    let results = ref [] in
    let queue = Queue.create () in
    List.iter (fun c -> Queue.push c queue) coroutines;
    while not (Queue.is_empty queue) do
      let co = Queue.pop queue in
      match co () with
      | Done v -> results := v :: !results
      | Yielded (v, resume) ->
        results := v :: !results;
        Queue.push resume queue
    done;
    List.rev !results

  (* Demo *)
  let demo () =
    Printf.printf "=== Coroutines ===\n";

    (* Two coroutines that interleave *)
    let counter name start stop : unit co =
      let rec loop i : unit co =
        if i > stop then pure ()
        else
          let* () = yield_ (i + (Char.code name.[0] * 1000)) in
          loop (i + 1)
      in
      loop start
    in

    let co1 () = run_one (counter "A" 1 5) in
    let co2 () = run_one (counter "B" 10 13) in

    let results = schedule [co1; co2] in
    Printf.printf "Interleaved output:\n";
    List.iter (fun v ->
      let tag = v / 1000 in
      let value = v mod 1000 in
      Printf.printf "  [%c] %d\n" (Char.chr tag) value
    ) results;
    Printf.printf "\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   5. EXCEPTIONS — As Continuations
   ══════════════════════════════════════════════════════════════════════════

   Exception handling is just delimited continuations where we discard
   the continuation on failure. This shows the unifying power of
   delimited continuations. *)

module ExnCont = struct
  (* A computation that might fail *)
  type 'a result = Ok of 'a | Error of string

  type 'a comp = ('a -> int result) -> int result

  let pure x : 'a comp = fun k -> k x

  let bind (m : 'a comp) (f : 'a -> 'b comp) : 'b comp =
    fun k -> m (fun a -> f a k)

  let ( let* ) = bind

  (* throw: discard the continuation and return an error *)
  let throw msg : 'a comp = fun _k -> Error msg

  (* catch: establish a handler *)
  let catch (m : int comp) (handler : string -> int comp) : int comp =
    fun k ->
      match m k with
      | Ok v -> Ok v
      | Error msg -> handler msg k

  (* run *)
  let run (m : int comp) : int result = m (fun x -> Ok x)

  (* Demo *)
  let demo () =
    Printf.printf "=== Exceptions as Continuations ===\n";

    (* Safe division *)
    let safe_div a b : int comp =
      if b = 0 then throw "division by zero"
      else pure (a / b)
    in

    (* Success case *)
    let r1 = run (
      let* x = safe_div 10 2 in
      let* y = safe_div x 1 in
      pure (x + y)
    ) in
    (match r1 with
     | Ok v -> Printf.printf "10/2 + 5/1 = %d\n" v
     | Error e -> Printf.printf "Error: %s\n" e);

    (* Failure case *)
    let r2 = run (
      let* x = safe_div 10 0 in
      pure (x + 1)
    ) in
    (match r2 with
     | Ok v -> Printf.printf "10/0 + 1 = %d\n" v
     | Error e -> Printf.printf "Error: %s\n" e);

    (* Caught failure *)
    let r3 = run (catch
      (let* x = safe_div 10 0 in pure (x + 1))
      (fun _msg -> pure (-1))
    ) in
    (match r3 with
     | Ok v -> Printf.printf "catch (10/0 + 1) = %d\n" v
     | Error e -> Printf.printf "Error: %s\n" e);

    Printf.printf "\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   6. STATE — As Continuations
   ══════════════════════════════════════════════════════════════════════════

   Mutable state can also be expressed using continuations.
   get captures the current state, put replaces it. *)

module StateCont = struct
  (* State monad via CPS *)
  type 'a state_m = int -> ('a * int)

  let pure x : 'a state_m = fun s -> (x, s)

  let bind (m : 'a state_m) (f : 'a -> 'b state_m) : 'b state_m =
    fun s ->
      let (a, s') = m s in
      f a s'

  let ( let* ) = bind

  let get : int state_m = fun s -> (s, s)

  let put (new_state : int) : unit state_m = fun _s -> ((), new_state)

  let modify (f : int -> int) : unit state_m =
    fun s -> ((), f s)

  let run (init : int) (m : 'a state_m) : 'a * int = m init

  (* Demo *)
  let demo () =
    Printf.printf "=== State as Continuations ===\n";

    (* Counter *)
    let counter =
      let* () = modify (fun s -> s + 1) in
      let* () = modify (fun s -> s + 1) in
      let* () = modify (fun s -> s * 10) in
      let* v = get in
      pure v
    in
    let (result, final_state) = run 0 counter in
    Printf.printf "counter: value=%d, state=%d\n" result final_state;

    (* Fibonacci via state *)
    let fib_state n =
      let rec loop i =
        if i >= n then
          let* s = get in
          pure s
        else
          let* s = get in
          (* state encodes (a, b) as a * 10000 + b *)
          let a = s / 10000 in
          let b = s mod 10000 in
          let* () = put (b * 10000 + (a + b)) in
          loop (i + 1)
      in
      loop 0
    in
    for n = 0 to 10 do
      let (result, _) = run (0 * 10000 + 1) (fib_state n) in
      let fib_val = result / 10000 in
      Printf.printf "fib(%d) = %d  " n fib_val
    done;
    Printf.printf "\n\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   7. GENERATORS — yield-based Iteration
   ══════════════════════════════════════════════════════════════════════════

   Generators produce values lazily, one at a time. *)

module Generator = struct
  (* A generator is a stream of values *)
  type 'a gen =
    | Nil
    | Cons of 'a * (unit -> 'a gen)

  (* yield from a list *)
  let of_list lst =
    let rec go = function
      | [] -> Nil
      | x :: xs -> Cons (x, fun () -> go xs)
    in go lst

  (* Natural numbers *)
  let naturals () =
    let rec go n = Cons (n, fun () -> go (n + 1)) in
    go 0

  (* Take first n elements *)
  let rec take n gen =
    if n <= 0 then []
    else match gen with
      | Nil -> []
      | Cons (x, next) -> x :: take (n - 1) (next ())

  (* Map over a generator *)
  let rec map f gen =
    match gen with
    | Nil -> Nil
    | Cons (x, next) -> Cons (f x, fun () -> map f (next ()))

  (* Filter *)
  let rec filter pred gen =
    match gen with
    | Nil -> Nil
    | Cons (x, next) ->
      if pred x then Cons (x, fun () -> filter pred (next ()))
      else filter pred (next ())

  (* Zip two generators *)
  let rec zip g1 g2 =
    match g1, g2 with
    | Cons (a, next1), Cons (b, next2) ->
      Cons ((a, b), fun () -> zip (next1 ()) (next2 ()))
    | _ -> Nil

  (* Scan (running fold) *)
  let rec scan f acc gen =
    match gen with
    | Nil -> Cons (acc, fun () -> Nil)
    | Cons (x, next) ->
      let acc' = f acc x in
      Cons (acc, fun () -> scan f acc' (next ()))

  (* Flatten: generator of generators -> generator *)
  let rec flatten gen =
    match gen with
    | Nil -> Nil
    | Cons (inner, next_outer) ->
      append_gen inner (fun () -> flatten (next_outer ()))

  and append_gen g1 g2_thunk =
    match g1 with
    | Nil -> g2_thunk ()
    | Cons (x, next) -> Cons (x, fun () -> append_gen (next ()) g2_thunk)

  (* Sieve of Eratosthenes — infinite stream of primes *)
  let primes () =
    let rec sieve gen =
      match gen with
      | Nil -> Nil
      | Cons (p, next) ->
        Cons (p, fun () ->
          sieve (filter (fun n -> n mod p <> 0) (next ())))
    in
    sieve (let rec from n = Cons (n, fun () -> from (n + 1)) in from 2)

  (* Demo *)
  let demo () =
    Printf.printf "=== Generators ===\n";

    (* Basic generator *)
    let g = of_list [1; 2; 3; 4; 5] in
    Printf.printf "from list: %s\n"
      (String.concat " " (List.map string_of_int (take 5 g)));

    (* Naturals *)
    Printf.printf "naturals: %s\n"
      (String.concat " " (List.map string_of_int (take 10 (naturals ()))));

    (* Map + filter *)
    let squares = map (fun x -> x * x) (naturals ()) in
    let even_squares = filter (fun x -> x mod 2 = 0) squares in
    Printf.printf "even squares: %s\n"
      (String.concat " " (List.map string_of_int (take 8 even_squares)));

    (* Primes *)
    let p = primes () in
    Printf.printf "primes: %s\n"
      (String.concat " " (List.map string_of_int (take 20 p)));

    (* Running sum *)
    let nums = of_list [1; 2; 3; 4; 5] in
    let running = scan ( + ) 0 nums in
    Printf.printf "running sum: %s\n"
      (String.concat " " (List.map string_of_int (take 6 running)));

    (* Zip *)
    let pairs = zip (of_list [1;2;3]) (of_list [10;20;30]) in
    Printf.printf "zip: %s\n"
      (String.concat " "
        (List.map (fun (a,b) -> Printf.sprintf "(%d,%d)" a b)
          (take 3 pairs)));

    Printf.printf "\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   8. BACKTRACKING SEARCH — Logic Programming Lite
   ══════════════════════════════════════════════════════════════════════════

   Combining non-determinism with failure gives us backtracking search.
   This is essentially a mini Prolog implemented via continuations. *)

module Backtrack = struct
  (* A search computation produces a list of solutions *)
  type 'a search = ('a -> int list) -> int list

  let pure x : 'a search = fun k -> k x
  let bind (m : 'a search) (f : 'a -> 'b search) : 'b search =
    fun k -> m (fun a -> f a k)
  let ( let* ) = bind

  let choose (options : int list) : int search =
    fun k -> List.concat_map k options

  let fail : int search = fun _k -> []

  let guard cond : unit search =
    if cond then pure () else fail

  (* Cut: take only the first solution *)
  let cut (m : int search) : int search =
    fun k ->
      match m k with
      | [] -> []
      | x :: _ -> [x]

  (* Interleave: fair enumeration of two searches *)
  let interleave (m1 : int search) (m2 : int search) : int search =
    fun k ->
      let r1 = m1 k and r2 = m2 k in
      let rec weave l1 l2 = match l1, l2 with
        | [], ys -> ys
        | xs, [] -> xs
        | x :: xs, y :: ys -> x :: y :: weave xs ys
      in
      weave r1 r2

  let run (m : int search) : int list = m (fun x -> [x])

  (* Demo: N-Queens *)
  let n_queens n =
    let safe queens col row =
      let rec check qs r = match qs with
        | [] -> true
        | q :: rest ->
          q <> col &&
          abs (q - col) <> abs (r - row) &&
          check rest (r + 1)
      in
      check queens 1
    in
    let rec place row queens =
      if row > n then
        (* Encode the solution as a single integer: each digit is a column *)
        let encoded = List.fold_left (fun acc q -> acc * 10 + q) 0 queens in
        pure encoded
      else
        let* col = choose (List.init n (fun i -> i + 1)) in
        let* () = guard (safe (List.rev queens) col row) in
        place (row + 1) (queens @ [col])
    in
    run (place 1 [])

  (* Demo *)
  let demo () =
    Printf.printf "=== Backtracking Search ===\n";

    (* N-Queens *)
    let solutions_4 = n_queens 4 in
    Printf.printf "4-Queens solutions: %d found\n" (List.length solutions_4);
    List.iter (fun s ->
      let rec decode n acc =
        if n = 0 then acc
        else decode (n / 10) ((n mod 10) :: acc)
      in
      let queens = decode s [] in
      Printf.printf "  [%s]\n"
        (String.concat "," (List.map string_of_int queens))
    ) solutions_4;

    let solutions_8 = n_queens 8 in
    Printf.printf "8-Queens solutions: %d found\n" (List.length solutions_8);

    (* Map coloring *)
    let colors = [1; 2; 3] in  (* 1=Red, 2=Green, 3=Blue *)
    let color_name = function
      | 1 -> "Red" | 2 -> "Green" | 3 -> "Blue" | _ -> "?"
    in
    let map_coloring = run (
      (* Color Australian states *)
      let* wa  = choose colors in
      let* nt  = choose colors in
      let* () = guard (wa <> nt) in
      let* sa  = choose colors in
      let* () = guard (sa <> wa) in
      let* () = guard (sa <> nt) in
      let* q   = choose colors in
      let* () = guard (q <> nt) in
      let* () = guard (q <> sa) in
      let* nsw = choose colors in
      let* () = guard (nsw <> q) in
      let* () = guard (nsw <> sa) in
      let* v   = choose colors in
      let* () = guard (v <> nsw) in
      let* () = guard (v <> sa) in
      (* Encode: wa*100000 + nt*10000 + sa*1000 + q*100 + nsw*10 + v *)
      pure (wa * 100000 + nt * 10000 + sa * 1000 + q * 100 + nsw * 10 + v)
    ) in
    Printf.printf "\nAustralia map coloring (%d solutions):\n"
      (List.length map_coloring);
    (match map_coloring with
     | first :: _ ->
       let wa = first / 100000 in
       let nt = (first / 10000) mod 10 in
       let sa = (first / 1000) mod 10 in
       let q  = (first / 100) mod 10 in
       let nsw = (first / 10) mod 10 in
       let v  = first mod 10 in
       Printf.printf "  WA=%s NT=%s SA=%s Q=%s NSW=%s V=%s\n"
         (color_name wa) (color_name nt) (color_name sa)
         (color_name q) (color_name nsw) (color_name v)
     | [] -> Printf.printf "  No solution!\n");

    Printf.printf "\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   9. CONTINUATION MONAD TRANSFORMER — Composing with Other Effects
   ══════════════════════════════════════════════════════════════════════════

   The continuation monad transformer (ContT) lets you add continuation
   powers to any existing monad. *)

module ContT = struct
  (* ContT r m a = (a -> m r) -> m r *)
  (* Specialized for m = identity, r = int *)

  type 'a cont_t = ('a -> int) -> int

  let pure (x : 'a) : 'a cont_t = fun k -> k x

  let bind (m : 'a cont_t) (f : 'a -> 'b cont_t) : 'b cont_t =
    fun k -> m (fun a -> f a k)

  let ( let* ) = bind

  let callcc (f : ('a -> 'b cont_t) -> 'a cont_t) : 'a cont_t =
    fun k -> f (fun a -> fun _k' -> k a) k

  let run (m : int cont_t) : int = m (fun x -> x)

  (* Demo *)
  let demo () =
    Printf.printf "=== Continuation Monad Transformer ===\n";

    (* call/cc example: early return *)
    let product_with_escape lst =
      run (callcc (fun escape ->
        let rec loop = function
          | [] -> pure 1
          | 0 :: _ -> escape 0  (* early return! *)
          | x :: xs ->
            let* rest = loop xs in
            pure (x * rest)
        in
        loop lst
      ))
    in

    Printf.printf "product [1;2;3;4] = %d\n" (product_with_escape [1;2;3;4]);
    Printf.printf "product [1;2;0;4] = %d (early exit at 0)\n"
      (product_with_escape [1;2;0;4]);
    Printf.printf "product [5;3;2;1] = %d\n" (product_with_escape [5;3;2;1]);

    (* Using call/cc for labeled loops *)
    let find_first_even lst =
      run (callcc (fun found ->
        let rec search = function
          | [] -> pure (-1)
          | x :: xs ->
            if x mod 2 = 0 then found x
            else search xs
        in
        search lst
      ))
    in

    Printf.printf "first even in [1;3;5;4;6] = %d\n"
      (find_first_even [1;3;5;4;6]);
    Printf.printf "first even in [1;3;5;7] = %d\n"
      (find_first_even [1;3;5;7]);

    Printf.printf "\n"
end

(* ══════════════════════════════════════════════════════════════════════════
   10. PUTTING IT ALL TOGETHER — The Unifying Principle
   ══════════════════════════════════════════════════════════════════════════

   The key insight of this module: delimited continuations are a
   universal control-flow mechanism. Everything above — non-determinism,
   coroutines, exceptions, state, generators, backtracking — is just
   a different *interpretation* of shift/reset.

   This is why continuations are sometimes called "the mother of all
   monads" (Filinski 1994): any monadic effect can be represented
   using delimited continuations. *)

module Summary = struct
  let demo () =
    Printf.printf "══════════════════════════════════════════════════════════════\n";
    Printf.printf "  Delimited Continuations — The Mother of All Monads\n";
    Printf.printf "══════════════════════════════════════════════════════════════\n";
    Printf.printf "\n";
    Printf.printf "Patterns demonstrated:\n";
    Printf.printf "  1. CPS Transformation    — explicit continuation passing\n";
    Printf.printf "  2. shift/reset           — capturing delimited continuations\n";
    Printf.printf "  3. Non-determinism (amb) — exploring all choices\n";
    Printf.printf "  4. Coroutines            — cooperative multitasking via yield\n";
    Printf.printf "  5. Exceptions            — error handling as abort\n";
    Printf.printf "  6. State                 — threading state via continuations\n";
    Printf.printf "  7. Generators            — lazy value production\n";
    Printf.printf "  8. Backtracking          — constraint solving via search\n";
    Printf.printf "  9. ContT (call/cc)       — continuation monad transformer\n";
    Printf.printf "\n";
    Printf.printf "Key insight: all of these are different interpretations of\n";
    Printf.printf "the same underlying mechanism — capturing and composing\n";
    Printf.printf "partial continuations.\n";
    Printf.printf "\n";
    Printf.printf "\"A continuation is the rest of the computation.\n";
    Printf.printf " A delimited continuation is the rest of the computation\n";
    Printf.printf " up to a boundary. That boundary makes all the difference.\"\n";
    Printf.printf "\n"
end

(* ── Main ── *)

let () =
  Summary.demo ();
  CPS.demo ();
  Delimited.demo ();
  NonDet.demo ();
  Coroutine.demo ();
  ExnCont.demo ();
  StateCont.demo ();
  Generator.demo ();
  Backtrack.demo ();
  ContT.demo ();
  Printf.printf "All demos completed successfully!\n"
