(* effects.ml — Algebraic Effects and Handlers
 *
 * A simulation of algebraic effects in OCaml using delimited continuations
 * (CPS-based). Demonstrates one of the most exciting developments in
 * programming language theory — effects as first-class values with handlers.
 *
 * Concepts demonstrated:
 * - Algebraic effects (operations + handlers)
 * - Delimited continuations (CPS transform)
 * - Effect polymorphism and composition
 * - Common effect patterns: State, Exception, Nondeterminism, Logging, Async
 * - Effect handler composition and modularity
 * - Free monad encoding of effects
 *
 * OCaml 5 has native effect handlers, but this module works on any OCaml
 * version by encoding effects via a free monad / CPS approach.
 *
 * Usage:
 *   ocamlfind ocamlopt -package fmt -linkpkg effects.ml -o effects 2>/dev/null || \
 *   ocamlfind ocamlc -package fmt -linkpkg effects.ml -o effects 2>/dev/null || \
 *   ocamlfind ocamlopt effects.ml -o effects 2>/dev/null || \
 *   ocamlfind ocamlc effects.ml -o effects 2>/dev/null || \
 *   ocamlfind ocamlopt -package ounit2 -linkpkg effects.ml -o effects 2>/dev/null || \
 *   ocamlopt effects.ml -o effects || \
 *   ocamlc effects.ml -o effects
 *)

(* ========================================================================= *)
(* Part 1: Free Monad — The Foundation                                       *)
(* ========================================================================= *)

(* A free monad lets us describe effectful computations as data,
   then interpret them with different handlers. *)

module type EFFECT_SIG = sig
  type 'a t
  (* Each effect is a functor — 'a is the "continuation type" *)
end

(* The free monad over an effect signature *)
module Free (E : EFFECT_SIG) = struct
  type 'a t =
    | Pure of 'a
    | Impure of ('a t) E.t

  let return x = Pure x

  let rec bind m f =
    match m with
    | Pure x -> f x
    | Impure eff ->
      (* We need to map the bind into the effect functor.
         This requires E to be a functor, which we handle via
         a provided map function. *)
      failwith "Use FreeF with explicit map"

  (* Free monad with explicit functor map *)
end

module FreeF (E : sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
end) = struct
  type 'a t =
    | Pure of 'a
    | Impure of ('a t) E.t

  let return x = Pure x

  let rec bind m f =
    match m with
    | Pure x -> f x
    | Impure eff -> Impure (E.map (fun m' -> bind m' f) eff)

  let map f m = bind m (fun x -> Pure (f x))

  let lift eff = Impure (E.map (fun x -> Pure x) eff)

  let rec fold ~pure ~impure m =
    match m with
    | Pure x -> pure x
    | Impure eff -> impure (E.map (fold ~pure ~impure) eff)
end

(* ========================================================================= *)
(* Part 2: State Effect                                                      *)
(* ========================================================================= *)

module StateEffect = struct
  (* State operations as a functor *)
  type 'a t =
    | Get of (int -> 'a)      (* Get state, continue with it *)
    | Put of int * 'a         (* Set state, then continue *)

  let map f = function
    | Get k -> Get (fun s -> f (k s))
    | Put (s, next) -> Put (s, f next)
end

module State = struct
  include FreeF(StateEffect)

  let get = Impure (StateEffect.Get (fun s -> Pure s))
  let put s = Impure (StateEffect.Put (s, Pure ()))

  let modify f = bind get (fun s -> put (f s))

  (* Run a stateful computation with an initial state *)
  let run init m =
    let rec go s = function
      | Pure x -> (x, s)
      | Impure (StateEffect.Get k) -> go s (k s)
      | Impure (StateEffect.Put (s', next)) -> go s' next
    in
    go init m

  (* Run and return only the result *)
  let eval init m = fst (run init m)

  (* Run and return only the final state *)
  let exec init m = snd (run init m)
end

(* ========================================================================= *)
(* Part 3: Exception Effect                                                  *)
(* ========================================================================= *)

module ExnEffect = struct
  type 'a t =
    | Raise of string          (* Raise an exception — no continuation *)
    | Catch of 'a * (string -> 'a)  (* Try/catch *)

  let map f = function
    | Raise msg -> Raise msg
    | Catch (body, handler) -> Catch (f body, fun msg -> f (handler msg))
end

module Exn = struct
  include FreeF(ExnEffect)

  let raise_ msg = Impure (ExnEffect.Raise msg)
  let catch body handler = Impure (ExnEffect.Catch (body, handler))

  (* Run, returning Ok or Error *)
  let run m =
    let rec go = function
      | Pure x -> Ok x
      | Impure (ExnEffect.Raise msg) -> Error msg
      | Impure (ExnEffect.Catch (body, handler)) ->
        match go body with
        | Ok x -> Ok x
        | Error msg -> go (handler msg)
    in
    go m
end

(* ========================================================================= *)
(* Part 4: Nondeterminism Effect                                             *)
(* ========================================================================= *)

module NondetEffect = struct
  type 'a t =
    | Fail                        (* No solutions *)
    | Choose of 'a * 'a          (* Binary choice *)

  let map f = function
    | Fail -> Fail
    | Choose (a, b) -> Choose (f a, f b)
end

module Nondet = struct
  include FreeF(NondetEffect)

  let fail = Impure NondetEffect.Fail
  let choose a b = Impure (NondetEffect.Choose (a, b))

  (* Choose from a list *)
  let rec choose_from = function
    | [] -> fail
    | [x] -> return x
    | x :: xs -> bind (choose (return x) (choose_from xs))
                   (fun m -> m)

  (* Collect all solutions *)
  let run_all m =
    let rec go = function
      | Pure x -> [x]
      | Impure NondetEffect.Fail -> []
      | Impure (NondetEffect.Choose (a, b)) -> go a @ go b
    in
    go m

  (* Get first solution *)
  let run_first m =
    let rec go = function
      | Pure x -> Some x
      | Impure NondetEffect.Fail -> None
      | Impure (NondetEffect.Choose (a, b)) ->
        match go a with
        | Some _ as result -> result
        | None -> go b
    in
    go m

  (* Guard: filter solutions *)
  let guard cond = if cond then return () else fail
end

(* ========================================================================= *)
(* Part 5: Writer/Logging Effect                                             *)
(* ========================================================================= *)

module WriterEffect = struct
  type 'a t =
    | Tell of string * 'a    (* Log a message, then continue *)

  let map f = function
    | Tell (msg, next) -> Tell (msg, f next)
end

module Writer = struct
  include FreeF(WriterEffect)

  let tell msg = Impure (WriterEffect.Tell (msg, Pure ()))

  (* Run and collect all log messages *)
  let run m =
    let rec go acc = function
      | Pure x -> (x, List.rev acc)
      | Impure (WriterEffect.Tell (msg, next)) -> go (msg :: acc) next
    in
    go [] m
end

(* ========================================================================= *)
(* Part 6: Reader Effect                                                     *)
(* ========================================================================= *)

module ReaderEffect = struct
  type 'a t =
    | Ask of (string -> 'a)    (* Read environment *)

  let map f = function
    | Ask k -> Ask (fun env -> f (k env))
end

module Reader = struct
  include FreeF(ReaderEffect)

  let ask = Impure (ReaderEffect.Ask (fun env -> Pure env))

  let run env m =
    let rec go = function
      | Pure x -> x
      | Impure (ReaderEffect.Ask k) -> go (k env)
    in
    go m
end

(* ========================================================================= *)
(* Part 7: Coroutine / Yield Effect                                          *)
(* ========================================================================= *)

module YieldEffect = struct
  type 'a t =
    | Yield of int * 'a       (* Yield a value, then continue *)

  let map f = function
    | Yield (v, next) -> Yield (v, f next)
end

module Coroutine = struct
  include FreeF(YieldEffect)

  let yield_ v = Impure (YieldEffect.Yield (v, Pure ()))

  type 'a status =
    | Done of 'a
    | Yielded of int * 'a t

  (* Step one yield *)
  let step = function
    | Pure x -> Done x
    | Impure (YieldEffect.Yield (v, next)) -> Yielded (v, next)

  (* Collect all yielded values *)
  let run m =
    let rec go acc = function
      | Pure x -> (x, List.rev acc)
      | Impure (YieldEffect.Yield (v, next)) -> go (v :: acc) next
    in
    go [] m

  (* Convert to a lazy sequence *)
  let to_seq m =
    let rec go m () =
      match m with
      | Pure _ -> Seq.Nil
      | Impure (YieldEffect.Yield (v, next)) -> Seq.Cons (v, go next)
    in
    go m
end

(* ========================================================================= *)
(* Part 8: CPS-Based Effect Handlers (More Flexible)                         *)
(* ========================================================================= *)

(* A more general approach using CPS (continuation-passing style) *)
module CPS = struct
  type ('a, 'r) cont = 'a -> 'r

  (* State handler in CPS *)
  module State = struct
    type 'a t = { run : 'r. int -> ('a -> int -> 'r) -> 'r }

    let return x = { run = fun s k -> k x s }

    let bind m f = { run = fun s k ->
      m.run s (fun a s' -> (f a).run s' k)
    }

    let get = { run = fun s k -> k s s }

    let put s = { run = fun _s k -> k () s }

    let modify f = { run = fun s k -> k () (f s) }

    let run_state init m = m.run init (fun a s -> (a, s))
    let eval_state init m = fst (run_state init m)
    let exec_state init m = snd (run_state init m)
  end

  (* Exception handler in CPS *)
  module Exn = struct
    type 'a t = { run : 'r. ('a -> 'r) -> (string -> 'r) -> 'r }

    let return x = { run = fun ok _err -> ok x }

    let bind m f = { run = fun ok err ->
      m.run (fun a -> (f a).run ok err) err
    }

    let raise_ msg = { run = fun _ok err -> err msg }

    let catch m handler = { run = fun ok err ->
      m.run ok (fun msg -> (handler msg).run ok err)
    }

    let run m = m.run (fun x -> Ok x) (fun msg -> Error msg)
  end

  (* Nondeterminism in CPS *)
  module Nondet = struct
    type 'a t = { run : 'r. ('a -> 'r -> 'r) -> 'r -> 'r }

    let return x = { run = fun cons nil -> cons x nil }

    let bind m f = { run = fun cons nil ->
      m.run (fun a acc -> (f a).run cons acc) nil
    }

    let fail = { run = fun _cons nil -> nil }

    let choose a b = { run = fun cons nil ->
      a.run cons (b.run cons nil)
    }

    let run_all m = m.run (fun x acc -> x :: acc) []

    let guard cond = if cond then return () else fail
  end
end

(* ========================================================================= *)
(* Part 9: Effect Composition via Coproducts                                 *)
(* ========================================================================= *)

(* Combine two effect signatures into one *)
module Coproduct (F : sig type 'a t val map : ('a -> 'b) -> 'a t -> 'b t end)
                 (G : sig type 'a t val map : ('a -> 'b) -> 'a t -> 'b t end) =
struct
  type 'a t =
    | Inl of 'a F.t
    | Inr of 'a G.t

  let map f = function
    | Inl x -> Inl (F.map f x)
    | Inr x -> Inr (G.map f x)

  (* Inject from left effect *)
  let inl x = Inl x
  (* Inject from right effect *)
  let inr x = Inr x
end

(* State + Writer combined *)
module StateWriter = struct
  module Combined = Coproduct(StateEffect)(WriterEffect)
  module M = FreeF(Combined)

  let get = M.Impure (Combined.Inl (StateEffect.Get (fun s -> M.Pure s)))
  let put s = M.Impure (Combined.Inl (StateEffect.Put (s, M.Pure ())))
  let tell msg = M.Impure (Combined.Inr (WriterEffect.Tell (msg, M.Pure ())))

  let run init m =
    let rec go s log = function
      | M.Pure x -> (x, s, List.rev log)
      | M.Impure (Combined.Inl (StateEffect.Get k)) -> go s log (k s)
      | M.Impure (Combined.Inl (StateEffect.Put (s', next))) -> go s' log next
      | M.Impure (Combined.Inr (WriterEffect.Tell (msg, next))) ->
        go s (msg :: log) next
    in
    go init [] m

  let bind = M.bind
  let return_ = M.return
end

(* ========================================================================= *)
(* Part 10: Example Applications                                            *)
(* ========================================================================= *)

(* Example 1: Stateful counter *)
let counter_example () =
  let open State in
  let computation =
    bind get (fun s ->
    bind (put (s + 1)) (fun () ->
    bind get (fun s ->
    bind (put (s * 2)) (fun () ->
    bind get (fun s ->
    return s)))))
  in
  run 0 computation  (* (2, 2) — start at 0, +1=1, *2=2 *)

(* Example 2: Safe division with exceptions *)
let safe_div_example () =
  let open Exn in
  let safe_div a b =
    if b = 0 then raise_ "Division by zero"
    else return (a / b)
  in
  let computation =
    bind (safe_div 10 2) (fun x ->
    bind (safe_div x 0) (fun _ ->
    return 999))
  in
  let with_catch =
    catch computation (fun msg ->
      return (- (String.length msg)))
  in
  (run computation, run with_catch)

(* Example 3: Pythagorean triples via nondeterminism *)
let pythagorean_triples n =
  let open Nondet in
  let range lo hi =
    let rec build acc i =
      if i < lo then choose_from acc
      else build (i :: acc) (i - 1)
    in
    build [] hi
  in
  let computation =
    bind (range 1 n) (fun a ->
    bind (range a n) (fun b ->
    bind (range b n) (fun c ->
    bind (guard (a*a + b*b = c*c)) (fun () ->
    return (a, b, c)))))
  in
  run_all computation

(* Example 4: Logged computation *)
let logged_example () =
  let open Writer in
  let computation =
    bind (tell "Starting computation") (fun () ->
    bind (tell "Computing 2 + 3") (fun () ->
    let result = 2 + 3 in
    bind (tell (Printf.sprintf "Result = %d" result)) (fun () ->
    return result)))
  in
  run computation

(* Example 5: Coroutine — Fibonacci generator *)
let fib_generator n =
  let open Coroutine in
  let rec go a b count =
    if count >= n then return ()
    else
      bind (yield_ a) (fun () ->
      go b (a + b) (count + 1))
  in
  run (go 0 1 0)

(* Example 6: Combined State + Writer *)
let state_writer_example () =
  let open StateWriter in
  let computation =
    bind get (fun s ->
    bind (tell (Printf.sprintf "Initial state: %d" s)) (fun () ->
    bind (put (s + 10)) (fun () ->
    bind get (fun s ->
    bind (tell (Printf.sprintf "After +10: %d" s)) (fun () ->
    bind (put (s * 3)) (fun () ->
    bind get (fun s ->
    bind (tell (Printf.sprintf "After *3: %d" s)) (fun () ->
    return_ s))))))))
  in
  run 5 computation  (* (45, 45, ["Initial state: 5"; "After +10: 15"; "After *3: 45"]) *)

(* Example 7: CPS-based state *)
let cps_state_example () =
  let open CPS.State in
  let computation =
    bind get (fun s ->
    bind (put (s + 100)) (fun () ->
    bind (modify (fun x -> x * 2)) (fun () ->
    bind get (fun s ->
    return s))))
  in
  run_state 42 computation  (* (284, 284) *)

(* Example 8: CPS nondeterminism — N-Queens *)
let n_queens n =
  let open CPS.Nondet in
  let safe queens col row =
    List.for_all (fun (c, r) ->
      c <> col && r <> row &&
      abs (c - col) <> abs (r - row)
    ) queens
  in
  let rec place queens row =
    if row > n then return (List.rev queens)
    else
      let rec try_col col =
        if col > n then fail
        else
          let attempt =
            bind (guard (safe queens col row)) (fun () ->
            place ((col, row) :: queens) (row + 1))
          in
          choose attempt (try_col (col + 1))
      in
      try_col 1
  in
  run_all (place [] 1)

(* Example 9: Reader effect — configuration *)
let reader_example () =
  let open Reader in
  let greet =
    bind ask (fun name ->
    return (Printf.sprintf "Hello, %s! Welcome to algebraic effects." name))
  in
  run "OCaml programmer" greet

(* ========================================================================= *)
(* Part 11: Tests                                                            *)
(* ========================================================================= *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_eq name expected actual =
  if expected = actual then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s (FAILED)\n" name
  end

let assert_true name cond =
  if cond then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s (FAILED)\n" name
  end

let () =
  Printf.printf "\n=== Algebraic Effects and Handlers Tests ===\n\n";

  (* State effect tests *)
  Printf.printf "--- State Effect ---\n";
  let (v, s) = counter_example () in
  assert_eq "counter result" 2 v;
  assert_eq "counter final state" 2 s;

  let (v2, s2) = State.run 10 (State.bind State.get (fun s -> State.return (s + 5))) in
  assert_eq "get returns initial state" 15 v2;
  assert_eq "state unchanged after get" 10 s2;

  let ((), s3) = State.run 0 (State.put 42) in
  assert_eq "put sets state" 42 s3;

  let ((), s4) = State.run 5 (State.modify (fun x -> x * 3)) in
  assert_eq "modify transforms state" 15 s4;

  assert_eq "eval_state returns value" 2 (State.eval 0 (
    State.bind (State.put 2) (fun () -> State.get)));
  assert_eq "exec_state returns state" 2 (State.exec 0 (
    State.bind (State.put 2) (fun () -> State.get)));

  (* Chained state operations *)
  let (v5, s5) = State.run 1 (
    State.bind (State.modify (fun x -> x + 1)) (fun () ->
    State.bind (State.modify (fun x -> x * 10)) (fun () ->
    State.bind (State.modify (fun x -> x - 3)) (fun () ->
    State.get)))) in
  assert_eq "chained modify result" 17 v5;
  assert_eq "chained modify state" 17 s5;

  (* Exception effect tests *)
  Printf.printf "\n--- Exception Effect ---\n";
  let (r1, r2) = safe_div_example () in
  assert_eq "uncaught exception" (Error "Division by zero") r1;
  assert_eq "caught exception" (Ok (-16)) r2;

  assert_eq "successful computation" (Ok 42) (Exn.run (Exn.return 42));
  assert_eq "raise without catch" (Error "boom") (Exn.run (Exn.raise_ "boom"));

  let nested_catch = Exn.catch
    (Exn.catch (Exn.raise_ "inner") (fun _ -> Exn.raise_ "outer"))
    (fun msg -> Exn.return msg) in
  assert_eq "nested catch" (Ok "outer") (Exn.run nested_catch);

  (* Nondeterminism tests *)
  Printf.printf "\n--- Nondeterminism Effect ---\n";
  let triples = pythagorean_triples 20 in
  assert_true "finds (3,4,5)" (List.mem (3, 4, 5) triples);
  assert_true "finds (5,12,13)" (List.mem (5, 12, 13) triples);
  assert_true "finds (8,15,17)" (List.mem (8, 15, 17) triples);
  assert_eq "correct number of triples" 6 (List.length triples);

  assert_eq "fail gives empty" [] (Nondet.run_all Nondet.fail);
  assert_eq "fail first is none" None (Nondet.run_first Nondet.fail);
  assert_eq "return gives singleton" [42] (Nondet.run_all (Nondet.return 42));
  assert_eq "first of return" (Some 42) (Nondet.run_first (Nondet.return 42));

  let choices = Nondet.run_all (
    Nondet.bind (Nondet.choose_from [1; 2; 3]) (fun x ->
    Nondet.bind (Nondet.guard (x > 1)) (fun () ->
    Nondet.return (x * 10)))) in
  assert_eq "filtered choices" [20; 30] choices;

  (* Writer effect tests *)
  Printf.printf "\n--- Writer Effect ---\n";
  let (result, logs) = logged_example () in
  assert_eq "logged result" 5 result;
  assert_eq "log count" 3 (List.length logs);
  assert_eq "first log" "Starting computation" (List.nth logs 0);
  assert_eq "last log" "Result = 5" (List.nth logs 2);

  let (v, logs2) = Writer.run (Writer.return 99) in
  assert_eq "pure writer value" 99 v;
  assert_eq "pure writer no logs" [] logs2;

  (* Reader effect tests *)
  Printf.printf "\n--- Reader Effect ---\n";
  let greeting = reader_example () in
  assert_eq "reader greeting" "Hello, OCaml programmer! Welcome to algebraic effects." greeting;
  assert_eq "reader with different env"
    "Hello, world! Welcome to algebraic effects."
    (Reader.run "world" (Reader.bind Reader.ask (fun name ->
      Reader.return (Printf.sprintf "Hello, %s! Welcome to algebraic effects." name))));

  (* Coroutine tests *)
  Printf.printf "\n--- Coroutine Effect ---\n";
  let ((), fibs) = fib_generator 10 in
  assert_eq "fibonacci sequence" [0; 1; 1; 2; 3; 5; 8; 13; 21; 34] fibs;

  let ((), empty) = Coroutine.run (Coroutine.return ()) in
  assert_eq "empty coroutine" [] empty;

  let seq = Coroutine.to_seq (
    Coroutine.bind (Coroutine.yield_ 1) (fun () ->
    Coroutine.bind (Coroutine.yield_ 2) (fun () ->
    Coroutine.bind (Coroutine.yield_ 3) (fun () ->
    Coroutine.return ())))) in
  assert_eq "coroutine to_seq" [1; 2; 3] (List.of_seq seq);

  (* Step-through coroutine *)
  let step1 = Coroutine.step (
    Coroutine.bind (Coroutine.yield_ 10) (fun () ->
    Coroutine.bind (Coroutine.yield_ 20) (fun () ->
    Coroutine.return 99))) in
  (match step1 with
   | Coroutine.Yielded (v, rest) ->
     assert_eq "first yield value" 10 v;
     (match Coroutine.step rest with
      | Coroutine.Yielded (v2, rest2) ->
        assert_eq "second yield value" 20 v2;
        (match Coroutine.step rest2 with
         | Coroutine.Done result -> assert_eq "final result" 99 result
         | _ -> assert_true "expected done" false)
      | _ -> assert_true "expected second yield" false)
   | _ -> assert_true "expected first yield" false);

  (* State+Writer combined tests *)
  Printf.printf "\n--- State + Writer Combined ---\n";
  let (result, state, logs) = state_writer_example () in
  assert_eq "combined result" 45 result;
  assert_eq "combined final state" 45 state;
  assert_eq "combined log count" 3 (List.length logs);
  assert_eq "combined log 1" "Initial state: 5" (List.nth logs 0);
  assert_eq "combined log 2" "After +10: 15" (List.nth logs 1);
  assert_eq "combined log 3" "After *3: 45" (List.nth logs 2);

  (* CPS State tests *)
  Printf.printf "\n--- CPS State ---\n";
  let (v_cps, s_cps) = cps_state_example () in
  assert_eq "CPS state result" 284 v_cps;
  assert_eq "CPS state final" 284 s_cps;

  assert_eq "CPS eval" 10 (CPS.State.eval_state 10 (CPS.State.return 10));
  assert_eq "CPS exec" 10 (CPS.State.exec_state 10 (CPS.State.return ()));

  (* CPS Exception tests *)
  Printf.printf "\n--- CPS Exception ---\n";
  assert_eq "CPS exn success" (Ok 42) (CPS.Exn.run (CPS.Exn.return 42));
  assert_eq "CPS exn raise" (Error "oops") (CPS.Exn.run (CPS.Exn.raise_ "oops"));
  assert_eq "CPS exn catch" (Ok "recovered")
    (CPS.Exn.run (CPS.Exn.catch (CPS.Exn.raise_ "err")
      (fun _ -> CPS.Exn.return "recovered")));

  (* CPS Nondeterminism tests *)
  Printf.printf "\n--- CPS Nondeterminism ---\n";
  let cps_choices = CPS.Nondet.run_all (
    CPS.Nondet.bind (CPS.Nondet.choose (CPS.Nondet.return 1)
                                         (CPS.Nondet.return 2)) (fun x ->
    CPS.Nondet.bind (CPS.Nondet.choose (CPS.Nondet.return 10)
                                         (CPS.Nondet.return 20)) (fun y ->
    CPS.Nondet.return (x + y)))) in
  assert_eq "CPS nondet products" [11; 21; 12; 22] cps_choices;

  (* N-Queens tests *)
  Printf.printf "\n--- N-Queens via Nondeterminism ---\n";
  let queens_4 = n_queens 4 in
  assert_eq "4-queens solutions" 2 (List.length queens_4);
  let queens_8 = n_queens 8 in
  assert_eq "8-queens solutions" 92 (List.length queens_8);

  (* Coproduct tests *)
  Printf.printf "\n--- Effect Coproduct ---\n";
  let module C = Coproduct(StateEffect)(WriterEffect) in
  let inl_test = C.Inl (StateEffect.Get (fun _ -> 42)) in
  (match inl_test with C.Inl _ -> assert_true "inl is left" true | _ -> assert_true "inl is left" false);
  let inr_test = C.Inr (WriterEffect.Tell ("hi", 42)) in
  (match inr_test with C.Inr _ -> assert_true "inr is right" true | _ -> assert_true "inr is right" false);
  let mapped = C.map (fun x -> x + 1) (C.Inl (StateEffect.Get (fun x -> x * 2))) in
  (match mapped with
   | C.Inl (StateEffect.Get f) -> assert_eq "coproduct map preserves structure" 11 (f 5)
   | _ -> assert_true "expected Inl" false);

  (* Free monad laws *)
  Printf.printf "\n--- Free Monad Laws ---\n";
  (* Left identity: return a >>= f ≡ f a *)
  let f x = State.put (x + 1) in
  let ((), s_left) = State.run 0 (State.bind (State.return 5) f) in
  let ((), s_right) = State.run 0 (f 5) in
  assert_eq "left identity" s_left s_right;

  (* Right identity: m >>= return ≡ m *)
  let m = State.bind (State.put 10) (fun () -> State.get) in
  let (v_ri1, s_ri1) = State.run 0 m in
  let (v_ri2, s_ri2) = State.run 0 (State.bind m State.return) in
  assert_eq "right identity value" v_ri1 v_ri2;
  assert_eq "right identity state" s_ri1 s_ri2;

  (* Associativity: (m >>= f) >>= g ≡ m >>= (fun x -> f x >>= g) *)
  let g x = State.bind State.get (fun s -> State.return (s + x)) in
  let m2 = State.put 3 in
  let (v_a1, _) = State.run 0 (State.bind (State.bind m2 f) g) in
  let (v_a2, _) = State.run 0 (State.bind m2 (fun x -> State.bind (f x) g)) in
  assert_eq "associativity" v_a1 v_a2;

  (* Summary *)
  Printf.printf "\n=== Results: %d passed, %d failed ===\n"
    !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
