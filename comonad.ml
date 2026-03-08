(* ============================================================================
 * Comonads -- Dual of Monads for Context-Dependent Computation
 * ============================================================================
 *
 * Comonads capture computations that produce values from a context.
 * While monads wrap values (return) and sequence computations (bind),
 * comonads extract values (extract) and extend computations (extend).
 *
 * This module implements:
 * - Comonad interface (extract, extend, duplicate, map)
 * - Identity Comonad -- trivial base case
 * - Env Comonad -- computation with read-only environment
 * - Traced Comonad -- computation from a monoidal query
 * - Store Comonad -- position-dependent computation (spreadsheets, cellular automata)
 * - Stream Comonad -- infinite streams with focus
 * - Zipper1D Comonad -- bidirectional cursor for 1D cellular automata
 * - Zipper2D Comonad -- 2D grid with focus for Game of Life
 *
 * Applications:
 * - 1D cellular automata (Wolfram Rule 110, Rule 30)
 * - Conway's Game of Life via comonadic extend
 * - Spreadsheet evaluation with Store comonad
 * - Moving average / signal smoothing
 * - Infinite stream processing with running statistics
 *
 * Usage: ocaml comonad.ml
 *)

(* ---- Comonad Signature ---- *)
module type COMONAD = sig
  type 'a t
  val extract : 'a t -> 'a
  val extend : ('a t -> 'b) -> 'a t -> 'b t
  val duplicate : 'a t -> 'a t t
  val map : ('a -> 'b) -> 'a t -> 'b t
end

(* ---- Identity Comonad ---- *)
module Identity : sig
  include COMONAD
  val create : 'a -> 'a t
  val run : 'a t -> 'a
end = struct
  type 'a t = 'a
  let create x = x
  let run x = x
  let extract x = x
  let map f x = f x
  let extend f x = f x
  let duplicate x = x
end

(* ---- Env Comonad (CoReader) ---- *)
module Env : sig
  type ('e, 'a) t
  val create : 'e -> 'a -> ('e, 'a) t
  val extract : ('e, 'a) t -> 'a
  val ask : ('e, 'a) t -> 'e
  val local : ('e -> 'e2) -> ('e, 'a) t -> ('e2, 'a) t
  val extend : (('e, 'a) t -> 'b) -> ('e, 'a) t -> ('e, 'b) t
  val duplicate : ('e, 'a) t -> ('e, ('e, 'a) t) t
  val map : ('a -> 'b) -> ('e, 'a) t -> ('e, 'b) t
end = struct
  type ('e, 'a) t = { env : 'e; value : 'a }
  let create e a = { env = e; value = a }
  let extract w = w.value
  let ask w = w.env
  let local f w = { env = f w.env; value = w.value }
  let extend f w = { env = w.env; value = f w }
  let duplicate w = { env = w.env; value = w }
  let map f w = { env = w.env; value = f w.value }
end

(* ---- Traced Comonad (CoWriter) ---- *)
module type MONOID = sig
  type t
  val empty : t
  val append : t -> t -> t
end

module Traced (M : MONOID) : sig
  type 'a t
  val create : (M.t -> 'a) -> 'a t
  val extract : 'a t -> 'a
  val trace : M.t -> 'a t -> 'a
  val extend : ('a t -> 'b) -> 'a t -> 'b t
  val duplicate : 'a t -> 'a t t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val listen : 'a t -> (M.t * 'a) t
end = struct
  type 'a t = M.t -> 'a
  let create f = f
  let extract f = f M.empty
  let trace m f = f m
  let extend g f = fun m -> g (fun m' -> f (M.append m m'))
  let duplicate f = fun m -> fun m' -> f (M.append m m')
  let map g f = fun m -> g (f m)
  let listen f = fun m -> (m, f m)
end

(* ---- Store Comonad ---- *)
module Store : sig
  type ('s, 'a) t
  val create : ('s -> 'a) -> 's -> ('s, 'a) t
  val extract : ('s, 'a) t -> 'a
  val peek : 's -> ('s, 'a) t -> 'a
  val peeks : ('s -> 's) -> ('s, 'a) t -> 'a
  val pos : ('s, 'a) t -> 's
  val seek : 's -> ('s, 'a) t -> ('s, 'a) t
  val seeks : ('s -> 's) -> ('s, 'a) t -> ('s, 'a) t
  val extend : (('s, 'a) t -> 'b) -> ('s, 'a) t -> ('s, 'b) t
  val duplicate : ('s, 'a) t -> ('s, ('s, 'a) t) t
  val map : ('a -> 'b) -> ('s, 'a) t -> ('s, 'b) t
  val experiment : ('s -> 's list) -> ('s, 'a) t -> 'a list
end = struct
  type ('s, 'a) t = { getter : 's -> 'a; position : 's }
  let create f s = { getter = f; position = s }
  let extract w = w.getter w.position
  let peek s w = w.getter s
  let peeks f w = w.getter (f w.position)
  let pos w = w.position
  let seek s w = { w with position = s }
  let seeks f w = { w with position = f w.position }
  let extend f w = { getter = (fun s -> f { w with position = s }); position = w.position }
  let duplicate w = { getter = (fun s -> { w with position = s }); position = w.position }
  let map f w = { getter = (fun s -> f (w.getter s)); position = w.position }
  let experiment f w = List.map (fun s -> w.getter s) (f w.position)
end

(* ---- Stream Comonad ---- *)
module Stream : sig
  type 'a t
  val create : 'a -> (unit -> 'a t) -> 'a t
  val unfold : ('s -> 'a * 's) -> 's -> 'a t
  val extract : 'a t -> 'a
  val tail : 'a t -> 'a t
  val extend : ('a t -> 'b) -> 'a t -> 'b t
  val duplicate : 'a t -> 'a t t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val take : int -> 'a t -> 'a list
  val drop : int -> 'a t -> 'a t
  val nth : int -> 'a t -> 'a
  val iterate : ('a -> 'a) -> 'a -> 'a t
  val zip_with : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val scan : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b t
end = struct
  type 'a t = { head : 'a; rest : unit -> 'a t }
  let create h r = { head = h; rest = r }
  let rec unfold f s =
    let (a, s') = f s in
    { head = a; rest = (fun () -> unfold f s') }
  let extract s = s.head
  let tail s = s.rest ()
  let rec map f s =
    { head = f s.head; rest = (fun () -> map f (s.rest ())) }
  let rec extend g s =
    { head = g s; rest = (fun () -> extend g (s.rest ())) }
  let rec duplicate s =
    { head = s; rest = (fun () -> duplicate (s.rest ())) }
  let take n s =
    let rec go acc n s =
      if n <= 0 then List.rev acc
      else go (s.head :: acc) (n - 1) (s.rest ())
    in go [] n s
  let rec drop n s =
    if n <= 0 then s else drop (n - 1) (s.rest ())
  let nth n s = extract (drop n s)
  let rec iterate f x =
    { head = x; rest = (fun () -> iterate f (f x)) }
  let rec zip_with f s1 s2 =
    { head = f s1.head s2.head;
      rest = (fun () -> zip_with f (s1.rest ()) (s2.rest ())) }
  let rec scan f acc s =
    let acc' = f acc s.head in
    { head = acc'; rest = (fun () -> scan f acc' (s.rest ())) }
end

(* ---- Zipper1D Comonad ---- *)
module Zipper1D : sig
  type 'a t
  val create : 'a list -> 'a -> 'a list -> 'a t
  val extract : 'a t -> 'a
  val left : 'a t -> 'a list
  val right : 'a t -> 'a list
  val move_left : 'a -> 'a t -> 'a t
  val move_right : 'a -> 'a t -> 'a t
  val extend : ('a t -> 'b) -> 'a t -> 'b t
  val duplicate : 'a t -> 'a t t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val to_list : 'a t -> 'a list
  val of_list : 'a -> 'a list -> 'a t
end = struct
  type 'a t = { lefts : 'a list; focus : 'a; rights : 'a list }
  let create l f r = { lefts = l; focus = f; rights = r }
  let extract z = z.focus
  let left z = z.lefts
  let right z = z.rights
  let move_left default z =
    match z.lefts with
    | [] -> { lefts = []; focus = default; rights = z.focus :: z.rights }
    | l :: ls -> { lefts = ls; focus = l; rights = z.focus :: z.rights }
  let move_right default z =
    match z.rights with
    | [] -> { lefts = z.focus :: z.lefts; focus = default; rights = [] }
    | r :: rs -> { lefts = z.focus :: z.lefts; focus = r; rights = rs }
  let iterate_left n default z =
    let rec go acc n z =
      if n <= 0 then List.rev acc
      else let z' = move_left default z in go (z' :: acc) (n - 1) z'
    in go [] n z
  let iterate_right n default z =
    let rec go acc n z =
      if n <= 0 then List.rev acc
      else let z' = move_right default z in go (z' :: acc) (n - 1) z'
    in go [] n z
  let extend f z =
    let d = z.focus in
    let ls = iterate_left (List.length z.lefts) d z in
    let rs = iterate_right (List.length z.rights) d z in
    { lefts = List.rev_map f ls; focus = f z; rights = List.map f rs }
  let duplicate z =
    let d = z.focus in
    let ls = iterate_left (List.length z.lefts) d z in
    let rs = iterate_right (List.length z.rights) d z in
    { lefts = List.rev ls; focus = z; rights = rs }
  let map f z =
    { lefts = List.map f z.lefts; focus = f z.focus; rights = List.map f z.rights }
  let to_list z = List.rev z.lefts @ [z.focus] @ z.rights
  let of_list default = function
    | [] -> { lefts = []; focus = default; rights = [] }
    | x :: xs -> { lefts = []; focus = x; rights = xs }
end

(* ---- Zipper2D Comonad ---- *)
module Zipper2D : sig
  type 'a t
  val create : 'a Zipper1D.t Zipper1D.t -> 'a t
  val extract : 'a t -> 'a
  val extend : ('a t -> 'b) -> 'a t -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val neighbors8 : 'a -> 'a t -> 'a list
  val of_grid : 'a -> 'a list list -> 'a t
  val to_grid : 'a t -> 'a list list
  val move_up : 'a -> 'a t -> 'a t
  val move_down : 'a -> 'a t -> 'a t
  val move_left : 'a -> 'a t -> 'a t
  val move_right : 'a -> 'a t -> 'a t
end = struct
  type 'a t = { grid : 'a Zipper1D.t Zipper1D.t }
  let create g = { grid = g }
  let extract w = Zipper1D.extract (Zipper1D.extract w.grid)
  let move_up default w =
    { grid = Zipper1D.move_left (Zipper1D.create [] default []) w.grid }
  let move_down default w =
    { grid = Zipper1D.move_right (Zipper1D.create [] default []) w.grid }
  let move_left default w =
    { grid = Zipper1D.map (Zipper1D.move_left default) w.grid }
  let move_right default w =
    { grid = Zipper1D.map (Zipper1D.move_right default) w.grid }
  let neighbors8 default w =
    let u = move_up default w in
    let d = move_down default w in
    let l = move_left default w in
    let r = move_right default w in
    List.map extract [u; d; l; r;
      move_left default u; move_right default u;
      move_left default d; move_right default d]
  let extend f w =
    let cr = Zipper1D.extract w.grid in
    let d = Zipper1D.extract cr in
    let apply_row w =
      let row = Zipper1D.extract w.grid in
      let nl = List.length (Zipper1D.left row) in
      let nr = List.length (Zipper1D.right row) in
      let ls = let rec g a n w = if n<=0 then List.rev a
        else let w'=move_left d w in g(w'::a)(n-1)w' in g [] nl w in
      let rs = let rec g a n w = if n<=0 then List.rev a
        else let w'=move_right d w in g(w'::a)(n-1)w' in g [] nr w in
      Zipper1D.create (List.rev_map f ls) (f w) (List.map f rs) in
    let nu = List.length (Zipper1D.left w.grid) in
    let nd = List.length (Zipper1D.right w.grid) in
    let up_rows =
      let rec go acc n w = if n<=0 then List.rev acc
        else let w'=move_up d w in go(apply_row w'::acc)(n-1)w'
      in go [] nu w in
    let down_rows =
      let rec go acc n w = if n<=0 then List.rev acc
        else let w'=move_down d w in go(apply_row w'::acc)(n-1)w'
      in go [] nd w in
    { grid = Zipper1D.create up_rows (apply_row w) down_rows }
  let map f w =
    { grid = Zipper1D.map (Zipper1D.map f) w.grid }
  let of_grid default = function
    | [] -> { grid = Zipper1D.create [] (Zipper1D.create [] default []) [] }
    | rows ->
      (match List.map (Zipper1D.of_list default) rows with
       | [] -> { grid = Zipper1D.create [] (Zipper1D.create [] default []) [] }
       | r :: rs -> { grid = Zipper1D.create [] r rs })
  let to_grid w = List.map Zipper1D.to_list (Zipper1D.to_list w.grid)
end

(* ============================================================================
 * Applications
 * ============================================================================ *)

module CellularAutomaton = struct
  let rule_fn rule_num left center right =
    let index = (if left then 4 else 0) + (if center then 2 else 0) + (if right then 1 else 0) in
    (rule_num lsr index) land 1 = 1

  let step rule_num z =
    let lv = match Zipper1D.left z with x :: _ -> x | [] -> false in
    let rv = match Zipper1D.right z with x :: _ -> x | [] -> false in
    rule_fn rule_num lv (Zipper1D.extract z) rv

  let evolve rule_num z = Zipper1D.extend (step rule_num) z

  let render z =
    String.concat "" (List.map (fun b -> if b then "#" else ".") (Zipper1D.to_list z))

  let run rule_num width steps =
    let half = width / 2 in
    let z = Zipper1D.create (List.init half (fun _ -> false) |> List.rev) true
              (List.init half (fun _ -> false)) in
    let rec go acc n z =
      if n <= 0 then List.rev acc
      else go (z :: acc) (n - 1) (evolve rule_num z)
    in go [z] steps z
end

module Spreadsheet = struct
  type cell = Num of float | Formula of (int * int -> float) * (int * int) list

  let eval_cell store =
    match Store.extract store with
    | Num x -> x
    | Formula (f, _) -> f (fun pos ->
        match Store.peek pos store with Num x -> x | Formula _ -> 0.0)

  let create_sheet data =
    Store.create (fun (r, c) ->
      if r >= 0 && r < Array.length data && c >= 0 && c < Array.length data.(0)
      then data.(r).(c) else Num 0.0) (0, 0)

  let eval_all sheet rows cols =
    let result = Store.extend eval_cell sheet in
    Array.init rows (fun r -> Array.init cols (fun c -> Store.peek (r, c) result))
end

module MovingAverage = struct
  let moving_avg window store =
    let values = Store.experiment (fun p ->
      List.init window (fun i -> p - window/2 + i)) store in
    List.fold_left (+.) 0.0 values /. float_of_int window

  let run data window =
    let store = Store.create (fun i ->
      if i >= 0 && i < Array.length data then data.(i) else 0.0) 0 in
    Array.init (Array.length data) (fun i -> moving_avg window (Store.seek i store))
end

module GameOfLife = struct
  let step w =
    let live = List.length (List.filter Fun.id (Zipper2D.neighbors8 false w)) in
    match Zipper2D.extract w, live with
    | true, 2 | true, 3 -> true
    | true, _ -> false
    | false, 3 -> true
    | false, _ -> false

  let evolve w = Zipper2D.extend step w

  let render w =
    List.map (fun row ->
      String.concat "" (List.map (fun b -> if b then "#" else ".") row)
    ) (Zipper2D.to_grid w)

  let glider () = Zipper2D.of_grid false [
    [false; true;  false; false; false];
    [false; false; true;  false; false];
    [true;  true;  true;  false; false];
    [false; false; false; false; false];
    [false; false; false; false; false]]
end

module RunningStats = struct
  let fibonacci = Stream.unfold (fun (a, b) -> (a, (b, a + b))) (0, 1)
  let naturals = Stream.iterate (fun n -> n + 1) 0
  let squares = Stream.map (fun n -> n * n) naturals
  let cumulative_sum s = Stream.scan (fun acc x -> acc +. x) 0.0 s
end

(* ============================================================================
 * Tests (55 tests)
 * ============================================================================ *)

let tests_passed = ref 0
let tests_failed = ref 0

let test name f =
  try f (); incr tests_passed; Printf.printf "  PASS: %s\n" name
  with e -> incr tests_failed; Printf.printf "  FAIL: %s -- %s\n" name (Printexc.to_string e)

let assert_equal ?(msg="") expected actual =
  if expected <> actual then failwith (if msg <> "" then msg else "values differ")

let assert_float_equal ?(eps=1e-9) expected actual =
  if abs_float (expected -. actual) > eps then
    failwith (Printf.sprintf "Expected %f but got %f" expected actual)

let () =
  Printf.printf "\n=== Comonads Test Suite ===\n\n";

  Printf.printf "Identity Comonad:\n";
  test "extract returns value" (fun () ->
    assert_equal 42 (Identity.extract (Identity.create 42)));
  test "map applies function" (fun () ->
    assert_equal 84 (Identity.extract (Identity.map (( * ) 2) (Identity.create 42))));
  test "extend applies contextual function" (fun () ->
    assert_equal 15 (Identity.extract (Identity.extend (fun w -> Identity.extract w + 5) (Identity.create 10))));
  test "law: extend extract = id" (fun () ->
    let w = Identity.create 99 in
    assert_equal (Identity.extract w) (Identity.extract (Identity.extend Identity.extract w)));

  Printf.printf "\nEnv Comonad:\n";
  test "extract returns value" (fun () ->
    assert_equal 42 (Env.extract (Env.create "config" 42)));
  test "ask returns environment" (fun () ->
    assert_equal "config" (Env.ask (Env.create "config" 42)));
  test "local transforms environment" (fun () ->
    let w' = Env.local (( + ) 5) (Env.create 10 "hello") in
    assert_equal 15 (Env.ask w'); assert_equal "hello" (Env.extract w'));
  test "map preserves environment" (fun () ->
    let w' = Env.map (( + ) 1) (Env.create "env" 10) in
    assert_equal "env" (Env.ask w'); assert_equal 11 (Env.extract w'));
  test "extend gives access to env and value" (fun () ->
    assert_equal 30 (Env.extract (Env.extend (fun w -> Env.ask w + Env.extract w) (Env.create 10 20))));
  test "law: extract (extend f w) = f w" (fun () ->
    let w = Env.create "x" 5 in let f w = Env.extract w * 2 in
    assert_equal (f w) (Env.extract (Env.extend f w)));

  Printf.printf "\nTraced Comonad:\n";
  let module IntSum = struct type t = int let empty = 0 let append = ( + ) end in
  let module TInt = Traced(IntSum) in
  test "extract evaluates at mempty" (fun () ->
    assert_equal 0 (TInt.extract (TInt.create (fun n -> n * n))));
  test "trace evaluates at point" (fun () ->
    assert_equal 25 (TInt.trace 5 (TInt.create (fun n -> n * n))));
  test "extend composes queries" (fun () ->
    let w' = TInt.extend (fun w -> TInt.trace 3 w + TInt.trace 7 w) (TInt.create (fun n -> n * 2)) in
    assert_equal 20 (TInt.extract w'));
  test "map transforms values" (fun () ->
    let w' = TInt.map (( * ) 10) (TInt.create (fun n -> n + 1)) in
    assert_equal 10 (TInt.extract w'); assert_equal 60 (TInt.trace 5 w'));

  Printf.printf "\nStore Comonad:\n";
  test "extract gets value at position" (fun () ->
    assert_equal 9 (Store.extract (Store.create (fun i -> i * i) 3)));
  test "peek looks at other position" (fun () ->
    assert_equal 25 (Store.peek 5 (Store.create (fun i -> i * i) 3)));
  test "pos returns current position" (fun () ->
    assert_equal 3 (Store.pos (Store.create (fun i -> i * i) 3)));
  test "seek moves to new position" (fun () ->
    assert_equal 49 (Store.extract (Store.seek 7 (Store.create (fun i -> i * i) 3))));
  test "seeks modifies position" (fun () ->
    assert_equal 25 (Store.extract (Store.seeks (( + ) 2) (Store.create (fun i -> i * i) 3))));
  test "peeks applies function to position" (fun () ->
    assert_equal 25 (Store.peeks (( + ) 2) (Store.create (fun i -> i * i) 3)));
  test "experiment maps positions" (fun () ->
    assert_equal [40; 50; 60] (Store.experiment (fun p -> [p-1; p; p+1]) (Store.create (fun i -> i * 10) 5)));
  test "extend creates new store" (fun () ->
    let avg = Store.extend (fun s ->
      List.fold_left (+.) 0.0 (Store.experiment (fun p -> [p-1; p; p+1]) s) /. 3.0
    ) (Store.create (fun i -> float_of_int i) 5) in
    assert_float_equal 5.0 (Store.extract avg));
  test "law: extract (extend extract) = extract" (fun () ->
    let s = Store.create (fun i -> i * 3) 4 in
    assert_equal (Store.extract s) (Store.extract (Store.extend Store.extract s)));
  test "map transforms values" (fun () ->
    assert_equal 10 (Store.extract (Store.map (( * ) 2) (Store.create Fun.id 5))));

  Printf.printf "\nStream Comonad:\n";
  test "extract gets head" (fun () ->
    assert_equal 0 (Stream.extract (Stream.iterate (( + ) 1) 0)));
  test "take gets first n" (fun () ->
    assert_equal [0;1;2;3;4] (Stream.take 5 (Stream.iterate (( + ) 1) 0)));
  test "nth gets element" (fun () ->
    assert_equal 10 (Stream.nth 10 (Stream.iterate (( + ) 1) 0)));
  test "map transforms" (fun () ->
    assert_equal [0;2;4;6;8] (Stream.take 5 (Stream.map (( * ) 2) (Stream.iterate (( + ) 1) 0))));
  test "unfold fibonacci" (fun () ->
    assert_equal [0;1;1;2;3;5;8;13] (Stream.take 8 (Stream.unfold (fun (a,b) -> (a,(b,a+b))) (0,1))));
  test "zip_with combines" (fun () ->
    assert_equal [11;13;15;17;19] (Stream.take 5 (Stream.zip_with (+) (Stream.iterate ((+)1) 1) (Stream.iterate ((+)1) 10))));
  test "scan accumulates" (fun () ->
    assert_equal [1;2;3;4;5] (Stream.take 5 (Stream.scan (+) 0 (Stream.iterate Fun.id 1))));
  test "drop skips" (fun () ->
    assert_equal 5 (Stream.extract (Stream.drop 5 (Stream.iterate (( + ) 1) 0))));
  test "extend at each position" (fun () ->
    let ps = Stream.extend (fun s -> Stream.extract s + Stream.nth 1 s) (Stream.iterate ((+)1) 0) in
    assert_equal [1;3;5;7;9] (Stream.take 5 ps));
  test "law: extend extract preserves" (fun () ->
    let s = Stream.iterate ((+)1) 0 in
    assert_equal (Stream.take 10 s) (Stream.take 10 (Stream.extend Stream.extract s)));

  Printf.printf "\nZipper1D Comonad:\n";
  test "extract gets focus" (fun () ->
    assert_equal 3 (Zipper1D.extract (Zipper1D.create [2;1] 3 [4;5])));
  test "move_left shifts" (fun () ->
    assert_equal 2 (Zipper1D.extract (Zipper1D.move_left 0 (Zipper1D.create [2;1] 3 [4;5]))));
  test "move_right shifts" (fun () ->
    assert_equal 4 (Zipper1D.extract (Zipper1D.move_right 0 (Zipper1D.create [2;1] 3 [4;5]))));
  test "move_left boundary" (fun () ->
    assert_equal 0 (Zipper1D.extract (Zipper1D.move_left 0 (Zipper1D.create [] 3 [4;5]))));
  test "to_list reconstructs" (fun () ->
    assert_equal [1;2;3;4;5] (Zipper1D.to_list (Zipper1D.create [2;1] 3 [4;5])));
  test "of_list creates zipper" (fun () ->
    let z = Zipper1D.of_list 0 [1;2;3] in
    assert_equal 1 (Zipper1D.extract z); assert_equal [1;2;3] (Zipper1D.to_list z));
  test "map transforms" (fun () ->
    assert_equal [10;20;30;40;50] (Zipper1D.to_list (Zipper1D.map (( * ) 10) (Zipper1D.create [2;1] 3 [4;5]))));
  test "extend computes from context" (fun () ->
    let sums = Zipper1D.extend (fun z ->
      let l = match Zipper1D.left z with x::_ -> x | [] -> 0 in
      let r = match Zipper1D.right z with x::_ -> x | [] -> 0 in
      l + Zipper1D.extract z + r) (Zipper1D.create [2;1] 3 [4;5]) in
    assert_equal 9 (Zipper1D.extract sums));

  Printf.printf "\nCellular Automaton:\n";
  test "Rule 110 pattern" (fun () ->
    let gs = CellularAutomaton.run 110 11 3 in
    assert_equal 4 (List.length gs);
    let s = CellularAutomaton.render (List.hd gs) in
    assert_equal '#' s.[String.length s / 2]);
  test "Rule 30 evolves" (fun () ->
    assert_equal 2 (List.length (CellularAutomaton.run 30 11 1)));
  test "10 generations" (fun () ->
    assert_equal 11 (List.length (CellularAutomaton.run 110 21 10)));

  Printf.printf "\nSpreadsheet:\n";
  test "numeric cells" (fun () ->
    let s = Spreadsheet.create_sheet [|[|Spreadsheet.Num 1.0; Spreadsheet.Num 2.0|]|] in
    assert_float_equal 1.0 (Spreadsheet.eval_cell s));
  test "formula cells" (fun () ->
    let d = [|[|Spreadsheet.Num 10.0; Spreadsheet.Num 20.0|];
              [|Spreadsheet.Formula ((fun get -> get(0,0) +. get(0,1)),[(0,0);(0,1)]); Spreadsheet.Num 0.0|]|] in
    assert_float_equal 30.0 (Spreadsheet.eval_all (Spreadsheet.create_sheet d) 2 2).(1).(0));

  Printf.printf "\nMoving Average:\n";
  test "smooths data" (fun () ->
    let r = MovingAverage.run [|1.0;2.0;3.0;4.0;5.0;6.0;7.0;8.0;9.0;10.0|] 3 in
    assert_float_equal 2.0 r.(1); assert_float_equal 3.0 r.(2));

  Printf.printf "\nGame of Life:\n";
  test "glider creates grid" (fun () ->
    assert_equal 5 (List.length (GameOfLife.render (GameOfLife.glider ()))));
  test "glider evolves" (fun () ->
    assert_equal 5 (List.length (GameOfLife.render (GameOfLife.evolve (GameOfLife.glider ())))));
  test "dead stays dead" (fun () ->
    let g = Zipper2D.of_grid false [[false;false;false];[false;false;false];[false;false;false]] in
    List.iter (List.iter (fun c -> assert_equal false c)) (Zipper2D.to_grid (GameOfLife.evolve g)));

  Printf.printf "\nRunning Stats:\n";
  test "fibonacci" (fun () ->
    assert_equal [0;1;1;2;3;5;8] (Stream.take 7 RunningStats.fibonacci));
  test "naturals" (fun () ->
    assert_equal [0;1;2;3;4] (Stream.take 5 RunningStats.naturals));
  test "squares" (fun () ->
    assert_equal [0;1;4;9;16] (Stream.take 5 RunningStats.squares));
  test "cumulative sum" (fun () ->
    assert_equal [1.0;2.0;3.0;4.0;5.0]
      (Stream.take 5 (RunningStats.cumulative_sum (Stream.unfold (fun () -> (1.0,())) ()))));

  Printf.printf "\nZipper2D:\n";
  test "extract focused" (fun () ->
    assert_equal 1 (Zipper2D.extract (Zipper2D.of_grid 0 [[1;2];[3;4]])));
  test "move_right" (fun () ->
    assert_equal 2 (Zipper2D.extract (Zipper2D.move_right 0 (Zipper2D.of_grid 0 [[1;2];[3;4]]))));
  test "move_down" (fun () ->
    assert_equal 3 (Zipper2D.extract (Zipper2D.move_down 0 (Zipper2D.of_grid 0 [[1;2];[3;4]]))));
  test "to_grid roundtrip" (fun () ->
    assert_equal [[1;2];[3;4]] (Zipper2D.to_grid (Zipper2D.of_grid 0 [[1;2];[3;4]])));
  test "map all cells" (fun () ->
    assert_equal [[10;20];[30;40]] (Zipper2D.to_grid (Zipper2D.map (( * )10) (Zipper2D.of_grid 0 [[1;2];[3;4]]))));

  Printf.printf "\nComonad Laws:\n";
  test "Store: extract . extend f = f" (fun () ->
    let s = Store.create float_of_int 5 in let f s = Store.extract s *. 2.0 +. 1.0 in
    assert_float_equal (f s) (Store.extract (Store.extend f s)));

  Printf.printf "\n=== Results: %d passed, %d failed ===\n" !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
