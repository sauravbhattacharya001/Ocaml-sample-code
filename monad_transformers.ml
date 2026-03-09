(* ================================================================== *)
(*  Monad Transformers                                                *)
(*  Composable monad stacks: StateT, ReaderT, WriterT, ExceptT,      *)
(*  OptionT, ListT, ContT with lift, layered stacking, and runners   *)
(* ================================================================== *)

(* ---- Module types ---- *)

module type MONAD = sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
end

module type MONOID = sig
  type t
  val empty : t
  val append : t -> t -> t
end

(* ---- Identity Monad ---- *)

module Identity : sig
  include MONAD
  val run : 'a t -> 'a
end = struct
  type 'a t = 'a
  let return x = x
  let bind m f = f m
  let map f m = f m
  let run m = m
end

(* ---- Option Monad ---- *)

module OptionM : sig
  include MONAD with type 'a t = 'a option
end = struct
  type 'a t = 'a option
  let return x = Some x
  let bind m f = match m with None -> None | Some x -> f x
  let map f m = match m with None -> None | Some x -> Some (f x)
end

(* ---- Result Monad ---- *)

module ResultM : sig
  type 'a t = ('a, string) result
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val fail : string -> 'a t
end = struct
  type 'a t = ('a, string) result
  let return x = Ok x
  let bind m f = match m with Error e -> Error e | Ok x -> f x
  let map f m = match m with Error e -> Error e | Ok x -> Ok (f x)
  let fail e = Error e
end

(* ---- List Monad ---- *)

module ListM : sig
  include MONAD with type 'a t = 'a list
end = struct
  type 'a t = 'a list
  let return x = [x]
  let bind m f = List.concat_map f m
  let map f m = List.map f m
end

(* ================================================================== *)
(*  OptionT - adds optional failure to any monad                      *)
(* ================================================================== *)

module OptionT (M : MONAD) : sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift : 'a M.t -> 'a t
  val none : 'a t
  val run : 'a t -> 'a option M.t
  val of_option : 'a option -> 'a t
  val get_or : 'a -> 'a t -> 'a M.t
  val filter : ('a -> bool) -> 'a t -> 'a t
  val or_else : 'a t -> 'a t -> 'a t
end = struct
  type 'a t = 'a option M.t

  let return x = M.return (Some x)
  let bind m f =
    M.bind m (function
      | None -> M.return None
      | Some x -> f x)
  let map f m =
    M.map (function None -> None | Some x -> Some (f x)) m
  let lift m = M.map (fun x -> Some x) m
  let none = M.return None
  let run m = m
  let of_option = function
    | Some x -> return x
    | None -> none
  let get_or default m =
    M.map (function None -> default | Some x -> x) m
  let filter pred m =
    M.map (function
      | Some x when pred x -> Some x
      | _ -> None) m
  let or_else m1 m2 =
    M.bind m1 (function
      | Some _ as r -> M.return r
      | None -> m2)
end

(* ================================================================== *)
(*  ExceptT - adds error handling to any monad                        *)
(* ================================================================== *)

module ExceptT (M : MONAD) : sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift : 'a M.t -> 'a t
  val throw : string -> 'a t
  val catch : 'a t -> (string -> 'a t) -> 'a t
  val run : 'a t -> ('a, string) result M.t
  val of_result : ('a, string) result -> 'a t
  val map_error : (string -> string) -> 'a t -> 'a t
  val ensure : bool -> string -> unit t
end = struct
  type 'a t = ('a, string) result M.t

  let return x = M.return (Ok x)
  let bind m f =
    M.bind m (function
      | Error e -> M.return (Error e)
      | Ok x -> f x)
  let map f m =
    M.map (function Error e -> Error e | Ok x -> Ok (f x)) m
  let lift m = M.map (fun x -> Ok x) m
  let throw e = M.return (Error e)
  let catch m handler =
    M.bind m (function
      | Ok _ as r -> M.return r
      | Error e -> handler e)
  let run m = m
  let of_result r = M.return r
  let map_error f m =
    M.map (function Error e -> Error (f e) | Ok _ as r -> r) m
  let ensure cond msg =
    if cond then return () else throw msg
end

(* ================================================================== *)
(*  ReaderT - adds read-only environment to any monad                 *)
(* ================================================================== *)

module ReaderT (E : sig type t end) (M : MONAD) : sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift : 'a M.t -> 'a t
  val ask : E.t t
  val asks : (E.t -> 'a) -> 'a t
  val local : (E.t -> E.t) -> 'a t -> 'a t
  val run : E.t -> 'a t -> 'a M.t
end = struct
  type 'a t = E.t -> 'a M.t

  let return x = fun _env -> M.return x
  let bind m f = fun env ->
    M.bind (m env) (fun x -> f x env)
  let map f m = fun env ->
    M.map f (m env)
  let lift m = fun _env -> m
  let ask = fun env -> M.return env
  let asks f = fun env -> M.return (f env)
  let local f m = fun env -> m (f env)
  let run env m = m env
end

(* ================================================================== *)
(*  WriterT - adds accumulated output to any monad                    *)
(* ================================================================== *)

module WriterT (W : MONOID) (M : MONAD) : sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift : 'a M.t -> 'a t
  val tell : W.t -> unit t
  val listen : 'a t -> ('a * W.t) t
  val censor : (W.t -> W.t) -> 'a t -> 'a t
  val run : 'a t -> ('a * W.t) M.t
end = struct
  type 'a t = ('a * W.t) M.t

  let return x = M.return (x, W.empty)
  let bind m f =
    M.bind m (fun (x, w1) ->
      M.map (fun (y, w2) -> (y, W.append w1 w2)) (f x))
  let map f m =
    M.map (fun (x, w) -> (f x, w)) m
  let lift m = M.map (fun x -> (x, W.empty)) m
  let tell w = M.return ((), w)
  let listen m = M.map (fun (x, w) -> ((x, w), w)) m
  let censor f m = M.map (fun (x, w) -> (x, f w)) m
  let run m = m
end

(* ================================================================== *)
(*  StateT - adds mutable state to any monad                          *)
(* ================================================================== *)

module StateT (S : sig type t end) (M : MONAD) : sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift : 'a M.t -> 'a t
  val get : S.t t
  val put : S.t -> unit t
  val modify : (S.t -> S.t) -> unit t
  val gets : (S.t -> 'a) -> 'a t
  val run : S.t -> 'a t -> ('a * S.t) M.t
  val eval : S.t -> 'a t -> 'a M.t
  val exec : S.t -> 'a t -> S.t M.t
end = struct
  type 'a t = S.t -> ('a * S.t) M.t

  let return x = fun s -> M.return (x, s)
  let bind m f = fun s ->
    M.bind (m s) (fun (x, s') -> f x s')
  let map f m = fun s ->
    M.map (fun (x, s') -> (f x, s')) (m s)
  let lift m = fun s ->
    M.map (fun x -> (x, s)) m
  let get = fun s -> M.return (s, s)
  let put s = fun _s -> M.return ((), s)
  let modify f = fun s -> M.return ((), f s)
  let gets f = fun s -> M.return (f s, s)
  let run s m = m s
  let eval s m = M.map fst (m s)
  let exec s m = M.map snd (m s)
end

(* ================================================================== *)
(*  ContT - continuation passing transform                            *)
(* ================================================================== *)

module ContT (M : MONAD) : sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift : 'a M.t -> 'a t
  val callcc : (('a -> 'b t) -> 'a t) -> 'a t
  val run : ('a -> 'a M.t) -> 'a t -> 'a M.t
  val run_identity : 'a t -> 'a M.t
end = struct
  (* 'a t = forall r. ('a -> r M.t) -> r M.t -- but OCaml needs a concrete type *)
  (* We fix the answer type to be the same as the result type for simplicity *)
  type 'a t = { run : 'r. ('a -> 'r M.t) -> 'r M.t }

  let return x = { run = fun k -> k x }
  let bind m f = { run = fun k -> m.run (fun a -> (f a).run k) }
  let map f m = { run = fun k -> m.run (fun a -> k (f a)) }
  let lift m = { run = fun k -> M.bind m k }
  let callcc f =
    { run = fun k ->
        let exit a = { run = fun _k' -> k a } in
        (f exit).run k }
  let run k m = m.run k
  let run_identity m = m.run M.return
end

(* ================================================================== *)
(*  ListT - nondeterminism transformer                                *)
(* ================================================================== *)

module ListT (M : MONAD) : sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift : 'a M.t -> 'a t
  val empty : 'a t
  val append : 'a t -> 'a t -> 'a t
  val of_list : 'a list -> 'a t
  val run : 'a t -> 'a list M.t
  val filter : ('a -> bool) -> 'a t -> 'a t
  val guard : bool -> unit t
end = struct
  type 'a t = 'a list M.t

  let return x = M.return [x]
  let bind m f =
    M.bind m (fun xs ->
      let rec go = function
        | [] -> M.return []
        | x :: rest ->
          M.bind (f x) (fun ys ->
            M.map (fun zs -> ys @ zs) (go rest))
      in go xs)
  let map f m = M.map (List.map f) m
  let lift m = M.map (fun x -> [x]) m
  let empty = M.return []
  let append m1 m2 = M.bind m1 (fun xs -> M.map (fun ys -> xs @ ys) m2)
  let of_list xs = M.return xs
  let run m = m
  let filter pred m = M.map (List.filter pred) m
  let guard b = if b then return () else empty
end

(* ================================================================== *)
(*  RWST - combined Reader + Writer + State transformer               *)
(* ================================================================== *)

module RWST (R : sig type t end) (W : MONOID) (S : sig type t end) (M : MONAD) : sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift : 'a M.t -> 'a t
  val ask : R.t t
  val asks : (R.t -> 'a) -> 'a t
  val local : (R.t -> R.t) -> 'a t -> 'a t
  val tell : W.t -> unit t
  val get : S.t t
  val put : S.t -> unit t
  val modify : (S.t -> S.t) -> unit t
  val run : R.t -> S.t -> 'a t -> ('a * S.t * W.t) M.t
end = struct
  type 'a t = R.t -> S.t -> ('a * S.t * W.t) M.t

  let return x = fun _r s -> M.return (x, s, W.empty)
  let bind m f = fun r s ->
    M.bind (m r s) (fun (a, s', w1) ->
      M.map (fun (b, s'', w2) -> (b, s'', W.append w1 w2)) (f a r s'))
  let map f m = fun r s ->
    M.map (fun (a, s', w) -> (f a, s', w)) (m r s)
  let lift m = fun _r s ->
    M.map (fun x -> (x, s, W.empty)) m
  let ask = fun r s -> M.return (r, s, W.empty)
  let asks f = fun r s -> M.return (f r, s, W.empty)
  let local f m = fun r s -> m (f r) s
  let tell w = fun _r s -> M.return ((), s, w)
  let get = fun _r s -> M.return (s, s, W.empty)
  let put s = fun _r _s -> M.return ((), s, W.empty)
  let modify f = fun _r s -> M.return ((), f s, W.empty)
  let run r s m = m r s
end

(* ================================================================== *)
(*  Concrete stacked transformer examples                             *)
(* ================================================================== *)

(* StateT over Option: stateful computation that can fail *)
module StateOption = struct
  module S = StateT (struct type t = int end) (OptionM)

  let safe_div a b =
    if b = 0 then
      S.lift None
    else
      S.return (a / b)

  let counter_with_div () =
    S.bind S.get (fun s ->
    S.bind (safe_div s 2) (fun half ->
    S.bind (S.put half) (fun () ->
    S.return half)))

  let run_example () =
    (* Start with state 10, divide by 2 *)
    match S.run 10 (counter_with_div ()) with
    | Some (result, state) -> Some (result, state)  (* Some (5, 5) *)
    | None -> None
end

(* ReaderT over Result: config-dependent computation with errors *)
module ReaderResult = struct
  type config = { max_value : int; prefix : string }

  module R = ReaderT (struct type t = config end) (ResultM)

  let validate_value v =
    R.bind R.ask (fun cfg ->
    if v > cfg.max_value then
      R.lift (ResultM.fail (Printf.sprintf "Value %d exceeds max %d" v cfg.max_value))
    else
      R.return (Printf.sprintf "%s_%d" cfg.prefix v))

  let run_example () =
    let cfg = { max_value = 100; prefix = "item" } in
    R.run cfg (validate_value 42)  (* Ok "item_42" *)
end

(* WriterT over Identity: pure logging *)
module WriterLog = struct
  module Log = struct
    type t = string list
    let empty = []
    let append = (@)
  end

  module W = WriterT (Log) (Identity)

  let factorial n =
    let rec go acc = function
      | 0 ->
        W.bind (W.tell ["  base case reached"]) (fun () ->
        W.return acc)
      | k ->
        W.bind (W.tell [Printf.sprintf "  step: %d * %d" k acc]) (fun () ->
        go (acc * k) (k - 1))
    in
    W.bind (W.tell [Printf.sprintf "computing %d!" n]) (fun () ->
    go 1 n)

  let run_example () =
    Identity.run (W.run (factorial 5))
    (* (120, ["computing 5!"; "  step: 5 * 1"; ...]) *)
end

(* ExceptT over List: nondeterminism with failure *)
module ExceptList = struct
  module E = ExceptT (ListM)

  let safe_sqrt x =
    if x < 0 then E.throw "negative"
    else E.return (Float.of_int x |> Float.sqrt |> Float.to_int)

  let run_example () =
    E.run (
      E.bind (E.lift [4; -1; 9; 16]) (fun x ->
      E.bind (safe_sqrt x) (fun root ->
      E.return (x, root)))
    )
    (* [Ok (4,2); Error "negative"; Ok (9,3); Ok (16,4)] *)
end

(* ContT: early exit via callcc *)
module ContExample = struct
  module C = ContT (Identity)

  let find_first_negative xs =
    C.callcc (fun exit ->
      let rec go = function
        | [] -> C.return 0
        | x :: rest ->
          if x < 0 then exit x
          else C.bind (C.return ()) (fun () -> go rest)
      in go xs)

  let run_example () =
    Identity.run (C.run_identity (find_first_negative [1; 2; -3; 4]))
    (* -3 *)
end

(* RWST: combined reader+writer+state *)
module RWSExample = struct
  module LogW = struct
    type t = string list
    let empty = []
    let append = (@)
  end

  type env = { multiplier : int }

  module RWS = RWST
    (struct type t = env end)
    (LogW)
    (struct type t = int end)
    (Identity)

  let process_value v =
    RWS.bind RWS.ask (fun env ->
    RWS.bind RWS.get (fun acc ->
    let result = v * env.multiplier in
    RWS.bind (RWS.tell [Printf.sprintf "processed %d -> %d" v result]) (fun () ->
    RWS.bind (RWS.put (acc + result)) (fun () ->
    RWS.return result))))

  let run_example () =
    let env = { multiplier = 3 } in
    Identity.run (RWS.run env 0 (
      RWS.bind (process_value 10) (fun _ ->
      RWS.bind (process_value 20) (fun _ ->
      RWS.bind RWS.get (fun total ->
      RWS.return total)))))
    (* (90, 90, ["processed 10 -> 30"; "processed 20 -> 60"]) *)
end

(* ================================================================== *)
(*  ListT + StateT stacked: nondeterminism with state                 *)
(* ================================================================== *)

module ListState = struct
  module L = ListT (OptionM)

  let pythagorean_triples n =
    L.bind (L.of_list (List.init n (fun i -> i + 1))) (fun a ->
    L.bind (L.of_list (List.init n (fun i -> i + 1))) (fun b ->
    L.bind (L.of_list (List.init n (fun i -> i + 1))) (fun c ->
    L.bind (L.guard (a*a + b*b = c*c && a <= b)) (fun () ->
    L.return (a, b, c)))))

  let run_example () =
    L.run (pythagorean_triples 20)
    (* Some [(3,4,5); (5,12,13); (6,8,10); (8,15,17); (9,12,15)] *)
end

(* ================================================================== *)
(*  OptionT stacked examples                                          *)
(* ================================================================== *)

module OptionTExample = struct
  module O = OptionT (Identity)

  let safe_head = function
    | [] -> O.none
    | x :: _ -> O.return x

  let safe_tail = function
    | [] -> O.none
    | _ :: xs -> O.return xs

  let second_element xs =
    O.bind (safe_tail xs) (fun tl ->
    safe_head tl)

  let run_example () =
    Identity.run (O.run (second_element [1; 2; 3])),   (* Some 2 *)
    Identity.run (O.run (second_element [1])),          (* None *)
    Identity.run (O.run (second_element []))            (* None *)
end

(* ================================================================== *)
(*  Monad law verification helpers                                    *)
(* ================================================================== *)

module Laws = struct
  (* Left identity:  return a >>= f  ≡  f a *)
  let check_left_identity (type a b)
    (module M : MONAD with type 'a t = a)
    ~(return : int -> a) ~(bind : a -> (int -> a) -> a)
    ~(eq : a -> a -> bool) ~(f : int -> a) (x : int) =
    let _ = (module M : MONAD) in
    eq (bind (return x) f) (f x)

  (* Right identity: m >>= return  ≡  m *)
  let check_right_identity
    ~(return : int -> 'a) ~(bind : 'a -> (int -> 'a) -> 'a)
    ~(eq : 'a -> 'a -> bool) (m : 'a) =
    eq (bind m return) m

  (* Associativity: (m >>= f) >>= g  ≡  m >>= (fun x -> f x >>= g) *)
  let check_associativity
    ~(bind : 'a -> (int -> 'a) -> 'a)
    ~(eq : 'a -> 'a -> bool)
    ~(f : int -> 'a) ~(g : int -> 'a) (m : 'a) =
    eq (bind (bind m f) g) (bind m (fun x -> bind (f x) g))
end

(* ================================================================== *)
(*  Tests                                                             *)
(* ================================================================== *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let test name f =
    if f () then (incr passed; Printf.printf "  PASS: %s\n" name)
    else (incr failed; Printf.printf "  FAIL: %s\n" name) in

  Printf.printf "=== Monad Transformers Tests ===\n\n";

  (* Identity *)
  Printf.printf "-- Identity Monad --\n";
  test "return and run" (fun () ->
    Identity.run (Identity.return 42) = 42);
  test "bind" (fun () ->
    Identity.run (Identity.bind (Identity.return 3) (fun x -> Identity.return (x * 2))) = 6);
  test "map" (fun () ->
    Identity.run (Identity.map (fun x -> x + 1) (Identity.return 10)) = 11);

  (* OptionT *)
  Printf.printf "\n-- OptionT --\n";
  let module OT = OptionT (Identity) in
  test "return wraps in Some" (fun () ->
    Identity.run (OT.run (OT.return 42)) = Some 42);
  test "none is None" (fun () ->
    Identity.run (OT.run OT.none) = None);
  test "bind some-some" (fun () ->
    Identity.run (OT.run (OT.bind (OT.return 3) (fun x -> OT.return (x * 2)))) = Some 6);
  test "bind some-none" (fun () ->
    Identity.run (OT.run (OT.bind (OT.return 3) (fun _ -> OT.none))) = None);
  test "bind none-some" (fun () ->
    Identity.run (OT.run (OT.bind OT.none (fun x -> OT.return (x + 1)))) = None);
  test "map some" (fun () ->
    Identity.run (OT.run (OT.map (fun x -> x * 3) (OT.return 5))) = Some 15);
  test "map none" (fun () ->
    Identity.run (OT.run (OT.map (fun x -> x + 1) OT.none)) = None);
  test "lift" (fun () ->
    Identity.run (OT.run (OT.lift (Identity.return 99))) = Some 99);
  test "of_option Some" (fun () ->
    Identity.run (OT.run (OT.of_option (Some 7))) = Some 7);
  test "of_option None" (fun () ->
    Identity.run (OT.run (OT.of_option None)) = None);
  test "get_or with Some" (fun () ->
    Identity.run (OT.get_or 0 (OT.return 5)) = 5);
  test "get_or with None" (fun () ->
    Identity.run (OT.get_or 0 OT.none) = 0);
  test "filter passing" (fun () ->
    Identity.run (OT.run (OT.filter (fun x -> x > 3) (OT.return 5))) = Some 5);
  test "filter failing" (fun () ->
    Identity.run (OT.run (OT.filter (fun x -> x > 3) (OT.return 1))) = None);
  test "or_else first succeeds" (fun () ->
    Identity.run (OT.run (OT.or_else (OT.return 1) (OT.return 2))) = Some 1);
  test "or_else first fails" (fun () ->
    Identity.run (OT.run (OT.or_else OT.none (OT.return 2))) = Some 2);

  (* ExceptT *)
  Printf.printf "\n-- ExceptT --\n";
  let module ET = ExceptT (Identity) in
  test "return wraps in Ok" (fun () ->
    Identity.run (ET.run (ET.return 42)) = Ok 42);
  test "throw wraps in Error" (fun () ->
    Identity.run (ET.run (ET.throw "oops")) = (Error "oops" : (int, string) result));
  test "bind ok-ok" (fun () ->
    Identity.run (ET.run (ET.bind (ET.return 3) (fun x -> ET.return (x + 1)))) = Ok 4);
  test "bind ok-err" (fun () ->
    Identity.run (ET.run (ET.bind (ET.return 3) (fun _ -> ET.throw "fail"))) = (Error "fail" : (int, string) result));
  test "bind err-ok" (fun () ->
    Identity.run (ET.run (ET.bind (ET.throw "fail") (fun x -> ET.return (x + 1)))) = (Error "fail" : (int, string) result));
  test "map ok" (fun () ->
    Identity.run (ET.run (ET.map (fun x -> x * 2) (ET.return 5))) = Ok 10);
  test "map err" (fun () ->
    Identity.run (ET.run (ET.map (fun x -> x * 2) (ET.throw "e"))) = (Error "e" : (int, string) result));
  test "lift" (fun () ->
    Identity.run (ET.run (ET.lift (Identity.return 7))) = Ok 7);
  test "catch with ok" (fun () ->
    Identity.run (ET.run (ET.catch (ET.return 5) (fun _ -> ET.return 0))) = Ok 5);
  test "catch with err" (fun () ->
    Identity.run (ET.run (ET.catch (ET.throw "x") (fun e -> ET.return (String.length e)))) = Ok 1);
  test "of_result Ok" (fun () ->
    Identity.run (ET.run (ET.of_result (Ok 42))) = Ok 42);
  test "of_result Error" (fun () ->
    Identity.run (ET.run (ET.of_result (Error "bad"))) = (Error "bad" : (int, string) result));
  test "map_error" (fun () ->
    Identity.run (ET.run (ET.map_error (fun e -> "wrapped: " ^ e) (ET.throw "x"))) = (Error "wrapped: x" : (int, string) result));
  test "ensure true" (fun () ->
    Identity.run (ET.run (ET.ensure true "msg")) = Ok ());
  test "ensure false" (fun () ->
    Identity.run (ET.run (ET.ensure false "msg")) = Error "msg");

  (* ReaderT *)
  Printf.printf "\n-- ReaderT --\n";
  let module RT = ReaderT (struct type t = int end) (Identity) in
  test "return ignores env" (fun () ->
    Identity.run (RT.run 999 (RT.return 42)) = 42);
  test "ask returns env" (fun () ->
    Identity.run (RT.run 7 RT.ask) = 7);
  test "asks projects env" (fun () ->
    Identity.run (RT.run 10 (RT.asks (fun x -> x * 2))) = 20);
  test "bind" (fun () ->
    Identity.run (RT.run 5 (RT.bind RT.ask (fun e -> RT.return (e + 1)))) = 6);
  test "local modifies env" (fun () ->
    Identity.run (RT.run 10 (RT.local (fun x -> x * 3) RT.ask)) = 30);
  test "lift" (fun () ->
    Identity.run (RT.run 0 (RT.lift (Identity.return 99))) = 99);
  test "map" (fun () ->
    Identity.run (RT.run 5 (RT.map (fun x -> x + 10) RT.ask)) = 15);

  (* WriterT *)
  Printf.printf "\n-- WriterT --\n";
  let module LogM = struct type t = string list let empty = [] let append = (@) end in
  let module WT = WriterT (LogM) (Identity) in
  test "return with empty log" (fun () ->
    Identity.run (WT.run (WT.return 42)) = (42, []));
  test "tell appends" (fun () ->
    Identity.run (WT.run (WT.tell ["hello"])) = ((), ["hello"]));
  test "bind accumulates log" (fun () ->
    Identity.run (WT.run (
      WT.bind (WT.tell ["a"]) (fun () ->
      WT.bind (WT.tell ["b"]) (fun () ->
      WT.return 1)))) = (1, ["a"; "b"]));
  test "listen" (fun () ->
    Identity.run (WT.run (WT.listen (
      WT.bind (WT.tell ["x"]) (fun () -> WT.return 5)
    ))) = ((5, ["x"]), ["x"]));
  test "censor" (fun () ->
    Identity.run (WT.run (WT.censor List.rev (
      WT.bind (WT.tell ["a"]) (fun () ->
      WT.bind (WT.tell ["b"]) (fun () ->
      WT.return 0))
    ))) = (0, ["b"; "a"]));
  test "lift" (fun () ->
    Identity.run (WT.run (WT.lift (Identity.return 7))) = (7, []));
  test "map" (fun () ->
    Identity.run (WT.run (WT.map (fun x -> x + 1) (WT.return 10))) = (11, []));

  (* StateT *)
  Printf.printf "\n-- StateT --\n";
  let module ST = StateT (struct type t = int end) (Identity) in
  test "return preserves state" (fun () ->
    Identity.run (ST.run 0 (ST.return 42)) = (42, 0));
  test "get returns state" (fun () ->
    Identity.run (ST.run 7 ST.get) = (7, 7));
  test "put sets state" (fun () ->
    Identity.run (ST.run 0 (ST.put 99)) = ((), 99));
  test "modify transforms state" (fun () ->
    Identity.run (ST.run 5 (ST.modify (fun x -> x * 2))) = ((), 10));
  test "gets projects state" (fun () ->
    Identity.run (ST.run 3 (ST.gets (fun x -> x + 10))) = (13, 3));
  test "eval drops state" (fun () ->
    Identity.run (ST.eval 5 (ST.return 42)) = 42);
  test "exec drops value" (fun () ->
    Identity.run (ST.exec 5 (ST.put 10)) = 10);
  test "bind threads state" (fun () ->
    Identity.run (ST.run 0 (
      ST.bind (ST.put 10) (fun () ->
      ST.bind ST.get (fun s ->
      ST.bind (ST.put (s + 5)) (fun () ->
      ST.return s))))) = (10, 15));
  test "lift" (fun () ->
    Identity.run (ST.run 0 (ST.lift (Identity.return 42))) = (42, 0));
  test "map" (fun () ->
    Identity.run (ST.run 0 (ST.map (fun x -> x * 2) (ST.return 7))) = (14, 0));

  (* ContT *)
  Printf.printf "\n-- ContT --\n";
  let module CT = ContT (Identity) in
  test "return" (fun () ->
    Identity.run (CT.run_identity (CT.return 42)) = 42);
  test "bind" (fun () ->
    Identity.run (CT.run_identity (CT.bind (CT.return 3) (fun x -> CT.return (x + 1)))) = 4);
  test "map" (fun () ->
    Identity.run (CT.run_identity (CT.map (fun x -> x * 2) (CT.return 5))) = 10);
  test "lift" (fun () ->
    Identity.run (CT.run_identity (CT.lift (Identity.return 99))) = 99);
  test "callcc early exit" (fun () ->
    Identity.run (CT.run_identity (ContExample.find_first_negative [1; 2; -3; 4])) = -3);
  test "callcc no exit" (fun () ->
    Identity.run (CT.run_identity (ContExample.find_first_negative [1; 2; 3])) = 0);

  (* ListT *)
  Printf.printf "\n-- ListT --\n";
  let module LT = ListT (Identity) in
  test "return" (fun () ->
    Identity.run (LT.run (LT.return 5)) = [5]);
  test "empty" (fun () ->
    Identity.run (LT.run LT.empty) = ([] : int list));
  test "bind" (fun () ->
    Identity.run (LT.run (LT.bind (LT.of_list [1;2;3]) (fun x -> LT.return (x * 10)))) = [10;20;30]);
  test "guard true" (fun () ->
    Identity.run (LT.run (LT.guard true)) = [()]);
  test "guard false" (fun () ->
    Identity.run (LT.run (LT.guard false)) = ([] : unit list));
  test "filter" (fun () ->
    Identity.run (LT.run (LT.filter (fun x -> x > 2) (LT.of_list [1;2;3;4]))) = [3;4]);
  test "append" (fun () ->
    Identity.run (LT.run (LT.append (LT.of_list [1;2]) (LT.of_list [3;4]))) = [1;2;3;4]);
  test "map" (fun () ->
    Identity.run (LT.run (LT.map (fun x -> x + 1) (LT.of_list [10;20]))) = [11;21]);
  test "lift" (fun () ->
    Identity.run (LT.run (LT.lift (Identity.return 42))) = [42]);

  (* StateOption example *)
  Printf.printf "\n-- StateOption (stacked) --\n";
  test "counter_with_div success" (fun () ->
    StateOption.run_example () = Some (5, 5));
  test "counter_with_div zero" (fun () ->
    let module S = StateT (struct type t = int end) (OptionM) in
    S.run 0 (StateOption.counter_with_div ()) = None);

  (* ReaderResult example *)
  Printf.printf "\n-- ReaderResult (stacked) --\n";
  test "validate under max" (fun () ->
    ReaderResult.run_example () = Ok "item_42");
  test "validate over max" (fun () ->
    let module R = ReaderT (struct type t = ReaderResult.config end) (ResultM) in
    let cfg = ReaderResult.{ max_value = 10; prefix = "x" } in
    R.run cfg (ReaderResult.validate_value 42) = Error "Value 42 exceeds max 10");

  (* WriterLog example *)
  Printf.printf "\n-- WriterLog (stacked) --\n";
  test "factorial 5" (fun () ->
    let (result, _log) = Identity.run (WriterLog.W.run (WriterLog.factorial 5)) in
    result = 120);
  test "factorial 0" (fun () ->
    let (result, log) = Identity.run (WriterLog.W.run (WriterLog.factorial 0)) in
    result = 1 && List.length log = 2);

  (* ExceptList example *)
  Printf.printf "\n-- ExceptList (stacked) --\n";
  test "safe_sqrt results" (fun () ->
    let results = ExceptList.run_example () in
    List.length results = 4 &&
    List.nth results 0 = Ok (4, 2) &&
    List.nth results 1 = Error "negative" &&
    List.nth results 2 = Ok (9, 3) &&
    List.nth results 3 = Ok (16, 4));

  (* ContExample *)
  Printf.printf "\n-- ContExample --\n";
  test "find first negative" (fun () ->
    ContExample.run_example () = -3);

  (* RWST *)
  Printf.printf "\n-- RWST --\n";
  test "RWS combined" (fun () ->
    let (total, state, log) = Identity.run (
      let module RWS = RWSExample.RWS in
      RWSExample.RWS.run { RWSExample.multiplier = 3 } 0 (
        RWS.bind (RWSExample.process_value 10) (fun _ ->
        RWS.bind (RWSExample.process_value 20) (fun _ ->
        RWS.bind RWS.get (fun total ->
        RWS.return total))))) in
    total = 90 && state = 90 && List.length log = 2);

  (* ListState pythagorean triples *)
  Printf.printf "\n-- ListT nondeterminism --\n";
  test "pythagorean triples" (fun () ->
    match ListState.run_example () with
    | Some triples ->
      List.mem (3,4,5) triples &&
      List.mem (5,12,13) triples &&
      List.for_all (fun (a,b,c) -> a*a + b*b = c*c) triples
    | None -> false);

  (* OptionT example *)
  Printf.printf "\n-- OptionT example --\n";
  test "second element of [1;2;3]" (fun () ->
    let (a, b, c) = OptionTExample.run_example () in
    a = Some 2 && b = None && c = None);

  (* Monad laws for Identity *)
  Printf.printf "\n-- Monad Laws (Identity) --\n";
  test "left identity" (fun () ->
    Laws.check_left_identity (module Identity)
      ~return:Identity.return ~bind:Identity.bind
      ~eq:(=) ~f:(fun x -> Identity.return (x * 2)) 7);
  test "right identity" (fun () ->
    Laws.check_right_identity
      ~return:Identity.return ~bind:Identity.bind
      ~eq:(=) (Identity.return 42));
  test "associativity" (fun () ->
    Laws.check_associativity
      ~bind:Identity.bind ~eq:(=)
      ~f:(fun x -> Identity.return (x + 1))
      ~g:(fun x -> Identity.return (x * 2))
      (Identity.return 5));

  (* Monad laws for OptionM *)
  Printf.printf "\n-- Monad Laws (Option) --\n";
  test "left identity" (fun () ->
    Laws.check_left_identity (module OptionM)
      ~return:OptionM.return ~bind:OptionM.bind
      ~eq:(=) ~f:(fun x -> OptionM.return (x * 2)) 7);
  test "right identity" (fun () ->
    Laws.check_right_identity
      ~return:OptionM.return ~bind:OptionM.bind
      ~eq:(=) (OptionM.return 42));
  test "associativity" (fun () ->
    Laws.check_associativity
      ~bind:OptionM.bind ~eq:(=)
      ~f:(fun x -> OptionM.return (x + 1))
      ~g:(fun x -> OptionM.return (x * 2))
      (OptionM.return 5));

  Printf.printf "\n=== Results: %d passed, %d failed ===\n" !passed !failed;
  if !failed > 0 then exit 1
