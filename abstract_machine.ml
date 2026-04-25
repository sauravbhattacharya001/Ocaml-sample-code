(* Abstract Machine Simulator
   Implements SECD, CEK, and Krivine abstract machines for lambda calculus.
   Features: step-by-step execution, environment/stack visualization,
   multiple evaluation strategies, 5 example programs, interactive REPL.
   Usage: ocaml abstract_machine.ml *)

(* ── Lambda Calculus AST ─────────────────────────────────────── *)

type expr =
  | Var of string
  | Lam of string * expr
  | App of expr * expr
  | Int of int
  | Add of expr * expr
  | Mul of expr * expr
  | If0 of expr * expr * expr
  | Let of string * expr * expr
  | Fix of string * expr  (* recursive binding *)

(* ── Pretty Printing ─────────────────────────────────────────── *)

let rec pp_expr = function
  | Var x -> x
  | Lam (x, body) -> Printf.sprintf "(λ%s. %s)" x (pp_expr body)
  | App (f, a) -> Printf.sprintf "(%s %s)" (pp_expr f) (pp_expr a)
  | Int n -> string_of_int n
  | Add (a, b) -> Printf.sprintf "(+ %s %s)" (pp_expr a) (pp_expr b)
  | Mul (a, b) -> Printf.sprintf "(* %s %s)" (pp_expr a) (pp_expr b)
  | If0 (c, t, e) -> Printf.sprintf "(if0 %s %s %s)" (pp_expr c) (pp_expr t) (pp_expr e)
  | Let (x, v, body) -> Printf.sprintf "(let %s = %s in %s)" x (pp_expr v) (pp_expr body)
  | Fix (x, body) -> Printf.sprintf "(fix %s. %s)" x (pp_expr body)

(* ── Parser ──────────────────────────────────────────────────── *)

module Parser = struct
  type token =
    | TLam | TDot | TLParen | TRParen | TIdent of string | TInt of int
    | TPlus | TStar | TIf0 | TLet | TEq | TIn | TFix

  let tokenize s =
    let buf = Buffer.create 16 in
    let tokens = ref [] in
    let i = ref 0 in
    let len = String.length s in
    let flush_ident () =
      if Buffer.length buf > 0 then begin
        let w = Buffer.contents buf in
        Buffer.clear buf;
        let tok = match w with
          | "lam" | "lambda" | "\\" -> TLam
          | "if0" -> TIf0
          | "let" -> TLet
          | "in" -> TIn
          | "fix" -> TFix
          | _ ->
            (try TInt (int_of_string w) with _ -> TIdent w)
        in
        tokens := tok :: !tokens
      end
    in
    while !i < len do
      let c = s.[!i] in
      (match c with
       | ' ' | '\t' | '\n' | '\r' -> flush_ident ()
       | '(' -> flush_ident (); tokens := TLParen :: !tokens
       | ')' -> flush_ident (); tokens := TRParen :: !tokens
       | '.' -> flush_ident (); tokens := TDot :: !tokens
       | '+' -> flush_ident (); tokens := TPlus :: !tokens
       | '*' -> flush_ident (); tokens := TStar :: !tokens
       | '=' -> flush_ident (); tokens := TEq :: !tokens
       | _ -> Buffer.add_char buf c);
      incr i
    done;
    flush_ident ();
    List.rev !tokens

  let parse_expr tokens =
    let toks = ref tokens in
    let peek () = match !toks with t :: _ -> Some t | [] -> None in
    let advance () = match !toks with _ :: rest -> toks := rest | [] -> () in
    let expect_tok () = match !toks with t :: rest -> toks := rest; t | [] -> failwith "Unexpected end" in
    let rec parse_atom () =
      match peek () with
      | Some (TInt n) -> advance (); Int n
      | Some (TIdent x) -> advance (); Var x
      | Some TLam ->
        advance ();
        let x = match expect_tok () with TIdent x -> x | _ -> failwith "Expected variable after lambda" in
        (match peek () with Some TDot -> advance () | _ -> ());
        let body = parse_full () in
        Lam (x, body)
      | Some TFix ->
        advance ();
        let x = match expect_tok () with TIdent x -> x | _ -> failwith "Expected variable after fix" in
        (match peek () with Some TDot -> advance () | _ -> ());
        let body = parse_full () in
        Fix (x, body)
      | Some TIf0 ->
        advance ();
        let c = parse_full () in
        let t = parse_full () in
        let e = parse_full () in
        If0 (c, t, e)
      | Some TLet ->
        advance ();
        let x = match expect_tok () with TIdent x -> x | _ -> failwith "Expected var" in
        (match peek () with Some TEq -> advance () | _ -> ());
        let v = parse_full () in
        (match peek () with Some TIn -> advance () | _ -> ());
        let body = parse_full () in
        Let (x, v, body)
      | Some TLParen ->
        advance ();
        (match peek () with
         | Some TPlus ->
           advance ();
           let a = parse_full () in
           let b = parse_full () in
           (match peek () with Some TRParen -> advance () | _ -> ());
           Add (a, b)
         | Some TStar ->
           advance ();
           let a = parse_full () in
           let b = parse_full () in
           (match peek () with Some TRParen -> advance () | _ -> ());
           Mul (a, b)
         | _ ->
           let e = parse_full () in
           (match peek () with Some TRParen -> advance (); e | _ ->
             (* application chain inside parens *)
             let rec apps acc =
               match peek () with
               | Some TRParen -> advance (); acc
               | None -> acc
               | _ -> let a = parse_atom () in apps (App (acc, a))
             in
             apps e))
      | _ -> failwith "Parse error"
    and parse_full () =
      let e = parse_atom () in
      let rec apps acc =
        match peek () with
        | Some (TInt _ | TIdent _ | TLParen) ->
          let a = parse_atom () in apps (App (acc, a))
        | _ -> acc
      in
      apps e
    in
    let result = parse_full () in
    result

  let parse s = parse_expr (tokenize s)
end

(* ── Substitution (for Krivine) ──────────────────────────────── *)

let counter = ref 0
let fresh base = incr counter; base ^ "_" ^ string_of_int !counter

let rec subst x v = function
  | Var y -> if y = x then v else Var y
  | Lam (y, _) as e when y = x -> e
  | Lam (y, body) ->
    let y' = fresh y in
    Lam (y', subst x v (subst y (Var y') body))
  | App (f, a) -> App (subst x v f, subst x v a)
  | Int n -> Int n
  | Add (a, b) -> Add (subst x v a, subst x v b)
  | Mul (a, b) -> Mul (subst x v a, subst x v b)
  | If0 (c, t, e) -> If0 (subst x v c, subst x v t, subst x v e)
  | Let (y, _, _) as e when y = x -> e
  | Let (y, ve, body) ->
    let y' = fresh y in
    Let (y', subst x v ve, subst x v (subst y (Var y') body))
  | Fix (y, _) as e when y = x -> e
  | Fix (y, body) ->
    let y' = fresh y in
    Fix (y', subst x v (subst y (Var y') body))

(* ══════════════════════════════════════════════════════════════ *)
(*  SECD Machine                                                  *)
(* ══════════════════════════════════════════════════════════════ *)

module SECD = struct
  type value =
    | VInt of int
    | VClosure of string * expr * env
    | VRecClosure of string * string * expr * env
  and env = (string * value) list

  type control =
    | CEval of expr
    | CApp
    | CAdd | CMul
    | CIf0 of expr * expr * env
    | CLet of string * expr * env

  type state = {
    stack: value list;
    env: env;
    control: control list;
    dump: (value list * env * control list) list;
  }

  let pp_value = function
    | VInt n -> string_of_int n
    | VClosure (x, body, _) -> Printf.sprintf "<closure λ%s. %s>" x (pp_expr body)
    | VRecClosure (f, x, body, _) -> Printf.sprintf "<rec-closure %s λ%s. %s>" f x (pp_expr body)

  let pp_stack stack =
    "[" ^ String.concat "; " (List.map pp_value stack) ^ "]"

  let pp_control = function
    | CEval e -> "eval(" ^ pp_expr e ^ ")"
    | CApp -> "app"
    | CAdd -> "add"
    | CMul -> "mul"
    | CIf0 _ -> "if0"
    | CLet (x, _, _) -> "let(" ^ x ^ ")"

  let pp_ctrl_list cl =
    "[" ^ String.concat "; " (List.map pp_control cl) ^ "]"

  let initial expr = {
    stack = [];
    env = [];
    control = [CEval expr];
    dump = [];
  }

  let step state =
    match state.control with
    | [] -> None
    | CEval (Int n) :: rest ->
      Some { state with stack = VInt n :: state.stack; control = rest }
    | CEval (Var x) :: rest ->
      let v = List.assoc x state.env in
      Some { state with stack = v :: state.stack; control = rest }
    | CEval (Lam (x, body)) :: rest ->
      Some { state with
             stack = VClosure (x, body, state.env) :: state.stack;
             control = rest }
    | CEval (Fix (f, Lam (x, body))) :: rest ->
      Some { state with
             stack = VRecClosure (f, x, body, state.env) :: state.stack;
             control = rest }
    | CEval (Fix _) :: _ -> failwith "Fix must wrap a lambda"
    | CEval (App (f, a)) :: rest ->
      Some { state with control = CEval a :: CEval f :: CApp :: rest }
    | CEval (Add (a, b)) :: rest ->
      Some { state with control = CEval a :: CEval b :: CAdd :: rest }
    | CEval (Mul (a, b)) :: rest ->
      Some { state with control = CEval a :: CEval b :: CMul :: rest }
    | CEval (If0 (c, t, e)) :: rest ->
      Some { state with control = CEval c :: CIf0 (t, e, state.env) :: rest }
    | CEval (Let (x, v, body)) :: rest ->
      Some { state with control = CEval v :: CLet (x, body, state.env) :: rest }
    | CApp :: rest ->
      (match state.stack with
       | arg :: VClosure (x, body, cenv) :: stack' ->
         Some { stack = [];
                env = (x, arg) :: cenv;
                control = [CEval body];
                dump = (stack', state.env, rest) :: state.dump }
       | arg :: VRecClosure (f, x, body, cenv) :: stack' ->
         let rec_v = VRecClosure (f, x, body, cenv) in
         Some { stack = [];
                env = (x, arg) :: (f, rec_v) :: cenv;
                control = [CEval body];
                dump = (stack', state.env, rest) :: state.dump }
       | _ -> failwith "SECD: bad application")
    | CAdd :: rest ->
      (match state.stack with
       | VInt b :: VInt a :: stack' ->
         Some { state with stack = VInt (a + b) :: stack'; control = rest }
       | _ -> failwith "SECD: add expects two ints")
    | CMul :: rest ->
      (match state.stack with
       | VInt b :: VInt a :: stack' ->
         Some { state with stack = VInt (a * b) :: stack'; control = rest }
       | _ -> failwith "SECD: mul expects two ints")
    | CIf0 (t, e, saved_env) :: rest ->
      (match state.stack with
       | VInt 0 :: stack' ->
         Some { state with stack = stack'; env = saved_env; control = CEval t :: rest }
       | VInt _ :: stack' ->
         Some { state with stack = stack'; env = saved_env; control = CEval e :: rest }
       | _ -> failwith "SECD: if0 expects int")
    | CLet (x, body, saved_env) :: rest ->
      (match state.stack with
       | v :: stack' ->
         Some { stack = [];
                env = (x, v) :: saved_env;
                control = [CEval body];
                dump = (stack', state.env, rest) :: state.dump }
       | _ -> failwith "SECD: let needs value")

  let return_from_dump state =
    match state.control, state.dump with
    | [], (stack', env', ctrl') :: dump' ->
      (match state.stack with
       | v :: _ ->
         Some { stack = v :: stack'; env = env'; control = ctrl'; dump = dump' }
       | [] -> None)
    | _ -> None

  let run ?(verbose=false) ?(max_steps=10000) expr =
    let st = ref (initial expr) in
    let steps = ref 0 in
    let continue_running = ref true in
    while !continue_running && !steps < max_steps do
      if verbose then
        Printf.printf "  [%d] S=%s C=%s\n" !steps
          (pp_stack !st.stack) (pp_ctrl_list !st.control);
      match step !st with
      | Some st' -> st := st'; incr steps
      | None ->
        (match return_from_dump !st with
         | Some st' -> st := st'; incr steps
         | None -> continue_running := false)
    done;
    if verbose then
      Printf.printf "  [%d] S=%s (final)\n" !steps (pp_stack !st.stack);
    match !st.stack with
    | v :: _ -> (v, !steps)
    | [] -> failwith "SECD: empty stack at end"
end

(* ══════════════════════════════════════════════════════════════ *)
(*  CEK Machine                                                   *)
(* ══════════════════════════════════════════════════════════════ *)

module CEK = struct
  type value =
    | VInt of int
    | VClosure of string * expr * env
    | VRecClosure of string * string * expr * env
  and env = (string * value) list

  type frame =
    | FArg of expr * env         (* evaluate argument next *)
    | FFun of value              (* function evaluated, apply to result *)
    | FAddL of expr * env        (* left operand of add *)
    | FAddR of int               (* right operand done *)
    | FMulL of expr * env
    | FMulR of int
    | FIf0 of expr * expr * env
    | FLet of string * expr * env

  type state =
    | Eval of expr * env * frame list
    | Apply of frame list * value

  let pp_value = function
    | VInt n -> string_of_int n
    | VClosure (x, body, _) -> Printf.sprintf "<λ%s. %s>" x (pp_expr body)
    | VRecClosure (f, x, body, _) -> Printf.sprintf "<rec %s λ%s. %s>" f x (pp_expr body)

  let pp_frame = function
    | FArg _ -> "arg(...)"
    | FFun v -> "fun(" ^ pp_value v ^ ")"
    | FAddL _ -> "addL"
    | FAddR n -> "addR(" ^ string_of_int n ^ ")"
    | FMulL _ -> "mulL"
    | FMulR n -> "mulR(" ^ string_of_int n ^ ")"
    | FIf0 _ -> "if0"
    | FLet (x, _, _) -> "let(" ^ x ^ ")"

  let pp_kont k = "[" ^ String.concat "; " (List.map pp_frame k) ^ "]"

  let initial expr = Eval (expr, [], [])

  let step = function
    | Eval (Int n, _, k) -> Some (Apply (k, VInt n))
    | Eval (Var x, env, k) ->
      Some (Apply (k, List.assoc x env))
    | Eval (Lam (x, body), env, k) ->
      Some (Apply (k, VClosure (x, body, env)))
    | Eval (Fix (f, Lam (x, body)), env, k) ->
      Some (Apply (k, VRecClosure (f, x, body, env)))
    | Eval (Fix _, _, _) -> failwith "Fix must wrap a lambda"
    | Eval (App (f, a), env, k) ->
      Some (Eval (f, env, FArg (a, env) :: k))
    | Eval (Add (a, b), env, k) ->
      Some (Eval (a, env, FAddL (b, env) :: k))
    | Eval (Mul (a, b), env, k) ->
      Some (Eval (a, env, FMulL (b, env) :: k))
    | Eval (If0 (c, t, e), env, k) ->
      Some (Eval (c, env, FIf0 (t, e, env) :: k))
    | Eval (Let (x, v, body), env, k) ->
      Some (Eval (v, env, FLet (x, body, env) :: k))
    | Apply (FArg (a, env) :: k, v) ->
      Some (Eval (a, env, FFun v :: k))
    | Apply (FFun (VClosure (x, body, cenv)) :: k, arg) ->
      Some (Eval (body, (x, arg) :: cenv, k))
    | Apply (FFun (VRecClosure (f, x, body, cenv)) :: k, arg) ->
      let rec_v = VRecClosure (f, x, body, cenv) in
      Some (Eval (body, (x, arg) :: (f, rec_v) :: cenv, k))
    | Apply (FFun _ :: _, _) -> failwith "CEK: applying non-function"
    | Apply (FAddL (b, env) :: k, VInt a) ->
      Some (Eval (b, env, FAddR a :: k))
    | Apply (FAddR a :: k, VInt b) ->
      Some (Apply (k, VInt (a + b)))
    | Apply (FMulL (b, env) :: k, VInt a) ->
      Some (Eval (b, env, FMulR a :: k))
    | Apply (FMulR a :: k, VInt b) ->
      Some (Apply (k, VInt (a * b)))
    | Apply (FIf0 (t, e, env) :: k, VInt 0) ->
      Some (Eval (t, env, k))
    | Apply (FIf0 (_, e, env) :: k, VInt _) ->
      Some (Eval (e, env, k))
    | Apply (FLet (x, body, env) :: k, v) ->
      Some (Eval (body, (x, v) :: env, k))
    | Apply ([], _) -> None
    | _ -> failwith "CEK: stuck"

  let pp_state = function
    | Eval (e, _, k) -> Printf.sprintf "  Eval(%s, K=%s)" (pp_expr e) (pp_kont k)
    | Apply (k, v) -> Printf.sprintf "  Apply(K=%s, %s)" (pp_kont k) (pp_value v)

  let run ?(verbose=false) ?(max_steps=10000) expr =
    let st = ref (initial expr) in
    let steps = ref 0 in
    let running = ref true in
    while !running && !steps < max_steps do
      if verbose then Printf.printf "  [%d] %s\n" !steps (pp_state !st);
      match step !st with
      | Some st' -> st := st'; incr steps
      | None -> running := false
    done;
    if verbose then Printf.printf "  [%d] %s (final)\n" !steps (pp_state !st);
    match !st with
    | Apply ([], v) -> (v, !steps)
    | _ -> failwith "CEK: did not reach final state"
end

(* ══════════════════════════════════════════════════════════════ *)
(*  Krivine Machine (call-by-name)                                *)
(* ══════════════════════════════════════════════════════════════ *)

module Krivine = struct
  (* Krivine uses closures on the stack; we use substitution for simplicity *)
  type state = {
    term: expr;
    stack: expr list;
  }

  let initial expr = { term = expr; stack = [] }

  let pp_state st =
    let stack_str = "[" ^ String.concat "; " (List.map pp_expr st.stack) ^ "]" in
    Printf.sprintf "  Term=%s Stack=%s" (pp_expr st.term) stack_str

  let step st =
    match st.term with
    | App (f, a) ->
      Some { term = f; stack = a :: st.stack }
    | Lam (x, body) ->
      (match st.stack with
       | arg :: rest ->
         Some { term = subst x arg body; stack = rest }
       | [] -> None)  (* weak head normal form *)
    | Let (x, v, body) ->
      Some { term = subst x v body; stack = st.stack }
    | Fix (f, body) ->
      Some { term = subst f (Fix (f, body)) body; stack = st.stack }
    | Add (Int a, Int b) ->
      Some { term = Int (a + b); stack = st.stack }
    | Mul (Int a, Int b) ->
      Some { term = Int (a * b); stack = st.stack }
    | If0 (Int 0, t, _) ->
      Some { term = t; stack = st.stack }
    | If0 (Int _, _, e) ->
      Some { term = e; stack = st.stack }
    (* Force evaluation of operands *)
    | Add (a, b) when (match a with Int _ -> false | _ -> true) ->
      (* Try to reduce a first - simplified approach *)
      let inner = { term = a; stack = [] } in
      let rec reduce s steps =
        if steps > 100 then s
        else match step_inner s with Some s' -> reduce s' (steps+1) | None -> s
      and step_inner s =
        match s.term with
        | App (f, arg) -> Some { term = f; stack = arg :: s.stack }
        | Lam (x, body) ->
          (match s.stack with arg :: rest -> Some { term = subst x arg body; stack = rest } | [] -> None)
        | Let (x, v, body) -> Some { term = subst x v body; stack = s.stack }
        | Fix (f, body) -> Some { term = subst f (Fix (f, body)) body; stack = s.stack }
        | _ -> None
      in
      let reduced = reduce inner 0 in
      Some { term = Add (reduced.term, b); stack = st.stack }
    | Add (Int _ as a, b) ->
      let inner = { term = b; stack = [] } in
      let rec reduce s steps =
        if steps > 100 then s
        else match step_inner s with Some s' -> reduce s' (steps+1) | None -> s
      and step_inner s =
        match s.term with
        | App (f, arg) -> Some { term = f; stack = arg :: s.stack }
        | Lam (x, body) ->
          (match s.stack with arg :: rest -> Some { term = subst x arg body; stack = rest } | [] -> None)
        | Let (x, v, body) -> Some { term = subst x v body; stack = s.stack }
        | Fix (f, body) -> Some { term = subst f (Fix (f, body)) body; stack = s.stack }
        | _ -> None
      in
      let reduced = reduce inner 0 in
      Some { term = Add (a, reduced.term); stack = st.stack }
    | Mul (a, b) when (match a with Int _ -> false | _ -> true) ->
      let inner = { term = a; stack = [] } in
      let rec reduce s steps =
        if steps > 100 then s
        else match step_inner s with Some s' -> reduce s' (steps+1) | None -> s
      and step_inner s =
        match s.term with
        | App (f, arg) -> Some { term = f; stack = arg :: s.stack }
        | Lam (x, body) ->
          (match s.stack with arg :: rest -> Some { term = subst x arg body; stack = rest } | [] -> None)
        | Let (x, v, body) -> Some { term = subst x v body; stack = s.stack }
        | Fix (f, body) -> Some { term = subst f (Fix (f, body)) body; stack = s.stack }
        | _ -> None
      in
      let reduced = reduce inner 0 in
      Some { term = Mul (reduced.term, b); stack = st.stack }
    | Mul (Int _ as a, b) ->
      let inner = { term = b; stack = [] } in
      let rec reduce s steps =
        if steps > 100 then s
        else match step_inner s with Some s' -> reduce s' (steps+1) | None -> s
      and step_inner s =
        match s.term with
        | App (f, arg) -> Some { term = f; stack = arg :: s.stack }
        | Lam (x, body) ->
          (match s.stack with arg :: rest -> Some { term = subst x arg body; stack = rest } | [] -> None)
        | Let (x, v, body) -> Some { term = subst x v body; stack = s.stack }
        | Fix (f, body) -> Some { term = subst f (Fix (f, body)) body; stack = s.stack }
        | _ -> None
      in
      let reduced = reduce inner 0 in
      Some { term = Mul (a, reduced.term); stack = st.stack }
    | If0 (c, t, e) when (match c with Int _ -> false | _ -> true) ->
      let inner = { term = c; stack = [] } in
      let rec reduce s steps =
        if steps > 100 then s
        else match step_inner s with Some s' -> reduce s' (steps+1) | None -> s
      and step_inner s =
        match s.term with
        | App (f, arg) -> Some { term = f; stack = arg :: s.stack }
        | Lam (x, body) ->
          (match s.stack with arg :: rest -> Some { term = subst x arg body; stack = rest } | [] -> None)
        | Let (x, v, body) -> Some { term = subst x v body; stack = s.stack }
        | Fix (f, body) -> Some { term = subst f (Fix (f, body)) body; stack = s.stack }
        | _ -> None
      in
      let reduced = reduce inner 0 in
      Some { term = If0 (reduced.term, t, e); stack = st.stack }
    | _ -> None

  let run ?(verbose=false) ?(max_steps=10000) expr =
    let st = ref (initial expr) in
    let steps = ref 0 in
    let running = ref true in
    while !running && !steps < max_steps do
      if verbose then Printf.printf "  [%d] %s\n" !steps (pp_state !st);
      match step !st with
      | Some st' -> st := st'; incr steps
      | None -> running := false
    done;
    if verbose then Printf.printf "  [%d] %s (final)\n" !steps (pp_state !st);
    (!st.term, !steps)
end

(* ── Example Programs ────────────────────────────────────────── *)

let examples = [
  ("identity",
   "(lam x. x) 42",
   "Apply identity function to 42");

  ("arithmetic",
   "(+ (* 3 4) 5)",
   "Compute 3*4 + 5 = 17");

  ("church_2",
   "(lam f. lam x. f (f x)) (lam n. (+ n 1)) 0",
   "Church numeral 2 applied to successor and 0");

  ("factorial",
   "let fact = fix f. lam n. if0 n 1 (* n (f (+ n (0 - 1)))) in fact 5",
   "Factorial of 5 using fix-point recursion");
   (* Note: we'll use a simpler version *)

  ("fibonacci",
   "let fib = fix f. lam n. if0 n 0 (if0 (+ n (0 - 1)) 1 (+ (f (+ n (0 - 1))) (f (+ n (0 - 2))))) in fib 6",
   "Fibonacci of 6 using fix-point");
]

(* Simpler examples that work with all machines *)
let simple_examples = [
  ("identity",
   App (Lam ("x", Var "x"), Int 42),
   "Apply identity to 42 → 42");

  ("arithmetic",
   Add (Mul (Int 3, Int 4), Int 5),
   "3*4 + 5 → 17");

  ("nested_let",
   Let ("x", Int 10, Let ("y", Int 20, Add (Var "x", Var "y"))),
   "let x=10 in let y=20 in x+y → 30");

  ("higher_order",
   App (App (Lam ("f", Lam ("x", App (Var "f", App (Var "f", Var "x")))),
             Lam ("n", Add (Var "n", Int 1))),
        Int 0),
   "Apply twice(succ) to 0 → 2");

  ("factorial_5",
   Let ("fact",
        Fix ("f", Lam ("n",
          If0 (Var "n", Int 1,
               Mul (Var "n", App (Var "f", Add (Var "n", Int (-1))))))),
        App (Var "fact", Int 5)),
   "5! = 120 using fixpoint recursion");
]

(* ── Comparison Runner ───────────────────────────────────────── *)

let run_comparison ?(verbose=false) (name, expr, desc) =
  Printf.printf "\n╔══ %s ══╗\n" name;
  Printf.printf "║ %s\n" desc;
  Printf.printf "║ Expr: %s\n" (pp_expr expr);
  Printf.printf "╚══%s══╝\n" (String.make (String.length name + 2) '═');

  Printf.printf "\n  ┌─ SECD Machine ─────────────────\n";
  (try
     let (v, steps) = SECD.run ~verbose ~max_steps:10000 expr in
     Printf.printf "  │ Result: %s\n" (SECD.pp_value v);
     Printf.printf "  │ Steps:  %d\n" steps;
     Printf.printf "  └────────────────────────────────\n"
   with e ->
     Printf.printf "  │ Error: %s\n" (Printexc.to_string e);
     Printf.printf "  └────────────────────────────────\n");

  Printf.printf "  ┌─ CEK Machine ──────────────────\n";
  (try
     let (v, steps) = CEK.run ~verbose ~max_steps:10000 expr in
     Printf.printf "  │ Result: %s\n" (CEK.pp_value v);
     Printf.printf "  │ Steps:  %d\n" steps;
     Printf.printf "  └────────────────────────────────\n"
   with e ->
     Printf.printf "  │ Error: %s\n" (Printexc.to_string e);
     Printf.printf "  └────────────────────────────────\n");

  Printf.printf "  ┌─ Krivine Machine (call-by-name)\n";
  (try
     let (term, steps) = Krivine.run ~verbose ~max_steps:10000 expr in
     Printf.printf "  │ Result: %s\n" (pp_expr term);
     Printf.printf "  │ Steps:  %d\n" steps;
     Printf.printf "  └────────────────────────────────\n"
   with e ->
     Printf.printf "  │ Error: %s\n" (Printexc.to_string e);
     Printf.printf "  └────────────────────────────────\n")

(* ── Interactive REPL ────────────────────────────────────────── *)

let repl () =
  Printf.printf "\n";
  Printf.printf "╔═══════════════════════════════════════════════════╗\n";
  Printf.printf "║     Abstract Machine Simulator                   ║\n";
  Printf.printf "║     SECD · CEK · Krivine                         ║\n";
  Printf.printf "╠═══════════════════════════════════════════════════╣\n";
  Printf.printf "║  Machines:                                       ║\n";
  Printf.printf "║    SECD    - Stack/Env/Control/Dump (call-by-val)║\n";
  Printf.printf "║    CEK     - Control/Env/Kontinuation (cbv)      ║\n";
  Printf.printf "║    Krivine - Call-by-name with substitution       ║\n";
  Printf.printf "╠═══════════════════════════════════════════════════╣\n";
  Printf.printf "║  Syntax:                                         ║\n";
  Printf.printf "║    lam x. E    lambda abstraction                ║\n";
  Printf.printf "║    (E1 E2)     application                       ║\n";
  Printf.printf "║    (+ E1 E2)   addition                          ║\n";
  Printf.printf "║    (* E1 E2)   multiplication                    ║\n";
  Printf.printf "║    if0 E T F   branch on zero                    ║\n";
  Printf.printf "║    let x = E in B  local binding                 ║\n";
  Printf.printf "║    fix f. E    recursive binding                 ║\n";
  Printf.printf "╠═══════════════════════════════════════════════════╣\n";
  Printf.printf "║  Commands:                                       ║\n";
  Printf.printf "║    :examples   run all built-in examples         ║\n";
  Printf.printf "║    :secd E     run only on SECD                  ║\n";
  Printf.printf "║    :cek E      run only on CEK                   ║\n";
  Printf.printf "║    :krivine E  run only on Krivine               ║\n";
  Printf.printf "║    :verbose E  run on all with step traces       ║\n";
  Printf.printf "║    :compare    run examples and compare machines  ║\n";
  Printf.printf "║    :help       show this help                    ║\n";
  Printf.printf "║    :quit       exit                              ║\n";
  Printf.printf "╚═══════════════════════════════════════════════════╝\n";
  Printf.printf "\n";

  let running = ref true in
  while !running do
    Printf.printf "λ> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let line = String.trim line in
      if line = "" then ()
      else if line = ":quit" || line = ":q" then running := false
      else if line = ":help" || line = ":h" then begin
        Printf.printf "  Enter a lambda calculus expression to evaluate on all 3 machines.\n";
        Printf.printf "  Use :secd, :cek, or :krivine to target one machine.\n";
        Printf.printf "  Use :verbose for step-by-step traces.\n"
      end
      else if line = ":examples" || line = ":ex" then begin
        Printf.printf "\n── Built-in Examples ──────────────────────────────\n";
        List.iter (fun (name, expr, desc) ->
          run_comparison (name, expr, desc)
        ) simple_examples
      end
      else if line = ":compare" then begin
        Printf.printf "\n── Machine Comparison ─────────────────────────────\n";
        Printf.printf "  %-15s %8s %8s %8s\n" "Example" "SECD" "CEK" "Krivine";
        Printf.printf "  %s\n" (String.make 45 '─');
        List.iter (fun (name, expr, _) ->
          let secd_s = try let (_, s) = SECD.run expr in string_of_int s with _ -> "err" in
          let cek_s = try let (_, s) = CEK.run expr in string_of_int s with _ -> "err" in
          let kriv_s = try let (_, s) = Krivine.run expr in string_of_int s with _ -> "err" in
          Printf.printf "  %-15s %8s %8s %8s\n" name secd_s cek_s kriv_s
        ) simple_examples;
        Printf.printf "\n  (Values show step counts per machine)\n"
      end
      else begin
        let is_verbose = String.length line > 8 && String.sub line 0 8 = ":verbose" in
        let target, input =
          if is_verbose then (`All, String.trim (String.sub line 8 (String.length line - 8)))
          else if String.length line > 5 && String.sub line 0 5 = ":secd" then
            (`SECD, String.trim (String.sub line 5 (String.length line - 5)))
          else if String.length line > 4 && String.sub line 0 4 = ":cek" then
            (`CEK, String.trim (String.sub line 4 (String.length line - 4)))
          else if String.length line > 8 && String.sub line 0 8 = ":krivine" then
            (`Krivine, String.trim (String.sub line 8 (String.length line - 8)))
          else (`All, line)
        in
        (try
           let expr = Parser.parse input in
           Printf.printf "  Parsed: %s\n\n" (pp_expr expr);
           (match target with
            | `All ->
              run_comparison ~verbose:is_verbose ("user-input", expr, input)
            | `SECD ->
              Printf.printf "  ┌─ SECD Machine ─────────────────\n";
              let (v, steps) = SECD.run ~verbose:true expr in
              Printf.printf "  │ Result: %s (%d steps)\n" (SECD.pp_value v) steps;
              Printf.printf "  └────────────────────────────────\n"
            | `CEK ->
              Printf.printf "  ┌─ CEK Machine ──────────────────\n";
              let (v, steps) = CEK.run ~verbose:true expr in
              Printf.printf "  │ Result: %s (%d steps)\n" (CEK.pp_value v) steps;
              Printf.printf "  └────────────────────────────────\n"
            | `Krivine ->
              Printf.printf "  ┌─ Krivine Machine ──────────────\n";
              let (t, steps) = Krivine.run ~verbose:true expr in
              Printf.printf "  │ Result: %s (%d steps)\n" (pp_expr t) steps;
              Printf.printf "  └────────────────────────────────\n")
         with e ->
           Printf.printf "  Error: %s\n" (Printexc.to_string e))
      end
  done;
  Printf.printf "\nGoodbye!\n"

(* ── Main ────────────────────────────────────────────────────── *)

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  match args with
  | ["--examples"] | ["-e"] ->
    List.iter (fun ex -> run_comparison ex) simple_examples
  | ["--compare"] | ["-c"] ->
    Printf.printf "── Machine Step Comparison ────────────────────────\n";
    Printf.printf "  %-15s %8s %8s %8s\n" "Example" "SECD" "CEK" "Krivine";
    Printf.printf "  %s\n" (String.make 45 '─');
    List.iter (fun (name, expr, _) ->
      let secd_s = try let (_, s) = SECD.run expr in string_of_int s with _ -> "err" in
      let cek_s = try let (_, s) = CEK.run expr in string_of_int s with _ -> "err" in
      let kriv_s = try let (_, s) = Krivine.run expr in string_of_int s with _ -> "err" in
      Printf.printf "  %-15s %8s %8s %8s\n" name secd_s cek_s kriv_s
    ) simple_examples
  | ["--help"] | ["-h"] ->
    Printf.printf "Abstract Machine Simulator\n";
    Printf.printf "Usage: ocaml abstract_machine.ml [options]\n";
    Printf.printf "  (no args)   Interactive REPL\n";
    Printf.printf "  --examples  Run built-in examples\n";
    Printf.printf "  --compare   Compare machine step counts\n"
  | _ -> repl ()
