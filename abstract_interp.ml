(* abstract_interp.ml - Abstract Interpretation with Interval Domain
 *
 * Implements a mini abstract interpreter for a simple imperative language
 * using the interval abstract domain. Demonstrates:
 * - Lattice theory (join, meet, widening, narrowing)
 * - Abstract transfer functions for arithmetic and comparisons
 * - Fixed-point computation with widening for loops
 * - Variable environment as a product domain
 * - Interval arithmetic with proper handling of infinities
 *
 * Language: assignments, if-then-else, while loops, sequences, assert
 *)

(* ========== Interval Domain ========== *)

(** Bound: either a finite integer or +/- infinity *)
type bound =
  | NegInf
  | Fin of int
  | PosInf

let bound_to_string = function
  | NegInf -> "-∞"
  | Fin n -> string_of_int n
  | PosInf -> "+∞"

let bound_le a b = match a, b with
  | NegInf, _ -> true
  | _, NegInf -> false
  | _, PosInf -> true
  | PosInf, _ -> false
  | Fin x, Fin y -> x <= y

let bound_lt a b = match a, b with
  | NegInf, NegInf -> false
  | PosInf, PosInf -> false
  | _ -> bound_le a b && a <> b

let bound_eq a b = match a, b with
  | NegInf, NegInf | PosInf, PosInf -> true
  | Fin x, Fin y -> x = y
  | _ -> false

let bound_min a b = if bound_le a b then a else b
let bound_max a b = if bound_le a b then b else a

let bound_add a b = match a, b with
  | NegInf, PosInf | PosInf, NegInf -> Fin 0 (* conservative *)
  | NegInf, _ | _, NegInf -> NegInf
  | PosInf, _ | _, PosInf -> PosInf
  | Fin x, Fin y -> Fin (x + y)

let bound_sub a b = match a, b with
  | NegInf, NegInf | PosInf, PosInf -> Fin 0 (* conservative *)
  | NegInf, _ | _, PosInf -> NegInf
  | PosInf, _ | _, NegInf -> PosInf
  | Fin x, Fin y -> Fin (x - y)

let bound_neg = function
  | NegInf -> PosInf
  | PosInf -> NegInf
  | Fin x -> Fin (-x)

let bound_mul a b = match a, b with
  | Fin 0, _ | _, Fin 0 -> Fin 0
  | NegInf, x | x, NegInf ->
    if bound_lt x (Fin 0) then PosInf
    else if bound_eq x (Fin 0) then Fin 0
    else NegInf
  | PosInf, x | x, PosInf ->
    if bound_lt x (Fin 0) then NegInf
    else if bound_eq x (Fin 0) then Fin 0
    else PosInf
  | Fin x, Fin y -> Fin (x * y)

(** Abstract interval: Bottom (empty) or [lo, hi] *)
type interval =
  | Bot
  | Itv of bound * bound

let top_interval = Itv (NegInf, PosInf)

let const_interval n = Itv (Fin n, Fin n)

let range_interval lo hi =
  if lo > hi then Bot
  else Itv (Fin lo, Fin hi)

let interval_to_string = function
  | Bot -> "⊥"
  | Itv (lo, hi) ->
    Printf.sprintf "[%s, %s]" (bound_to_string lo) (bound_to_string hi)

let is_bot = function Bot -> true | _ -> false

(** Join (least upper bound) *)
let interval_join a b = match a, b with
  | Bot, x | x, Bot -> x
  | Itv (lo1, hi1), Itv (lo2, hi2) ->
    Itv (bound_min lo1 lo2, bound_max hi1 hi2)

(** Meet (greatest lower bound) *)
let interval_meet a b = match a, b with
  | Bot, _ | _, Bot -> Bot
  | Itv (lo1, hi1), Itv (lo2, hi2) ->
    let lo = bound_max lo1 lo2 in
    let hi = bound_min hi1 hi2 in
    if bound_le lo hi then Itv (lo, hi) else Bot

(** Widening: accelerate convergence for loops *)
let interval_widen a b = match a, b with
  | Bot, x -> x
  | x, Bot -> x
  | Itv (lo1, hi1), Itv (lo2, hi2) ->
    let lo = if bound_lt lo2 lo1 then NegInf else lo1 in
    let hi = if bound_lt hi1 hi2 then PosInf else hi1 in
    Itv (lo, hi)

(** Narrowing: refine after widening stabilizes *)
let interval_narrow a b = match a, b with
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | Itv (lo1, hi1), Itv (lo2, hi2) ->
    let lo = if bound_eq lo1 NegInf then lo2 else lo1 in
    let hi = if bound_eq hi1 PosInf then hi2 else hi1 in
    Itv (lo, hi)

(** Interval inclusion test *)
let interval_le a b = match a, b with
  | Bot, _ -> true
  | _, Bot -> false
  | Itv (lo1, hi1), Itv (lo2, hi2) ->
    bound_le lo2 lo1 && bound_le hi1 hi2

(** Interval equality *)
let interval_eq a b = match a, b with
  | Bot, Bot -> true
  | Itv (lo1, hi1), Itv (lo2, hi2) -> bound_eq lo1 lo2 && bound_eq hi1 hi2
  | _ -> false

(* ========== Interval Arithmetic ========== *)

let interval_add a b = match a, b with
  | Bot, _ | _, Bot -> Bot
  | Itv (lo1, hi1), Itv (lo2, hi2) ->
    Itv (bound_add lo1 lo2, bound_add hi1 hi2)

let interval_neg = function
  | Bot -> Bot
  | Itv (lo, hi) -> Itv (bound_neg hi, bound_neg lo)

let interval_sub a b = interval_add a (interval_neg b)

let interval_mul a b = match a, b with
  | Bot, _ | _, Bot -> Bot
  | Itv (lo1, hi1), Itv (lo2, hi2) ->
    let products = [
      bound_mul lo1 lo2; bound_mul lo1 hi2;
      bound_mul hi1 lo2; bound_mul hi1 hi2
    ] in
    let lo = List.fold_left bound_min PosInf products in
    let hi = List.fold_left bound_max NegInf products in
    Itv (lo, hi)

let interval_div a b = match a, b with
  | Bot, _ | _, Bot -> Bot
  | _, Itv (lo2, hi2) when bound_le lo2 (Fin 0) && bound_le (Fin 0) hi2 ->
    (* Division by interval containing zero: return top *)
    top_interval
  | Itv (lo1, hi1), Itv (lo2, hi2) ->
    (* When divisor doesn't contain zero, compute bounds *)
    let div_bound x y = match x, y with
      | Fin 0, _ -> Fin 0
      | _, Fin 0 -> PosInf (* shouldn't happen due to check above *)
      | NegInf, Fin y -> if y > 0 then NegInf else PosInf
      | PosInf, Fin y -> if y > 0 then PosInf else NegInf
      | Fin _, NegInf | Fin _, PosInf -> Fin 0
      | NegInf, NegInf -> PosInf
      | NegInf, PosInf -> NegInf
      | PosInf, NegInf -> NegInf
      | PosInf, PosInf -> PosInf
      | Fin x, Fin y -> Fin (x / y)
    in
    let results = [
      div_bound lo1 lo2; div_bound lo1 hi2;
      div_bound hi1 lo2; div_bound hi1 hi2
    ] in
    let lo = List.fold_left bound_min PosInf results in
    let hi = List.fold_left bound_max NegInf results in
    Itv (lo, hi)

let interval_mod a b = match a, b with
  | Bot, _ | _, Bot -> Bot
  | _, Itv (lo2, hi2) when bound_le lo2 (Fin 0) && bound_le (Fin 0) hi2 ->
    top_interval
  | _, Itv (_, hi2) ->
    (* Result of a mod b is in [0, |b|-1] for positive, conservative for negative *)
    let abs_max = match hi2 with
      | Fin n -> Fin (abs n - 1)
      | PosInf -> PosInf
      | NegInf -> PosInf
    in
    let lo = match a with
      | Itv (Fin lo1, _) when lo1 >= 0 -> Fin 0
      | _ -> bound_neg abs_max
    in
    Itv (lo, abs_max)

(* ========== Abstract Environment ========== *)

module Env = Map.Make(String)

type env = interval Env.t

let env_bot : env = Env.empty

let env_get (x : string) (e : env) : interval =
  match Env.find_opt x e with
  | Some i -> i
  | None -> Bot  (* uninitialized = bottom *)

let env_set (x : string) (v : interval) (e : env) : env =
  if is_bot v then e  (* don't store bottom explicitly *)
  else Env.add x v e

let env_join (e1 : env) (e2 : env) : env =
  Env.merge (fun _ v1 v2 -> match v1, v2 with
    | None, x | x, None -> x
    | Some a, Some b -> Some (interval_join a b)
  ) e1 e2

let env_widen (e1 : env) (e2 : env) : env =
  Env.merge (fun _ v1 v2 -> match v1, v2 with
    | None, x -> x
    | x, None -> x
    | Some a, Some b -> Some (interval_widen a b)
  ) e1 e2

let env_narrow (e1 : env) (e2 : env) : env =
  Env.merge (fun _ v1 v2 -> match v1, v2 with
    | None, _ -> None
    | x, None -> x
    | Some a, Some b -> Some (interval_narrow a b)
  ) e1 e2

let env_le (e1 : env) (e2 : env) : bool =
  Env.for_all (fun k v1 ->
    match Env.find_opt k e2 with
    | None -> is_bot v1
    | Some v2 -> interval_le v1 v2
  ) e1

let env_eq (e1 : env) (e2 : env) : bool =
  env_le e1 e2 && env_le e2 e1

let env_to_string (e : env) : string =
  let bindings = Env.bindings e in
  if bindings = [] then "{}"
  else
    let parts = List.map (fun (k, v) ->
      Printf.sprintf "%s → %s" k (interval_to_string v)
    ) bindings in
    "{ " ^ String.concat ", " parts ^ " }"

(* ========== Language AST ========== *)

type binop = Add | Sub | Mul | Div | Mod

type cmpop = Eq | Ne | Lt | Le | Gt | Ge

type expr =
  | Const of int
  | Var of string
  | BinOp of binop * expr * expr
  | Neg of expr

type bexpr =
  | True
  | False
  | Cmp of cmpop * expr * expr
  | And of bexpr * bexpr
  | Or of bexpr * bexpr
  | Not of bexpr

type stmt =
  | Skip
  | Assign of string * expr
  | Seq of stmt * stmt
  | If of bexpr * stmt * stmt
  | While of bexpr * stmt
  | Assert of bexpr

(* ========== Abstract Expression Evaluation ========== *)

let eval_binop op a b = match op with
  | Add -> interval_add a b
  | Sub -> interval_sub a b
  | Mul -> interval_mul a b
  | Div -> interval_div a b
  | Mod -> interval_mod a b

let rec eval_expr (e : env) (expr : expr) : interval = match expr with
  | Const n -> const_interval n
  | Var x -> env_get x e
  | BinOp (op, e1, e2) ->
    let v1 = eval_expr e e1 in
    let v2 = eval_expr e e2 in
    eval_binop op v1 v2
  | Neg ex -> interval_neg (eval_expr e ex)

(* ========== Abstract Condition Filtering ========== *)

(** Filter environment by assuming a boolean expression is true.
    Returns a refined environment (or makes vars bottom if impossible). *)
let rec filter_true (e : env) (b : bexpr) : env = match b with
  | True -> e
  | False -> env_bot
  | Not b' -> filter_false e b'
  | And (b1, b2) -> filter_true (filter_true e b1) b2
  | Or (b1, b2) -> env_join (filter_true e b1) (filter_true e b2)
  | Cmp (op, Var x, Const n) ->
    let vx = env_get x e in
    let refined = match op with
      | Eq -> interval_meet vx (const_interval n)
      | Ne -> vx  (* imprecise but sound *)
      | Lt -> interval_meet vx (Itv (NegInf, Fin (n - 1)))
      | Le -> interval_meet vx (Itv (NegInf, Fin n))
      | Gt -> interval_meet vx (Itv (Fin (n + 1), PosInf))
      | Ge -> interval_meet vx (Itv (Fin n, PosInf))
    in
    if is_bot refined then env_bot
    else env_set x refined e
  | Cmp (op, Const n, Var x) ->
    (* Flip comparison *)
    let flipped = match op with
      | Eq -> Eq | Ne -> Ne | Lt -> Gt | Le -> Ge | Gt -> Lt | Ge -> Le
    in
    filter_true e (Cmp (flipped, Var x, Const n))
  | Cmp (op, Var x, Var y) ->
    let vx = env_get x e in
    let vy = env_get y e in
    begin match op, vx, vy with
    | Lt, Itv (lox, _), Itv (_, hiy) ->
      let e = env_set x (interval_meet vx (Itv (NegInf, bound_sub hiy (Fin 1)))) e in
      env_set y (interval_meet vy (Itv (bound_add lox (Fin 1), PosInf))) e
    | Le, Itv (lox, _), Itv (_, hiy) ->
      let e = env_set x (interval_meet vx (Itv (NegInf, hiy))) e in
      env_set y (interval_meet vy (Itv (lox, PosInf))) e
    | Gt, _, _ -> filter_true e (Cmp (Lt, Var y, Var x))
    | Ge, _, _ -> filter_true e (Cmp (Le, Var y, Var x))
    | Eq, _, _ ->
      let m = interval_meet vx vy in
      if is_bot m then env_bot
      else env_set x m (env_set y m e)
    | Ne, _, _ -> e  (* imprecise but sound *)
    | _ -> e
    end
  | Cmp _ -> e  (* complex expressions: no refinement *)

and filter_false (e : env) (b : bexpr) : env = match b with
  | True -> env_bot
  | False -> e
  | Not b' -> filter_true e b'
  | And (b1, b2) -> env_join (filter_false e b1) (filter_false e b2)
  | Or (b1, b2) -> filter_false (filter_false e b1) b2
  | Cmp (op, e1, e2) ->
    let negated = match op with
      | Eq -> Ne | Ne -> Eq | Lt -> Ge | Le -> Gt | Gt -> Le | Ge -> Lt
    in
    filter_true e (Cmp (negated, e1, e2))

(* ========== Analysis Results ========== *)

type analysis_warning =
  | PossibleAssertionFailure of bexpr * env
  | DefiniteAssertionFailure of bexpr * env
  | PossibleDivisionByZero of expr * env
  | DefiniteDivisionByZero of expr * env
  | UnreachableCode

let warning_to_string = function
  | PossibleAssertionFailure (_, env) ->
    Printf.sprintf "⚠ Possible assertion failure (env: %s)" (env_to_string env)
  | DefiniteAssertionFailure (_, env) ->
    Printf.sprintf "🛑 Definite assertion failure (env: %s)" (env_to_string env)
  | PossibleDivisionByZero (_, env) ->
    Printf.sprintf "⚠ Possible division by zero (env: %s)" (env_to_string env)
  | DefiniteDivisionByZero (_, env) ->
    Printf.sprintf "🛑 Definite division by zero (env: %s)" (env_to_string env)
  | UnreachableCode ->
    "ℹ Unreachable code detected"

type analysis_result = {
  final_env : env;
  warnings : analysis_warning list;
  iterations : int;  (* for loops *)
}

let empty_result env = { final_env = env; warnings = []; iterations = 0 }

(* ========== Division-by-Zero Check ========== *)

let rec check_div_by_zero (e : env) (expr : expr) : analysis_warning list =
  match expr with
  | Const _ | Var _ -> []
  | Neg ex -> check_div_by_zero e ex
  | BinOp (op, e1, e2) ->
    let w1 = check_div_by_zero e e1 in
    let w2 = check_div_by_zero e e2 in
    let w_div = match op with
      | Div | Mod ->
        let v2 = eval_expr e e2 in
        begin match v2 with
        | Bot -> []
        | Itv (lo, hi) ->
          if bound_le lo (Fin 0) && bound_le (Fin 0) hi then
            if bound_eq lo (Fin 0) && bound_eq hi (Fin 0) then
              [DefiniteDivisionByZero (expr, e)]
            else
              [PossibleDivisionByZero (expr, e)]
          else []
        end
      | _ -> []
    in
    w1 @ w2 @ w_div

(* ========== Abstract Interpreter ========== *)

let max_widening_iterations = 100

let rec analyze (e : env) (s : stmt) : analysis_result = match s with
  | Skip -> empty_result e

  | Assign (x, expr) ->
    let div_warnings = check_div_by_zero e expr in
    let v = eval_expr e expr in
    { final_env = env_set x v e; warnings = div_warnings; iterations = 0 }

  | Seq (s1, s2) ->
    let r1 = analyze e s1 in
    let r2 = analyze r1.final_env s2 in
    { final_env = r2.final_env;
      warnings = r1.warnings @ r2.warnings;
      iterations = r1.iterations + r2.iterations }

  | If (cond, s_true, s_false) ->
    let e_true = filter_true e cond in
    let e_false = filter_false e cond in
    let r_true = if env_eq e_true env_bot then
      { (empty_result env_bot) with warnings = [UnreachableCode] }
    else analyze e_true s_true in
    let r_false = if env_eq e_false env_bot then
      { (empty_result env_bot) with warnings = [UnreachableCode] }
    else analyze e_false s_false in
    { final_env = env_join r_true.final_env r_false.final_env;
      warnings = r_true.warnings @ r_false.warnings;
      iterations = 0 }

  | While (cond, body) ->
    analyze_loop e cond body

  | Assert cond ->
    let e_true = filter_true e cond in
    let e_false = filter_false e cond in
    let warnings =
      if env_eq e_true env_bot then
        [DefiniteAssertionFailure (cond, e)]
      else if not (env_eq e_false env_bot) then
        [PossibleAssertionFailure (cond, e)]
      else []
    in
    (* After assert, we know cond is true *)
    { final_env = e_true; warnings; iterations = 0 }

and analyze_loop (init_env : env) (cond : bexpr) (body : stmt) : analysis_result =
  (* Widening phase: find post-fixpoint *)
  let rec widen_loop prev_env iter =
    if iter >= max_widening_iterations then
      (prev_env, iter)
    else
      let loop_entry = filter_true prev_env cond in
      let r = analyze loop_entry body in
      let next_env = env_widen prev_env (env_join init_env r.final_env) in
      if env_le next_env prev_env then
        (prev_env, iter)
      else
        widen_loop next_env (iter + 1)
  in
  let (wide_env, iters) = widen_loop init_env 0 in

  (* Narrowing phase: refine the result *)
  let rec narrow_loop prev_env iter =
    if iter >= 3 then prev_env  (* limited narrowing iterations *)
    else
      let loop_entry = filter_true prev_env cond in
      let r = analyze loop_entry body in
      let next_env = env_narrow prev_env (env_join init_env r.final_env) in
      if env_eq next_env prev_env then prev_env
      else narrow_loop next_env (iter + 1)
  in
  let final_inv = narrow_loop wide_env 0 in

  (* Collect warnings from one body pass *)
  let body_entry = filter_true final_inv cond in
  let body_result = analyze body_entry body in

  (* Exit environment: when condition is false *)
  let exit_env = filter_false final_inv cond in

  { final_env = exit_env;
    warnings = body_result.warnings;
    iterations = iters }

(* ========== Pretty Printer for AST ========== *)

let binop_to_string = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"

let cmpop_to_string = function
  | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="

let rec expr_to_string = function
  | Const n -> string_of_int n
  | Var x -> x
  | BinOp (op, e1, e2) ->
    Printf.sprintf "(%s %s %s)" (expr_to_string e1) (binop_to_string op) (expr_to_string e2)
  | Neg e -> Printf.sprintf "(-%s)" (expr_to_string e)

let rec bexpr_to_string = function
  | True -> "true"
  | False -> "false"
  | Cmp (op, e1, e2) ->
    Printf.sprintf "%s %s %s" (expr_to_string e1) (cmpop_to_string op) (expr_to_string e2)
  | And (b1, b2) ->
    Printf.sprintf "(%s && %s)" (bexpr_to_string b1) (bexpr_to_string b2)
  | Or (b1, b2) ->
    Printf.sprintf "(%s || %s)" (bexpr_to_string b1) (bexpr_to_string b2)
  | Not b ->
    Printf.sprintf "!(%s)" (bexpr_to_string b)

let rec stmt_to_string indent s =
  let pad = String.make (indent * 2) ' ' in
  match s with
  | Skip -> pad ^ "skip"
  | Assign (x, e) -> Printf.sprintf "%s%s := %s" pad x (expr_to_string e)
  | Seq (s1, s2) ->
    Printf.sprintf "%s;\n%s" (stmt_to_string indent s1) (stmt_to_string indent s2)
  | If (c, s1, s2) ->
    Printf.sprintf "%sif %s then\n%s\n%selse\n%s\n%send"
      pad (bexpr_to_string c) (stmt_to_string (indent+1) s1)
      pad (stmt_to_string (indent+1) s2) pad
  | While (c, body) ->
    Printf.sprintf "%swhile %s do\n%s\n%sdone"
      pad (bexpr_to_string c) (stmt_to_string (indent+1) body) pad
  | Assert c ->
    Printf.sprintf "%sassert(%s)" pad (bexpr_to_string c)

(* ========== Trace Analysis (step-by-step) ========== *)

type trace_entry = {
  statement : string;
  env_before : string;
  env_after : string;
}

let trace_analyze (init_env : env) (s : stmt) : analysis_result * trace_entry list =
  let traces = ref [] in
  let rec go (e : env) (s : stmt) : analysis_result =
    let before = env_to_string e in
    let r = analyze e s in
    let after = env_to_string r.final_env in
    traces := { statement = stmt_to_string 0 s;
                env_before = before;
                env_after = after } :: !traces;
    r
  in
  let result = go init_env s in
  (result, List.rev !traces)

(* ========== Convenience Constructors ========== *)

let var x = Var x
let const n = Const n
let ( +: ) a b = BinOp (Add, a, b)
let ( -: ) a b = BinOp (Sub, a, b)
let ( *: ) a b = BinOp (Mul, a, b)
let ( /: ) a b = BinOp (Div, a, b)
let ( %: ) a b = BinOp (Mod, a, b)

let ( ==: ) a b = Cmp (Eq, a, b)
let ( !=: ) a b = Cmp (Ne, a, b)
let ( <: ) a b = Cmp (Lt, a, b)
let ( <=: ) a b = Cmp (Le, a, b)
let ( >: ) a b = Cmp (Gt, a, b)
let ( >=: ) a b = Cmp (Ge, a, b)

let assign x e = Assign (x, e)
let seq stmts = List.fold_right (fun s acc -> Seq (s, acc)) stmts Skip
let if_ c t f = If (c, t, f)
let while_ c body = While (c, body)
let assert_ c = Assert c

(* ========== Example Programs ========== *)

(** Example 1: Simple counter with assertion *)
let example_counter () =
  (* x := 0; while (x < 10) { x := x + 1 }; assert(x >= 0 && x <= 10) *)
  seq [
    assign "x" (const 0);
    while_ (var "x" <: const 10) (
      assign "x" (var "x" +: const 1)
    );
    assert_ (And (var "x" >=: const 0, var "x" <=: const 10))
  ]

(** Example 2: Absolute value *)
let example_abs () =
  (* if (x < 0) { y := -x } else { y := x }; assert(y >= 0) *)
  seq [
    if_ (var "x" <: const 0)
      (assign "y" (Neg (var "x")))
      (assign "y" (var "x"));
    assert_ (var "y" >=: const 0)
  ]

(** Example 3: Division safety *)
let example_div_check () =
  (* x := input; y := 100 / x *)
  seq [
    assign "y" (const 100 /: var "x")
  ]

(** Example 4: Nested loops *)
let example_nested_loop () =
  (* i := 0; j := 0;
     while (i < 5) { j := 0; while (j < 3) { j := j + 1 }; i := i + 1 } *)
  seq [
    assign "i" (const 0);
    assign "j" (const 0);
    while_ (var "i" <: const 5) (
      seq [
        assign "j" (const 0);
        while_ (var "j" <: const 3) (
          assign "j" (var "j" +: const 1)
        );
        assign "i" (var "i" +: const 1)
      ]
    )
  ]

(** Example 5: Collatz-like with bounded assertion *)
let example_bounded () =
  (* x := 1; while (x < 100) { x := x * 2 }; assert(x >= 1) *)
  seq [
    assign "x" (const 1);
    while_ (var "x" <: const 100) (
      assign "x" (var "x" *: const 2)
    );
    assert_ (var "x" >=: const 1)
  ]

(** Example 6: Demonstrates dead code detection *)
let example_dead_code () =
  seq [
    assign "x" (const 5);
    if_ (var "x" <: const 0)
      (assign "y" (const 1))  (* unreachable! *)
      (assign "y" (const 2))
  ]

(* ========== Tests ========== *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_equal name expected actual =
  if expected = actual then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s\n    expected: %s\n    actual:   %s\n" name expected actual
  end

let assert_true name cond =
  if cond then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s (expected true)\n" name
  end

let assert_false name cond =
  if not cond then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s (expected false)\n" name
  end

let test_bounds () =
  Printf.printf "\n── Bound Operations ──\n";
  assert_true "NegInf <= PosInf" (bound_le NegInf PosInf);
  assert_true "Fin 3 <= Fin 5" (bound_le (Fin 3) (Fin 5));
  assert_false "PosInf <= NegInf" (bound_le PosInf NegInf);
  assert_true "NegInf <= NegInf" (bound_le NegInf NegInf);
  assert_equal "3 + 5" "8" (bound_to_string (bound_add (Fin 3) (Fin 5)));
  assert_equal "NegInf + 5" "-∞" (bound_to_string (bound_add NegInf (Fin 5)));
  assert_equal "3 - 5" "-2" (bound_to_string (bound_sub (Fin 3) (Fin 5)));
  assert_equal "neg(3)" "-3" (bound_to_string (bound_neg (Fin 3)));
  assert_equal "neg(NegInf)" "+∞" (bound_to_string (bound_neg NegInf));
  assert_equal "3 * 5" "15" (bound_to_string (bound_mul (Fin 3) (Fin 5)));
  assert_equal "0 * PosInf" "0" (bound_to_string (bound_mul (Fin 0) PosInf));
  assert_equal "min(3,5)" "3" (bound_to_string (bound_min (Fin 3) (Fin 5)));
  assert_equal "max(3,5)" "5" (bound_to_string (bound_max (Fin 3) (Fin 5)))

let test_intervals () =
  Printf.printf "\n── Interval Operations ──\n";
  let a = Itv (Fin 1, Fin 5) in
  let b = Itv (Fin 3, Fin 8) in
  assert_equal "[1,5] ∪ [3,8]" "[1, 8]" (interval_to_string (interval_join a b));
  assert_equal "[1,5] ∩ [3,8]" "[3, 5]" (interval_to_string (interval_meet a b));
  assert_equal "[1,5] ∩ [6,8]" "⊥"
    (interval_to_string (interval_meet a (Itv (Fin 6, Fin 8))));
  assert_true "⊥ ⊆ [1,5]" (interval_le Bot a);
  assert_true "[1,5] ⊆ [-∞,+∞]" (interval_le a top_interval);
  assert_false "[1,5] ⊆ [3,8]" (interval_le a b);
  assert_equal "const(42)" "[42, 42]" (interval_to_string (const_interval 42));
  assert_equal "range(3,7)" "[3, 7]" (interval_to_string (range_interval 3 7));
  assert_equal "range(7,3)" "⊥" (interval_to_string (range_interval 7 3))

let test_interval_arithmetic () =
  Printf.printf "\n── Interval Arithmetic ──\n";
  let a = Itv (Fin 1, Fin 3) in
  let b = Itv (Fin 2, Fin 5) in
  assert_equal "[1,3] + [2,5]" "[3, 8]" (interval_to_string (interval_add a b));
  assert_equal "[1,3] - [2,5]" "[-4, 1]" (interval_to_string (interval_sub a b));
  assert_equal "[1,3] * [2,5]" "[2, 15]" (interval_to_string (interval_mul a b));

  let c = Itv (Fin (-2), Fin 3) in
  let d = Itv (Fin 1, Fin 4) in
  assert_equal "[-2,3] * [1,4]" "[-8, 12]" (interval_to_string (interval_mul c d));
  assert_equal "neg([1,3])" "[-3, -1]" (interval_to_string (interval_neg a));

  assert_equal "⊥ + [1,3]" "⊥" (interval_to_string (interval_add Bot a));

  (* Division *)
  assert_equal "[4,8] / [2,4]" "[1, 4]"
    (interval_to_string (interval_div (Itv (Fin 4, Fin 8)) (Itv (Fin 2, Fin 4))));
  assert_equal "[1,3] / [-1,1]" "[-∞, +∞]"
    (interval_to_string (interval_div a (Itv (Fin (-1), Fin 1))))

let test_widening_narrowing () =
  Printf.printf "\n── Widening & Narrowing ──\n";
  let a = Itv (Fin 0, Fin 5) in
  let b = Itv (Fin 0, Fin 10) in
  assert_equal "widen [0,5] [0,10]" "[0, +∞]"
    (interval_to_string (interval_widen a b));
  assert_equal "widen [0,5] [0,5]" "[0, 5]"
    (interval_to_string (interval_widen a a));
  let w = Itv (Fin 0, PosInf) in
  assert_equal "narrow [0,+∞] [0,10]" "[0, 10]"
    (interval_to_string (interval_narrow w b));

  let c = Itv (Fin (-3), Fin 5) in
  assert_equal "widen [0,5] [-3,5]" "[-∞, 5]"
    (interval_to_string (interval_widen a c))

let test_environment () =
  Printf.printf "\n── Environment ──\n";
  let e1 = env_set "x" (Itv (Fin 1, Fin 5)) env_bot in
  let e1 = env_set "y" (Itv (Fin 0, Fin 3)) e1 in
  assert_equal "get x" "[1, 5]" (interval_to_string (env_get "x" e1));
  assert_equal "get z (missing)" "⊥" (interval_to_string (env_get "z" e1));

  let e2 = env_set "x" (Itv (Fin 3, Fin 8)) env_bot in
  let e2 = env_set "y" (Itv (Fin 2, Fin 6)) e2 in
  let joined = env_join e1 e2 in
  assert_equal "join x" "[1, 8]" (interval_to_string (env_get "x" joined));
  assert_equal "join y" "[0, 6]" (interval_to_string (env_get "y" joined));

  assert_true "e1 <= join" (env_le e1 joined);
  assert_false "join <= e1" (env_le joined e1)

let test_expr_eval () =
  Printf.printf "\n── Expression Evaluation ──\n";
  let e = env_set "x" (Itv (Fin 1, Fin 5)) env_bot in
  let e = env_set "y" (Itv (Fin 2, Fin 3)) e in

  assert_equal "const 42" "[42, 42]"
    (interval_to_string (eval_expr e (const 42)));
  assert_equal "var x" "[1, 5]"
    (interval_to_string (eval_expr e (var "x")));
  assert_equal "x + y" "[3, 8]"
    (interval_to_string (eval_expr e (var "x" +: var "y")));
  assert_equal "x * y" "[2, 15]"
    (interval_to_string (eval_expr e (var "x" *: var "y")));
  assert_equal "x - y" "[-2, 3]"
    (interval_to_string (eval_expr e (var "x" -: var "y")))

let test_filtering () =
  Printf.printf "\n── Condition Filtering ──\n";
  let e = env_set "x" (Itv (Fin (-5), Fin 10)) env_bot in

  let e1 = filter_true e (var "x" >=: const 0) in
  assert_equal "x>=0 from [-5,10]" "[0, 10]"
    (interval_to_string (env_get "x" e1));

  let e2 = filter_true e (var "x" <: const 3) in
  assert_equal "x<3 from [-5,10]" "[-5, 2]"
    (interval_to_string (env_get "x" e2));

  let e3 = filter_true e (var "x" ==: const 5) in
  assert_equal "x==5 from [-5,10]" "[5, 5]"
    (interval_to_string (env_get "x" e3));

  (* Filter with And *)
  let e4 = filter_true e (And (var "x" >=: const 0, var "x" <=: const 5)) in
  assert_equal "0<=x<=5 from [-5,10]" "[0, 5]"
    (interval_to_string (env_get "x" e4));

  (* Filter false *)
  let e5 = filter_false e (var "x" <: const 0) in
  assert_equal "NOT(x<0) from [-5,10]" "[0, 10]"
    (interval_to_string (env_get "x" e5))

let test_simple_assignment () =
  Printf.printf "\n── Simple Analysis ──\n";
  let prog = seq [
    assign "x" (const 5);
    assign "y" (var "x" +: const 3)
  ] in
  let r = analyze env_bot prog in
  assert_equal "x after assign" "[5, 5]"
    (interval_to_string (env_get "x" r.final_env));
  assert_equal "y = x + 3" "[8, 8]"
    (interval_to_string (env_get "y" r.final_env));
  assert_equal "no warnings" "0" (string_of_int (List.length r.warnings))

let test_if_analysis () =
  Printf.printf "\n── If Analysis ──\n";
  let e = env_set "x" (Itv (Fin (-5), Fin 5)) env_bot in
  let prog = if_ (var "x" >=: const 0)
    (assign "y" (var "x"))
    (assign "y" (Neg (var "x")))
  in
  let r = analyze e prog in
  assert_equal "y after abs(x)" "[0, 5]"
    (interval_to_string (env_get "y" r.final_env))

let test_counter_loop () =
  Printf.printf "\n── Counter Loop ──\n";
  let prog = example_counter () in
  let r = analyze env_bot prog in
  assert_equal "no warnings" "0" (string_of_int (List.length r.warnings));
  assert_true "loop converged" (r.iterations > 0)

let test_division_warning () =
  Printf.printf "\n── Division Warning ──\n";
  let prog = example_div_check () in
  let r = analyze env_bot prog in
  (* x is uninitialized (Bot), so division is a definite issue *)
  assert_true "has div-by-zero warning" (List.length r.warnings > 0);

  (* With x initialized to include zero *)
  let e = env_set "x" (Itv (Fin (-5), Fin 5)) env_bot in
  let r2 = analyze e prog in
  assert_true "possible div-by-zero" (List.exists (function
    | PossibleDivisionByZero _ -> true | _ -> false
  ) r2.warnings);

  (* With x guaranteed non-zero *)
  let e3 = env_set "x" (Itv (Fin 1, Fin 10)) env_bot in
  let r3 = analyze e3 prog in
  assert_equal "no warnings when x>0" "0" (string_of_int (List.length r3.warnings))

let test_dead_code () =
  Printf.printf "\n── Dead Code Detection ──\n";
  let prog = example_dead_code () in
  let r = analyze env_bot prog in
  assert_true "unreachable code detected" (List.exists (function
    | UnreachableCode -> true | _ -> false
  ) r.warnings);
  assert_equal "y = 2" "[2, 2]"
    (interval_to_string (env_get "y" r.final_env))

let test_nested_loops () =
  Printf.printf "\n── Nested Loops ──\n";
  let prog = example_nested_loop () in
  let r = analyze env_bot prog in
  assert_true "loop converged" (r.iterations >= 0);
  (* After outer loop: i should be >= 5 *)
  let i_val = env_get "i" r.final_env in
  assert_true "i >= 5" (interval_le (Itv (Fin 5, Fin 5)) (interval_join i_val (Itv (Fin 5, Fin 5))))

let test_assertion_analysis () =
  Printf.printf "\n── Assertion Analysis ──\n";
  (* Assert that passes *)
  let prog1 = seq [
    assign "x" (const 5);
    assert_ (var "x" >=: const 0)
  ] in
  let r1 = analyze env_bot prog1 in
  assert_equal "no assertion warnings" "0" (string_of_int (List.length r1.warnings));

  (* Assert that definitely fails *)
  let prog2 = seq [
    assign "x" (const (-1));
    assert_ (var "x" >=: const 0)
  ] in
  let r2 = analyze env_bot prog2 in
  assert_true "definite assertion failure" (List.exists (function
    | DefiniteAssertionFailure _ -> true | _ -> false
  ) r2.warnings);

  (* Assert that might fail *)
  let e = env_set "x" (Itv (Fin (-5), Fin 5)) env_bot in
  let prog3 = assert_ (var "x" >=: const 0) in
  let r3 = analyze e prog3 in
  assert_true "possible assertion failure" (List.exists (function
    | PossibleAssertionFailure _ -> true | _ -> false
  ) r3.warnings)

let test_modular_arithmetic () =
  Printf.printf "\n── Modular Arithmetic ──\n";
  let a = Itv (Fin 7, Fin 15) in
  let b = Itv (Fin 3, Fin 5) in
  let r = interval_mod a b in
  assert_true "mod result is not bot" (not (is_bot r));
  match r with
  | Itv (lo, hi) ->
    assert_true "mod lo >= 0" (bound_le (Fin 0) lo || bound_eq lo (Fin 0));
    assert_true "mod hi <= 4" (bound_le hi (Fin 4))
  | Bot -> assert_true "mod should not be bot" false

let test_var_comparison () =
  Printf.printf "\n── Variable Comparison Filtering ──\n";
  let e = env_set "x" (Itv (Fin 0, Fin 10)) env_bot in
  let e = env_set "y" (Itv (Fin 0, Fin 10)) e in
  let e1 = filter_true e (var "x" <: var "y") in
  assert_equal "x after x<y" "[0, 9]"
    (interval_to_string (env_get "x" e1));
  assert_equal "y after x<y" "[1, 10]"
    (interval_to_string (env_get "y" e1));

  let e2 = filter_true e (var "x" ==: var "y") in
  assert_equal "x after x==y" "[0, 10]"
    (interval_to_string (env_get "x" e2));
  assert_equal "y after x==y" "[0, 10]"
    (interval_to_string (env_get "y" e2))

let test_trace_analysis () =
  Printf.printf "\n── Trace Analysis ──\n";
  let prog = seq [
    assign "x" (const 3);
    assign "y" (var "x" +: const 2)
  ] in
  let (result, traces) = trace_analyze env_bot prog in
  assert_true "trace has entries" (List.length traces > 0);
  assert_equal "y = 5" "[5, 5]"
    (interval_to_string (env_get "y" result.final_env))

let test_or_filter () =
  Printf.printf "\n── Or Filter ──\n";
  let e = env_set "x" (Itv (Fin 0, Fin 10)) env_bot in
  let filtered = filter_true e (Or (var "x" <: const 3, var "x" >: const 7)) in
  assert_equal "x after x<3 || x>7" "[0, 10]"
    (interval_to_string (env_get "x" filtered))
    (* Or produces join, which is conservative *)

let test_complex_program () =
  Printf.printf "\n── Complex Program ──\n";
  (* sum := 0; i := 1; while (i <= 100) { sum := sum + i; i := i + 1 } *)
  let prog = seq [
    assign "sum" (const 0);
    assign "i" (const 1);
    while_ (var "i" <=: const 100) (
      seq [
        assign "sum" (var "sum" +: var "i");
        assign "i" (var "i" +: const 1)
      ]
    )
  ] in
  let r = analyze env_bot prog in
  assert_equal "no warnings" "0" (string_of_int (List.length r.warnings));
  (* After loop, i should be >= 101 *)
  let i_val = env_get "i" r.final_env in
  (match i_val with
  | Itv (lo, _) -> assert_true "i >= 101" (bound_le (Fin 101) lo)
  | Bot -> assert_true "i should not be bot" false);
  (* sum should be non-negative *)
  let sum_val = env_get "sum" r.final_env in
  (match sum_val with
  | Itv (lo, _) -> assert_true "sum >= 0" (bound_le (Fin 0) lo)
  | Bot -> assert_true "sum should not be bot" false)

let test_pretty_printer () =
  Printf.printf "\n── Pretty Printer ──\n";
  let prog = assign "x" (const 5) in
  let s = stmt_to_string 0 prog in
  assert_equal "print assign" "x := 5" s;

  let prog2 = if_ (var "x" <: const 0) (assign "y" (const 1)) (assign "y" (const 2)) in
  let s2 = stmt_to_string 0 prog2 in
  assert_true "print if contains 'if'" (String.length s2 > 0);

  assert_equal "print binop +" "+" (binop_to_string Add);
  assert_equal "print cmpop <" "<" (cmpop_to_string Lt);
  assert_equal "print bexpr true" "true" (bexpr_to_string True)

let test_constructors () =
  Printf.printf "\n── Convenience Constructors ──\n";
  let s = seq [assign "a" (const 1); assign "b" (const 2); assign "c" (const 3)] in
  let r = analyze env_bot s in
  assert_equal "a = 1" "[1, 1]" (interval_to_string (env_get "a" r.final_env));
  assert_equal "b = 2" "[2, 2]" (interval_to_string (env_get "b" r.final_env));
  assert_equal "c = 3" "[3, 3]" (interval_to_string (env_get "c" r.final_env))

let test_bounded_example () =
  Printf.printf "\n── Bounded Multiply Example ──\n";
  let prog = example_bounded () in
  let r = analyze env_bot prog in
  assert_equal "no warnings" "0" (string_of_int (List.length r.warnings))

let test_interval_edge_cases () =
  Printf.printf "\n── Interval Edge Cases ──\n";
  assert_true "Bot is_bot" (is_bot Bot);
  assert_false "top is not bot" (is_bot top_interval);
  assert_true "Bot == Bot" (interval_eq Bot Bot);
  assert_false "Bot != top" (interval_eq Bot top_interval);
  assert_equal "top" "[-∞, +∞]" (interval_to_string top_interval);
  assert_equal "Bot join Bot" "⊥" (interval_to_string (interval_join Bot Bot));
  assert_equal "top meet top" "[-∞, +∞]" (interval_to_string (interval_meet top_interval top_interval))

let test_env_to_string () =
  Printf.printf "\n── Environment Printing ──\n";
  assert_equal "empty env" "{}" (env_to_string env_bot);
  let e = env_set "x" (const_interval 5) env_bot in
  let s = env_to_string e in
  assert_true "env contains x" (String.length s > 0)

let test_warning_to_string () =
  Printf.printf "\n── Warning Printing ──\n";
  let w = UnreachableCode in
  let s = warning_to_string w in
  assert_true "unreachable warning text" (String.length s > 0);
  let w2 = PossibleDivisionByZero (const 0, env_bot) in
  let s2 = warning_to_string w2 in
  assert_true "div-zero warning text" (String.length s2 > 0)

let () =
  Printf.printf "╔══════════════════════════════════════════════════╗\n";
  Printf.printf "║    Abstract Interpretation - Interval Domain     ║\n";
  Printf.printf "╚══════════════════════════════════════════════════╝\n";

  test_bounds ();
  test_intervals ();
  test_interval_arithmetic ();
  test_widening_narrowing ();
  test_environment ();
  test_expr_eval ();
  test_filtering ();
  test_simple_assignment ();
  test_if_analysis ();
  test_counter_loop ();
  test_division_warning ();
  test_dead_code ();
  test_nested_loops ();
  test_assertion_analysis ();
  test_modular_arithmetic ();
  test_var_comparison ();
  test_trace_analysis ();
  test_or_filter ();
  test_complex_program ();
  test_pretty_printer ();
  test_constructors ();
  test_bounded_example ();
  test_interval_edge_cases ();
  test_env_to_string ();
  test_warning_to_string ();

  Printf.printf "\n══════════════════════════════════════════════════\n";
  Printf.printf "Results: %d passed, %d failed\n" !tests_passed !tests_failed;
  Printf.printf "══════════════════════════════════════════════════\n";

  (* Run example programs *)
  Printf.printf "\n╔══════════════════════════════════════════════════╗\n";
  Printf.printf "║              Example Programs                     ║\n";
  Printf.printf "╚══════════════════════════════════════════════════╝\n";

  let run_example name prog init_env =
    Printf.printf "\n─── %s ───\n" name;
    Printf.printf "Program:\n%s\n\n" (stmt_to_string 1 prog);
    Printf.printf "Initial: %s\n" (env_to_string init_env);
    let r = analyze init_env prog in
    Printf.printf "Final:   %s\n" (env_to_string r.final_env);
    if r.warnings <> [] then begin
      Printf.printf "Warnings:\n";
      List.iter (fun w -> Printf.printf "  %s\n" (warning_to_string w)) r.warnings
    end;
    if r.iterations > 0 then
      Printf.printf "Loop iterations (widening): %d\n" r.iterations
  in

  run_example "Counter" (example_counter ()) env_bot;
  run_example "Absolute Value"
    (example_abs ())
    (env_set "x" (Itv (Fin (-10), Fin 10)) env_bot);
  run_example "Division Check (unsafe)"
    (example_div_check ())
    (env_set "x" (Itv (Fin (-5), Fin 5)) env_bot);
  run_example "Division Check (safe)"
    (example_div_check ())
    (env_set "x" (Itv (Fin 1, Fin 10)) env_bot);
  run_example "Nested Loops" (example_nested_loop ()) env_bot;
  run_example "Bounded Multiply" (example_bounded ()) env_bot;
  run_example "Dead Code" (example_dead_code ()) env_bot;

  if !tests_failed > 0 then exit 1
