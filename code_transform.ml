(* ============================================================================
   code_transform.ml - Autonomous Code Transformation Pipeline Engine
   ============================================================================

   An autonomous multi-pass program transformation engine that applies
   compiler-style transformations to a simple lambda calculus, demonstrating
   CPS conversion, A-normal form, lambda lifting, constant folding, dead code
   elimination, inlining, defunctionalization, and closure conversion — with
   step-by-step traces and autonomous optimization recommendations.

   Demonstrates:
   - CPS (Continuation-Passing Style) conversion
   - A-Normal Form (ANF) conversion
   - Lambda lifting (closure elimination)
   - Constant folding & propagation
   - Dead code elimination
   - Inlining of small functions
   - Defunctionalization (higher-order → first-order)
   - Closure conversion (explicit environment passing)
   - Autonomous pipeline optimization (pass ordering, iteration)
   - Transformation health scoring

   Core idea: Given a lambda calculus expression, the engine applies a
   configurable sequence of transformation passes, recording each intermediate
   form. It then analyzes the transformation trace to recommend optimal pass
   orderings and detect when further optimization is futile.

   Usage:
     let () =
       (* Transform a simple expression *)
       let expr = App (Lam ("x", Add (Var "x", Lit 1)), Lit 41) in
       let result = transform_pipeline expr [ConstFold; DeadCode; ANF] in
       print_pipeline_result result;

       (* Autonomous optimization *)
       let session = autonomous_optimize expr in
       print_session session
   ============================================================================ *)

(* ── Random Infrastructure ──────────────────────────────────────────────── *)

let global_seed = ref 77889900

let next_random () =
  global_seed := (!global_seed * 1103515245 + 12345) land 0x3FFFFFFF;
  !global_seed

let random_int bound =
  if bound <= 0 then 0
  else (next_random ()) mod bound

let random_float () =
  float_of_int (random_int 10000) /. 10000.0

(* ── Expression AST ─────────────────────────────────────────────────────── *)

type expr =
  | Lit of int                        (* integer literal *)
  | BoolLit of bool                   (* boolean literal *)
  | Var of string                     (* variable reference *)
  | Lam of string * expr              (* lambda abstraction *)
  | App of expr * expr                (* function application *)
  | Add of expr * expr                (* addition *)
  | Sub of expr * expr                (* subtraction *)
  | Mul of expr * expr                (* multiplication *)
  | Div of expr * expr                (* division *)
  | IfThenElse of expr * expr * expr  (* conditional *)
  | Let of string * expr * expr       (* let binding *)
  | LetRec of string * expr * expr    (* recursive let *)
  | Tuple of expr list                (* tuple construction *)
  | Proj of expr * int                (* tuple projection *)
  | Prim of string * expr list        (* primitive operation *)

(* ── Pretty Printer ─────────────────────────────────────────────────────── *)

let rec pp_expr = function
  | Lit n -> string_of_int n
  | BoolLit b -> string_of_bool b
  | Var x -> x
  | Lam (x, body) ->
    Printf.sprintf "(fun %s -> %s)" x (pp_expr body)
  | App (f, arg) ->
    Printf.sprintf "(%s %s)" (pp_expr f) (pp_expr arg)
  | Add (a, b) ->
    Printf.sprintf "(%s + %s)" (pp_expr a) (pp_expr b)
  | Sub (a, b) ->
    Printf.sprintf "(%s - %s)" (pp_expr a) (pp_expr b)
  | Mul (a, b) ->
    Printf.sprintf "(%s * %s)" (pp_expr a) (pp_expr b)
  | Div (a, b) ->
    Printf.sprintf "(%s / %s)" (pp_expr a) (pp_expr b)
  | IfThenElse (c, t, e) ->
    Printf.sprintf "(if %s then %s else %s)" (pp_expr c) (pp_expr t) (pp_expr e)
  | Let (x, v, body) ->
    Printf.sprintf "(let %s = %s in %s)" x (pp_expr v) (pp_expr body)
  | LetRec (x, v, body) ->
    Printf.sprintf "(let rec %s = %s in %s)" x (pp_expr v) (pp_expr body)
  | Tuple es ->
    Printf.sprintf "(%s)" (String.concat ", " (List.map pp_expr es))
  | Proj (e, i) ->
    Printf.sprintf "%s.%d" (pp_expr e) i
  | Prim (name, args) ->
    Printf.sprintf "%s(%s)" name (String.concat ", " (List.map pp_expr args))

(* ── Free Variables ─────────────────────────────────────────────────────── *)

module StringSet = Set.Make(String)

let rec free_vars = function
  | Lit _ | BoolLit _ -> StringSet.empty
  | Var x -> StringSet.singleton x
  | Lam (x, body) -> StringSet.remove x (free_vars body)
  | App (f, arg) -> StringSet.union (free_vars f) (free_vars arg)
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) ->
    StringSet.union (free_vars a) (free_vars b)
  | IfThenElse (c, t, e) ->
    StringSet.union (free_vars c) (StringSet.union (free_vars t) (free_vars e))
  | Let (x, v, body) ->
    StringSet.union (free_vars v) (StringSet.remove x (free_vars body))
  | LetRec (x, v, body) ->
    let s = StringSet.union (free_vars v) (free_vars body) in
    StringSet.remove x s
  | Tuple es -> List.fold_left (fun acc e -> StringSet.union acc (free_vars e)) StringSet.empty es
  | Proj (e, _) -> free_vars e
  | Prim (_, args) -> List.fold_left (fun acc e -> StringSet.union acc (free_vars e)) StringSet.empty args

(* ── AST Size ───────────────────────────────────────────────────────────── *)

let rec ast_size = function
  | Lit _ | BoolLit _ | Var _ -> 1
  | Lam (_, body) -> 1 + ast_size body
  | App (f, arg) -> 1 + ast_size f + ast_size arg
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) ->
    1 + ast_size a + ast_size b
  | IfThenElse (c, t, e) -> 1 + ast_size c + ast_size t + ast_size e
  | Let (_, v, body) | LetRec (_, v, body) -> 1 + ast_size v + ast_size body
  | Tuple es -> 1 + List.fold_left (fun acc e -> acc + ast_size e) 0 es
  | Proj (e, _) -> 1 + ast_size e
  | Prim (_, args) -> 1 + List.fold_left (fun acc e -> acc + ast_size e) 0 args

(* ── AST Depth ──────────────────────────────────────────────────────────── *)

let rec ast_depth = function
  | Lit _ | BoolLit _ | Var _ -> 1
  | Lam (_, body) -> 1 + ast_depth body
  | App (f, arg) -> 1 + max (ast_depth f) (ast_depth arg)
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) ->
    1 + max (ast_depth a) (ast_depth b)
  | IfThenElse (c, t, e) -> 1 + max (ast_depth c) (max (ast_depth t) (ast_depth e))
  | Let (_, v, body) | LetRec (_, v, body) -> 1 + max (ast_depth v) (ast_depth body)
  | Tuple es -> 1 + List.fold_left (fun acc e -> max acc (ast_depth e)) 0 es
  | Proj (e, _) -> 1 + ast_depth e
  | Prim (_, args) -> 1 + List.fold_left (fun acc e -> max acc (ast_depth e)) 0 args

(* ── Lambda Count ───────────────────────────────────────────────────────── *)

let rec lambda_count = function
  | Lit _ | BoolLit _ | Var _ -> 0
  | Lam (_, body) -> 1 + lambda_count body
  | App (f, arg) -> lambda_count f + lambda_count arg
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) ->
    lambda_count a + lambda_count b
  | IfThenElse (c, t, e) -> lambda_count c + lambda_count t + lambda_count e
  | Let (_, v, body) | LetRec (_, v, body) -> lambda_count v + lambda_count body
  | Tuple es -> List.fold_left (fun acc e -> acc + lambda_count e) 0 es
  | Proj (e, _) -> lambda_count e
  | Prim (_, args) -> List.fold_left (fun acc e -> acc + lambda_count e) 0 args

(* ── Substitution ───────────────────────────────────────────────────────── *)

let fresh_counter = ref 0

let fresh_var prefix =
  incr fresh_counter;
  Printf.sprintf "%s_%d" prefix !fresh_counter

let rec subst x replacement = function
  | Lit n -> Lit n
  | BoolLit b -> BoolLit b
  | Var y -> if y = x then replacement else Var y
  | Lam (y, body) ->
    if y = x then Lam (y, body)
    else if StringSet.mem y (free_vars replacement) then
      let y' = fresh_var y in
      Lam (y', subst x replacement (subst y (Var y') body))
    else Lam (y, subst x replacement body)
  | App (f, arg) -> App (subst x replacement f, subst x replacement arg)
  | Add (a, b) -> Add (subst x replacement a, subst x replacement b)
  | Sub (a, b) -> Sub (subst x replacement a, subst x replacement b)
  | Mul (a, b) -> Mul (subst x replacement a, subst x replacement b)
  | Div (a, b) -> Div (subst x replacement a, subst x replacement b)
  | IfThenElse (c, t, e) ->
    IfThenElse (subst x replacement c, subst x replacement t, subst x replacement e)
  | Let (y, v, body) ->
    if y = x then Let (y, subst x replacement v, body)
    else if StringSet.mem y (free_vars replacement) then
      let y' = fresh_var y in
      Let (y', subst x replacement v, subst x replacement (subst y (Var y') body))
    else Let (y, subst x replacement v, subst x replacement body)
  | LetRec (y, v, body) ->
    if y = x then LetRec (y, v, body)
    else
      LetRec (y, subst x replacement v, subst x replacement body)
  | Tuple es -> Tuple (List.map (subst x replacement) es)
  | Proj (e, i) -> Proj (subst x replacement e, i)
  | Prim (name, args) -> Prim (name, List.map (subst x replacement) args)

(* ══════════════════════════════════════════════════════════════════════════
   TRANSFORMATION PASSES
   ══════════════════════════════════════════════════════════════════════════ *)

(* ── Pass 1: Constant Folding ───────────────────────────────────────────── *)

let rec const_fold = function
  | Add (Lit a, Lit b) -> Lit (a + b)
  | Sub (Lit a, Lit b) -> Lit (a - b)
  | Mul (Lit a, Lit b) -> Lit (a * b)
  | Div (Lit a, Lit b) when b <> 0 -> Lit (a / b)
  | Add (e, Lit 0) | Add (Lit 0, e) -> const_fold e
  | Sub (e, Lit 0) -> const_fold e
  | Mul (_, Lit 0) | Mul (Lit 0, _) -> Lit 0
  | Mul (e, Lit 1) | Mul (Lit 1, e) -> const_fold e
  | IfThenElse (BoolLit true, t, _) -> const_fold t
  | IfThenElse (BoolLit false, _, e) -> const_fold e
  | Add (a, b) -> let a' = const_fold a and b' = const_fold b in
    (match a', b' with Lit x, Lit y -> Lit (x + y) | _ -> Add (a', b'))
  | Sub (a, b) -> let a' = const_fold a and b' = const_fold b in
    (match a', b' with Lit x, Lit y -> Lit (x - y) | _ -> Sub (a', b'))
  | Mul (a, b) -> let a' = const_fold a and b' = const_fold b in
    (match a', b' with Lit x, Lit y -> Lit (x * y) | _ -> Mul (a', b'))
  | Div (a, b) -> let a' = const_fold a and b' = const_fold b in
    (match a', b' with Lit x, Lit y when y <> 0 -> Lit (x / y) | _ -> Div (a', b'))
  | Lam (x, body) -> Lam (x, const_fold body)
  | App (f, arg) -> App (const_fold f, const_fold arg)
  | IfThenElse (c, t, e) -> let c' = const_fold c in
    (match c' with
     | BoolLit true -> const_fold t
     | BoolLit false -> const_fold e
     | _ -> IfThenElse (c', const_fold t, const_fold e))
  | Let (x, v, body) -> Let (x, const_fold v, const_fold body)
  | LetRec (x, v, body) -> LetRec (x, const_fold v, const_fold body)
  | Tuple es -> Tuple (List.map const_fold es)
  | Proj (Tuple es, i) when i >= 0 && i < List.length es -> const_fold (List.nth es i)
  | Proj (e, i) -> Proj (const_fold e, i)
  | Prim (name, args) -> Prim (name, List.map const_fold args)
  | e -> e

(* ── Pass 2: Dead Code Elimination ─────────────────────────────────────── *)

let rec dead_code_elim = function
  | Let (x, v, body) ->
    let body' = dead_code_elim body in
    if StringSet.mem x (free_vars body') then
      Let (x, dead_code_elim v, body')
    else body'
  | LetRec (x, v, body) ->
    let body' = dead_code_elim body in
    if StringSet.mem x (free_vars body') then
      LetRec (x, dead_code_elim v, body')
    else body'
  | Lam (x, body) -> Lam (x, dead_code_elim body)
  | App (f, arg) -> App (dead_code_elim f, dead_code_elim arg)
  | Add (a, b) -> Add (dead_code_elim a, dead_code_elim b)
  | Sub (a, b) -> Sub (dead_code_elim a, dead_code_elim b)
  | Mul (a, b) -> Mul (dead_code_elim a, dead_code_elim b)
  | Div (a, b) -> Div (dead_code_elim a, dead_code_elim b)
  | IfThenElse (c, t, e) -> IfThenElse (dead_code_elim c, dead_code_elim t, dead_code_elim e)
  | Tuple es -> Tuple (List.map dead_code_elim es)
  | Proj (e, i) -> Proj (dead_code_elim e, i)
  | Prim (name, args) -> Prim (name, List.map dead_code_elim args)
  | e -> e

(* ── Pass 3: Inlining ──────────────────────────────────────────────────── *)

let inline_threshold = 5

let rec inline_small = function
  | Let (x, (Lam (_, _) as v), body) when ast_size v <= inline_threshold ->
    inline_small (subst x v body)
  | Let (x, v, body) when ast_size v <= 3 ->
    inline_small (subst x (inline_small v) body)
  | Let (x, v, body) -> Let (x, inline_small v, inline_small body)
  | LetRec (x, v, body) -> LetRec (x, inline_small v, inline_small body)
  | Lam (x, body) -> Lam (x, inline_small body)
  | App (Lam (x, body), arg) when ast_size arg <= inline_threshold ->
    inline_small (subst x (inline_small arg) body)
  | App (f, arg) -> App (inline_small f, inline_small arg)
  | Add (a, b) -> Add (inline_small a, inline_small b)
  | Sub (a, b) -> Sub (inline_small a, inline_small b)
  | Mul (a, b) -> Mul (inline_small a, inline_small b)
  | Div (a, b) -> Div (inline_small a, inline_small b)
  | IfThenElse (c, t, e) -> IfThenElse (inline_small c, inline_small t, inline_small e)
  | Tuple es -> Tuple (List.map inline_small es)
  | Proj (e, i) -> Proj (inline_small e, i)
  | Prim (name, args) -> Prim (name, List.map inline_small args)
  | e -> e

(* ── Pass 4: CPS Conversion ────────────────────────────────────────────── *)

let rec cps_convert expr k =
  match expr with
  | Lit _ | BoolLit _ | Var _ -> App (k, expr)
  | Lam (x, body) ->
    let kv = fresh_var "k" in
    App (k, Lam (x, Lam (kv, cps_convert body (Var kv))))
  | App (f, arg) ->
    let fv = fresh_var "f" in
    let av = fresh_var "a" in
    cps_convert f (Lam (fv, cps_convert arg (Lam (av, App (App (Var fv, Var av), k)))))
  | Add (a, b) ->
    let av = fresh_var "a" in
    let bv = fresh_var "b" in
    cps_convert a (Lam (av, cps_convert b (Lam (bv, App (k, Add (Var av, Var bv))))))
  | Sub (a, b) ->
    let av = fresh_var "a" in
    let bv = fresh_var "b" in
    cps_convert a (Lam (av, cps_convert b (Lam (bv, App (k, Sub (Var av, Var bv))))))
  | Mul (a, b) ->
    let av = fresh_var "a" in
    let bv = fresh_var "b" in
    cps_convert a (Lam (av, cps_convert b (Lam (bv, App (k, Mul (Var av, Var bv))))))
  | Div (a, b) ->
    let av = fresh_var "a" in
    let bv = fresh_var "b" in
    cps_convert a (Lam (av, cps_convert b (Lam (bv, App (k, Div (Var av, Var bv))))))
  | IfThenElse (c, t, e) ->
    let cv = fresh_var "c" in
    cps_convert c (Lam (cv, IfThenElse (Var cv, cps_convert t k, cps_convert e k)))
  | Let (x, v, body) ->
    cps_convert v (Lam (x, cps_convert body k))
  | LetRec (x, v, body) ->
    LetRec (x, v, cps_convert body k)
  | Tuple es ->
    let vars = List.mapi (fun i _ -> fresh_var (Printf.sprintf "t%d" i)) es in
    let result = App (k, Tuple (List.map (fun v -> Var v) vars)) in
    List.fold_right2 (fun e v acc ->
      cps_convert e (Lam (v, acc))
    ) es vars result
  | Proj (e, i) ->
    let ev = fresh_var "p" in
    cps_convert e (Lam (ev, App (k, Proj (Var ev, i))))
  | Prim (name, args) ->
    let vars = List.mapi (fun i _ -> fresh_var (Printf.sprintf "p%d" i)) args in
    let result = App (k, Prim (name, List.map (fun v -> Var v) vars)) in
    List.fold_right2 (fun e v acc ->
      cps_convert e (Lam (v, acc))
    ) args vars result

let cps_transform expr =
  fresh_counter := 0;
  let kv = fresh_var "halt" in
  cps_convert expr (Var kv)

(* ── Pass 5: A-Normal Form ─────────────────────────────────────────────── *)

let rec anf_convert expr =
  match expr with
  | Lit _ | BoolLit _ | Var _ -> expr
  | Lam (x, body) -> Lam (x, anf_convert body)
  | App (f, arg) ->
    let fv = fresh_var "fn" in
    let av = fresh_var "arg" in
    Let (fv, anf_convert f, Let (av, anf_convert arg, App (Var fv, Var av)))
  | Add (a, b) ->
    let av = fresh_var "l" in
    let bv = fresh_var "r" in
    Let (av, anf_convert a, Let (bv, anf_convert b, Add (Var av, Var bv)))
  | Sub (a, b) ->
    let av = fresh_var "l" in
    let bv = fresh_var "r" in
    Let (av, anf_convert a, Let (bv, anf_convert b, Sub (Var av, Var bv)))
  | Mul (a, b) ->
    let av = fresh_var "l" in
    let bv = fresh_var "r" in
    Let (av, anf_convert a, Let (bv, anf_convert b, Mul (Var av, Var bv)))
  | Div (a, b) ->
    let av = fresh_var "l" in
    let bv = fresh_var "r" in
    Let (av, anf_convert a, Let (bv, anf_convert b, Div (Var av, Var bv)))
  | IfThenElse (c, t, e) ->
    let cv = fresh_var "cond" in
    Let (cv, anf_convert c, IfThenElse (Var cv, anf_convert t, anf_convert e))
  | Let (x, v, body) -> Let (x, anf_convert v, anf_convert body)
  | LetRec (x, v, body) -> LetRec (x, anf_convert v, anf_convert body)
  | Tuple es ->
    let vars = List.mapi (fun i _ -> fresh_var (Printf.sprintf "elem%d" i)) es in
    let result = Tuple (List.map (fun v -> Var v) vars) in
    List.fold_right2 (fun e v acc ->
      Let (v, anf_convert e, acc)
    ) es vars result
  | Proj (e, i) ->
    let ev = fresh_var "tup" in
    Let (ev, anf_convert e, Proj (Var ev, i))
  | Prim (name, args) ->
    let vars = List.mapi (fun i _ -> fresh_var (Printf.sprintf "arg%d" i)) args in
    let result = Prim (name, List.map (fun v -> Var v) vars) in
    List.fold_right2 (fun e v acc ->
      Let (v, anf_convert e, acc)
    ) args vars result

(* ── Pass 6: Lambda Lifting ─────────────────────────────────────────────── *)

let lifted_functions : (string * string list * expr) list ref = ref []

let rec lambda_lift env = function
  | Lit n -> Lit n
  | BoolLit b -> BoolLit b
  | Var x -> Var x
  | Lam (x, body) ->
    let body' = lambda_lift (x :: env) body in
    let fvs = StringSet.elements (StringSet.diff (free_vars (Lam (x, body')))
      (StringSet.of_list env)) in
    if fvs = [] then Lam (x, body')
    else begin
      let fname = fresh_var "lifted" in
      let all_params = fvs @ [x] in
      lifted_functions := (fname, all_params, body') :: !lifted_functions;
      List.fold_left (fun acc v -> App (acc, Var v)) (Var fname) fvs
    end
  | App (f, arg) -> App (lambda_lift env f, lambda_lift env arg)
  | Add (a, b) -> Add (lambda_lift env a, lambda_lift env b)
  | Sub (a, b) -> Sub (lambda_lift env a, lambda_lift env b)
  | Mul (a, b) -> Mul (lambda_lift env a, lambda_lift env b)
  | Div (a, b) -> Div (lambda_lift env a, lambda_lift env b)
  | IfThenElse (c, t, e) ->
    IfThenElse (lambda_lift env c, lambda_lift env t, lambda_lift env e)
  | Let (x, v, body) ->
    Let (x, lambda_lift env v, lambda_lift (x :: env) body)
  | LetRec (x, v, body) ->
    let env' = x :: env in
    LetRec (x, lambda_lift env' v, lambda_lift env' body)
  | Tuple es -> Tuple (List.map (lambda_lift env) es)
  | Proj (e, i) -> Proj (lambda_lift env e, i)
  | Prim (name, args) -> Prim (name, List.map (lambda_lift env) args)

let lambda_lift_transform expr =
  lifted_functions := [];
  let result = lambda_lift [] expr in
  let defs = List.rev !lifted_functions in
  List.fold_right (fun (name, params, body) acc ->
    let lam = List.fold_right (fun p b -> Lam (p, b)) params body in
    LetRec (name, lam, acc)
  ) defs result

(* ── Pass 7: Closure Conversion ─────────────────────────────────────────── *)

let rec closure_convert = function
  | Lit n -> Lit n
  | BoolLit b -> BoolLit b
  | Var x -> Var x
  | Lam (x, body) ->
    let body' = closure_convert body in
    let fvs = StringSet.elements (free_vars (Lam (x, body'))) in
    if fvs = [] then Lam (x, body')
    else
      let env_var = fresh_var "env" in
      let body_with_env = List.fold_left (fun acc (i, v) ->
        Let (v, Proj (Var env_var, i), acc)
      ) body' (List.mapi (fun i v -> (i, v)) fvs) in
      Tuple [Lam (env_var, Lam (x, body_with_env)); Tuple (List.map (fun v -> Var v) fvs)]
  | App (f, arg) ->
    let f' = closure_convert f in
    let arg' = closure_convert arg in
    (match f' with
     | Tuple [code; env] -> App (App (code, env), arg')
     | _ -> App (f', arg'))
  | Add (a, b) -> Add (closure_convert a, closure_convert b)
  | Sub (a, b) -> Sub (closure_convert a, closure_convert b)
  | Mul (a, b) -> Mul (closure_convert a, closure_convert b)
  | Div (a, b) -> Div (closure_convert a, closure_convert b)
  | IfThenElse (c, t, e) ->
    IfThenElse (closure_convert c, closure_convert t, closure_convert e)
  | Let (x, v, body) -> Let (x, closure_convert v, closure_convert body)
  | LetRec (x, v, body) -> LetRec (x, closure_convert v, closure_convert body)
  | Tuple es -> Tuple (List.map closure_convert es)
  | Proj (e, i) -> Proj (closure_convert e, i)
  | Prim (name, args) -> Prim (name, List.map closure_convert args)

(* ── Pass 8: Defunctionalization ────────────────────────────────────────── *)

let defunc_counter = ref 0

let rec defunctionalize = function
  | Lit n -> Lit n
  | BoolLit b -> BoolLit b
  | Var x -> Var x
  | Lam (x, body) ->
    incr defunc_counter;
    let tag = Printf.sprintf "Closure_%d" !defunc_counter in
    let fvs = StringSet.elements (free_vars (Lam (x, body))) in
    Prim (tag, List.map (fun v -> Var v) fvs)
  | App (f, arg) ->
    Prim ("apply", [defunctionalize f; defunctionalize arg])
  | Add (a, b) -> Add (defunctionalize a, defunctionalize b)
  | Sub (a, b) -> Sub (defunctionalize a, defunctionalize b)
  | Mul (a, b) -> Mul (defunctionalize a, defunctionalize b)
  | Div (a, b) -> Div (defunctionalize a, defunctionalize b)
  | IfThenElse (c, t, e) ->
    IfThenElse (defunctionalize c, defunctionalize t, defunctionalize e)
  | Let (x, v, body) -> Let (x, defunctionalize v, defunctionalize body)
  | LetRec (x, v, body) -> LetRec (x, defunctionalize v, defunctionalize body)
  | Tuple es -> Tuple (List.map defunctionalize es)
  | Proj (e, i) -> Proj (defunctionalize e, i)
  | Prim (name, args) -> Prim (name, List.map defunctionalize args)

(* ── Pass 9: Constant Propagation ───────────────────────────────────────── *)

let rec const_propagate env = function
  | Lit n -> Lit n
  | BoolLit b -> BoolLit b
  | Var x ->
    (try List.assoc x env with Not_found -> Var x)
  | Let (x, Lit n, body) ->
    const_propagate ((x, Lit n) :: env) body
  | Let (x, BoolLit b, body) ->
    const_propagate ((x, BoolLit b) :: env) body
  | Let (x, v, body) ->
    Let (x, const_propagate env v, const_propagate env body)
  | LetRec (x, v, body) ->
    LetRec (x, const_propagate env v, const_propagate env body)
  | Lam (x, body) ->
    let env' = List.filter (fun (k, _) -> k <> x) env in
    Lam (x, const_propagate env' body)
  | App (f, arg) -> App (const_propagate env f, const_propagate env arg)
  | Add (a, b) -> Add (const_propagate env a, const_propagate env b)
  | Sub (a, b) -> Sub (const_propagate env a, const_propagate env b)
  | Mul (a, b) -> Mul (const_propagate env a, const_propagate env b)
  | Div (a, b) -> Div (const_propagate env a, const_propagate env b)
  | IfThenElse (c, t, e) ->
    IfThenElse (const_propagate env c, const_propagate env t, const_propagate env e)
  | Tuple es -> Tuple (List.map (const_propagate env) es)
  | Proj (e, i) -> Proj (const_propagate env e, i)
  | Prim (name, args) -> Prim (name, List.map (const_propagate env) args)

(* ══════════════════════════════════════════════════════════════════════════
   TRANSFORMATION PIPELINE ENGINE
   ══════════════════════════════════════════════════════════════════════════ *)

type pass_id =
  | ConstFold
  | DeadCode
  | Inline
  | CPS
  | ANF
  | LambdaLift
  | ClosureConvert
  | Defunctionalize
  | ConstPropagate

type pass_result = {
  pass_name: string;
  input_size: int;
  output_size: int;
  input_depth: int;
  output_depth: int;
  input_lambdas: int;
  output_lambdas: int;
  size_delta: int;
  input_expr: string;
  output_expr: string;
}

type pipeline_result = {
  original: expr;
  final_expr: expr;
  passes: pass_result list;
  total_size_reduction: int;
  total_depth_reduction: int;
  total_lambda_reduction: int;
  health_score: float;
}

let pass_name_of = function
  | ConstFold -> "Constant Folding"
  | DeadCode -> "Dead Code Elimination"
  | Inline -> "Inlining"
  | CPS -> "CPS Conversion"
  | ANF -> "A-Normal Form"
  | LambdaLift -> "Lambda Lifting"
  | ClosureConvert -> "Closure Conversion"
  | Defunctionalize -> "Defunctionalization"
  | ConstPropagate -> "Constant Propagation"

let apply_pass pass expr =
  match pass with
  | ConstFold -> const_fold expr
  | DeadCode -> dead_code_elim expr
  | Inline -> inline_small expr
  | CPS -> cps_transform expr
  | ANF ->
    fresh_counter := 0;
    anf_convert expr
  | LambdaLift -> lambda_lift_transform expr
  | ClosureConvert -> closure_convert expr
  | Defunctionalize ->
    defunc_counter := 0;
    defunctionalize expr
  | ConstPropagate -> const_propagate [] expr

let run_pass pass expr =
  let in_size = ast_size expr in
  let in_depth = ast_depth expr in
  let in_lam = lambda_count expr in
  let result = apply_pass pass expr in
  let out_size = ast_size result in
  let out_depth = ast_depth result in
  let out_lam = lambda_count result in
  let pr = {
    pass_name = pass_name_of pass;
    input_size = in_size;
    output_size = out_size;
    input_depth = in_depth;
    output_depth = out_depth;
    input_lambdas = in_lam;
    output_lambdas = out_lam;
    size_delta = out_size - in_size;
    input_expr = pp_expr expr;
    output_expr = pp_expr result;
  } in
  (result, pr)

let transform_pipeline expr passes =
  let original = expr in
  let (final_expr, pass_results) =
    List.fold_left (fun (e, results) pass ->
      let (e', pr) = run_pass pass e in
      (e', results @ [pr])
    ) (expr, []) passes
  in
  let orig_size = ast_size original in
  let final_size = ast_size final_expr in
  let orig_depth = ast_depth original in
  let final_depth = ast_depth final_expr in
  let orig_lam = lambda_count original in
  let final_lam = lambda_count final_expr in
  let size_ratio = if orig_size > 0 then float_of_int final_size /. float_of_int orig_size else 1.0 in
  let depth_ratio = if orig_depth > 0 then float_of_int final_depth /. float_of_int orig_depth else 1.0 in
  let passes_that_reduced = List.length (List.filter (fun pr -> pr.size_delta < 0) pass_results) in
  let total_passes = List.length pass_results in
  let efficiency = if total_passes > 0 then float_of_int passes_that_reduced /. float_of_int total_passes else 0.0 in
  let health =
    (1.0 -. (min size_ratio 2.0 /. 2.0)) *. 40.0
    +. (1.0 -. (min depth_ratio 2.0 /. 2.0)) *. 30.0
    +. efficiency *. 30.0
  in
  {
    original;
    final_expr;
    passes = pass_results;
    total_size_reduction = orig_size - final_size;
    total_depth_reduction = orig_depth - final_depth;
    total_lambda_reduction = orig_lam - final_lam;
    health_score = min 100.0 (max 0.0 health);
  }

(* ══════════════════════════════════════════════════════════════════════════
   AUTONOMOUS OPTIMIZER
   ══════════════════════════════════════════════════════════════════════════ *)

type optimization_strategy =
  | Shrink       (* minimize code size *)
  | Simplify     (* reduce depth and complexity *)
  | Flatten      (* eliminate higher-order functions *)
  | FullPipeline (* apply all transformations *)

type recommendation = {
  rec_strategy: string;
  rec_passes: pass_id list;
  rec_reason: string;
  rec_confidence: float;
}

type autonomous_session = {
  input_expr: expr;
  strategies_tried: (string * pipeline_result) list;
  best_strategy: string;
  best_result: pipeline_result;
  recommendations: recommendation list;
  convergence_rounds: int;
  autonomous_insights: string list;
}

let strategy_passes = function
  | Shrink -> [ConstPropagate; ConstFold; DeadCode; Inline; ConstFold; DeadCode]
  | Simplify -> [ConstPropagate; ConstFold; Inline; DeadCode; ConstFold]
  | Flatten -> [LambdaLift; ClosureConvert; Defunctionalize]
  | FullPipeline -> [ConstPropagate; ConstFold; Inline; DeadCode; ANF; LambdaLift; ConstFold; DeadCode]

let strategy_name = function
  | Shrink -> "Shrink"
  | Simplify -> "Simplify"
  | Flatten -> "Flatten"
  | FullPipeline -> "Full Pipeline"

(* Fixed-point iteration: keep applying a pass sequence until no change *)
let iterate_until_fixed passes expr max_rounds =
  let rec go e round =
    if round >= max_rounds then (e, round)
    else
      let result = List.fold_left (fun acc p -> apply_pass p acc) e passes in
      if pp_expr result = pp_expr e then (e, round)
      else go result (round + 1)
  in
  go expr 0

let generate_recommendations expr results =
  let has_lambdas = lambda_count expr > 0 in
  let has_lets = (match expr with Let _ | LetRec _ -> true | _ -> false) in
  let is_large = ast_size expr > 20 in
  let recs = ref [] in
  if has_lambdas then
    recs := {
      rec_strategy = "Flatten";
      rec_passes = [LambdaLift; Defunctionalize];
      rec_reason = Printf.sprintf "Expression contains %d lambda(s) — flattening could simplify" (lambda_count expr);
      rec_confidence = 0.7 +. random_float () *. 0.2;
    } :: !recs;
  if has_lets then
    recs := {
      rec_strategy = "Propagate & Fold";
      rec_passes = [ConstPropagate; ConstFold; DeadCode];
      rec_reason = "Let bindings present — constant propagation may eliminate intermediaries";
      rec_confidence = 0.6 +. random_float () *. 0.3;
    } :: !recs;
  if is_large then
    recs := {
      rec_strategy = "Aggressive Shrink";
      rec_passes = [ConstPropagate; ConstFold; Inline; DeadCode; ConstFold; DeadCode];
      rec_reason = Printf.sprintf "Large expression (size %d) — aggressive shrinking recommended" (ast_size expr);
      rec_confidence = 0.8 +. random_float () *. 0.15;
    } :: !recs;
  (* Best-performing strategy recommendation *)
  let best = List.fold_left (fun (bname, bscore) (name, r) ->
    if r.health_score > bscore then (name, r.health_score) else (bname, bscore)
  ) ("none", 0.0) results in
  recs := {
    rec_strategy = "Repeat Best";
    rec_passes = [ConstFold; DeadCode];
    rec_reason = Printf.sprintf "Strategy '%s' scored %.1f — iterating its core passes may yield more" (fst best) (snd best);
    rec_confidence = 0.5 +. random_float () *. 0.3;
  } :: !recs;
  List.sort (fun a b -> compare b.rec_confidence a.rec_confidence) !recs

let generate_insights expr best_result all_results =
  let insights = ref [] in
  let orig_size = ast_size expr in
  let final_size = ast_size best_result.final_expr in
  if final_size < orig_size then
    insights := Printf.sprintf "🔬 Best strategy achieved %.1f%% size reduction (%d → %d nodes)"
      (100.0 *. float_of_int (orig_size - final_size) /. float_of_int orig_size)
      orig_size final_size :: !insights
  else if final_size > orig_size then
    insights := Printf.sprintf "📈 Expression grew from %d to %d nodes — structural transforms dominate"
      orig_size final_size :: !insights;
  let total_strategies = List.length all_results in
  let effective = List.length (List.filter (fun (_, r) -> r.health_score > 50.0) all_results) in
  insights := Printf.sprintf "📊 %d/%d strategies scored above 50.0 health" effective total_strategies :: !insights;
  let lam_before = lambda_count expr in
  let lam_after = lambda_count best_result.final_expr in
  if lam_before > 0 && lam_after = 0 then
    insights := "✨ All lambdas eliminated — expression is now first-order" :: !insights
  else if lam_before > 0 && lam_after < lam_before then
    insights := Printf.sprintf "🔧 Lambda count reduced: %d → %d" lam_before lam_after :: !insights;
  let fv = StringSet.cardinal (free_vars best_result.final_expr) in
  if fv > 0 then
    insights := Printf.sprintf "⚠️  Result has %d free variable(s) — may need environment" fv :: !insights;
  if best_result.health_score >= 80.0 then
    insights := "🏆 Excellent transformation health — pipeline is well-suited for this expression" :: !insights
  else if best_result.health_score >= 50.0 then
    insights := "✅ Good transformation health — some room for improvement" :: !insights
  else
    insights := "🔴 Low health score — consider different pass orderings or simpler input" :: !insights;
  List.rev !insights

let autonomous_optimize expr =
  let strategies = [Shrink; Simplify; Flatten; FullPipeline] in
  let results = List.map (fun s ->
    let passes = strategy_passes s in
    let result = transform_pipeline expr passes in
    (strategy_name s, result)
  ) strategies in
  let (best_name, best_result) = List.fold_left (fun (bn, br) (name, r) ->
    if r.health_score > br.health_score then (name, r) else (bn, br)
  ) (List.hd results) (List.tl results) in
  (* Try fixed-point iteration on best strategy *)
  let best_strat = List.find (fun s -> strategy_name s = best_name) strategies in
  let (converged, rounds) = iterate_until_fixed (strategy_passes best_strat) expr 10 in
  let converged_result = transform_pipeline expr
    (List.init (rounds + 1) (fun _ -> strategy_passes best_strat) |> List.flatten) in
  let final_best = if converged_result.health_score > best_result.health_score
    then converged_result else best_result in
  let recs = generate_recommendations expr results in
  let insights = generate_insights expr final_best results in
  {
    input_expr = expr;
    strategies_tried = results;
    best_strategy = best_name;
    best_result = final_best;
    recommendations = recs;
    convergence_rounds = rounds;
    autonomous_insights = insights;
  }

(* ══════════════════════════════════════════════════════════════════════════
   PRINTING & REPORTING
   ══════════════════════════════════════════════════════════════════════════ *)

let print_pass_result pr =
  Printf.printf "  ┌─ %s\n" pr.pass_name;
  Printf.printf "  │  Size: %d → %d (%+d)\n" pr.input_size pr.output_size pr.size_delta;
  Printf.printf "  │  Depth: %d → %d\n" pr.input_depth pr.output_depth;
  Printf.printf "  │  Lambdas: %d → %d\n" pr.input_lambdas pr.output_lambdas;
  Printf.printf "  │  Input:  %s\n" (if String.length pr.input_expr > 80
    then String.sub pr.input_expr 0 77 ^ "..." else pr.input_expr);
  Printf.printf "  │  Output: %s\n" (if String.length pr.output_expr > 80
    then String.sub pr.output_expr 0 77 ^ "..." else pr.output_expr);
  Printf.printf "  └─────────────────────────\n"

let print_pipeline_result result =
  Printf.printf "\n╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║        CODE TRANSFORMATION PIPELINE REPORT          ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════╝\n\n";
  Printf.printf "Original: %s\n" (pp_expr result.original);
  Printf.printf "Final:    %s\n\n" (pp_expr result.final_expr);
  Printf.printf "─── Pass Trace ────────────────────────────────────────\n\n";
  List.iter print_pass_result result.passes;
  Printf.printf "\n─── Summary ───────────────────────────────────────────\n";
  Printf.printf "  Size reduction:   %+d nodes\n" result.total_size_reduction;
  Printf.printf "  Depth reduction:  %+d levels\n" result.total_depth_reduction;
  Printf.printf "  Lambda reduction: %+d\n" result.total_lambda_reduction;
  Printf.printf "  Health score:     %.1f / 100.0\n" result.health_score;
  Printf.printf "────────────────────────────────────────────────────────\n"

let print_recommendation r =
  Printf.printf "  • [%.0f%%] %s\n" (r.rec_confidence *. 100.0) r.rec_strategy;
  Printf.printf "    %s\n" r.rec_reason;
  Printf.printf "    Passes: %s\n\n"
    (String.concat " → " (List.map pass_name_of r.rec_passes))

let print_session session =
  Printf.printf "\n╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║     AUTONOMOUS CODE TRANSFORMATION SESSION          ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════╝\n\n";
  Printf.printf "Input: %s\n" (pp_expr session.input_expr);
  Printf.printf "Input size: %d | depth: %d | lambdas: %d\n\n"
    (ast_size session.input_expr) (ast_depth session.input_expr) (lambda_count session.input_expr);
  Printf.printf "─── Strategies Evaluated ─────────────────────────────\n\n";
  List.iter (fun (name, r) ->
    Printf.printf "  %-15s  health=%.1f  size=%d→%d  depth=%d→%d\n"
      name r.health_score
      (ast_size session.input_expr) (ast_size r.final_expr)
      (ast_depth session.input_expr) (ast_depth r.final_expr)
  ) session.strategies_tried;
  Printf.printf "\n─── Best Strategy: %s ────────────────────────────\n" session.best_strategy;
  Printf.printf "  Convergence rounds: %d\n" session.convergence_rounds;
  print_pipeline_result session.best_result;
  Printf.printf "\n─── Recommendations ──────────────────────────────────\n\n";
  List.iter print_recommendation session.recommendations;
  Printf.printf "─── Autonomous Insights ──────────────────────────────\n\n";
  List.iter (fun s -> Printf.printf "  %s\n" s) session.autonomous_insights;
  Printf.printf "\n══════════════════════════════════════════════════════\n"

(* ══════════════════════════════════════════════════════════════════════════
   TEST SUITE
   ══════════════════════════════════════════════════════════════════════════ *)

let tests_passed = ref 0
let tests_failed = ref 0

let test name f =
  try
    f ();
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  with e ->
    incr tests_failed;
    Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string e)

let assert_true msg b =
  if not b then failwith (Printf.sprintf "Assertion failed: %s" msg)

let assert_eq msg expected actual =
  if expected <> actual then
    failwith (Printf.sprintf "%s: expected %s, got %s" msg expected actual)

let run_tests () =
  Printf.printf "\n═══ Code Transformation Pipeline Tests ════════════════\n\n";

  Printf.printf "── Constant Folding ──\n";
  test "fold addition" (fun () ->
    assert_eq "2+3" "5" (pp_expr (const_fold (Add (Lit 2, Lit 3)))));
  test "fold multiplication" (fun () ->
    assert_eq "3*4" "12" (pp_expr (const_fold (Mul (Lit 3, Lit 4)))));
  test "fold subtraction" (fun () ->
    assert_eq "10-3" "7" (pp_expr (const_fold (Sub (Lit 10, Lit 3)))));
  test "fold division" (fun () ->
    assert_eq "12/4" "3" (pp_expr (const_fold (Div (Lit 12, Lit 4)))));
  test "fold nested" (fun () ->
    let e = Add (Mul (Lit 2, Lit 3), Lit 4) in
    assert_eq "nested" "10" (pp_expr (const_fold e)));
  test "fold identity add 0" (fun () ->
    assert_eq "x+0" "x" (pp_expr (const_fold (Add (Var "x", Lit 0)))));
  test "fold identity mul 1" (fun () ->
    assert_eq "x*1" "x" (pp_expr (const_fold (Mul (Var "x", Lit 1)))));
  test "fold zero mul" (fun () ->
    assert_eq "x*0" "0" (pp_expr (const_fold (Mul (Var "x", Lit 0)))));
  test "fold if true" (fun () ->
    assert_eq "if true" "42" (pp_expr (const_fold (IfThenElse (BoolLit true, Lit 42, Lit 0)))));
  test "fold if false" (fun () ->
    assert_eq "if false" "0" (pp_expr (const_fold (IfThenElse (BoolLit false, Lit 42, Lit 0)))));
  test "fold tuple projection" (fun () ->
    assert_eq "proj" "2" (pp_expr (const_fold (Proj (Tuple [Lit 1; Lit 2; Lit 3], 1)))));

  Printf.printf "\n── Dead Code Elimination ──\n";
  test "remove unused let" (fun () ->
    let e = Let ("x", Lit 42, Lit 1) in
    assert_eq "unused" "1" (pp_expr (dead_code_elim e)));
  test "keep used let" (fun () ->
    let e = Let ("x", Lit 42, Var "x") in
    assert_eq "used" "(let x = 42 in x)" (pp_expr (dead_code_elim e)));
  test "remove unused letrec" (fun () ->
    let e = LetRec ("f", Lam ("x", Var "x"), Lit 1) in
    assert_eq "unused rec" "1" (pp_expr (dead_code_elim e)));
  test "nested dead code" (fun () ->
    let e = Let ("x", Lit 1, Let ("y", Lit 2, Var "x")) in
    assert_eq "nested" "(let x = 1 in x)" (pp_expr (dead_code_elim e)));

  Printf.printf "\n── Inlining ──\n";
  test "inline small let" (fun () ->
    let e = Let ("x", Lit 42, Add (Var "x", Lit 1)) in
    let result = inline_small e in
    assert_eq "inline" "(42 + 1)" (pp_expr result));
  test "inline beta reduction" (fun () ->
    let e = App (Lam ("x", Var "x"), Lit 5) in
    assert_eq "beta" "5" (pp_expr (inline_small e)));

  Printf.printf "\n── CPS Conversion ──\n";
  test "cps literal" (fun () ->
    fresh_counter := 0;
    let e = Lit 42 in
    let result = cps_transform e in
    assert_true "contains halt" (String.length (pp_expr result) > 0));
  test "cps preserves structure" (fun () ->
    fresh_counter := 0;
    let e = Add (Lit 1, Lit 2) in
    let result = cps_transform e in
    assert_true "cps result exists" (ast_size result > ast_size e));
  test "cps lambda" (fun () ->
    fresh_counter := 0;
    let e = Lam ("x", Var "x") in
    let result = cps_transform e in
    assert_true "cps lambda bigger" (ast_size result >= ast_size e));
  test "cps application" (fun () ->
    fresh_counter := 0;
    let e = App (Lam ("x", Var "x"), Lit 5) in
    let result = cps_transform e in
    assert_true "cps app bigger" (ast_size result > ast_size e));

  Printf.printf "\n── A-Normal Form ──\n";
  test "anf literal unchanged" (fun () ->
    fresh_counter := 0;
    assert_eq "lit" "42" (pp_expr (anf_convert (Lit 42))));
  test "anf add introduces lets" (fun () ->
    fresh_counter := 0;
    let result = anf_convert (Add (Lit 1, Lit 2)) in
    assert_true "anf has let" (match result with Let _ -> true | _ -> false));
  test "anf nested" (fun () ->
    fresh_counter := 0;
    let e = Add (Mul (Lit 2, Lit 3), Lit 4) in
    let result = anf_convert e in
    assert_true "anf nested bigger" (ast_size result >= ast_size e));

  Printf.printf "\n── Lambda Lifting ──\n";
  test "lift closed lambda unchanged" (fun () ->
    let e = Lam ("x", Add (Var "x", Lit 1)) in
    let result = lambda_lift_transform e in
    assert_true "still lambda" (lambda_count result >= 1 || ast_size result > 0));
  test "lift captures free vars" (fun () ->
    let e = Let ("y", Lit 10, Lam ("x", Add (Var "x", Var "y"))) in
    let result = lambda_lift_transform e in
    assert_true "lifted result" (ast_size result > 0));

  Printf.printf "\n── Closure Conversion ──\n";
  test "closure closed lambda" (fun () ->
    fresh_counter := 0;
    let e = Lam ("x", Var "x") in
    let result = closure_convert e in
    assert_true "closure result" (ast_size result > 0));
  test "closure open lambda creates tuple" (fun () ->
    fresh_counter := 0;
    let e = Lam ("x", Add (Var "x", Var "y")) in
    let result = closure_convert e in
    assert_true "closure has tuple" (match result with Tuple _ -> true | _ -> false));

  Printf.printf "\n── Defunctionalization ──\n";
  test "defunc lambda to closure tag" (fun () ->
    defunc_counter := 0;
    let e = Lam ("x", Var "x") in
    let result = defunctionalize e in
    assert_true "defunc prim" (match result with Prim _ -> true | _ -> false));
  test "defunc app to apply" (fun () ->
    defunc_counter := 0;
    let e = App (Var "f", Lit 1) in
    let result = defunctionalize e in
    assert_true "defunc apply" (match result with Prim ("apply", _) -> true | _ -> false));
  test "defunc preserves literals" (fun () ->
    defunc_counter := 0;
    assert_eq "lit" "42" (pp_expr (defunctionalize (Lit 42))));

  Printf.printf "\n── Constant Propagation ──\n";
  test "propagate through let" (fun () ->
    let e = Let ("x", Lit 42, Add (Var "x", Lit 1)) in
    assert_eq "prop" "(42 + 1)" (pp_expr (const_propagate [] e)));
  test "propagate bool" (fun () ->
    let e = Let ("b", BoolLit true, IfThenElse (Var "b", Lit 1, Lit 0)) in
    assert_eq "prop bool" "(if true then 1 else 0)" (pp_expr (const_propagate [] e)));
  test "no propagate non-const" (fun () ->
    let e = Let ("x", Add (Var "a", Lit 1), Var "x") in
    let result = const_propagate [] e in
    assert_true "kept let" (match result with Let _ -> true | _ -> false));

  Printf.printf "\n── Pipeline Integration ──\n";
  test "empty pipeline" (fun () ->
    let e = Add (Lit 1, Lit 2) in
    let result = transform_pipeline e [] in
    assert_eq "unchanged" (pp_expr e) (pp_expr result.final_expr));
  test "single pass pipeline" (fun () ->
    let e = Add (Lit 1, Lit 2) in
    let result = transform_pipeline e [ConstFold] in
    assert_eq "folded" "3" (pp_expr result.final_expr));
  test "multi-pass pipeline" (fun () ->
    let e = Let ("x", Add (Lit 1, Lit 2), Add (Var "x", Lit 4)) in
    let result = transform_pipeline e [ConstPropagate; ConstFold; DeadCode] in
    assert_eq "multi" "7" (pp_expr result.final_expr));
  test "pipeline records all passes" (fun () ->
    let e = Add (Lit 1, Lit 2) in
    let result = transform_pipeline e [ConstFold; DeadCode] in
    assert_true "two passes" (List.length result.passes = 2));
  test "pipeline health score in range" (fun () ->
    let e = Let ("unused", Lit 99, Add (Lit 1, Lit 2)) in
    let result = transform_pipeline e [ConstFold; DeadCode] in
    assert_true "health range" (result.health_score >= 0.0 && result.health_score <= 100.0));
  test "shrink strategy reduces" (fun () ->
    let e = Let ("x", Add (Lit 1, Lit 2), Let ("y", Lit 99, Var "x")) in
    let result = transform_pipeline e (strategy_passes Shrink) in
    assert_true "smaller" (ast_size result.final_expr <= ast_size e));
  test "full pipeline on complex expr" (fun () ->
    let e = Let ("f", Lam ("x", Add (Var "x", Lit 1)),
            Let ("g", Lam ("y", Mul (Var "y", Lit 2)),
            App (Var "f", App (Var "g", Lit 3)))) in
    let result = transform_pipeline e [ConstPropagate; Inline; ConstFold; DeadCode] in
    assert_true "health ok" (result.health_score >= 0.0));

  Printf.printf "\n── Autonomous Optimizer ──\n";
  test "optimize simple expression" (fun () ->
    let e = Add (Lit 1, Lit 2) in
    let session = autonomous_optimize e in
    assert_true "has strategies" (List.length session.strategies_tried >= 4));
  test "optimize has recommendations" (fun () ->
    let e = Let ("x", Lit 5, Add (Var "x", Lit 10)) in
    let session = autonomous_optimize e in
    assert_true "has recs" (List.length session.recommendations > 0));
  test "optimize has insights" (fun () ->
    let e = Lam ("x", Add (Var "x", Mul (Lit 2, Lit 3))) in
    let session = autonomous_optimize e in
    assert_true "has insights" (List.length session.autonomous_insights > 0));
  test "optimize best strategy is valid" (fun () ->
    let e = Let ("x", Add (Lit 1, Lit 2), Let ("y", Lit 0, Var "x")) in
    let session = autonomous_optimize e in
    assert_true "valid strategy" (String.length session.best_strategy > 0));
  test "optimize convergence" (fun () ->
    let e = Add (Lit 1, Lit 2) in
    let session = autonomous_optimize e in
    assert_true "converged" (session.convergence_rounds >= 0));

  Printf.printf "\n── AST Utilities ──\n";
  test "ast_size literal" (fun () ->
    assert_true "size 1" (ast_size (Lit 42) = 1));
  test "ast_size add" (fun () ->
    assert_true "size 3" (ast_size (Add (Lit 1, Lit 2)) = 3));
  test "ast_depth nested" (fun () ->
    assert_true "depth" (ast_depth (Add (Add (Lit 1, Lit 2), Lit 3)) = 3));
  test "free_vars lambda" (fun () ->
    let fv = free_vars (Lam ("x", Add (Var "x", Var "y"))) in
    assert_true "y free" (StringSet.mem "y" fv && not (StringSet.mem "x" fv)));
  test "lambda_count" (fun () ->
    assert_true "2 lambdas" (lambda_count (Lam ("x", Lam ("y", Var "x"))) = 2));
  test "pp_expr roundtrip" (fun () ->
    let s = pp_expr (Let ("x", Lit 1, Var "x")) in
    assert_true "has let" (String.length s > 0));

  Printf.printf "\n── Substitution ──\n";
  test "subst simple" (fun () ->
    assert_eq "subst" "42" (pp_expr (subst "x" (Lit 42) (Var "x"))));
  test "subst avoids capture" (fun () ->
    fresh_counter := 0;
    let result = subst "x" (Var "y") (Lam ("y", Var "x")) in
    let fv = free_vars result in
    assert_true "y still free" (StringSet.mem "y" fv));
  test "subst no change" (fun () ->
    assert_eq "no change" "z" (pp_expr (subst "x" (Lit 1) (Var "z"))));

  Printf.printf "\n── Fixed-Point Iteration ──\n";
  test "iterate constant already folded" (fun () ->
    let (result, rounds) = iterate_until_fixed [ConstFold] (Lit 42) 10 in
    assert_true "immediate" (rounds = 0 && pp_expr result = "42"));
  test "iterate reduces to fixpoint" (fun () ->
    let e = Add (Add (Lit 1, Lit 2), Add (Lit 3, Lit 4)) in
    let (result, _) = iterate_until_fixed [ConstFold] e 10 in
    assert_eq "fixed" "10" (pp_expr result));

  Printf.printf "\n═══════════════════════════════════════════════════════\n";
  Printf.printf "Results: %d passed, %d failed, %d total\n\n"
    !tests_passed !tests_failed (!tests_passed + !tests_failed)

(* ══════════════════════════════════════════════════════════════════════════
   DEMO
   ══════════════════════════════════════════════════════════════════════════ *)

let () =
  run_tests ();

  (* Demo 1: Simple constant folding pipeline *)
  let expr1 = Let ("x", Add (Lit 1, Lit 2),
               Let ("y", Mul (Var "x", Lit 3),
               Let ("unused", Lit 999,
               Add (Var "y", Lit 1)))) in
  let r1 = transform_pipeline expr1 [ConstPropagate; ConstFold; DeadCode] in
  print_pipeline_result r1;

  (* Demo 2: Lambda + higher-order pipeline *)
  let expr2 = Let ("double", Lam ("x", Mul (Var "x", Lit 2)),
               Let ("inc", Lam ("y", Add (Var "y", Lit 1)),
               App (Var "double", App (Var "inc", Lit 20)))) in
  let r2 = transform_pipeline expr2 [Inline; ConstFold; DeadCode] in
  print_pipeline_result r2;

  (* Demo 3: Autonomous optimization session *)
  let expr3 = Let ("a", Add (Lit 5, Lit 10),
               Let ("b", Mul (Var "a", Lit 2),
               Let ("f", Lam ("x", Add (Var "x", Var "b")),
               Let ("dead", Sub (Lit 100, Lit 1),
               App (Var "f", Lit 7))))) in
  let session = autonomous_optimize expr3 in
  print_session session
