(* type_infer.ml — Hindley-Milner Type Inference Engine
 *
 * Implements Algorithm W for a mini functional language with:
 *   - Integer and boolean literals
 *   - Variables and let-bindings (with polymorphism)
 *   - Lambda abstractions and function application
 *   - If-then-else expressions
 *   - Recursive let-bindings (let rec)
 *   - Binary operators (+, -, *, =, <)
 *   - Pairs and fst/snd projections
 *
 * Concepts demonstrated:
 *   - Algebraic data types for AST and types
 *   - Mutable state for type variable generation
 *   - Unification with occurs check
 *   - Substitution composition and application
 *   - Generalization and instantiation (polymorphism)
 *   - Algorithm W (Damas-Milner)
 *   - Module design with clean API surface
 *
 * Usage:
 *   let expr = Let("id", Lam("x", Var "x"), App(Var "id", IntLit 42)) in
 *   let ty = infer expr in
 *   Printf.printf "Type: %s\n" (string_of_ty ty)
 *   (* Output: Type: int *)
 *)

(* ── Types ────────────────────────────────────────────────────────── *)

(** Type representation *)
type ty =
  | TInt                         (** integer type *)
  | TBool                        (** boolean type *)
  | TVar of string               (** type variable, e.g. 'a *)
  | TFun of ty * ty              (** function type: t1 -> t2 *)
  | TPair of ty * ty             (** pair type: t1 * t2 *)

(** Type scheme: universally quantified type *)
type scheme = Forall of string list * ty

(** Expression AST for the mini-language *)
type expr =
  | IntLit of int                (** integer literal *)
  | BoolLit of bool              (** boolean literal *)
  | Var of string                (** variable reference *)
  | Lam of string * expr         (** lambda: fun x -> body *)
  | App of expr * expr           (** function application *)
  | Let of string * expr * expr  (** let x = e1 in e2 *)
  | LetRec of string * expr * expr (** let rec f = e1 in e2 *)
  | If of expr * expr * expr     (** if cond then e1 else e2 *)
  | BinOp of binop * expr * expr (** binary operation *)
  | Pair of expr * expr          (** pair construction (e1, e2) *)
  | Fst of expr                  (** first projection *)
  | Snd of expr                  (** second projection *)

(** Binary operators *)
and binop = Add | Sub | Mul | Eq | Lt

(** Type environment: maps variable names to type schemes *)
type env = (string * scheme) list

(* ── Pretty printing ──────────────────────────────────────────────── *)

(** Convert a type to a human-readable string *)
let rec string_of_ty = function
  | TInt -> "int"
  | TBool -> "bool"
  | TVar a -> a
  | TFun (t1, t2) ->
    let s1 = match t1 with
      | TFun _ -> "(" ^ string_of_ty t1 ^ ")"
      | _ -> string_of_ty t1
    in
    s1 ^ " -> " ^ string_of_ty t2
  | TPair (t1, t2) ->
    let s1 = match t1 with
      | TFun _ -> "(" ^ string_of_ty t1 ^ ")"
      | _ -> string_of_ty t1
    in
    let s2 = match t2 with
      | TFun _ -> "(" ^ string_of_ty t2 ^ ")"
      | _ -> string_of_ty t2
    in
    s1 ^ " * " ^ s2

(** Convert a binary operator to string *)
let string_of_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Eq -> "=" | Lt -> "<"

(** Convert an expression to string (for error messages) *)
let rec string_of_expr = function
  | IntLit n -> string_of_int n
  | BoolLit b -> string_of_bool b
  | Var x -> x
  | Lam (x, body) -> Printf.sprintf "(fun %s -> %s)" x (string_of_expr body)
  | App (e1, e2) -> Printf.sprintf "(%s %s)" (string_of_expr e1) (string_of_expr e2)
  | Let (x, e1, e2) ->
    Printf.sprintf "(let %s = %s in %s)" x (string_of_expr e1) (string_of_expr e2)
  | LetRec (f, e1, e2) ->
    Printf.sprintf "(let rec %s = %s in %s)" f (string_of_expr e1) (string_of_expr e2)
  | If (c, t, e) ->
    Printf.sprintf "(if %s then %s else %s)"
      (string_of_expr c) (string_of_expr t) (string_of_expr e)
  | BinOp (op, e1, e2) ->
    Printf.sprintf "(%s %s %s)"
      (string_of_expr e1) (string_of_binop op) (string_of_expr e2)
  | Pair (e1, e2) ->
    Printf.sprintf "(%s, %s)" (string_of_expr e1) (string_of_expr e2)
  | Fst e -> Printf.sprintf "(fst %s)" (string_of_expr e)
  | Snd e -> Printf.sprintf "(snd %s)" (string_of_expr e)

(* ── Fresh type variables ─────────────────────────────────────────── *)

let type_var_counter = ref 0

(** Generate a fresh type variable *)
let fresh_tyvar () =
  let n = !type_var_counter in
  incr type_var_counter;
  let name =
    if n < 26 then Printf.sprintf "'%c" (Char.chr (97 + n))
    else Printf.sprintf "'t%d" n
  in
  TVar name

(** Reset the type variable counter (useful for predictable test output) *)
let reset_tyvars () = type_var_counter := 0

(* ── Substitution ─────────────────────────────────────────────────── *)

(** A substitution maps type variable names to types *)
type subst = (string * ty) list

(** Empty substitution *)
let empty_subst : subst = []

(** Apply a substitution to a type *)
let rec apply_ty (s : subst) = function
  | TInt -> TInt
  | TBool -> TBool
  | TVar a ->
    (match List.assoc_opt a s with
     | Some t -> t
     | None -> TVar a)
  | TFun (t1, t2) -> TFun (apply_ty s t1, apply_ty s t2)
  | TPair (t1, t2) -> TPair (apply_ty s t1, apply_ty s t2)

(** Apply a substitution to a type scheme *)
let apply_scheme (s : subst) (Forall (vars, ty)) =
  (* Remove bound variables from the substitution *)
  let s' = List.filter (fun (v, _) -> not (List.mem v vars)) s in
  Forall (vars, apply_ty s' ty)

(** Apply a substitution to an environment *)
let apply_env (s : subst) (env : env) : env =
  List.map (fun (name, scheme) -> (name, apply_scheme s scheme)) env

(** Compose two substitutions: apply s2 then s1 *)
let compose_subst (s1 : subst) (s2 : subst) : subst =
  let s2' = List.map (fun (v, t) -> (v, apply_ty s1 t)) s2 in
  let s1_only = List.filter (fun (v, _) ->
    not (List.exists (fun (v', _) -> v = v') s2')
  ) s1 in
  s2' @ s1_only

(* ── Free type variables ──────────────────────────────────────────── *)

(** Collect free type variables in a type *)
let rec ftv_ty = function
  | TInt | TBool -> []
  | TVar a -> [a]
  | TFun (t1, t2) -> ftv_ty t1 @ ftv_ty t2
  | TPair (t1, t2) -> ftv_ty t1 @ ftv_ty t2

(** Collect free type variables in a scheme *)
let ftv_scheme (Forall (vars, ty)) =
  List.filter (fun v -> not (List.mem v vars)) (ftv_ty ty)

(** Collect free type variables in an environment *)
let ftv_env (env : env) =
  List.concat_map (fun (_, scheme) -> ftv_scheme scheme) env

(** Remove duplicates from a list *)
let unique lst =
  List.fold_left (fun acc x ->
    if List.mem x acc then acc else x :: acc
  ) [] lst |> List.rev

(* ── Unification ──────────────────────────────────────────────────── *)

exception TypeError of string

(** Occurs check: does type variable `a` appear in type `t`? *)
let rec occurs (a : string) = function
  | TInt | TBool -> false
  | TVar b -> a = b
  | TFun (t1, t2) -> occurs a t1 || occurs a t2
  | TPair (t1, t2) -> occurs a t1 || occurs a t2

(** Unify two types, returning a substitution *)
let rec unify (t1 : ty) (t2 : ty) : subst =
  match t1, t2 with
  | TInt, TInt -> empty_subst
  | TBool, TBool -> empty_subst
  | TVar a, t | t, TVar a ->
    if t = TVar a then empty_subst
    else if occurs a t then
      raise (TypeError (Printf.sprintf
        "Infinite type: %s occurs in %s" a (string_of_ty t)))
    else [(a, t)]
  | TFun (a1, r1), TFun (a2, r2) ->
    let s1 = unify a1 a2 in
    let s2 = unify (apply_ty s1 r1) (apply_ty s1 r2) in
    compose_subst s2 s1
  | TPair (a1, b1), TPair (a2, b2) ->
    let s1 = unify a1 a2 in
    let s2 = unify (apply_ty s1 b1) (apply_ty s1 b2) in
    compose_subst s2 s1
  | _ ->
    raise (TypeError (Printf.sprintf
      "Cannot unify %s with %s" (string_of_ty t1) (string_of_ty t2)))

(* ── Generalization and Instantiation ─────────────────────────────── *)

(** Generalize a type over variables not free in the environment *)
let generalize (env : env) (ty : ty) : scheme =
  let env_ftvs = unique (ftv_env env) in
  let ty_ftvs = unique (ftv_ty ty) in
  let gen_vars = List.filter (fun v -> not (List.mem v env_ftvs)) ty_ftvs in
  Forall (gen_vars, ty)

(** Instantiate a type scheme with fresh type variables *)
let instantiate (Forall (vars, ty)) : ty =
  let subst = List.map (fun v -> (v, fresh_tyvar ())) vars in
  apply_ty subst ty

(* ── Algorithm W ──────────────────────────────────────────────────── *)

(** Look up a variable in the environment *)
let lookup (env : env) (x : string) : scheme =
  match List.assoc_opt x env with
  | Some scheme -> scheme
  | None -> raise (TypeError (Printf.sprintf "Unbound variable: %s" x))

(** Infer the type of a binary operator *)
let infer_binop = function
  | Add | Sub | Mul -> (TInt, TInt, TInt)  (* int -> int -> int *)
  | Eq -> let tv = fresh_tyvar () in (tv, tv, TBool)  (* 'a -> 'a -> bool *)
  | Lt -> (TInt, TInt, TBool)  (* int -> int -> bool *)

(** Algorithm W: infer the type of an expression in a given environment.
    Returns (substitution, inferred_type). *)
let rec algorithm_w (env : env) (expr : expr) : subst * ty =
  match expr with
  | IntLit _ -> (empty_subst, TInt)

  | BoolLit _ -> (empty_subst, TBool)

  | Var x ->
    let scheme = lookup env x in
    let ty = instantiate scheme in
    (empty_subst, ty)

  | Lam (x, body) ->
    let arg_ty = fresh_tyvar () in
    let env' = (x, Forall ([], arg_ty)) :: env in
    let (s1, body_ty) = algorithm_w env' body in
    (s1, TFun (apply_ty s1 arg_ty, body_ty))

  | App (e1, e2) ->
    let result_ty = fresh_tyvar () in
    let (s1, fun_ty) = algorithm_w env e1 in
    let (s2, arg_ty) = algorithm_w (apply_env s1 env) e2 in
    let s3 = unify (apply_ty s2 fun_ty) (TFun (arg_ty, result_ty)) in
    (compose_subst s3 (compose_subst s2 s1), apply_ty s3 result_ty)

  | Let (x, e1, e2) ->
    let (s1, t1) = algorithm_w env e1 in
    let env' = apply_env s1 env in
    let scheme = generalize env' t1 in
    let (s2, t2) = algorithm_w ((x, scheme) :: env') e2 in
    (compose_subst s2 s1, t2)

  | LetRec (f, e1, e2) ->
    let rec_ty = fresh_tyvar () in
    let env' = (f, Forall ([], rec_ty)) :: env in
    let (s1, t1) = algorithm_w env' e1 in
    let s2 = unify (apply_ty s1 rec_ty) t1 in
    let s12 = compose_subst s2 s1 in
    let env'' = apply_env s12 env in
    let scheme = generalize env'' (apply_ty s12 rec_ty) in
    let (s3, t2) = algorithm_w ((f, scheme) :: env'') e2 in
    (compose_subst s3 s12, t2)

  | If (cond, then_e, else_e) ->
    let (s1, cond_ty) = algorithm_w env cond in
    let s2 = unify cond_ty TBool in
    let s12 = compose_subst s2 s1 in
    let (s3, then_ty) = algorithm_w (apply_env s12 env) then_e in
    let s123 = compose_subst s3 s12 in
    let (s4, else_ty) = algorithm_w (apply_env s123 env) else_e in
    let s1234 = compose_subst s4 s123 in
    let s5 = unify (apply_ty s4 then_ty) else_ty in
    (compose_subst s5 s1234, apply_ty s5 else_ty)

  | BinOp (op, e1, e2) ->
    let (t_left, t_right, t_result) = infer_binop op in
    let (s1, t1) = algorithm_w env e1 in
    let s2 = unify t1 t_left in
    let s12 = compose_subst s2 s1 in
    let (s3, t2) = algorithm_w (apply_env s12 env) e2 in
    let s4 = unify t2 (apply_ty s3 (apply_ty s2 t_right)) in
    (compose_subst s4 (compose_subst s3 s12),
     apply_ty s4 (apply_ty s3 (apply_ty s2 t_result)))

  | Pair (e1, e2) ->
    let (s1, t1) = algorithm_w env e1 in
    let (s2, t2) = algorithm_w (apply_env s1 env) e2 in
    (compose_subst s2 s1, TPair (apply_ty s2 t1, t2))

  | Fst e ->
    let a = fresh_tyvar () in
    let b = fresh_tyvar () in
    let (s1, t1) = algorithm_w env e in
    let s2 = unify t1 (TPair (a, b)) in
    (compose_subst s2 s1, apply_ty s2 a)

  | Snd e ->
    let a = fresh_tyvar () in
    let b = fresh_tyvar () in
    let (s1, t1) = algorithm_w env e in
    let s2 = unify t1 (TPair (a, b)) in
    (compose_subst s2 s1, apply_ty s2 b)

(* ── Public API ───────────────────────────────────────────────────── *)

(** Infer the type of an expression (top-level entry point) *)
let infer ?(env = []) (expr : expr) : ty =
  reset_tyvars ();
  let (s, ty) = algorithm_w env expr in
  apply_ty s ty

(** Infer and return the type as a string *)
let infer_string ?(env = []) (expr : expr) : string =
  string_of_ty (infer ~env expr)

(** Check if an expression is well-typed (returns true/false) *)
let is_well_typed ?(env = []) (expr : expr) : bool =
  try
    ignore (infer ~env expr);
    true
  with TypeError _ -> false

(** Type-check and return either Ok(type_string) or Error(message) *)
let type_check ?(env = []) (expr : expr) : (string, string) result =
  try Ok (infer_string ~env expr)
  with TypeError msg -> Error msg

(* ── Convenience constructors ─────────────────────────────────────── *)

(** Create an integer addition expression *)
let ( +: ) e1 e2 = BinOp (Add, e1, e2)

(** Create an integer subtraction expression *)
let ( -: ) e1 e2 = BinOp (Sub, e1, e2)

(** Create an integer multiplication expression *)
let ( *: ) e1 e2 = BinOp (Mul, e1, e2)

(** Create an equality comparison *)
let ( =: ) e1 e2 = BinOp (Eq, e1, e2)

(** Create a less-than comparison *)
let ( <: ) e1 e2 = BinOp (Lt, e1, e2)

(* ── Demo / self-test ─────────────────────────────────────────────── *)

let () =
  let test name expr expected =
    reset_tyvars ();
    let result = infer_string expr in
    let pass = result = expected in
    Printf.printf "%s %s: %s = %s\n"
      (if pass then "PASS" else "FAIL") name result expected;
    if not pass then
      Printf.printf "  Expression: %s\n" (string_of_expr expr)
  in

  let test_error name expr =
    reset_tyvars ();
    match type_check expr with
    | Error _ -> Printf.printf "PASS %s: correctly rejected\n" name
    | Ok ty -> Printf.printf "FAIL %s: expected error, got %s\n" name ty
  in

  print_endline "=== Hindley-Milner Type Inference Demo ===\n";

  (* Basic literals *)
  test "int_lit" (IntLit 42) "int";
  test "bool_lit" (BoolLit true) "bool";

  (* Identity function: fun x -> x  :  'a -> 'a *)
  test "identity" (Lam ("x", Var "x")) "'a -> 'a";

  (* Constant function: fun x -> fun y -> x  :  'a -> 'b -> 'a *)
  test "const_fn" (Lam ("x", Lam ("y", Var "x"))) "'a -> 'b -> 'a";

  (* Application: (fun x -> x) 42  :  int *)
  test "app_id_int" (App (Lam ("x", Var "x"), IntLit 42)) "int";

  (* Arithmetic: fun x -> x + 1  :  int -> int *)
  test "arith" (Lam ("x", IntLit 1 +: Var "x")) "int -> int";

  (* Let polymorphism: let id = fun x -> x in (id 1, id true) *)
  test "let_poly"
    (Let ("id", Lam ("x", Var "x"),
      Pair (App (Var "id", IntLit 1),
            App (Var "id", BoolLit true))))
    "int * bool";

  (* If-then-else: fun x -> if x then 1 else 0  :  bool -> int *)
  test "if_expr"
    (Lam ("x", If (Var "x", IntLit 1, IntLit 0)))
    "bool -> int";

  (* Recursive factorial:
     let rec fact = fun n -> if n = 0 then 1 else n * fact(n - 1) *)
  test "factorial"
    (LetRec ("fact",
      Lam ("n", If (Var "n" =: IntLit 0,
                    IntLit 1,
                    Var "n" *: App (Var "fact", Var "n" -: IntLit 1))),
      Var "fact"))
    "int -> int";

  (* Pair: (1, true)  :  int * bool *)
  test "pair" (Pair (IntLit 1, BoolLit true)) "int * bool";

  (* Fst: fst (1, true)  :  int *)
  test "fst_pair" (Fst (Pair (IntLit 1, BoolLit true))) "int";

  (* Snd: snd (1, true)  :  bool *)
  test "snd_pair" (Snd (Pair (IntLit 1, BoolLit true))) "bool";

  (* Higher-order: fun f -> fun x -> f x  :  ('a -> 'b) -> 'a -> 'b *)
  test "apply_fn"
    (Lam ("f", Lam ("x", App (Var "f", Var "x"))))
    "('a -> 'b) -> 'a -> 'b";

  (* Compose: fun f -> fun g -> fun x -> f (g x) *)
  test "compose"
    (Lam ("f", Lam ("g", Lam ("x",
      App (Var "f", App (Var "g", Var "x"))))))
    "('a -> 'b) -> ('c -> 'a) -> 'c -> 'b";

  (* Error: type mismatch in if branches *)
  test_error "if_branch_mismatch"
    (If (BoolLit true, IntLit 1, BoolLit false));

  (* Error: applying non-function *)
  test_error "apply_non_fn"
    (App (IntLit 42, IntLit 1));

  (* Error: infinite type (self-application: fun x -> x x) *)
  test_error "infinite_type"
    (Lam ("x", App (Var "x", Var "x")));

  (* Error: unbound variable *)
  test_error "unbound_var"
    (Var "undefined_var");

  (* Error: condition not bool *)
  test_error "non_bool_cond"
    (If (IntLit 1, IntLit 2, IntLit 3));

  print_endline "\n=== Demo complete ==="
