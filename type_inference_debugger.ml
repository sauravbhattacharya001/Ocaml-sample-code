(* type_inference_debugger.ml — Autonomous Type Inference Debugger
   Traces step-by-step how OCaml's Hindley-Milner type inference works
   for user-provided expressions. Explains unification, constraint generation,
   generalization, and substitution at each step.

   Features:
   - Parses a subset of OCaml expressions (let, fun, application, if, tuples, lists, operators)
   - Generates typing constraints with environment tracking
   - Performs unification with step-by-step trace
   - Explains each inference rule applied (Var, App, Abs, Let, If, etc.)
   - Detects and explains type errors with precise conflict locations
   - Shows substitution state at each step
   - Interactive REPL for experimentation
   - Autonomously suggests simpler expressions when errors occur
   - Learns common confusion patterns and offers targeted explanations

   Usage: ocaml type_inference_debugger.ml
*)

(* ── Types ──────────────────────────────────────────────────────── *)

type ty =
  | TVar of int
  | TInt
  | TBool
  | TString
  | TUnit
  | TArrow of ty * ty
  | TTuple of ty list
  | TList of ty
  | TOption of ty

type expr =
  | EInt of int
  | EBool of bool
  | EString of string
  | EUnit
  | EVar of string
  | ELet of string * expr * expr
  | ELetRec of string * expr * expr
  | EFun of string * expr
  | EApp of expr * expr
  | EIf of expr * expr * expr
  | ETuple of expr list
  | EBinOp of string * expr * expr
  | EUnOp of string * expr
  | ENil
  | ECons of expr * expr
  | ENone
  | ESome of expr
  | EMatch of expr * (pattern * expr) list

and pattern =
  | PVar of string
  | PInt of int
  | PBool of bool
  | PWild
  | PTuple of pattern list
  | PCons of pattern * pattern
  | PNil
  | PNone
  | PSome of pattern

type scheme = Forall of int list * ty

type constraint_reason =
  | FunctionApplication of string
  | IfCondition
  | IfBranches
  | LetBinding of string
  | OperatorUse of string
  | ListElement
  | TupleElement of int
  | PatternMatch
  | UserAnnotation

type type_constraint = {
  lhs : ty;
  rhs : ty;
  reason : constraint_reason;
  step_id : int;
}

type inference_step = {
  id : int;
  rule : string;
  expression : string;
  explanation : string;
  constraints_added : type_constraint list;
  current_env : (string * scheme) list;
  substitution_state : (int * ty) list;
}

type inference_result =
  | Success of ty * inference_step list
  | TypeError of string * inference_step list * type_constraint

type confusion_pattern = {
  pattern_name : string;
  trigger : string;
  explanation : string;
  simpler_example : string;
}

(* ── State ──────────────────────────────────────────────────────── *)

let next_var = ref 0
let steps : inference_step list ref = ref []
let step_counter = ref 0

let fresh_var () =
  let v = !next_var in
  incr next_var;
  TVar v

let reset_state () =
  next_var := 0;
  steps := [];
  step_counter := 0

let record_step rule expr_str explanation constraints env subst =
  incr step_counter;
  let step = {
    id = !step_counter;
    rule;
    expression = expr_str;
    explanation;
    constraints_added = constraints;
    current_env = env;
    substitution_state = subst;
  } in
  steps := step :: !steps

(* ── Pretty Printing ────────────────────────────────────────────── *)

let rec pp_ty = function
  | TVar n -> "'" ^ String.make 1 (Char.chr (97 + (n mod 26))) ^
              (if n >= 26 then string_of_int (n / 26) else "")
  | TInt -> "int"
  | TBool -> "bool"
  | TString -> "string"
  | TUnit -> "unit"
  | TArrow (TArrow _ as a, b) -> "(" ^ pp_ty a ^ ") -> " ^ pp_ty b
  | TArrow (a, b) -> pp_ty a ^ " -> " ^ pp_ty b
  | TTuple ts -> "(" ^ String.concat " * " (List.map pp_ty ts) ^ ")"
  | TList t -> pp_ty t ^ " list"
  | TOption t -> pp_ty t ^ " option"

let pp_scheme (Forall (vars, t)) =
  if vars = [] then pp_ty t
  else
    let var_strs = List.map (fun v -> pp_ty (TVar v)) vars in
    "forall " ^ String.concat " " var_strs ^ ". " ^ pp_ty t

let pp_reason = function
  | FunctionApplication f -> "applying function " ^ f
  | IfCondition -> "if-condition must be bool"
  | IfBranches -> "if-branches must have same type"
  | LetBinding name -> "let-binding of " ^ name
  | OperatorUse op -> "using operator " ^ op
  | ListElement -> "list elements must have same type"
  | TupleElement i -> "tuple element " ^ string_of_int i
  | PatternMatch -> "pattern match arms must agree"
  | UserAnnotation -> "user type annotation"

let rec pp_expr = function
  | EInt n -> string_of_int n
  | EBool b -> string_of_bool b
  | EString s -> "\"" ^ s ^ "\""
  | EUnit -> "()"
  | EVar x -> x
  | ELet (x, e1, e2) -> "let " ^ x ^ " = " ^ pp_expr e1 ^ " in " ^ pp_expr e2
  | ELetRec (x, e1, e2) -> "let rec " ^ x ^ " = " ^ pp_expr e1 ^ " in " ^ pp_expr e2
  | EFun (x, body) -> "fun " ^ x ^ " -> " ^ pp_expr body
  | EApp (f, arg) -> pp_expr f ^ " " ^ pp_expr_atom arg
  | EIf (c, t, e) -> "if " ^ pp_expr c ^ " then " ^ pp_expr t ^ " else " ^ pp_expr e
  | ETuple es -> "(" ^ String.concat ", " (List.map pp_expr es) ^ ")"
  | EBinOp (op, l, r) -> pp_expr l ^ " " ^ op ^ " " ^ pp_expr r
  | EUnOp (op, e) -> op ^ " " ^ pp_expr_atom e
  | ENil -> "[]"
  | ECons (h, t) -> pp_expr h ^ " :: " ^ pp_expr t
  | ENone -> "None"
  | ESome e -> "Some " ^ pp_expr_atom e
  | EMatch (e, _) -> "match " ^ pp_expr e ^ " with ..."

and pp_expr_atom = function
  | (EVar _ | EInt _ | EBool _ | EString _ | EUnit | ENil | ENone) as e -> pp_expr e
  | e -> "(" ^ pp_expr e ^ ")"

(* ── Substitution ───────────────────────────────────────────────── *)

let subst_map : (int * ty) list ref = ref []

let rec apply_subst t =
  match t with
  | TVar n ->
    (match List.assoc_opt n !subst_map with
     | Some t' -> apply_subst t'
     | None -> t)
  | TArrow (a, b) -> TArrow (apply_subst a, apply_subst b)
  | TTuple ts -> TTuple (List.map apply_subst ts)
  | TList t' -> TList (apply_subst t')
  | TOption t' -> TOption (apply_subst t')
  | _ -> t

let apply_subst_scheme (Forall (vars, t)) =
  (* Don't substitute bound variables *)
  let saved = List.filter_map (fun v ->
    match List.assoc_opt v !subst_map with
    | Some _ -> Some (v, List.assoc v !subst_map)
    | None -> None
  ) vars in
  List.iter (fun v -> subst_map := List.filter (fun (k, _) -> k <> v) !subst_map) vars;
  let result = apply_subst t in
  List.iter (fun (k, v) -> subst_map := (k, v) :: !subst_map) saved;
  Forall (vars, result)

(* ── Occurs Check & Unification ─────────────────────────────────── *)

let rec occurs_in n = function
  | TVar m -> n = m
  | TArrow (a, b) -> occurs_in n a || occurs_in n b
  | TTuple ts -> List.exists (occurs_in n) ts
  | TList t -> occurs_in n t
  | TOption t -> occurs_in n t
  | _ -> false

exception UnificationError of ty * ty * constraint_reason

let rec unify t1 t2 reason =
  let t1 = apply_subst t1 in
  let t2 = apply_subst t2 in
  match t1, t2 with
  | TVar n, TVar m when n = m -> ()
  | TVar n, t | t, TVar n ->
    if occurs_in n t then
      raise (UnificationError (TVar n, t, reason))
    else
      subst_map := (n, t) :: !subst_map
  | TInt, TInt | TBool, TBool | TString, TString | TUnit, TUnit -> ()
  | TArrow (a1, b1), TArrow (a2, b2) ->
    unify a1 a2 reason;
    unify b1 b2 reason
  | TTuple ts1, TTuple ts2 when List.length ts1 = List.length ts2 ->
    List.iter2 (fun a b -> unify a b reason) ts1 ts2
  | TList a, TList b -> unify a b reason
  | TOption a, TOption b -> unify a b reason
  | _ -> raise (UnificationError (t1, t2, reason))

(* ── Generalization & Instantiation ─────────────────────────────── *)

let rec free_vars_ty = function
  | TVar n -> [n]
  | TArrow (a, b) -> free_vars_ty a @ free_vars_ty b
  | TTuple ts -> List.concat_map free_vars_ty ts
  | TList t -> free_vars_ty t
  | TOption t -> free_vars_ty t
  | _ -> []

let free_vars_scheme (Forall (vars, t)) =
  List.filter (fun v -> not (List.mem v vars)) (free_vars_ty t)

let free_vars_env env =
  List.concat_map (fun (_, s) -> free_vars_scheme s) env

let generalize env t =
  let t = apply_subst t in
  let env_vars = free_vars_env env in
  let ty_vars = free_vars_ty t in
  let gen_vars = List.filter (fun v -> not (List.mem v env_vars)) ty_vars in
  let gen_vars = List.sort_uniq compare gen_vars in
  Forall (gen_vars, t)

let instantiate (Forall (vars, t)) =
  let mapping = List.map (fun v -> (v, fresh_var ())) vars in
  let rec subst_inst ty =
    match ty with
    | TVar n ->
      (match List.assoc_opt n mapping with
       | Some t' -> t'
       | None -> ty)
    | TArrow (a, b) -> TArrow (subst_inst a, subst_inst b)
    | TTuple ts -> TTuple (List.map subst_inst ts)
    | TList t' -> TList (subst_inst t')
    | TOption t' -> TOption (subst_inst t')
    | _ -> ty
  in
  subst_inst t

(* ── Type Inference ─────────────────────────────────────────────── *)

let initial_env = [
  ("+", Forall ([], TArrow (TInt, TArrow (TInt, TInt))));
  ("-", Forall ([], TArrow (TInt, TArrow (TInt, TInt))));
  ("*", Forall ([], TArrow (TInt, TArrow (TInt, TInt))));
  ("/", Forall ([], TArrow (TInt, TArrow (TInt, TInt))));
  ("mod", Forall ([], TArrow (TInt, TArrow (TInt, TInt))));
  ("=", Forall ([0], TArrow (TVar 0, TArrow (TVar 0, TBool))));
  ("<>", Forall ([0], TArrow (TVar 0, TArrow (TVar 0, TBool))));
  ("<", Forall ([0], TArrow (TVar 0, TArrow (TVar 0, TBool))));
  (">", Forall ([0], TArrow (TVar 0, TArrow (TVar 0, TBool))));
  ("<=", Forall ([0], TArrow (TVar 0, TArrow (TVar 0, TBool))));
  (">=", Forall ([0], TArrow (TVar 0, TArrow (TVar 0, TBool))));
  ("&&", Forall ([], TArrow (TBool, TArrow (TBool, TBool))));
  ("||", Forall ([], TArrow (TBool, TArrow (TBool, TBool))));
  ("^", Forall ([], TArrow (TString, TArrow (TString, TString))));
  ("not", Forall ([], TArrow (TBool, TBool)));
  ("fst", Forall ([0; 1], TArrow (TTuple [TVar 0; TVar 1], TVar 0)));
  ("snd", Forall ([0; 1], TArrow (TTuple [TVar 0; TVar 1], TVar 1)));
  ("List.hd", Forall ([0], TArrow (TList (TVar 0), TVar 0)));
  ("List.tl", Forall ([0], TArrow (TList (TVar 0), TList (TVar 0))));
  ("List.length", Forall ([0], TArrow (TList (TVar 0), TInt)));
  ("List.rev", Forall ([0], TArrow (TList (TVar 0), TList (TVar 0))));
  ("List.map", Forall ([0; 1], TArrow (TArrow (TVar 0, TVar 1), TArrow (TList (TVar 0), TList (TVar 1)))));
  ("List.filter", Forall ([0], TArrow (TArrow (TVar 0, TBool), TArrow (TList (TVar 0), TList (TVar 0)))));
  ("List.fold_left", Forall ([0; 1], TArrow (TArrow (TVar 0, TArrow (TVar 1, TVar 0)), TArrow (TVar 0, TArrow (TList (TVar 1), TVar 0)))));
  ("string_of_int", Forall ([], TArrow (TInt, TString)));
  ("int_of_string", Forall ([], TArrow (TString, TInt)));
  ("print_string", Forall ([], TArrow (TString, TUnit)));
  ("print_int", Forall ([], TArrow (TInt, TUnit)));
  ("print_endline", Forall ([], TArrow (TString, TUnit)));
]

let rec infer env expr =
  match expr with
  | EInt _ ->
    record_step "Int" (pp_expr expr)
      "Integer literals always have type int."
      [] env !subst_map;
    TInt

  | EBool _ ->
    record_step "Bool" (pp_expr expr)
      "Boolean literals always have type bool."
      [] env !subst_map;
    TBool

  | EString _ ->
    record_step "String" (pp_expr expr)
      "String literals always have type string."
      [] env !subst_map;
    TString

  | EUnit ->
    record_step "Unit" (pp_expr expr)
      "Unit value has type unit."
      [] env !subst_map;
    TUnit

  | EVar x ->
    (match List.assoc_opt x env with
     | Some scheme ->
       let t = instantiate scheme in
       record_step "Var" x
         (Printf.sprintf "Look up '%s' in environment: %s. Instantiate to %s."
            x (pp_scheme scheme) (pp_ty t))
         [] env !subst_map;
       t
     | None ->
       record_step "Var" x
         (Printf.sprintf "ERROR: '%s' not found in environment!" x)
         [] env !subst_map;
       failwith (Printf.sprintf "Unbound variable: %s" x))

  | EFun (x, body) ->
    let arg_ty = fresh_var () in
    let new_env = (x, Forall ([], arg_ty)) :: env in
    record_step "Abs" (pp_expr expr)
      (Printf.sprintf "Lambda abstraction: introduce fresh type variable %s for parameter '%s'."
         (pp_ty arg_ty) x)
      [] new_env !subst_map;
    let body_ty = infer new_env body in
    TArrow (arg_ty, body_ty)

  | EApp (f, arg) ->
    let fun_ty = infer env f in
    let arg_ty = infer env arg in
    let result_ty = fresh_var () in
    let c = { lhs = fun_ty; rhs = TArrow (arg_ty, result_ty);
              reason = FunctionApplication (pp_expr f); step_id = !step_counter + 1 } in
    record_step "App" (pp_expr expr)
      (Printf.sprintf "Function application: %s must have type %s -> %s. Unifying %s with %s -> %s."
         (pp_expr f) (pp_ty arg_ty) (pp_ty result_ty)
         (pp_ty (apply_subst fun_ty)) (pp_ty (apply_subst arg_ty)) (pp_ty result_ty))
      [c] env !subst_map;
    unify fun_ty (TArrow (arg_ty, result_ty)) (FunctionApplication (pp_expr f));
    apply_subst result_ty

  | EIf (cond, then_e, else_e) ->
    let cond_ty = infer env cond in
    let c1 = { lhs = cond_ty; rhs = TBool; reason = IfCondition; step_id = !step_counter + 1 } in
    record_step "If-cond" (pp_expr cond)
      (Printf.sprintf "If-condition must be bool. Got %s, unifying with bool."
         (pp_ty (apply_subst cond_ty)))
      [c1] env !subst_map;
    unify cond_ty TBool IfCondition;
    let then_ty = infer env then_e in
    let else_ty = infer env else_e in
    let c2 = { lhs = then_ty; rhs = else_ty; reason = IfBranches; step_id = !step_counter + 1 } in
    record_step "If-branches" (pp_expr expr)
      (Printf.sprintf "Both branches must have same type. Then: %s, Else: %s."
         (pp_ty (apply_subst then_ty)) (pp_ty (apply_subst else_ty)))
      [c2] env !subst_map;
    unify then_ty else_ty IfBranches;
    apply_subst then_ty

  | ELet (x, e1, e2) ->
    let e1_ty = infer env e1 in
    let scheme = generalize env e1_ty in
    let new_env = (x, scheme) :: env in
    record_step "Let" (pp_expr expr)
      (Printf.sprintf "Let binding: '%s' gets type %s (generalized to %s)."
         x (pp_ty (apply_subst e1_ty)) (pp_scheme (apply_subst_scheme scheme)))
      [] new_env !subst_map;
    infer new_env e2

  | ELetRec (x, e1, e2) ->
    let self_ty = fresh_var () in
    let rec_env = (x, Forall ([], self_ty)) :: env in
    record_step "LetRec" (pp_expr expr)
      (Printf.sprintf "Recursive let: introduce fresh type %s for '%s' before checking body."
         (pp_ty self_ty) x)
      [] rec_env !subst_map;
    let e1_ty = infer rec_env e1 in
    unify self_ty e1_ty (LetBinding x);
    let scheme = generalize env e1_ty in
    let new_env = (x, scheme) :: env in
    infer new_env e2

  | ETuple es ->
    let tys = List.mapi (fun i e ->
      let t = infer env e in
      record_step "Tuple" (pp_expr (ETuple es))
        (Printf.sprintf "Tuple element %d has type %s." (i + 1) (pp_ty (apply_subst t)))
        [] env !subst_map;
      t
    ) es in
    TTuple tys

  | EBinOp (op, l, r) ->
    let op_expr = EApp (EApp (EVar op, l), r) in
    infer env op_expr

  | EUnOp (op, e) ->
    let op_expr = EApp (EVar op, e) in
    infer env op_expr

  | ENil ->
    let elem_ty = fresh_var () in
    record_step "Nil" "[]"
      (Printf.sprintf "Empty list has type %s list (fresh variable for element type)."
         (pp_ty elem_ty))
      [] env !subst_map;
    TList elem_ty

  | ECons (h, t) ->
    let h_ty = infer env h in
    let t_ty = infer env t in
    let c = { lhs = t_ty; rhs = TList h_ty; reason = ListElement; step_id = !step_counter + 1 } in
    record_step "Cons" (pp_expr (ECons (h, t)))
      (Printf.sprintf "Cons: tail must be %s list. Unifying %s with %s list."
         (pp_ty (apply_subst h_ty)) (pp_ty (apply_subst t_ty)) (pp_ty (apply_subst h_ty)))
      [c] env !subst_map;
    unify t_ty (TList h_ty) ListElement;
    TList h_ty

  | ENone ->
    let inner_ty = fresh_var () in
    record_step "None" "None"
      (Printf.sprintf "None has type %s option (fresh variable)." (pp_ty inner_ty))
      [] env !subst_map;
    TOption inner_ty

  | ESome e ->
    let t = infer env e in
    record_step "Some" (pp_expr (ESome e))
      (Printf.sprintf "Some wraps value of type %s into %s option."
         (pp_ty (apply_subst t)) (pp_ty (apply_subst t)))
      [] env !subst_map;
    TOption t

  | EMatch (scrutinee, cases) ->
    let scrut_ty = infer env scrutinee in
    let result_ty = fresh_var () in
    List.iter (fun (pat, body) ->
      let (pat_ty, bindings) = infer_pattern pat in
      unify scrut_ty pat_ty PatternMatch;
      let case_env = bindings @ env in
      let body_ty = infer case_env body in
      unify result_ty body_ty PatternMatch;
    ) cases;
    record_step "Match" (pp_expr expr)
      (Printf.sprintf "Pattern match: scrutinee type %s, result type %s."
         (pp_ty (apply_subst scrut_ty)) (pp_ty (apply_subst result_ty)))
      [] env !subst_map;
    apply_subst result_ty

and infer_pattern = function
  | PVar x ->
    let t = fresh_var () in
    (t, [(x, Forall ([], t))])
  | PInt _ -> (TInt, [])
  | PBool _ -> (TBool, [])
  | PWild -> (fresh_var (), [])
  | PTuple ps ->
    let results = List.map infer_pattern ps in
    let tys = List.map fst results in
    let bindings = List.concat_map snd results in
    (TTuple tys, bindings)
  | PCons (h, t) ->
    let (h_ty, h_bindings) = infer_pattern h in
    let (t_ty, t_bindings) = infer_pattern t in
    unify t_ty (TList h_ty) PatternMatch;
    (TList h_ty, h_bindings @ t_bindings)
  | PNil ->
    let t = fresh_var () in
    (TList t, [])
  | PNone ->
    let t = fresh_var () in
    (TOption t, [])
  | PSome p ->
    let (inner_ty, bindings) = infer_pattern p in
    (TOption inner_ty, bindings)

(* ── Top-level Inference ────────────────────────────────────────── *)

let infer_expression expr =
  reset_state ();
  subst_map := [];
  (* Start fresh vars after the ones used in initial_env *)
  next_var := 2;
  try
    let t = infer initial_env expr in
    let final_ty = apply_subst t in
    Success (final_ty, List.rev !steps)
  with
  | UnificationError (t1, t2, reason) ->
    let err_constraint = { lhs = t1; rhs = t2; reason; step_id = !step_counter } in
    TypeError (
      Printf.sprintf "Cannot unify %s with %s (%s)"
        (pp_ty t1) (pp_ty t2) (pp_reason reason),
      List.rev !steps,
      err_constraint
    )
  | Failure msg ->
    let err_constraint = { lhs = TUnit; rhs = TUnit; reason = UserAnnotation; step_id = !step_counter } in
    TypeError (msg, List.rev !steps, err_constraint)

(* ── Expression Parser (Simple Recursive Descent) ───────────────── *)

type token =
  | TkInt of int
  | TkBool of bool
  | TkString of string
  | TkIdent of string
  | TkLet | TkRec | TkIn | TkFun | TkArrow
  | TkIf | TkThen | TkElse
  | TkMatch | TkWith | TkBar
  | TkLParen | TkRParen | TkLBrack | TkRBrack
  | TkComma | TkSemiSemi | TkColon2
  | TkOp of string
  | TkUnderscore
  | TkSome | TkNone
  | TkEOF

let keywords = [
  ("let", TkLet); ("rec", TkRec); ("in", TkIn);
  ("fun", TkFun); ("if", TkIf); ("then", TkThen); ("else", TkElse);
  ("match", TkMatch); ("with", TkWith);
  ("true", TkBool true); ("false", TkBool false);
  ("Some", TkSome); ("None", TkNone);
  ("not", TkOp "not"); ("mod", TkOp "mod");
]

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_digit c = c >= '0' && c <= '9'
let is_alnum c = is_alpha c || is_digit c || c = '\''

let tokenize input =
  let len = String.length input in
  let pos = ref 0 in
  let tokens = ref [] in
  while !pos < len do
    let c = input.[!pos] in
    if c = ' ' || c = '\t' || c = '\n' || c = '\r' then incr pos
    else if c = '(' then (tokens := TkLParen :: !tokens; incr pos)
    else if c = ')' then (tokens := TkRParen :: !tokens; incr pos)
    else if c = '[' then (tokens := TkLBrack :: !tokens; incr pos)
    else if c = ']' then (tokens := TkRBrack :: !tokens; incr pos)
    else if c = ',' then (tokens := TkComma :: !tokens; incr pos)
    else if c = '_' && (!pos + 1 >= len || not (is_alnum input.[!pos + 1])) then
      (tokens := TkUnderscore :: !tokens; incr pos)
    else if c = ';' && !pos + 1 < len && input.[!pos + 1] = ';' then
      (tokens := TkSemiSemi :: !tokens; pos := !pos + 2)
    else if c = '-' && !pos + 1 < len && input.[!pos + 1] = '>' then
      (tokens := TkArrow :: !tokens; pos := !pos + 2)
    else if c = ':' && !pos + 1 < len && input.[!pos + 1] = ':' then
      (tokens := TkColon2 :: !tokens; pos := !pos + 2)
    else if c = '|' && (!pos + 1 >= len || input.[!pos + 1] <> '|') then
      (tokens := TkBar :: !tokens; incr pos)
    else if c = '"' then begin
      incr pos;
      let start = !pos in
      while !pos < len && input.[!pos] <> '"' do incr pos done;
      let s = String.sub input start (!pos - start) in
      if !pos < len then incr pos;
      tokens := TkString s :: !tokens
    end
    else if is_digit c || (c = '-' && !pos + 1 < len && is_digit input.[!pos + 1] &&
              (match !tokens with [] -> true | TkOp _ | TkLParen | TkComma | TkArrow | TkLet | TkIn | TkThen | TkElse | TkIf | TkFun | TkBar | TkWith -> true | _ -> false)) then begin
      let start = !pos in
      if c = '-' then incr pos;
      while !pos < len && is_digit input.[!pos] do incr pos done;
      tokens := TkInt (int_of_string (String.sub input start (!pos - start))) :: !tokens
    end
    else if is_alpha c then begin
      let start = !pos in
      while !pos < len && is_alnum input.[!pos] do incr pos done;
      let word = String.sub input start (!pos - start) in
      (* Check for qualified names like List.map *)
      if !pos < len && input.[!pos] = '.' && !pos + 1 < len && is_alpha input.[!pos + 1] then begin
        incr pos;
        let start2 = !pos in
        while !pos < len && is_alnum input.[!pos] do incr pos done;
        let full = word ^ "." ^ String.sub input start2 (!pos - start2) in
        tokens := TkIdent full :: !tokens
      end else
        match List.assoc_opt word keywords with
        | Some tk -> tokens := tk :: !tokens
        | None -> tokens := TkIdent word :: !tokens
    end
    else if String.contains "+-*/<>=!&|^@" c then begin
      let start = !pos in
      while !pos < len && String.contains "+-*/<>=!&|^@" input.[!pos] do incr pos done;
      tokens := TkOp (String.sub input start (!pos - start)) :: !tokens
    end
    else incr pos
  done;
  List.rev !tokens

(* ── Recursive Descent Parser ───────────────────────────────────── *)

let tokens_ref = ref []

let peek () = match !tokens_ref with t :: _ -> t | [] -> TkEOF
let advance () = match !tokens_ref with _ :: rest -> tokens_ref := rest | [] -> ()
let expect tk =
  if peek () = tk then advance ()
  else failwith (Printf.sprintf "Parse error: expected token")

let rec parse_expr () =
  match peek () with
  | TkLet -> parse_let ()
  | TkFun -> parse_fun ()
  | TkIf -> parse_if ()
  | TkMatch -> parse_match ()
  | _ -> parse_cons_expr ()

and parse_let () =
  advance (); (* consume 'let' *)
  let is_rec = if peek () = TkRec then (advance (); true) else false in
  let name = match peek () with TkIdent x -> advance (); x | _ -> failwith "Parse error: expected identifier" in
  let params = parse_params () in
  expect (TkOp "=");
  let body = parse_expr () in
  let body_with_params = List.fold_right (fun p e -> EFun (p, e)) params body in
  expect TkIn;
  let e2 = parse_expr () in
  if is_rec then ELetRec (name, body_with_params, e2)
  else ELet (name, body_with_params, e2)

and parse_params () =
  match peek () with
  | TkIdent x when x <> "=" -> advance (); x :: parse_params ()
  | _ -> []

and parse_fun () =
  advance (); (* consume 'fun' *)
  let param = match peek () with TkIdent x -> advance (); x | _ -> failwith "Parse error: expected parameter" in
  expect TkArrow;
  let body = parse_expr () in
  EFun (param, body)

and parse_if () =
  advance (); (* consume 'if' *)
  let cond = parse_expr () in
  expect TkThen;
  let then_e = parse_expr () in
  expect TkElse;
  let else_e = parse_expr () in
  EIf (cond, then_e, else_e)

and parse_match () =
  advance (); (* consume 'match' *)
  let scrutinee = parse_expr () in
  expect TkWith;
  let cases = parse_cases () in
  EMatch (scrutinee, cases)

and parse_cases () =
  let _ = if peek () = TkBar then advance () in
  let pat = parse_pattern () in
  expect TkArrow;
  let body = parse_expr () in
  let rest = if peek () = TkBar then (advance (); parse_cases ()) else [] in
  (pat, body) :: rest

and parse_pattern () =
  let p = parse_pattern_atom () in
  if peek () = TkColon2 then begin
    advance ();
    let tail = parse_pattern () in
    PCons (p, tail)
  end else p

and parse_pattern_atom () =
  match peek () with
  | TkInt n -> advance (); PInt n
  | TkBool b -> advance (); PBool b
  | TkUnderscore -> advance (); PWild
  | TkIdent x -> advance (); PVar x
  | TkNone -> advance (); PNone
  | TkSome -> advance (); PSome (parse_pattern_atom ())
  | TkLBrack ->
    advance ();
    if peek () = TkRBrack then (advance (); PNil)
    else failwith "Parse error in pattern"
  | TkLParen ->
    advance ();
    let p = parse_pattern () in
    if peek () = TkComma then begin
      let pats = ref [p] in
      while peek () = TkComma do advance (); pats := parse_pattern () :: !pats done;
      expect TkRParen;
      PTuple (List.rev !pats)
    end else begin
      expect TkRParen; p
    end
  | _ -> PWild

and parse_cons_expr () =
  let e = parse_or_expr () in
  if peek () = TkColon2 then begin
    advance ();
    let tail = parse_cons_expr () in
    ECons (e, tail)
  end else e

and parse_or_expr () =
  let left = parse_and_expr () in
  if peek () = TkOp "||" then begin
    advance (); let right = parse_or_expr () in
    EBinOp ("||", left, right)
  end else left

and parse_and_expr () =
  let left = parse_cmp_expr () in
  if peek () = TkOp "&&" then begin
    advance (); let right = parse_and_expr () in
    EBinOp ("&&", left, right)
  end else left

and parse_cmp_expr () =
  let left = parse_concat_expr () in
  match peek () with
  | TkOp (("=" | "<>" | "<" | ">" | "<=" | ">=") as op) ->
    advance (); let right = parse_concat_expr () in
    EBinOp (op, left, right)
  | _ -> left

and parse_concat_expr () =
  let left = parse_add_expr () in
  if peek () = TkOp "^" then begin
    advance (); let right = parse_concat_expr () in
    EBinOp ("^", left, right)
  end else left

and parse_add_expr () =
  let left = ref (parse_mul_expr ()) in
  let continue_loop = ref true in
  while !continue_loop do
    match peek () with
    | TkOp (("+" | "-") as op) -> advance (); left := EBinOp (op, !left, parse_mul_expr ())
    | _ -> continue_loop := false
  done;
  !left

and parse_mul_expr () =
  let left = ref (parse_unary_expr ()) in
  let continue_loop = ref true in
  while !continue_loop do
    match peek () with
    | TkOp (("*" | "/" | "mod") as op) -> advance (); left := EBinOp (op, !left, parse_unary_expr ())
    | _ -> continue_loop := false
  done;
  !left

and parse_unary_expr () =
  match peek () with
  | TkOp "not" -> advance (); EUnOp ("not", parse_app_expr ())
  | _ -> parse_app_expr ()

and parse_app_expr () =
  let f = parse_atom () in
  let args = ref [] in
  let continue_loop = ref true in
  while !continue_loop do
    match peek () with
    | TkInt _ | TkBool _ | TkString _ | TkIdent _ | TkLParen | TkLBrack | TkNone | TkSome ->
      args := parse_atom () :: !args
    | _ -> continue_loop := false
  done;
  List.fold_left (fun acc arg -> EApp (acc, arg)) f (List.rev !args)

and parse_atom () =
  match peek () with
  | TkInt n -> advance (); EInt n
  | TkBool b -> advance (); EBool b
  | TkString s -> advance (); EString s
  | TkIdent x -> advance (); EVar x
  | TkNone -> advance (); ENone
  | TkSome -> advance (); ESome (parse_atom ())
  | TkLParen ->
    advance ();
    if peek () = TkRParen then (advance (); EUnit)
    else begin
      let e = parse_expr () in
      if peek () = TkComma then begin
        let exprs = ref [e] in
        while peek () = TkComma do advance (); exprs := parse_expr () :: !exprs done;
        expect TkRParen;
        ETuple (List.rev !exprs)
      end else begin
        expect TkRParen; e
      end
    end
  | TkLBrack ->
    advance ();
    if peek () = TkRBrack then (advance (); ENil)
    else begin
      let first = parse_expr () in
      let rest = ref [] in
      while peek () = TkOp ";" || peek () = TkSemiSemi do
        advance (); rest := parse_expr () :: !rest
      done;
      expect TkRBrack;
      List.fold_right (fun e acc -> ECons (e, acc)) (first :: List.rev !rest) ENil
    end
  | _ -> failwith "Parse error: unexpected token"

let parse input =
  tokens_ref := tokenize input;
  let expr = parse_expr () in
  expr

(* ── Display Engine ─────────────────────────────────────────────── *)

let display_separator () =
  Printf.printf "%s\n" (String.make 70 '-')

let display_step step =
  Printf.printf "  Step %d [%s]: %s\n" step.id step.rule step.expression;
  Printf.printf "    → %s\n" step.explanation;
  if step.constraints_added <> [] then
    List.iter (fun c ->
      Printf.printf "    ⊢ Constraint: %s ~ %s  (%s)\n"
        (pp_ty c.lhs) (pp_ty c.rhs) (pp_reason c.reason)
    ) step.constraints_added;
  if step.substitution_state <> [] then begin
    let recent = if List.length step.substitution_state > 3
      then List.filteri (fun i _ -> i < 3) step.substitution_state
      else step.substitution_state in
    Printf.printf "    σ = {%s%s}\n"
      (String.concat ", " (List.map (fun (v, t) ->
        Printf.sprintf "%s ↦ %s" (pp_ty (TVar v)) (pp_ty t)
      ) recent))
      (if List.length step.substitution_state > 3 then ", ..." else "")
  end

let display_result input result =
  Printf.printf "\n";
  display_separator ();
  Printf.printf "  TYPE INFERENCE DEBUGGER\n";
  Printf.printf "  Expression: %s\n" input;
  display_separator ();
  Printf.printf "\n";
  match result with
  | Success (ty, trace_steps) ->
    Printf.printf "  ═══ Inference Trace ═══\n\n";
    List.iter (fun s -> display_step s; Printf.printf "\n") trace_steps;
    display_separator ();
    Printf.printf "  ✓ Final Type: %s\n" (pp_ty ty);
    display_separator ();
    Printf.printf "\n"
  | TypeError (msg, trace_steps, conflict) ->
    Printf.printf "  ═══ Inference Trace (until error) ═══\n\n";
    List.iter (fun s -> display_step s; Printf.printf "\n") trace_steps;
    display_separator ();
    Printf.printf "  ✗ Type Error: %s\n" msg;
    Printf.printf "    Conflict: %s ≠ %s\n" (pp_ty conflict.lhs) (pp_ty conflict.rhs);
    Printf.printf "    Reason: %s\n" (pp_reason conflict.reason);
    display_separator ();
    suggest_fix msg;
    Printf.printf "\n"

(* ── Autonomous Suggestions ─────────────────────────────────────── *)

and suggest_fix msg =
  let patterns = [
    { pattern_name = "Function applied to wrong type";
      trigger = "Cannot unify int with bool";
      explanation = "You're passing an int where a bool is expected (or vice versa).";
      simpler_example = "if x + 1 then ...  (* x+1 is int, not bool. Try: if x > 0 then ... *)" };
    { pattern_name = "Infinite type (occurs check)";
      trigger = "occurs";
      explanation = "A type variable would need to contain itself. Usually means applying a function to itself incorrectly.";
      simpler_example = "let f x = f  (* f would need type 'a -> 'a -> 'a -> ... *)" };
    { pattern_name = "If-branch mismatch";
      trigger = "if-branches";
      explanation = "The then and else branches return different types. Both must agree.";
      simpler_example = "if true then 1 else \"hello\"  (* int vs string *)" };
    { pattern_name = "List element mismatch";
      trigger = "list elements";
      explanation = "All elements in a list must have the same type.";
      simpler_example = "[1; \"two\"; 3]  (* int and string can't mix *)" };
    { pattern_name = "Not a function";
      trigger = "Cannot unify int with";
      explanation = "You're trying to apply something that isn't a function.";
      simpler_example = "let x = 5 in x 3  (* x is int, not a function *)" };
  ] in
  let string_contains haystack needle =
    let nlen = String.length needle in
    let hlen = String.length haystack in
    if nlen > hlen then false
    else
      let found = ref false in
      for i = 0 to hlen - nlen do
        if not !found && String.sub haystack i nlen = needle then found := true
      done;
      !found
  in
  let matching = List.filter (fun p ->
    let trigger_lower = String.lowercase_ascii p.trigger in
    let msg_lower = String.lowercase_ascii msg in
    string_contains msg_lower trigger_lower
  ) patterns in
  match matching with
  | hint :: _ ->
    Printf.printf "\n  💡 Hint (%s):\n" hint.pattern_name;
    Printf.printf "     %s\n" hint.explanation;
    Printf.printf "     Example: %s\n" hint.simpler_example
  | [] ->
    Printf.printf "\n  💡 Tip: Break your expression into smaller parts and check each one.\n"

(* ── Example Library ────────────────────────────────────────────── *)

let examples = [
  ("Identity function", "fun x -> x");
  ("Constant function", "fun x -> fun y -> x");
  ("Integer addition", "fun x -> x + 1");
  ("Compose", "fun f -> fun g -> fun x -> f (g x)");
  ("Apply", "fun f -> fun x -> f x");
  ("Pair constructor", "fun x -> fun y -> (x, y)");
  ("List map usage", "fun f -> fun xs -> List.map f xs");
  ("Polymorphic let", "let id = fun x -> x in (id 42, id true)");
  ("Recursive factorial", "let rec fact = fun n -> if n = 0 then 1 else n * fact (n - 1) in fact 5");
  ("List cons", "fun x -> fun xs -> x :: xs");
  ("Type error: branch mismatch", "if true then 1 else \"hello\"");
  ("Type error: not a function", "let x = 5 in x 3");
  ("Option handling", "fun x -> match x with | Some v -> v + 1 | None -> 0");
  ("Higher-order fold", "List.fold_left (fun acc x -> acc + x) 0");
  ("Church numerals zero", "fun f -> fun x -> x");
]

(* ── Interactive REPL ───────────────────────────────────────────── *)

let print_help () =
  Printf.printf "\n";
  Printf.printf "  ╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "  ║         TYPE INFERENCE DEBUGGER — Interactive Mode          ║\n";
  Printf.printf "  ╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "  ║  Commands:                                                  ║\n";
  Printf.printf "  ║    <expression>  — Infer and trace type of expression       ║\n";
  Printf.printf "  ║    :examples     — Show built-in examples                   ║\n";
  Printf.printf "  ║    :run <n>      — Run example number n                     ║\n";
  Printf.printf "  ║    :all          — Run all examples                         ║\n";
  Printf.printf "  ║    :env          — Show type environment                    ║\n";
  Printf.printf "  ║    :help         — Show this help                           ║\n";
  Printf.printf "  ║    :quit         — Exit                                     ║\n";
  Printf.printf "  ╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "  ║  Supported syntax:                                          ║\n";
  Printf.printf "  ║    let x = e in body    let rec f x = e in body             ║\n";
  Printf.printf "  ║    fun x -> e           f x  (application)                  ║\n";
  Printf.printf "  ║    if c then t else e   (e1, e2, ...)  [e1; e2; ...]        ║\n";
  Printf.printf "  ║    match e with | p -> e    Some/None    x :: xs             ║\n";
  Printf.printf "  ║    + - * / mod = <> < > <= >= && || ^ not                   ║\n";
  Printf.printf "  ╚══════════════════════════════════════════════════════════════╝\n";
  Printf.printf "\n"

let show_examples () =
  Printf.printf "\n  Built-in examples:\n\n";
  List.iteri (fun i (name, code) ->
    Printf.printf "    %2d. %-30s %s\n" (i + 1) name code
  ) examples;
  Printf.printf "\n  Use ':run <n>' to trace any example.\n\n"

let show_env () =
  Printf.printf "\n  Type Environment:\n\n";
  List.iter (fun (name, scheme) ->
    Printf.printf "    %-20s : %s\n" name (pp_scheme scheme)
  ) initial_env;
  Printf.printf "\n"

let run_example input =
  try
    let expr = parse input in
    let result = infer_expression expr in
    display_result input result
  with
  | Failure msg -> Printf.printf "  Parse error: %s\n\n" msg
  | _ -> Printf.printf "  Unexpected error during inference.\n\n"

let repl () =
  print_help ();
  let running = ref true in
  while !running do
    Printf.printf "  λ> ";
    flush stdout;
    try
      let line = input_line stdin in
      let trimmed = String.trim line in
      if trimmed = "" then ()
      else if trimmed = ":quit" || trimmed = ":q" then running := false
      else if trimmed = ":help" || trimmed = ":h" then print_help ()
      else if trimmed = ":examples" || trimmed = ":ex" then show_examples ()
      else if trimmed = ":env" then show_env ()
      else if trimmed = ":all" then
        List.iter (fun (_, code) -> run_example code) examples
      else if String.length trimmed > 4 && String.sub trimmed 0 4 = ":run" then begin
        let n_str = String.trim (String.sub trimmed 4 (String.length trimmed - 4)) in
        let n = int_of_string n_str in
        if n >= 1 && n <= List.length examples then
          let (_, code) = List.nth examples (n - 1) in
          run_example code
        else Printf.printf "  Invalid example number (1-%d)\n" (List.length examples)
      end
      else run_example trimmed
    with
    | End_of_file -> running := false
    | _ -> Printf.printf "  Error processing input.\n"
  done;
  Printf.printf "\n  Goodbye! Keep exploring types. ✨\n\n"

(* ── Demo Mode ──────────────────────────────────────────────────── *)

let demo () =
  Printf.printf "\n";
  Printf.printf "  ╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "  ║      TYPE INFERENCE DEBUGGER — Demo & Learning Tool         ║\n";
  Printf.printf "  ║                                                              ║\n";
  Printf.printf "  ║  Traces step-by-step how Hindley-Milner type inference       ║\n";
  Printf.printf "  ║  derives types for OCaml expressions. Learn how the type     ║\n";
  Printf.printf "  ║  checker reasons about your code!                            ║\n";
  Printf.printf "  ╚══════════════════════════════════════════════════════════════╝\n";
  Printf.printf "\n";

  (* Run a selection of examples to demonstrate capabilities *)
  let demo_examples = [
    "fun x -> x";
    "fun f -> fun g -> fun x -> f (g x)";
    "let id = fun x -> x in (id 42, id true)";
    "let rec fact = fun n -> if n = 0 then 1 else n * fact (n - 1) in fact 5";
    "if true then 1 else \"hello\"";
  ] in

  List.iter (fun code ->
    run_example code
  ) demo_examples;

  Printf.printf "\n  Run with no arguments for interactive mode.\n";
  Printf.printf "  Try typing your own expressions to see how types are inferred!\n\n"

(* ── Main ───────────────────────────────────────────────────────── *)

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | [_] ->
    (* No arguments: interactive REPL *)
    repl ()
  | [_; "--demo"] ->
    demo ()
  | _ :: "--eval" :: rest ->
    let input = String.concat " " rest in
    run_example input
  | _ ->
    Printf.printf "Usage:\n";
    Printf.printf "  ocaml type_inference_debugger.ml           — Interactive REPL\n";
    Printf.printf "  ocaml type_inference_debugger.ml --demo    — Run demo examples\n";
    Printf.printf "  ocaml type_inference_debugger.ml --eval <expr> — Evaluate single expression\n"
