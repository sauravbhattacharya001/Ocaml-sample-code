(* ============================================================================
   refactoring_autopilot.ml - Autonomous Refactoring Autopilot Engine
   ============================================================================

   An autonomous refactoring opportunity detector and auto-applier for a
   simple OCaml-like lambda calculus AST. The engine scans expressions for
   8 categories of refactoring opportunities, ranks them by confidence,
   applies safe transformations iteratively until fixpoint, and generates
   an interactive HTML dashboard showing before/after comparison, finding
   details, transformation traces, and health scoring.

   Demonstrates:
   - Eta reduction (fun x -> f x → f)
   - Dead let-binding elimination
   - Constant folding (arithmetic on literals)
   - Identity function elimination (App(id, e) → e)
   - Redundant match simplification
   - Nested if simplification (if c then true else false → c, etc.)
   - Let inlining (single-use simple bindings)
   - Common subexpression detection and lifting
   - Iterative fixpoint refactoring with transformation traces
   - Complexity reduction and health scoring (0-100)
   - Autonomous natural-language insight generation
   - Self-contained interactive HTML dashboard

   Usage:
     ocamlopt refactoring_autopilot.ml -o refactoring_autopilot
     ./refactoring_autopilot

   Or interpreted:
     ocaml refactoring_autopilot.ml
   ============================================================================ *)

(* ── Random Infrastructure ──────────────────────────────────────────────── *)

let global_seed = ref 42424242

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
  | Lit of int
  | BoolLit of bool
  | Var of string
  | Lam of string * expr
  | App of expr * expr
  | Let of string * expr * expr
  | LetRec of string * expr * expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | IfThenElse of expr * expr * expr
  | Tuple of expr list
  | Match of expr * (pattern * expr) list
  | Seq of expr list

and pattern =
  | PWild
  | PVar of string
  | PLit of int
  | PBool of bool
  | PTuple of pattern list
  | PCons of string * pattern list

(* ── Pretty Printer ─────────────────────────────────────────────────────── *)

let rec pp_expr = function
  | Lit n -> if n < 0 then "(" ^ string_of_int n ^ ")" else string_of_int n
  | BoolLit b -> string_of_bool b
  | Var x -> x
  | Lam (x, body) -> "(fun " ^ x ^ " -> " ^ pp_expr body ^ ")"
  | App (f, arg) -> "(" ^ pp_expr f ^ " " ^ pp_expr arg ^ ")"
  | Let (x, e1, e2) ->
    "(let " ^ x ^ " = " ^ pp_expr e1 ^ " in " ^ pp_expr e2 ^ ")"
  | LetRec (x, e1, e2) ->
    "(let rec " ^ x ^ " = " ^ pp_expr e1 ^ " in " ^ pp_expr e2 ^ ")"
  | Add (a, b) -> "(" ^ pp_expr a ^ " + " ^ pp_expr b ^ ")"
  | Sub (a, b) -> "(" ^ pp_expr a ^ " - " ^ pp_expr b ^ ")"
  | Mul (a, b) -> "(" ^ pp_expr a ^ " * " ^ pp_expr b ^ ")"
  | Div (a, b) -> "(" ^ pp_expr a ^ " / " ^ pp_expr b ^ ")"
  | IfThenElse (c, t, e) ->
    "(if " ^ pp_expr c ^ " then " ^ pp_expr t ^ " else " ^ pp_expr e ^ ")"
  | Tuple es -> "(" ^ String.concat ", " (List.map pp_expr es) ^ ")"
  | Match (scrut, arms) ->
    "(match " ^ pp_expr scrut ^ " with " ^
    String.concat " | " (List.map (fun (p, e) -> pp_pattern p ^ " -> " ^ pp_expr e) arms) ^
    ")"
  | Seq es -> "(begin " ^ String.concat "; " (List.map pp_expr es) ^ " end)"

and pp_pattern = function
  | PWild -> "_"
  | PVar x -> x
  | PLit n -> string_of_int n
  | PBool b -> string_of_bool b
  | PTuple ps -> "(" ^ String.concat ", " (List.map pp_pattern ps) ^ ")"
  | PCons (name, []) -> name
  | PCons (name, ps) -> name ^ "(" ^ String.concat ", " (List.map pp_pattern ps) ^ ")"

(* ── Utility: free variables ────────────────────────────────────────────── *)

let rec free_vars = function
  | Lit _ | BoolLit _ -> []
  | Var x -> [x]
  | Lam (x, body) -> List.filter (fun v -> v <> x) (free_vars body)
  | App (f, arg) -> free_vars f @ free_vars arg
  | Let (x, e1, e2) -> free_vars e1 @ List.filter (fun v -> v <> x) (free_vars e2)
  | LetRec (x, e1, e2) ->
    List.filter (fun v -> v <> x) (free_vars e1) @
    List.filter (fun v -> v <> x) (free_vars e2)
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> free_vars a @ free_vars b
  | IfThenElse (c, t, e) -> free_vars c @ free_vars t @ free_vars e
  | Tuple es | Seq es -> List.concat_map free_vars es
  | Match (scrut, arms) ->
    free_vars scrut @ List.concat_map (fun (p, e) ->
      let bound = pattern_vars p in
      List.filter (fun v -> not (List.mem v bound)) (free_vars e)
    ) arms

and pattern_vars = function
  | PWild | PLit _ | PBool _ -> []
  | PVar x -> [x]
  | PTuple ps | PCons (_, ps) -> List.concat_map pattern_vars ps

(* ── Utility: expression size / equality ────────────────────────────────── *)

let rec expr_size = function
  | Lit _ | BoolLit _ | Var _ -> 1
  | Lam (_, body) -> 1 + expr_size body
  | App (f, arg) -> 1 + expr_size f + expr_size arg
  | Let (_, e1, e2) | LetRec (_, e1, e2) -> 1 + expr_size e1 + expr_size e2
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> 1 + expr_size a + expr_size b
  | IfThenElse (c, t, e) -> 1 + expr_size c + expr_size t + expr_size e
  | Tuple es | Seq es -> 1 + List.fold_left (fun acc e -> acc + expr_size e) 0 es
  | Match (s, arms) -> 1 + expr_size s + List.fold_left (fun acc (_, e) -> acc + expr_size e) 0 arms

let rec expr_equal a b = match a, b with
  | Lit x, Lit y -> x = y
  | BoolLit x, BoolLit y -> x = y
  | Var x, Var y -> x = y
  | Lam (x1, b1), Lam (x2, b2) -> x1 = x2 && expr_equal b1 b2
  | App (f1, a1), App (f2, a2) -> expr_equal f1 f2 && expr_equal a1 a2
  | Let (x1, e1a, e1b), Let (x2, e2a, e2b) -> x1 = x2 && expr_equal e1a e2a && expr_equal e1b e2b
  | LetRec (x1, e1a, e1b), LetRec (x2, e2a, e2b) -> x1 = x2 && expr_equal e1a e2a && expr_equal e1b e2b
  | Add (a1, b1), Add (a2, b2) -> expr_equal a1 a2 && expr_equal b1 b2
  | Sub (a1, b1), Sub (a2, b2) -> expr_equal a1 a2 && expr_equal b1 b2
  | Mul (a1, b1), Mul (a2, b2) -> expr_equal a1 a2 && expr_equal b1 b2
  | Div (a1, b1), Div (a2, b2) -> expr_equal a1 a2 && expr_equal b1 b2
  | IfThenElse (c1, t1, e1), IfThenElse (c2, t2, e2) -> expr_equal c1 c2 && expr_equal t1 t2 && expr_equal e1 e2
  | Tuple es1, Tuple es2 | Seq es1, Seq es2 ->
    List.length es1 = List.length es2 && List.for_all2 expr_equal es1 es2
  | Match (s1, arms1), Match (s2, arms2) ->
    expr_equal s1 s2 && List.length arms1 = List.length arms2 &&
    List.for_all2 (fun (p1, e1) (p2, e2) -> pattern_equal p1 p2 && expr_equal e1 e2) arms1 arms2
  | _ -> false

and pattern_equal a b = match a, b with
  | PWild, PWild -> true
  | PVar x, PVar y -> x = y
  | PLit x, PLit y -> x = y
  | PBool x, PBool y -> x = y
  | PTuple ps1, PTuple ps2 | PCons (_, ps1), PCons (_, ps2) ->
    List.length ps1 = List.length ps2 && List.for_all2 pattern_equal ps1 ps2
  | _ -> false

(* ── Utility: substitution ──────────────────────────────────────────────── *)

let rec subst var replacement = function
  | Var x when x = var -> replacement
  | Var _ as e -> e
  | Lit _ | BoolLit _ as e -> e
  | Lam (x, _) as e when x = var -> e  (* shadowed *)
  | Lam (x, body) -> Lam (x, subst var replacement body)
  | App (f, arg) -> App (subst var replacement f, subst var replacement arg)
  | Let (x, e1, e2) ->
    let e1' = subst var replacement e1 in
    if x = var then Let (x, e1', e2) else Let (x, e1', subst var replacement e2)
  | LetRec (x, e1, e2) ->
    if x = var then LetRec (x, e1, e2)
    else LetRec (x, subst var replacement e1, subst var replacement e2)
  | Add (a, b) -> Add (subst var replacement a, subst var replacement b)
  | Sub (a, b) -> Sub (subst var replacement a, subst var replacement b)
  | Mul (a, b) -> Mul (subst var replacement a, subst var replacement b)
  | Div (a, b) -> Div (subst var replacement a, subst var replacement b)
  | IfThenElse (c, t, e) ->
    IfThenElse (subst var replacement c, subst var replacement t, subst var replacement e)
  | Tuple es -> Tuple (List.map (subst var replacement) es)
  | Seq es -> Seq (List.map (subst var replacement) es)
  | Match (scrut, arms) ->
    Match (subst var replacement scrut,
      List.map (fun (p, e) ->
        if List.mem var (pattern_vars p) then (p, e)
        else (p, subst var replacement e)
      ) arms)

(* count occurrences of a variable in an expression *)
let rec count_var var = function
  | Var x -> if x = var then 1 else 0
  | Lit _ | BoolLit _ -> 0
  | Lam (x, body) -> if x = var then 0 else count_var var body
  | App (f, arg) -> count_var var f + count_var var arg
  | Let (x, e1, e2) -> count_var var e1 + (if x = var then 0 else count_var var e2)
  | LetRec (x, e1, e2) ->
    (if x = var then 0 else count_var var e1 + count_var var e2)
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> count_var var a + count_var var b
  | IfThenElse (c, t, e) -> count_var var c + count_var var t + count_var var e
  | Tuple es | Seq es -> List.fold_left (fun acc e -> acc + count_var var e) 0 es
  | Match (scrut, arms) ->
    count_var var scrut + List.fold_left (fun acc (p, e) ->
      if List.mem var (pattern_vars p) then acc else acc + count_var var e) 0 arms

(* is expression "simple" enough to inline? *)
let is_simple = function
  | Lit _ | BoolLit _ | Var _ -> true
  | _ -> false

(* ── Finding types ──────────────────────────────────────────────────────── *)

type category =
  | EtaReduction
  | DeadLetBinding
  | ConstantFolding
  | IdentityElimination
  | RedundantMatch
  | NestedIfSimplification
  | LetInlining
  | CommonSubexpression

type finding = {
  category : category;
  description : string;
  confidence : float;
  original : expr;
  suggested : expr;
  size_delta : int;  (* negative = smaller *)
}

type trace_step = {
  step_num : int;
  applied_category : category;
  before : expr;
  after : expr;
}

type detector_stats = {
  detector_name : string;
  findings_count : int;
  applied_count : int;
}

type session = {
  input_expr : expr;
  final_expr : expr;
  all_findings : finding list;
  applied_findings : finding list;
  trace : trace_step list;
  complexity_reduction : int;
  health_score : int;
  detector_stats : detector_stats list;
  insights : string list;
}

let category_name = function
  | EtaReduction -> "Eta Reduction"
  | DeadLetBinding -> "Dead Let Binding"
  | ConstantFolding -> "Constant Folding"
  | IdentityElimination -> "Identity Elimination"
  | RedundantMatch -> "Redundant Match"
  | NestedIfSimplification -> "Nested If Simplification"
  | LetInlining -> "Let Inlining"
  | CommonSubexpression -> "Common Subexpression"

let category_color = function
  | EtaReduction -> "#e74c3c"
  | DeadLetBinding -> "#3498db"
  | ConstantFolding -> "#2ecc71"
  | IdentityElimination -> "#9b59b6"
  | RedundantMatch -> "#f39c12"
  | NestedIfSimplification -> "#1abc9c"
  | LetInlining -> "#e67e22"
  | CommonSubexpression -> "#34495e"

(* ── Detector 1: Eta Reduction ──────────────────────────────────────────── *)
(* fun x -> f x  →  f   (when x not free in f) *)

let detect_eta expr =
  let findings = ref [] in
  let rec scan e = match e with
    | Lam (x, App (f, Var y)) when x = y && not (List.mem x (free_vars f)) ->
      findings := {
        category = EtaReduction;
        description = Printf.sprintf "fun %s -> %s %s can be eta-reduced to %s" x (pp_expr f) x (pp_expr f);
        confidence = 0.95;
        original = e;
        suggested = f;
        size_delta = -(expr_size e - expr_size f);
      } :: !findings;
      scan f
    | Lam (_, body) -> scan body
    | App (f, arg) -> scan f; scan arg
    | Let (_, e1, e2) | LetRec (_, e1, e2) -> scan e1; scan e2
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> scan a; scan b
    | IfThenElse (c, t, e) -> scan c; scan t; scan e
    | Tuple es | Seq es -> List.iter scan es
    | Match (s, arms) -> scan s; List.iter (fun (_, e) -> scan e) arms
    | Lit _ | BoolLit _ | Var _ -> ()
  in
  scan expr; !findings

(* ── Detector 2: Dead Let Binding ───────────────────────────────────────── *)

let detect_dead_let expr =
  let findings = ref [] in
  let rec scan e = match e with
    | Let (x, e1, e2) when count_var x e2 = 0 ->
      findings := {
        category = DeadLetBinding;
        description = Printf.sprintf "let %s = ... is never used in body" x;
        confidence = 0.99;
        original = e;
        suggested = e2;
        size_delta = -(1 + expr_size e1);
      } :: !findings;
      scan e1; scan e2
    | Let (_, e1, e2) | LetRec (_, e1, e2) -> scan e1; scan e2
    | Lam (_, body) -> scan body
    | App (f, arg) -> scan f; scan arg
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> scan a; scan b
    | IfThenElse (c, t, e) -> scan c; scan t; scan e
    | Tuple es | Seq es -> List.iter scan es
    | Match (s, arms) -> scan s; List.iter (fun (_, e) -> scan e) arms
    | Lit _ | BoolLit _ | Var _ -> ()
  in
  scan expr; !findings

(* ── Detector 3: Constant Folding ───────────────────────────────────────── *)

let detect_constant_fold expr =
  let findings = ref [] in
  let try_fold e = match e with
    | Add (Lit a, Lit b) ->
      Some { category = ConstantFolding;
             description = Printf.sprintf "%d + %d = %d" a b (a+b);
             confidence = 1.0; original = e; suggested = Lit (a+b); size_delta = -2; }
    | Sub (Lit a, Lit b) ->
      Some { category = ConstantFolding;
             description = Printf.sprintf "%d - %d = %d" a b (a-b);
             confidence = 1.0; original = e; suggested = Lit (a-b); size_delta = -2; }
    | Mul (Lit a, Lit b) ->
      Some { category = ConstantFolding;
             description = Printf.sprintf "%d * %d = %d" a b (a*b);
             confidence = 1.0; original = e; suggested = Lit (a*b); size_delta = -2; }
    | Div (Lit a, Lit b) when b <> 0 ->
      Some { category = ConstantFolding;
             description = Printf.sprintf "%d / %d = %d" a b (a/b);
             confidence = 1.0; original = e; suggested = Lit (a/b); size_delta = -2; }
    | Mul (Lit 0, _) | Mul (_, Lit 0) ->
      Some { category = ConstantFolding;
             description = "multiplication by 0";
             confidence = 0.9; original = e; suggested = Lit 0; size_delta = -(expr_size e - 1); }
    | Mul (Lit 1, b) ->
      Some { category = ConstantFolding;
             description = "multiplication by 1";
             confidence = 0.95; original = e; suggested = b; size_delta = -2; }
    | Mul (a, Lit 1) ->
      Some { category = ConstantFolding;
             description = "multiplication by 1";
             confidence = 0.95; original = e; suggested = a; size_delta = -2; }
    | Add (Lit 0, b) ->
      Some { category = ConstantFolding;
             description = "addition of 0";
             confidence = 0.95; original = e; suggested = b; size_delta = -2; }
    | Add (a, Lit 0) ->
      Some { category = ConstantFolding;
             description = "addition of 0";
             confidence = 0.95; original = e; suggested = a; size_delta = -2; }
    | Sub (a, Lit 0) ->
      Some { category = ConstantFolding;
             description = "subtraction of 0";
             confidence = 0.95; original = e; suggested = a; size_delta = -2; }
    | _ -> None
  in
  let rec scan e =
    (match try_fold e with Some f -> findings := f :: !findings | None -> ());
    match e with
    | Lam (_, body) -> scan body
    | App (f, arg) -> scan f; scan arg
    | Let (_, e1, e2) | LetRec (_, e1, e2) -> scan e1; scan e2
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> scan a; scan b
    | IfThenElse (c, t, e) -> scan c; scan t; scan e
    | Tuple es | Seq es -> List.iter scan es
    | Match (s, arms) -> scan s; List.iter (fun (_, e) -> scan e) arms
    | Lit _ | BoolLit _ | Var _ -> ()
  in
  scan expr; !findings

(* ── Detector 4: Identity Function Elimination ──────────────────────────── *)
(* App(fun x -> x, e) → e *)

let detect_identity_elim expr =
  let findings = ref [] in
  let rec scan e = match e with
    | App (Lam (x, Var y), arg) when x = y ->
      findings := {
        category = IdentityElimination;
        description = Printf.sprintf "(fun %s -> %s) applied — identity elimination" x x;
        confidence = 1.0; original = e; suggested = arg;
        size_delta = -(2 + expr_size arg - expr_size arg);  (* removes the wrapper *)
      } :: !findings;
      scan arg
    | Lam (_, body) -> scan body
    | App (f, arg) -> scan f; scan arg
    | Let (_, e1, e2) | LetRec (_, e1, e2) -> scan e1; scan e2
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> scan a; scan b
    | IfThenElse (c, t, e) -> scan c; scan t; scan e
    | Tuple es | Seq es -> List.iter scan es
    | Match (s, arms) -> scan s; List.iter (fun (_, e) -> scan e) arms
    | Lit _ | BoolLit _ | Var _ -> ()
  in
  scan expr; !findings

(* ── Detector 5: Redundant Match ────────────────────────────────────────── *)
(* match e with _ -> body  or  match e with x -> body *)

let detect_redundant_match expr =
  let findings = ref [] in
  let rec scan e = match e with
    | Match (scrut, [(PWild, body)]) ->
      findings := {
        category = RedundantMatch;
        description = "match with single wildcard arm — redundant";
        confidence = 0.95; original = e; suggested = body;
        size_delta = -(1 + expr_size scrut);
      } :: !findings;
      scan scrut; scan body
    | Match (scrut, [(PVar x, body)]) ->
      let suggested = Let (x, scrut, body) in
      findings := {
        category = RedundantMatch;
        description = Printf.sprintf "match with single var arm '%s' — use let binding" x;
        confidence = 0.85; original = e; suggested;
        size_delta = 0;
      } :: !findings;
      scan scrut; scan body
    | Lam (_, body) -> scan body
    | App (f, arg) -> scan f; scan arg
    | Let (_, e1, e2) | LetRec (_, e1, e2) -> scan e1; scan e2
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> scan a; scan b
    | IfThenElse (c, t, e) -> scan c; scan t; scan e
    | Tuple es | Seq es -> List.iter scan es
    | Match (s, arms) -> scan s; List.iter (fun (_, e) -> scan e) arms
    | Lit _ | BoolLit _ | Var _ -> ()
  in
  scan expr; !findings

(* ── Detector 6: Nested If Simplification ───────────────────────────────── *)

let detect_nested_if expr =
  let findings = ref [] in
  let rec scan e = match e with
    | IfThenElse (c, BoolLit true, BoolLit false) ->
      findings := {
        category = NestedIfSimplification;
        description = "if c then true else false → c";
        confidence = 0.98; original = e; suggested = c; size_delta = -2;
      } :: !findings;
      scan c
    | IfThenElse (c, BoolLit false, BoolLit true) ->
      let neg = App (Var "not", c) in
      findings := {
        category = NestedIfSimplification;
        description = "if c then false else true → not c";
        confidence = 0.95; original = e; suggested = neg; size_delta = -1;
      } :: !findings;
      scan c
    | IfThenElse (_, t, e_branch) when expr_equal t e_branch ->
      findings := {
        category = NestedIfSimplification;
        description = "if c then e else e → e (both branches identical)";
        confidence = 0.99; original = e; suggested = t; size_delta = -(1 + expr_size t);
      } :: !findings;
      scan t
    | IfThenElse (c, t, e_branch) -> scan c; scan t; scan e_branch
    | Lam (_, body) -> scan body
    | App (f, arg) -> scan f; scan arg
    | Let (_, e1, e2) | LetRec (_, e1, e2) -> scan e1; scan e2
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> scan a; scan b
    | Tuple es | Seq es -> List.iter scan es
    | Match (s, arms) -> scan s; List.iter (fun (_, e) -> scan e) arms
    | Lit _ | BoolLit _ | Var _ -> ()
  in
  scan expr; !findings

(* ── Detector 7: Let Inlining ───────────────────────────────────────────── *)
(* let x = <simple> in <body where x used once> → substitute *)

let detect_let_inline expr =
  let findings = ref [] in
  let rec scan e = match e with
    | Let (x, e1, e2) when is_simple e1 && count_var x e2 = 1 ->
      let suggested = subst x e1 e2 in
      findings := {
        category = LetInlining;
        description = Printf.sprintf "let %s = %s used once — inline" x (pp_expr e1);
        confidence = 0.90; original = e; suggested;
        size_delta = -(1 + expr_size e1);
      } :: !findings;
      scan e1; scan e2
    | Let (_, e1, e2) | LetRec (_, e1, e2) -> scan e1; scan e2
    | Lam (_, body) -> scan body
    | App (f, arg) -> scan f; scan arg
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> scan a; scan b
    | IfThenElse (c, t, e) -> scan c; scan t; scan e
    | Tuple es | Seq es -> List.iter scan es
    | Match (s, arms) -> scan s; List.iter (fun (_, e) -> scan e) arms
    | Lit _ | BoolLit _ | Var _ -> ()
  in
  scan expr; !findings

(* ── Detector 8: Common Subexpression Detection ─────────────────────────── *)

let detect_common_subexpr expr =
  let findings = ref [] in
  let sub_table : (string, int) Hashtbl.t = Hashtbl.create 32 in
  let rec collect e =
    let s = expr_size e in
    if s >= 3 then begin  (* only non-trivial subexpressions *)
      let key = pp_expr e in
      let cur = try Hashtbl.find sub_table key with Not_found -> 0 in
      Hashtbl.replace sub_table key (cur + 1)
    end;
    match e with
    | Lam (_, body) -> collect body
    | App (f, arg) -> collect f; collect arg
    | Let (_, e1, e2) | LetRec (_, e1, e2) -> collect e1; collect e2
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> collect a; collect b
    | IfThenElse (c, t, e) -> collect c; collect t; collect e
    | Tuple es | Seq es -> List.iter collect es
    | Match (s, arms) -> collect s; List.iter (fun (_, e) -> collect e) arms
    | Lit _ | BoolLit _ | Var _ -> ()
  in
  collect expr;
  Hashtbl.iter (fun key count ->
    if count >= 2 then
      findings := {
        category = CommonSubexpression;
        description = Printf.sprintf "'%s' appears %d times — lift to let binding" key count;
        confidence = 0.70;
        original = expr;
        suggested = expr;  (* actual transformation is complex; flag only *)
        size_delta = 0;
      } :: !findings
  ) sub_table;
  !findings

(* ── Run All Detectors ──────────────────────────────────────────────────── *)

let run_all_detectors expr =
  detect_eta expr @
  detect_dead_let expr @
  detect_constant_fold expr @
  detect_identity_elim expr @
  detect_redundant_match expr @
  detect_nested_if expr @
  detect_let_inline expr @
  detect_common_subexpr expr

(* ── Apply Single Refactoring ───────────────────────────────────────────── *)

let rec apply_refactoring finding e =
  if expr_equal e finding.original then finding.suggested
  else match e with
  | Lam (x, body) -> Lam (x, apply_refactoring finding body)
  | App (f, arg) -> App (apply_refactoring finding f, apply_refactoring finding arg)
  | Let (x, e1, e2) -> Let (x, apply_refactoring finding e1, apply_refactoring finding e2)
  | LetRec (x, e1, e2) -> LetRec (x, apply_refactoring finding e1, apply_refactoring finding e2)
  | Add (a, b) -> Add (apply_refactoring finding a, apply_refactoring finding b)
  | Sub (a, b) -> Sub (apply_refactoring finding a, apply_refactoring finding b)
  | Mul (a, b) -> Mul (apply_refactoring finding a, apply_refactoring finding b)
  | Div (a, b) -> Div (apply_refactoring finding a, apply_refactoring finding b)
  | IfThenElse (c, t, el) ->
    IfThenElse (apply_refactoring finding c, apply_refactoring finding t, apply_refactoring finding el)
  | Tuple es -> Tuple (List.map (apply_refactoring finding) es)
  | Seq es -> Seq (List.map (apply_refactoring finding) es)
  | Match (s, arms) ->
    Match (apply_refactoring finding s,
      List.map (fun (p, body) -> (p, apply_refactoring finding body)) arms)
  | e -> e

(* ── Apply All (fixpoint) ──────────────────────────────────────────────── *)

let apply_all expr =
  let trace = ref [] in
  let applied = ref [] in
  let step_count = ref 0 in
  let max_iterations = 50 in
  let rec loop current iteration =
    if iteration >= max_iterations then current
    else
      (* only apply findings with confidence > threshold and not CSE *)
      let findings = run_all_detectors current in
      let actionable = List.filter (fun f ->
        f.confidence >= 0.80 && f.category <> CommonSubexpression
      ) findings in
      match actionable with
      | [] -> current
      | f :: _ ->
        let next = apply_refactoring f current in
        if expr_equal next current then
          (* try next finding *)
          let rest = List.filter (fun f2 -> not (expr_equal f2.original f.original)) actionable in
          (match rest with
           | [] -> current
           | f2 :: _ ->
             let next2 = apply_refactoring f2 current in
             if expr_equal next2 current then current
             else begin
               incr step_count;
               trace := { step_num = !step_count; applied_category = f2.category;
                          before = current; after = next2 } :: !trace;
               applied := f2 :: !applied;
               loop next2 (iteration + 1)
             end)
        else begin
          incr step_count;
          trace := { step_num = !step_count; applied_category = f.category;
                     before = current; after = next } :: !trace;
          applied := f :: !applied;
          loop next (iteration + 1)
        end
  in
  let final = loop expr 0 in
  (final, List.rev !trace, List.rev !applied)

(* ── Scoring ────────────────────────────────────────────────────────────── *)

let compute_complexity_reduction original final =
  let s0 = expr_size original in
  let s1 = expr_size final in
  if s0 = 0 then 0
  else
    let reduction = float_of_int (s0 - s1) /. float_of_int s0 *. 100.0 in
    max 0 (min 100 (int_of_float reduction))

let compute_health_score expr =
  let findings = run_all_detectors expr in
  let actionable = List.filter (fun f -> f.confidence >= 0.5) findings in
  let count = List.length actionable in
  let size = expr_size expr in
  (* fewer findings per size = healthier *)
  if size = 0 then 100
  else
    let density = float_of_int count /. float_of_int size in
    let score = 100.0 -. (density *. 500.0) in
    max 0 (min 100 (int_of_float score))

(* ── Detector Stats ─────────────────────────────────────────────────────── *)

let compute_detector_stats all_findings applied_findings =
  let categories = [EtaReduction; DeadLetBinding; ConstantFolding; IdentityElimination;
                    RedundantMatch; NestedIfSimplification; LetInlining; CommonSubexpression] in
  List.map (fun cat ->
    let found = List.length (List.filter (fun f -> f.category = cat) all_findings) in
    let applied = List.length (List.filter (fun f -> f.category = cat) applied_findings) in
    { detector_name = category_name cat; findings_count = found; applied_count = applied }
  ) categories

(* ── Insight Generation ─────────────────────────────────────────────────── *)

let generate_insights session =
  let insights = ref [] in
  let add s = insights := s :: !insights in

  if session.complexity_reduction > 30 then
    add (Printf.sprintf "Significant simplification achieved: %d%% complexity reduction." session.complexity_reduction);
  if session.complexity_reduction = 0 then
    add "No complexity reduction — code is already well-optimized or findings were advisory-only.";

  let cse_count = List.length (List.filter (fun f -> f.category = CommonSubexpression) session.all_findings) in
  if cse_count > 0 then
    add (Printf.sprintf "Found %d common subexpression(s) — consider extracting to let bindings for clarity." cse_count);

  let dead_count = List.length (List.filter (fun f -> f.category = DeadLetBinding) session.all_findings) in
  if dead_count > 0 then
    add (Printf.sprintf "Detected %d dead let binding(s) — unused code can confuse maintainers." dead_count);

  let eta_count = List.length (List.filter (fun f -> f.category = EtaReduction) session.all_findings) in
  if eta_count > 0 then
    add (Printf.sprintf "%d eta-reducible lambda(s) found — idiomatic OCaml prefers point-free where clear." eta_count);

  if session.health_score >= 90 then
    add "Code health is excellent — minimal refactoring opportunities remain."
  else if session.health_score >= 70 then
    add "Code health is good — a few targeted refactorings could improve readability."
  else if session.health_score >= 50 then
    add "Code health is moderate — several refactoring opportunities exist."
  else
    add "Code health needs attention — significant refactoring would improve maintainability.";

  let total_applied = List.length session.applied_findings in
  let total_found = List.length session.all_findings in
  if total_applied > 0 && total_found > total_applied then
    add (Printf.sprintf "Applied %d of %d findings — remaining %d are advisory or below confidence threshold."
      total_applied total_found (total_found - total_applied));

  List.rev !insights

(* ── Full Pipeline ──────────────────────────────────────────────────────── *)

let run_autopilot expr =
  let all_findings = run_all_detectors expr in
  let (final, trace, applied_findings) = apply_all expr in
  let complexity_reduction = compute_complexity_reduction expr final in
  let health_score = compute_health_score final in
  let detector_stats = compute_detector_stats all_findings applied_findings in
  let session = {
    input_expr = expr;
    final_expr = final;
    all_findings;
    applied_findings;
    trace;
    complexity_reduction;
    health_score;
    detector_stats;
    insights = [];
  } in
  let insights = generate_insights session in
  { session with insights }

(* ── Text Report ────────────────────────────────────────────────────────── *)

let print_session session =
  Printf.printf "\n╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║         REFACTORING AUTOPILOT — SESSION REPORT             ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║ Input:  %s\n" (pp_expr session.input_expr);
  Printf.printf "║ Output: %s\n" (pp_expr session.final_expr);
  Printf.printf "║ Size:   %d → %d nodes\n" (expr_size session.input_expr) (expr_size session.final_expr);
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║ Complexity Reduction: %d%%\n" session.complexity_reduction;
  Printf.printf "║ Health Score:         %d/100\n" session.health_score;
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║ Findings: %d total, %d applied\n"
    (List.length session.all_findings) (List.length session.applied_findings);
  Printf.printf "╠──────────────────────────────────────────────────────────────╣\n";
  List.iter (fun f ->
    Printf.printf "║  [%.2f] %-25s %s\n" f.confidence (category_name f.category) f.description
  ) session.all_findings;
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║ Transformation Trace (%d steps):\n" (List.length session.trace);
  List.iter (fun t ->
    Printf.printf "║  Step %d [%s]: %s → %s\n"
      t.step_num (category_name t.applied_category)
      (pp_expr t.before) (pp_expr t.after)
  ) session.trace;
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║ Detector Statistics:\n";
  List.iter (fun d ->
    if d.findings_count > 0 then
      Printf.printf "║  %-28s found: %d  applied: %d\n" d.detector_name d.findings_count d.applied_count
  ) session.detector_stats;
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║ Insights:\n";
  List.iter (fun s -> Printf.printf "║  • %s\n" s) session.insights;
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n\n"

(* ── HTML Dashboard ─────────────────────────────────────────────────────── *)

let html_escape s =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c -> match c with
    | '<' -> Buffer.add_string buf "&lt;"
    | '>' -> Buffer.add_string buf "&gt;"
    | '&' -> Buffer.add_string buf "&amp;"
    | '"' -> Buffer.add_string buf "&quot;"
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let generate_dashboard session =
  let b = Buffer.create 8192 in
  let add s = Buffer.add_string b s in
  add "<!DOCTYPE html><html lang='en'><head><meta charset='UTF-8'>\n";
  add "<meta name='viewport' content='width=device-width,initial-scale=1'>\n";
  add "<title>Refactoring Autopilot Dashboard</title>\n";
  add "<style>\n";
  add "* { margin:0; padding:0; box-sizing:border-box; }\n";
  add "body { font-family:'Segoe UI',system-ui,sans-serif; background:#0f0f23; color:#e0e0e0; padding:20px; }\n";
  add ".header { text-align:center; padding:30px 0; }\n";
  add ".header h1 { font-size:2em; color:#00ff88; }\n";
  add ".header .subtitle { color:#888; margin-top:8px; }\n";
  add ".grid { display:grid; grid-template-columns:1fr 1fr; gap:20px; max-width:1400px; margin:20px auto; }\n";
  add ".card { background:#1a1a2e; border-radius:12px; padding:20px; border:1px solid #333; }\n";
  add ".card h2 { color:#00ff88; margin-bottom:15px; font-size:1.1em; }\n";
  add ".full-width { grid-column: 1/-1; }\n";
  add ".gauge { width:120px; height:120px; border-radius:50%; display:inline-flex; align-items:center; justify-content:center; font-size:2em; font-weight:bold; margin:10px; }\n";
  add ".gauge-good { background:conic-gradient(#00ff88 var(--pct), #333 0); }\n";
  add ".gauge-label { display:block; text-align:center; font-size:0.8em; color:#888; margin-top:5px; }\n";
  add ".score-container { display:flex; justify-content:center; gap:40px; }\n";
  add ".score-wrap { text-align:center; }\n";
  add ".score-inner { background:#0f0f23; border-radius:50%; width:100px; height:100px; display:flex; align-items:center; justify-content:center; margin:10px auto; }\n";
  add "table { width:100%; border-collapse:collapse; }\n";
  add "th,td { padding:8px 12px; text-align:left; border-bottom:1px solid #333; font-size:0.9em; }\n";
  add "th { color:#00ff88; }\n";
  add ".badge { padding:2px 8px; border-radius:4px; font-size:0.8em; color:#fff; }\n";
  add ".insight { background:#162447; padding:10px 15px; border-radius:8px; margin:8px 0; border-left:3px solid #00ff88; }\n";
  add "pre { background:#0f0f23; padding:15px; border-radius:8px; overflow-x:auto; font-size:0.85em; border:1px solid #333; }\n";
  add ".bar { height:20px; border-radius:4px; min-width:2px; }\n";
  add ".bar-row { display:flex; align-items:center; gap:10px; margin:6px 0; }\n";
  add ".bar-label { width:200px; text-align:right; font-size:0.85em; }\n";
  add ".bar-container { flex:1; background:#333; border-radius:4px; height:20px; }\n";
  add ".bar-value { font-size:0.85em; width:60px; }\n";
  add ".trace-step { background:#162447; padding:10px 15px; border-radius:8px; margin:8px 0; border-left:3px solid #3498db; }\n";
  add ".trace-step .step-header { color:#3498db; font-weight:bold; }\n";
  add "</style></head><body>\n";

  (* Header *)
  add "<div class='header'><h1>🔧 Refactoring Autopilot</h1>\n";
  add "<p class='subtitle'>Autonomous Code Simplification Engine</p></div>\n";

  (* Scores *)
  add "<div class='grid'><div class='card full-width'><h2>📊 Scores</h2>\n";
  add "<div class='score-container'>\n";
  Printf.ksprintf add "<div class='score-wrap'><div class='gauge gauge-good' style='--pct:%d%%'><div class='score-inner'>%d%%</div></div><span class='gauge-label'>Complexity Reduction</span></div>\n"
    session.complexity_reduction session.complexity_reduction;
  Printf.ksprintf add "<div class='score-wrap'><div class='gauge gauge-good' style='--pct:%d%%'><div class='score-inner'>%d</div></div><span class='gauge-label'>Health Score</span></div>\n"
    session.health_score session.health_score;
  Printf.ksprintf add "<div class='score-wrap'><div class='score-inner' style='font-size:1.8em;font-weight:bold;color:#00ff88'>%d→%d</div><span class='gauge-label'>AST Nodes</span></div>\n"
    (expr_size session.input_expr) (expr_size session.final_expr);
  add "</div></div>\n";

  (* Before/After *)
  add "<div class='card'><h2>📝 Before</h2>\n";
  Printf.ksprintf add "<pre>%s</pre></div>\n" (html_escape (pp_expr session.input_expr));
  add "<div class='card'><h2>✅ After</h2>\n";
  Printf.ksprintf add "<pre>%s</pre></div>\n" (html_escape (pp_expr session.final_expr));

  (* Findings Table *)
  add "<div class='card full-width'><h2>🔍 Findings</h2>\n";
  add "<table><tr><th>Category</th><th>Description</th><th>Confidence</th></tr>\n";
  List.iter (fun f ->
    Printf.ksprintf add "<tr><td><span class='badge' style='background:%s'>%s</span></td><td>%s</td><td>%.0f%%</td></tr>\n"
      (category_color f.category) (category_name f.category)
      (html_escape f.description) (f.confidence *. 100.0)
  ) session.all_findings;
  add "</table></div>\n";

  (* Detector Bar Chart *)
  add "<div class='card'><h2>📊 Detector Breakdown</h2>\n";
  let max_found = List.fold_left (fun acc d -> max acc d.findings_count) 1 session.detector_stats in
  List.iter (fun d ->
    if d.findings_count > 0 then begin
      let pct = d.findings_count * 100 / max_found in
      Printf.ksprintf add "<div class='bar-row'><div class='bar-label'>%s</div><div class='bar-container'><div class='bar' style='width:%d%%;background:#00ff88'></div></div><div class='bar-value'>%d found / %d applied</div></div>\n"
        d.detector_name pct d.findings_count d.applied_count
    end
  ) session.detector_stats;
  add "</div>\n";

  (* Transformation Trace *)
  add "<div class='card'><h2>🔄 Transformation Trace</h2>\n";
  if session.trace = [] then
    add "<p style='color:#888'>No transformations applied — code is already clean.</p>\n"
  else
    List.iter (fun t ->
      Printf.ksprintf add "<div class='trace-step'><div class='step-header'>Step %d — %s</div><pre>%s\n  ↓\n%s</pre></div>\n"
        t.step_num (category_name t.applied_category)
        (html_escape (pp_expr t.before)) (html_escape (pp_expr t.after))
    ) session.trace;
  add "</div>\n";

  (* Insights *)
  add "<div class='card full-width'><h2>💡 Insights</h2>\n";
  List.iter (fun s ->
    Printf.ksprintf add "<div class='insight'>%s</div>\n" (html_escape s)
  ) session.insights;
  add "</div></div>\n";

  add "</body></html>\n";
  Buffer.contents b

(* ── Test Helpers (for external test file) ──────────────────────────────── *)

let finding_count_for cat findings =
  List.length (List.filter (fun f -> f.category = cat) findings)

(* ── Main ───────────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Refactoring Autopilot Engine ===\n\n";

  (* Example 1: Eta-reducible lambda *)
  let e1 = Lam ("x", App (Var "f", Var "x")) in
  let s1 = run_autopilot e1 in
  print_session s1;

  (* Example 2: Dead let binding *)
  let e2 = Let ("unused", Add (Lit 1, Lit 2), Var "y") in
  let s2 = run_autopilot e2 in
  print_session s2;

  (* Example 3: Constant folding chain *)
  let e3 = Add (Mul (Lit 3, Lit 4), Sub (Lit 10, Lit 3)) in
  let s3 = run_autopilot e3 in
  print_session s3;

  (* Example 4: Identity elimination *)
  let e4 = App (Lam ("x", Var "x"), Add (Lit 1, Lit 2)) in
  let s4 = run_autopilot e4 in
  print_session s4;

  (* Example 5: Redundant match *)
  let e5 = Match (Var "x", [(PWild, Lit 42)]) in
  let s5 = run_autopilot e5 in
  print_session s5;

  (* Example 6: Nested if simplification *)
  let e6 = IfThenElse (Var "flag", BoolLit true, BoolLit false) in
  let s6 = run_autopilot e6 in
  print_session s6;

  (* Example 7: Let inlining *)
  let e7 = Let ("a", Lit 5, Add (Var "a", Lit 10)) in
  let s7 = run_autopilot e7 in
  print_session s7;

  (* Example 8: Complex expression with multiple opportunities *)
  let e8 =
    Let ("unused", Lit 99,
      Let ("id", Lam ("x", Var "x"),
        App (Var "id",
          Add (Mul (Lit 2, Lit 3),
            IfThenElse (Var "cond", BoolLit true, BoolLit false)))))
  in
  let s8 = run_autopilot e8 in
  print_session s8;

  (* Example 9: Common subexpressions *)
  let shared = Add (Var "a", Var "b") in
  let e9 = Tuple [shared; Mul (shared, Lit 2); shared] in
  let s9 = run_autopilot e9 in
  print_session s9;

  (* Example 10: Deeply nested with all opportunities *)
  let e10 =
    Let ("dead", Lit 0,
      Lam ("y", App (Var "f", Var "y")))
  in
  let s10 = run_autopilot e10 in
  print_session s10;

  (* Write dashboard for last complex example *)
  let dashboard = generate_dashboard s8 in
  let oc = open_out "refactoring_autopilot_dashboard.html" in
  output_string oc dashboard;
  close_out oc;
  Printf.printf "Dashboard written to refactoring_autopilot_dashboard.html\n"
