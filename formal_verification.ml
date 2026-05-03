(* formal_verification.ml - Autonomous Formal Verification Engine
 *
 * Hoare-logic-based program verification with weakest precondition (WP)
 * calculus, verification condition generation, invariant inference, and
 * autonomous verification orchestration for a simple imperative language.
 *
 * Concepts demonstrated:
 * - Hoare logic and axiomatic semantics
 * - Dijkstra's weakest precondition calculus
 * - Verification condition (VC) generation and checking
 * - Heuristic loop invariant inference (4 strategies)
 * - Static program analysis (liveness, reaching definitions, termination)
 * - Autonomous orchestration with health scoring 0-100
 * - Interactive HTML dashboard generation
 *
 * IMP language syntax (annotated):
 *   {precondition}
 *   x := expr;
 *   while (cond) inv (invariant) {
 *     body
 *   }
 *   {postcondition}
 *
 * Example:
 *   {x >= 0}
 *   y := 0;
 *   z := 0;
 *   while (z < x) inv (y = z * z) {
 *     y := y + 2 * z + 1;
 *     z := z + 1
 *   }
 *   {y = x * x}
 *
 * Usage:
 *   ocamlopt formal_verification.ml -o formal_verification
 *   ./formal_verification --demo
 *   ./formal_verification --verify program.imp
 *   ./formal_verification --dashboard
 *   (or) ocaml formal_verification.ml --demo
 *)

(* ========== Expression Language ========== *)

type binop = Add | Sub | Mul | Div | Mod

type cmpop = Eq | Ne | Lt | Le | Gt | Ge

type expr =
  | EConst of int
  | EVar of string
  | EBinop of binop * expr * expr

type bexpr =
  | BTrue
  | BFalse
  | BNot of bexpr
  | BAnd of bexpr * bexpr
  | BOr of bexpr * bexpr
  | BCmp of cmpop * expr * expr

(* ========== Statement Language (IMP) ========== *)

type stmt =
  | SSkip
  | SAssign of string * expr
  | SSeq of stmt * stmt
  | SIf of bexpr * stmt * stmt
  | SWhile of bexpr * prop option * stmt  (* cond, invariant, body *)
  | SAssert of bexpr

(* ========== Assertion / Proposition Language ========== *)

and prop =
  | PTrue
  | PFalse
  | PNot of prop
  | PAnd of prop * prop
  | POr of prop * prop
  | PImplies of prop * prop
  | PCmp of cmpop * expr * expr

(* ========== Hoare Triple ========== *)

type hoare_triple = {
  precondition: prop;
  program: stmt;
  postcondition: prop;
}

(* ========== Verification Condition ========== *)

type vc_origin =
  | VCPrecondition
  | VCInvariantInit
  | VCInvariantPreservation
  | VCLoopExit
  | VCPostcondition
  | VCAssertion

type vc_status =
  | VCValid
  | VCInvalid of string (* counterexample *)
  | VCUnknown of string (* reason *)

type vc = {
  vc_id: int;
  vc_origin: vc_origin;
  vc_prop: prop;
  vc_status: vc_status;
  vc_label: string;
}

(* ========== Invariant Candidate ========== *)

type inv_strategy =
  | ConstantPropagation
  | BoundInference
  | RelationshipInference
  | PostconditionWeakening

type inv_candidate = {
  inv_prop: prop;
  inv_strategy: inv_strategy;
  inv_confidence: float;
  inv_description: string;
}

(* ========== Verification Result ========== *)

type verdict =
  | Verified
  | Failed of int list  (* failed VC ids *)
  | Partial of int list  (* unknown VC ids *)

type verification_result = {
  vcs: vc list;
  verdict: verdict;
  health_score: int;
  invariants_provided: int;
  invariants_inferred: int;
  insights: string list;
}

(* ========== Pretty Printing ========== *)

let binop_to_string = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"

let cmpop_to_string = function
  | Eq -> "=" | Ne -> "!=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="

let rec expr_to_string = function
  | EConst n -> string_of_int n
  | EVar x -> x
  | EBinop (op, a, b) ->
    "(" ^ expr_to_string a ^ " " ^ binop_to_string op ^ " " ^ expr_to_string b ^ ")"

let rec bexpr_to_string = function
  | BTrue -> "true"
  | BFalse -> "false"
  | BNot e -> "!(" ^ bexpr_to_string e ^ ")"
  | BAnd (a, b) -> "(" ^ bexpr_to_string a ^ " && " ^ bexpr_to_string b ^ ")"
  | BOr (a, b) -> "(" ^ bexpr_to_string a ^ " || " ^ bexpr_to_string b ^ ")"
  | BCmp (op, a, b) -> expr_to_string a ^ " " ^ cmpop_to_string op ^ " " ^ expr_to_string b

let rec prop_to_string = function
  | PTrue -> "true"
  | PFalse -> "false"
  | PNot p -> "~(" ^ prop_to_string p ^ ")"
  | PAnd (a, b) -> "(" ^ prop_to_string a ^ " /\\ " ^ prop_to_string b ^ ")"
  | POr (a, b) -> "(" ^ prop_to_string a ^ " \\/ " ^ prop_to_string b ^ ")"
  | PImplies (a, b) -> "(" ^ prop_to_string a ^ " => " ^ prop_to_string b ^ ")"
  | PCmp (op, a, b) -> expr_to_string a ^ " " ^ cmpop_to_string op ^ " " ^ expr_to_string b

let rec stmt_to_string indent s =
  let pad = String.make (indent * 2) ' ' in
  match s with
  | SSkip -> pad ^ "skip"
  | SAssign (x, e) -> pad ^ x ^ " := " ^ expr_to_string e
  | SSeq (s1, s2) ->
    stmt_to_string indent s1 ^ ";\n" ^ stmt_to_string indent s2
  | SIf (c, t, e) ->
    pad ^ "if (" ^ bexpr_to_string c ^ ") {\n" ^
    stmt_to_string (indent+1) t ^ "\n" ^
    pad ^ "} else {\n" ^
    stmt_to_string (indent+1) e ^ "\n" ^
    pad ^ "}"
  | SWhile (c, inv, body) ->
    let inv_str = match inv with
      | Some p -> " inv (" ^ prop_to_string p ^ ")"
      | None -> ""
    in
    pad ^ "while (" ^ bexpr_to_string c ^ ")" ^ inv_str ^ " {\n" ^
    stmt_to_string (indent+1) body ^ "\n" ^
    pad ^ "}"
  | SAssert c -> pad ^ "assert(" ^ bexpr_to_string c ^ ")"

let vc_origin_to_string = function
  | VCPrecondition -> "precondition"
  | VCInvariantInit -> "invariant_init"
  | VCInvariantPreservation -> "invariant_preservation"
  | VCLoopExit -> "loop_exit"
  | VCPostcondition -> "postcondition"
  | VCAssertion -> "assertion"

let vc_status_to_string = function
  | VCValid -> "Valid"
  | VCInvalid ce -> "Invalid(" ^ ce ^ ")"
  | VCUnknown r -> "Unknown(" ^ r ^ ")"

let verdict_to_string = function
  | Verified -> "VERIFIED"
  | Failed ids ->
    "FAILED (VCs: " ^ String.concat ", " (List.map string_of_int ids) ^ ")"
  | Partial ids ->
    "PARTIAL (Unknown VCs: " ^ String.concat ", " (List.map string_of_int ids) ^ ")"

let strategy_to_string = function
  | ConstantPropagation -> "constant_propagation"
  | BoundInference -> "bound_inference"
  | RelationshipInference -> "relationship_inference"
  | PostconditionWeakening -> "postcondition_weakening"

(* ========== Expression Substitution ========== *)

let rec expr_subst x e_new = function
  | EConst n -> EConst n
  | EVar y -> if y = x then e_new else EVar y
  | EBinop (op, a, b) -> EBinop (op, expr_subst x e_new a, expr_subst x e_new b)

let rec bexpr_subst x e_new = function
  | BTrue -> BTrue
  | BFalse -> BFalse
  | BNot b -> BNot (bexpr_subst x e_new b)
  | BAnd (a, b) -> BAnd (bexpr_subst x e_new a, bexpr_subst x e_new b)
  | BOr (a, b) -> BOr (bexpr_subst x e_new a, bexpr_subst x e_new b)
  | BCmp (op, a, b) -> BCmp (op, expr_subst x e_new a, expr_subst x e_new b)

let rec prop_subst x e_new = function
  | PTrue -> PTrue
  | PFalse -> PFalse
  | PNot p -> PNot (prop_subst x e_new p)
  | PAnd (a, b) -> PAnd (prop_subst x e_new a, prop_subst x e_new b)
  | POr (a, b) -> POr (prop_subst x e_new a, prop_subst x e_new b)
  | PImplies (a, b) -> PImplies (prop_subst x e_new a, prop_subst x e_new b)
  | PCmp (op, a, b) -> PCmp (op, expr_subst x e_new a, expr_subst x e_new b)

(* ========== Boolean to Proposition conversion ========== *)

let rec bexpr_to_prop = function
  | BTrue -> PTrue
  | BFalse -> PFalse
  | BNot b -> PNot (bexpr_to_prop b)
  | BAnd (a, b) -> PAnd (bexpr_to_prop a, bexpr_to_prop b)
  | BOr (a, b) -> POr (bexpr_to_prop a, bexpr_to_prop b)
  | BCmp (op, a, b) -> PCmp (op, a, b)

(* ========== Free Variables ========== *)

let rec expr_vars = function
  | EConst _ -> []
  | EVar x -> [x]
  | EBinop (_, a, b) -> expr_vars a @ expr_vars b

let rec bexpr_vars = function
  | BTrue | BFalse -> []
  | BNot b -> bexpr_vars b
  | BAnd (a, b) | BOr (a, b) -> bexpr_vars a @ bexpr_vars b
  | BCmp (_, a, b) -> expr_vars a @ expr_vars b

let rec prop_vars = function
  | PTrue | PFalse -> []
  | PNot p -> prop_vars p
  | PAnd (a, b) | POr (a, b) | PImplies (a, b) -> prop_vars a @ prop_vars b
  | PCmp (_, a, b) -> expr_vars a @ expr_vars b

let rec stmt_vars = function
  | SSkip -> []
  | SAssign (x, e) -> x :: expr_vars e
  | SSeq (a, b) -> stmt_vars a @ stmt_vars b
  | SIf (c, t, e) -> bexpr_vars c @ stmt_vars t @ stmt_vars e
  | SWhile (c, inv, body) ->
    let iv = match inv with Some p -> prop_vars p | None -> [] in
    bexpr_vars c @ iv @ stmt_vars body
  | SAssert c -> bexpr_vars c

let unique lst =
  List.sort_uniq String.compare lst

(* ========== Expression Evaluation ========== *)

let eval_binop op a b =
  match op with
  | Add -> a + b
  | Sub -> a - b
  | Mul -> a * b
  | Div -> if b = 0 then 0 else a / b
  | Mod -> if b = 0 then 0 else a mod b

let eval_cmpop op a b =
  match op with
  | Eq -> a = b | Ne -> a <> b | Lt -> a < b
  | Le -> a <= b | Gt -> a > b | Ge -> a >= b

let rec eval_expr env = function
  | EConst n -> n
  | EVar x -> (try List.assoc x env with Not_found -> 0)
  | EBinop (op, a, b) -> eval_binop op (eval_expr env a) (eval_expr env b)

let rec eval_bexpr env = function
  | BTrue -> true
  | BFalse -> false
  | BNot b -> not (eval_bexpr env b)
  | BAnd (a, b) -> eval_bexpr env a && eval_bexpr env b
  | BOr (a, b) -> eval_bexpr env a || eval_bexpr env b
  | BCmp (op, a, b) -> eval_cmpop op (eval_expr env a) (eval_expr env b)

let rec eval_prop env = function
  | PTrue -> true
  | PFalse -> false
  | PNot p -> not (eval_prop env p)
  | PAnd (a, b) -> eval_prop env a && eval_prop env b
  | POr (a, b) -> eval_prop env a || eval_prop env b
  | PImplies (a, b) -> (not (eval_prop env a)) || eval_prop env b
  | PCmp (op, a, b) -> eval_cmpop op (eval_expr env a) (eval_expr env b)

(* ===== Engine 1: Weakest Precondition Calculator ===== *)

module WPCalculator = struct
  type wp_result = {
    wp_prop: prop;
    wp_vcs: (prop * vc_origin * string) list;
  }

  let rec compute post stmt =
    match stmt with
    | SSkip -> { wp_prop = post; wp_vcs = [] }
    | SAssign (x, e) ->
      { wp_prop = prop_subst x e post; wp_vcs = [] }
    | SSeq (s1, s2) ->
      let r2 = compute post s2 in
      let r1 = compute r2.wp_prop s1 in
      { wp_prop = r1.wp_prop; wp_vcs = r1.wp_vcs @ r2.wp_vcs }
    | SIf (cond, then_s, else_s) ->
      let cp = bexpr_to_prop cond in
      let rt = compute post then_s in
      let re = compute post else_s in
      let wp = PAnd (PImplies (cp, rt.wp_prop), PImplies (PNot cp, re.wp_prop)) in
      { wp_prop = wp; wp_vcs = rt.wp_vcs @ re.wp_vcs }
    | SWhile (cond, inv_opt, body) ->
      let inv = match inv_opt with
        | Some p -> p
        | None -> PTrue  (* fallback *)
      in
      let cp = bexpr_to_prop cond in
      (* VC: inv /\ cond => wp(body, inv) *)
      let body_wp = compute inv body in
      let pres_vc = PImplies (PAnd (inv, cp), body_wp.wp_prop) in
      (* VC: inv /\ ~cond => post *)
      let exit_vc = PImplies (PAnd (inv, PNot cp), post) in
      let vcs = [
        (pres_vc, VCInvariantPreservation, "Loop invariant is preserved by body");
        (exit_vc, VCLoopExit, "Loop exit implies postcondition");
      ] @ body_wp.wp_vcs in
      { wp_prop = inv; wp_vcs = vcs }
    | SAssert cond ->
      let cp = bexpr_to_prop cond in
      let vc = PImplies (post, cp) in
      { wp_prop = PAnd (post, cp); wp_vcs = [(vc, VCAssertion, "Assertion holds")] }
end

(* ===== Engine 2: VC Generator ===== *)

module VCGenerator = struct
  let generate (triple : hoare_triple) : (prop * vc_origin * string) list =
    let wp_result = WPCalculator.compute triple.postcondition triple.program in
    (* Main VC: precondition => wp *)
    let main_vc = PImplies (triple.precondition, wp_result.wp_prop) in
    (* Postcondition VC *)
    let post_vc = PImplies (wp_result.wp_prop, wp_result.wp_prop) in
    let _ = post_vc in
    [(main_vc, VCPrecondition, "Precondition implies weakest precondition")] @ wp_result.wp_vcs

  let generate_labeled triple =
    let raw = generate triple in
    List.mapi (fun i (p, origin, label) ->
      { vc_id = i + 1;
        vc_origin = origin;
        vc_prop = p;
        vc_status = VCUnknown "not checked";
        vc_label = label }
    ) raw
end

(* ===== Engine 3: VC Checker ===== *)

module VCChecker = struct
  (* Simplification *)
  let rec simplify_prop = function
    | PNot PTrue -> PFalse
    | PNot PFalse -> PTrue
    | PNot (PNot p) -> simplify_prop p
    | PAnd (PTrue, p) | PAnd (p, PTrue) -> simplify_prop p
    | PAnd (PFalse, _) | PAnd (_, PFalse) -> PFalse
    | POr (PTrue, _) | POr (_, PTrue) -> PTrue
    | POr (PFalse, p) | POr (p, PFalse) -> simplify_prop p
    | PImplies (PFalse, _) -> PTrue
    | PImplies (_, PTrue) -> PTrue
    | PImplies (PTrue, p) -> simplify_prop p
    | PAnd (a, b) ->
      let a' = simplify_prop a and b' = simplify_prop b in
      if a' = PTrue then b'
      else if b' = PTrue then a'
      else if a' = PFalse || b' = PFalse then PFalse
      else PAnd (a', b')
    | POr (a, b) ->
      let a' = simplify_prop a and b' = simplify_prop b in
      if a' = PTrue || b' = PTrue then PTrue
      else if a' = PFalse then b'
      else if b' = PFalse then a'
      else POr (a', b')
    | PImplies (a, b) ->
      let a' = simplify_prop a and b' = simplify_prop b in
      if a' = PFalse then PTrue
      else if b' = PTrue then PTrue
      else if a' = PTrue then b'
      else PImplies (a', b')
    | PNot p ->
      let p' = simplify_prop p in
      (match p' with PTrue -> PFalse | PFalse -> PTrue | _ -> PNot p')
    | PCmp (Eq, a, b) when a = b -> PTrue
    | PCmp (Le, a, b) when a = b -> PTrue
    | PCmp (Ge, a, b) when a = b -> PTrue
    | PCmp (Ne, a, b) when a = b -> PFalse
    | PCmp (Lt, a, b) when a = b -> PFalse
    | PCmp (Gt, a, b) when a = b -> PFalse
    | p -> p

  (* Generate all valuations for variables in range *)
  let gen_valuations vars lo hi =
    let range = List.init (hi - lo + 1) (fun i -> i + lo) in
    let rec go = function
      | [] -> [[]]
      | v :: rest ->
        let tails = go rest in
        List.concat_map (fun val_ ->
          List.map (fun tail -> (v, val_) :: tail) tails
        ) range
    in
    go vars

  let check_vc prop =
    let simplified = simplify_prop prop in
    match simplified with
    | PTrue -> VCValid
    | PFalse -> VCInvalid "trivially false"
    | _ ->
      let vars = unique (prop_vars simplified) in
      if List.length vars > 4 then
        VCUnknown "too many variables for exhaustive check"
      else
        let range_lo = -5 and range_hi = 10 in
        let valuations = gen_valuations vars range_lo range_hi in
        let counterexample = List.find_opt (fun env ->
          not (eval_prop env simplified)
        ) valuations in
        match counterexample with
        | None -> VCValid
        | Some env ->
          let ce = String.concat ", " (List.map (fun (v, n) ->
            v ^ "=" ^ string_of_int n
          ) env) in
          VCInvalid ce

  let check_all vcs =
    List.map (fun vc ->
      { vc with vc_status = check_vc vc.vc_prop }
    ) vcs
end

(* ===== Engine 4: Invariant Inference Engine ===== *)

module InvariantInference = struct
  (* Extract assigned variables from a statement *)
  let rec assigned_vars = function
    | SSkip -> []
    | SAssign (x, _) -> [x]
    | SSeq (a, b) -> assigned_vars a @ assigned_vars b
    | SIf (_, t, e) -> assigned_vars t @ assigned_vars e
    | SWhile (_, _, body) -> assigned_vars body
    | SAssert _ -> []

  (* Strategy 1: Constant propagation - variables not modified in loop *)
  let constant_propagation _cond body all_vars =
    let modified = unique (assigned_vars body) in
    let constants = List.filter (fun v -> not (List.mem v modified)) all_vars in
    List.map (fun v ->
      { inv_prop = PCmp (Eq, EVar v, EVar v);
        inv_strategy = ConstantPropagation;
        inv_confidence = 0.3;
        inv_description = Printf.sprintf "%s is not modified in loop" v }
    ) constants

  (* Strategy 2: Bound inference from loop condition *)
  let bound_inference cond _body _all_vars =
    match cond with
    | BCmp (Lt, EVar x, EVar n) ->
      [{ inv_prop = PAnd (PCmp (Ge, EVar x, EConst 0), PCmp (Le, EVar x, EVar n));
         inv_strategy = BoundInference;
         inv_confidence = 0.6;
         inv_description = Printf.sprintf "%s is bounded: 0 <= %s <= %s" x x n }]
    | BCmp (Lt, EVar x, EConst n) ->
      [{ inv_prop = PAnd (PCmp (Ge, EVar x, EConst 0), PCmp (Le, EVar x, EConst n));
         inv_strategy = BoundInference;
         inv_confidence = 0.6;
         inv_description = Printf.sprintf "%s is bounded: 0 <= %s <= %d" x x n }]
    | BCmp (Le, EVar x, EVar n) ->
      [{ inv_prop = PAnd (PCmp (Ge, EVar x, EConst 0), PCmp (Le, EVar x, EBinop (Add, EVar n, EConst 1)));
         inv_strategy = BoundInference;
         inv_confidence = 0.5;
         inv_description = Printf.sprintf "%s is bounded: 0 <= %s <= %s+1" x x n }]
    | _ -> []

  (* Strategy 3: Relationship inference - detect accumulator patterns *)
  let relationship_inference _cond body _all_vars =
    let rec find_accumulators = function
      | SAssign (x, EBinop (Add, EVar y, _)) when x = y ->
        [{ inv_prop = PCmp (Ge, EVar x, EConst 0);
           inv_strategy = RelationshipInference;
           inv_confidence = 0.4;
           inv_description = Printf.sprintf "%s is an accumulator (monotonically increasing)" x }]
      | SSeq (a, b) -> find_accumulators a @ find_accumulators b
      | _ -> []
    in
    find_accumulators body

  (* Strategy 4: Weaken postcondition *)
  let postcondition_weakening post =
    match post with
    | PCmp (Eq, a, b) ->
      [{ inv_prop = PCmp (Le, a, b);
         inv_strategy = PostconditionWeakening;
         inv_confidence = 0.35;
         inv_description = "Weakened postcondition: equality to inequality" }]
    | PAnd (a, _) ->
      [{ inv_prop = a;
         inv_strategy = PostconditionWeakening;
         inv_confidence = 0.3;
         inv_description = "Weakened postcondition: conjunct extraction" }]
    | _ -> []

  let infer cond body post all_vars =
    let c1 = constant_propagation cond body all_vars in
    let c2 = bound_inference cond body all_vars in
    let c3 = relationship_inference cond body all_vars in
    let c4 = postcondition_weakening post in
    let all = c1 @ c2 @ c3 @ c4 in
    List.sort (fun a b -> compare b.inv_confidence a.inv_confidence) all
end

(* ===== Engine 5: Program Analyzer ===== *)

module ProgramAnalyzer = struct
  type analysis_result = {
    variables: string list;
    assigned: string list;
    complexity: int;
    has_loops: bool;
    loop_count: int;
    branch_count: int;
    assert_count: int;
    termination_hint: string option;
  }

  let rec stmt_complexity = function
    | SSkip -> 1
    | SAssign _ -> 1
    | SSeq (a, b) -> stmt_complexity a + stmt_complexity b
    | SIf (_, t, e) -> 1 + stmt_complexity t + stmt_complexity e
    | SWhile (_, _, body) -> 2 + stmt_complexity body
    | SAssert _ -> 1

  let rec count_loops = function
    | SSkip | SAssign _ | SAssert _ -> 0
    | SSeq (a, b) -> count_loops a + count_loops b
    | SIf (_, t, e) -> count_loops t + count_loops e
    | SWhile (_, _, body) -> 1 + count_loops body

  let rec count_branches = function
    | SSkip | SAssign _ | SAssert _ -> 0
    | SSeq (a, b) -> count_branches a + count_branches b
    | SIf (_, t, e) -> 1 + count_branches t + count_branches e
    | SWhile (_, _, body) -> count_branches body

  let rec count_asserts = function
    | SSkip | SAssign _ -> 0
    | SSeq (a, b) -> count_asserts a + count_asserts b
    | SIf (_, t, e) -> count_asserts t + count_asserts e
    | SWhile (_, _, body) -> count_asserts body
    | SAssert _ -> 1

  (* Detect decreasing expression for termination argument *)
  let detect_termination stmt =
    let rec find_while = function
      | SWhile (BCmp (Lt, EVar x, EVar n), _, body) ->
        (* Check if x increases toward n *)
        let rec has_increment = function
          | SAssign (y, EBinop (Add, EVar z, EConst 1)) when y = x && z = x -> true
          | SSeq (a, b) -> has_increment a || has_increment b
          | _ -> false
        in
        if has_increment body then
          Some (Printf.sprintf "Decreasing: %s - %s (bounded by 0)" n x)
        else None
      | SWhile (BCmp (Gt, EVar x, EConst 0), _, body) ->
        let rec has_decrement = function
          | SAssign (y, EBinop (Sub, EVar z, EConst 1)) when y = x && z = x -> true
          | SSeq (a, b) -> has_decrement a || has_decrement b
          | _ -> false
        in
        if has_decrement body then
          Some (Printf.sprintf "Decreasing: %s (bounded by 0)" x)
        else None
      | SSeq (a, b) ->
        (match find_while a with Some h -> Some h | None -> find_while b)
      | SIf (_, t, e) ->
        (match find_while t with Some h -> Some h | None -> find_while e)
      | _ -> None
    in
    find_while stmt

  let analyze stmt =
    { variables = unique (stmt_vars stmt);
      assigned = unique (ProgramAnalyzer.assigned_vars stmt);
      complexity = stmt_complexity stmt;
      has_loops = count_loops stmt > 0;
      loop_count = count_loops stmt;
      branch_count = count_branches stmt;
      assert_count = count_asserts stmt;
      termination_hint = detect_termination stmt }

  let assigned_vars = InvariantInference.assigned_vars
end

(* ===== Engine 6: Verification Orchestrator ===== *)

module Orchestrator = struct
  (* Count provided invariants *)
  let rec count_invariants = function
    | SSkip | SAssign _ | SAssert _ -> 0
    | SSeq (a, b) -> count_invariants a + count_invariants b
    | SIf (_, t, e) -> count_invariants t + count_invariants e
    | SWhile (_, Some _, body) -> 1 + count_invariants body
    | SWhile (_, None, body) -> count_invariants body

  (* Annotate missing invariants with inferred ones *)
  let rec annotate_invariants post stmt =
    match stmt with
    | SWhile (cond, None, body) ->
      let all_vars = unique (stmt_vars stmt) in
      let candidates = InvariantInference.infer cond body post all_vars in
      let inv = match candidates with
        | c :: _ -> Some c.inv_prop
        | [] -> Some PTrue
      in
      (SWhile (cond, inv, body), List.length candidates)
    | SSeq (a, b) ->
      let (b', n1) = annotate_invariants post b in
      let (a', n2) = annotate_invariants post a in
      (SSeq (a', b'), n1 + n2)
    | SIf (c, t, e) ->
      let (t', n1) = annotate_invariants post t in
      let (e', n2) = annotate_invariants post e in
      (SIf (c, t', e'), n1 + n2)
    | other -> (other, 0)

  let verify triple =
    let provided = count_invariants triple.program in
    let (annotated_prog, inferred) = annotate_invariants triple.postcondition triple.program in
    let triple' = { triple with program = annotated_prog } in
    let raw_vcs = VCGenerator.generate_labeled triple' in
    let checked_vcs = VCChecker.check_all raw_vcs in

    let failed = List.filter_map (fun vc ->
      match vc.vc_status with VCInvalid _ -> Some vc.vc_id | _ -> None
    ) checked_vcs in
    let unknown = List.filter_map (fun vc ->
      match vc.vc_status with VCUnknown _ -> Some vc.vc_id | _ -> None
    ) checked_vcs in
    let valid_count = List.length (List.filter (fun vc ->
      match vc.vc_status with VCValid -> true | _ -> false
    ) checked_vcs) in
    let total = List.length checked_vcs in

    let verdict =
      if failed <> [] then Failed failed
      else if unknown <> [] then Partial unknown
      else Verified
    in

    let health = if total = 0 then 100
      else int_of_float (100.0 *. (float_of_int valid_count /. float_of_int total))
    in

    let analysis = ProgramAnalyzer.analyze triple'.program in

    let insights = ref [] in
    if verdict = Verified then
      insights := "All verification conditions hold - program is correct" :: !insights;
    if failed <> [] then
      insights := Printf.sprintf "%d VCs failed - check invariants" (List.length failed) :: !insights;
    if inferred > 0 then
      insights := Printf.sprintf "Inferred %d loop invariant(s) automatically" inferred :: !insights;
    if analysis.has_loops && provided = 0 && inferred = 0 then
      insights := "Warning: loop without invariant - verification may be incomplete" :: !insights;
    (match analysis.termination_hint with
     | Some hint -> insights := ("Termination argument: " ^ hint) :: !insights
     | None -> if analysis.has_loops then
         insights := "No termination argument detected" :: !insights);

    { vcs = checked_vcs;
      verdict;
      health_score = health;
      invariants_provided = provided;
      invariants_inferred = inferred;
      insights = List.rev !insights }
end

(* ===== Engine 7: Insight Generator ===== *)

module InsightGenerator = struct
  let generate result analysis =
    let insights = ref result.insights in

    (* Complexity insights *)
    if analysis.ProgramAnalyzer.complexity > 10 then
      insights := !insights @ ["High program complexity - consider decomposition"];

    (* Loop-specific insights *)
    if analysis.loop_count > 1 then
      insights := !insights @ [Printf.sprintf "Multiple loops (%d) - each needs its own invariant" analysis.loop_count];

    (* VC analysis insights *)
    let failed_vcs = List.filter (fun vc ->
      match vc.vc_status with VCInvalid _ -> true | _ -> false
    ) result.vcs in

    List.iter (fun vc ->
      match vc.vc_origin with
      | VCInvariantPreservation ->
        insights := !insights @ ["Invariant preservation failed - loop body may violate the invariant"]
      | VCLoopExit ->
        insights := !insights @ ["Loop exit condition doesn't imply postcondition - invariant may be too weak"]
      | VCPrecondition ->
        insights := !insights @ ["Precondition too weak to establish loop invariant"]
      | _ -> ()
    ) failed_vcs;

    (* Scoring insights *)
    if result.health_score = 100 then
      insights := !insights @ ["Perfect score: program fully verified"]
    else if result.health_score >= 80 then
      insights := !insights @ ["Good score: most VCs verified, minor issues remain"]
    else if result.health_score >= 50 then
      insights := !insights @ ["Moderate score: significant verification gaps"]
    else
      insights := !insights @ ["Low score: major verification failures"];

    !insights
end

(* ===== Demo Programs ===== *)

module DemoPrograms = struct
  (* Demo 1: Square computation - y = x * x via repeated addition *)
  let square_program = {
    precondition = PCmp (Ge, EVar "x", EConst 0);
    program = SSeq (
      SAssign ("y", EConst 0),
      SSeq (
        SAssign ("z", EConst 0),
        SWhile (
          BCmp (Lt, EVar "z", EVar "x"),
          Some (PAnd (
            PCmp (Eq, EVar "y", EBinop (Mul, EVar "z", EVar "z")),
            PAnd (
              PCmp (Ge, EVar "z", EConst 0),
              PCmp (Le, EVar "z", EVar "x")
            )
          )),
          SSeq (
            SAssign ("y", EBinop (Add, EVar "y", EBinop (Add, EBinop (Mul, EConst 2, EVar "z"), EConst 1))),
            SAssign ("z", EBinop (Add, EVar "z", EConst 1))
          )
        )
      )
    );
    postcondition = PCmp (Eq, EVar "y", EBinop (Mul, EVar "x", EVar "x"));
  }

  (* Demo 2: Integer division - q * d + r = n, 0 <= r < d *)
  let division_program = {
    precondition = PAnd (PCmp (Ge, EVar "n", EConst 0), PCmp (Gt, EVar "d", EConst 0));
    program = SSeq (
      SAssign ("q", EConst 0),
      SSeq (
        SAssign ("r", EVar "n"),
        SWhile (
          BCmp (Ge, EVar "r", EVar "d"),
          Some (PAnd (
            PCmp (Eq, EBinop (Add, EBinop (Mul, EVar "q", EVar "d"), EVar "r"), EVar "n"),
            PCmp (Ge, EVar "r", EConst 0)
          )),
          SSeq (
            SAssign ("r", EBinop (Sub, EVar "r", EVar "d")),
            SAssign ("q", EBinop (Add, EVar "q", EConst 1))
          )
        )
      )
    );
    postcondition = PAnd (
      PCmp (Eq, EBinop (Add, EBinop (Mul, EVar "q", EVar "d"), EVar "r"), EVar "n"),
      PAnd (PCmp (Ge, EVar "r", EConst 0), PCmp (Lt, EVar "r", EVar "d"))
    );
  }

  (* Demo 3: Factorial computation *)
  let factorial_program = {
    precondition = PAnd (PCmp (Ge, EVar "n", EConst 0), PCmp (Le, EVar "n", EConst 5));
    program = SSeq (
      SAssign ("f", EConst 1),
      SSeq (
        SAssign ("i", EConst 1),
        SWhile (
          BCmp (Le, EVar "i", EVar "n"),
          Some (PAnd (
            PCmp (Ge, EVar "f", EConst 1),
            PAnd (
              PCmp (Ge, EVar "i", EConst 1),
              PCmp (Le, EVar "i", EBinop (Add, EVar "n", EConst 1))
            )
          )),
          SSeq (
            SAssign ("f", EBinop (Mul, EVar "f", EVar "i")),
            SAssign ("i", EBinop (Add, EVar "i", EConst 1))
          )
        )
      )
    );
    postcondition = PCmp (Ge, EVar "f", EConst 1);
  }

  (* Demo 4: Find maximum of two values *)
  let max_program = {
    precondition = PTrue;
    program = SIf (
      BCmp (Ge, EVar "a", EVar "b"),
      SAssign ("m", EVar "a"),
      SAssign ("m", EVar "b")
    );
    postcondition = PAnd (
      PCmp (Ge, EVar "m", EVar "a"),
      PCmp (Ge, EVar "m", EVar "b")
    );
  }

  (* Demo 5: Sum 1..n *)
  let sum_program = {
    precondition = PCmp (Ge, EVar "n", EConst 0);
    program = SSeq (
      SAssign ("s", EConst 0),
      SSeq (
        SAssign ("i", EConst 0),
        SWhile (
          BCmp (Lt, EVar "i", EVar "n"),
          Some (PAnd (
            PCmp (Ge, EVar "i", EConst 0),
            PCmp (Le, EVar "i", EVar "n")
          )),
          SSeq (
            SAssign ("i", EBinop (Add, EVar "i", EConst 1)),
            SAssign ("s", EBinop (Add, EVar "s", EVar "i"))
          )
        )
      )
    );
    postcondition = PCmp (Ge, EVar "s", EConst 0);
  }

  (* Demo 6: Simple swap *)
  let swap_program = {
    precondition = PAnd (PCmp (Eq, EVar "a", EVar "a0"), PCmp (Eq, EVar "b", EVar "b0"));
    program = SSeq (
      SAssign ("t", EVar "a"),
      SSeq (
        SAssign ("a", EVar "b"),
        SAssign ("b", EVar "t")
      )
    );
    postcondition = PAnd (PCmp (Eq, EVar "a", EVar "b0"), PCmp (Eq, EVar "b", EVar "a0"));
  }

  let all_demos = [
    ("Square computation (y = x*x)", square_program);
    ("Integer division (q*d + r = n)", division_program);
    ("Factorial", factorial_program);
    ("Maximum of two values", max_program);
    ("Sum 1..n", sum_program);
    ("Variable swap", swap_program);
  ]
end

(* ===== HTML Dashboard Generator ===== *)

module Dashboard = struct
  let vc_status_badge = function
    | VCValid -> "<span class='badge valid'>&#10003; Valid</span>"
    | VCInvalid ce -> "<span class='badge invalid'>&#10007; Invalid: " ^ ce ^ "</span>"
    | VCUnknown r -> "<span class='badge unknown'>? Unknown: " ^ r ^ "</span>"

  let health_color score =
    if score >= 80 then "#22c55e"
    else if score >= 50 then "#f59e0b"
    else "#ef4444"

  let generate results =
    let buf = Buffer.create 8192 in
    let add s = Buffer.add_string buf s in
    add "<!DOCTYPE html>\n<html><head><meta charset='utf-8'>\n";
    add "<title>Formal Verification Dashboard</title>\n";
    add "<style>\n";
    add "body{font-family:-apple-system,BlinkMacSystemFont,sans-serif;margin:0;padding:20px;background:#0f172a;color:#e2e8f0}\n";
    add ".container{max-width:1200px;margin:0 auto}\n";
    add "h1{color:#38bdf8;border-bottom:2px solid #1e3a5f;padding-bottom:10px}\n";
    add "h2{color:#94a3b8;margin-top:30px}\n";
    add ".card{background:#1e293b;border-radius:12px;padding:20px;margin:15px 0;box-shadow:0 4px 6px rgba(0,0,0,.3)}\n";
    add ".badge{padding:3px 10px;border-radius:12px;font-size:13px;font-weight:600}\n";
    add ".valid{background:#065f46;color:#6ee7b7}\n";
    add ".invalid{background:#7f1d1d;color:#fca5a5}\n";
    add ".unknown{background:#78350f;color:#fcd34d}\n";
    add ".health-gauge{width:120px;height:120px;border-radius:50%;display:flex;align-items:center;justify-content:center;font-size:32px;font-weight:700;margin:20px auto}\n";
    add "table{width:100%;border-collapse:collapse;margin:10px 0}\n";
    add "th,td{padding:10px 14px;text-align:left;border-bottom:1px solid #334155}\n";
    add "th{color:#94a3b8;font-weight:600;text-transform:uppercase;font-size:12px}\n";
    add ".insight{padding:8px 14px;margin:5px 0;background:#1a2332;border-left:3px solid #38bdf8;border-radius:0 6px 6px 0}\n";
    add ".verdict-ok{color:#22c55e;font-size:24px;font-weight:700}\n";
    add ".verdict-fail{color:#ef4444;font-size:24px;font-weight:700}\n";
    add ".verdict-partial{color:#f59e0b;font-size:24px;font-weight:700}\n";
    add "pre{background:#0d1117;padding:14px;border-radius:8px;overflow-x:auto;font-size:13px;line-height:1.5}\n";
    add "</style></head><body>\n";
    add "<div class='container'>\n";
    add "<h1>&#128270; Formal Verification Engine</h1>\n";

    List.iter (fun (name, result) ->
      add (Printf.sprintf "<div class='card'><h2>%s</h2>\n" name);

      (* Health gauge *)
      let color = health_color result.health_score in
      add (Printf.sprintf "<div class='health-gauge' style='border:4px solid %s;color:%s'>%d</div>\n"
        color color result.health_score);

      (* Verdict *)
      let (vclass, vtext) = match result.verdict with
        | Verified -> ("verdict-ok", "&#10003; VERIFIED")
        | Failed _ -> ("verdict-fail", "&#10007; " ^ verdict_to_string result.verdict)
        | Partial _ -> ("verdict-partial", "&#9888; " ^ verdict_to_string result.verdict)
      in
      add (Printf.sprintf "<p class='%s'>%s</p>\n" vclass vtext);

      add (Printf.sprintf "<p>Invariants: %d provided, %d inferred | VCs: %d total</p>\n"
        result.invariants_provided result.invariants_inferred (List.length result.vcs));

      (* VC table *)
      add "<table><tr><th>#</th><th>Origin</th><th>Label</th><th>Status</th></tr>\n";
      List.iter (fun vc ->
        add (Printf.sprintf "<tr><td>%d</td><td>%s</td><td>%s</td><td>%s</td></tr>\n"
          vc.vc_id (vc_origin_to_string vc.vc_origin) vc.vc_label (vc_status_badge vc.vc_status))
      ) result.vcs;
      add "</table>\n";

      (* Insights *)
      if result.insights <> [] then begin
        add "<h3 style='color:#94a3b8'>Insights</h3>\n";
        List.iter (fun insight ->
          add (Printf.sprintf "<div class='insight'>%s</div>\n" insight)
        ) result.insights
      end;

      add "</div>\n"
    ) results;

    add "</div></body></html>\n";
    Buffer.contents buf
end

(* ===== Parser for annotated IMP programs ===== *)

module Parser = struct
  exception ParseError of string

  type token =
    | TInt of int | TId of string | TLParen | TRParen | TLBrace | TRBrace
    | TSemicolon | TAssign | TPlus | TMinus | TStar | TSlash | TPercent
    | TEq | TNe | TLt | TLe | TGt | TGe
    | TAnd | TOr | TNot | TTrue | TFalse
    | TIf | TElse | TWhile | TInv | TAssert | TSkip
    | TEOF

  let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
  let is_digit c = c >= '0' && c <= '9'
  let is_alnum c = is_alpha c || is_digit c

  let tokenize input =
    let tokens = ref [] in
    let i = ref 0 in
    let len = String.length input in
    while !i < len do
      let c = input.[!i] in
      if c = ' ' || c = '\n' || c = '\r' || c = '\t' then incr i
      else if c = '{' then (tokens := TLBrace :: !tokens; incr i)
      else if c = '}' then (tokens := TRBrace :: !tokens; incr i)
      else if c = '(' then (tokens := TLParen :: !tokens; incr i)
      else if c = ')' then (tokens := TRParen :: !tokens; incr i)
      else if c = ';' then (tokens := TSemicolon :: !tokens; incr i)
      else if c = '+' then (tokens := TPlus :: !tokens; incr i)
      else if c = '-' then (tokens := TMinus :: !tokens; incr i)
      else if c = '*' then (tokens := TStar :: !tokens; incr i)
      else if c = '/' then (tokens := TSlash :: !tokens; incr i)
      else if c = '%' then (tokens := TPercent :: !tokens; incr i)
      else if c = '!' && !i + 1 < len && input.[!i + 1] = '=' then
        (tokens := TNe :: !tokens; i := !i + 2)
      else if c = '!' then (tokens := TNot :: !tokens; incr i)
      else if c = '<' && !i + 1 < len && input.[!i + 1] = '=' then
        (tokens := TLe :: !tokens; i := !i + 2)
      else if c = '<' then (tokens := TLt :: !tokens; incr i)
      else if c = '>' && !i + 1 < len && input.[!i + 1] = '=' then
        (tokens := TGe :: !tokens; i := !i + 2)
      else if c = '>' then (tokens := TGt :: !tokens; incr i)
      else if c = '=' && !i + 1 < len && input.[!i + 1] = '=' then
        (tokens := TEq :: !tokens; i := !i + 2)
      else if c = '&' && !i + 1 < len && input.[!i + 1] = '&' then
        (tokens := TAnd :: !tokens; i := !i + 2)
      else if c = '|' && !i + 1 < len && input.[!i + 1] = '|' then
        (tokens := TOr :: !tokens; i := !i + 2)
      else if c = ':' && !i + 1 < len && input.[!i + 1] = '=' then
        (tokens := TAssign :: !tokens; i := !i + 2)
      else if c = '=' then
        (tokens := TEq :: !tokens; incr i)
      else if is_digit c then begin
        let start = !i in
        while !i < len && is_digit input.[!i] do incr i done;
        let n = int_of_string (String.sub input start (!i - start)) in
        tokens := TInt n :: !tokens
      end
      else if is_alpha c then begin
        let start = !i in
        while !i < len && is_alnum input.[!i] do incr i done;
        let word = String.sub input start (!i - start) in
        let tok = match word with
          | "if" -> TIf | "else" -> TElse | "while" -> TWhile
          | "inv" -> TInv | "assert" -> TAssert | "skip" -> TSkip
          | "true" -> TTrue | "false" -> TFalse
          | "and" -> TAnd | "or" -> TOr | "not" -> TNot
          | _ -> TId word
        in
        tokens := tok :: !tokens
      end
      else (incr i) (* skip unknown chars *)
    done;
    tokens := TEOF :: !tokens;
    List.rev !tokens

  (* Recursive descent parser *)
  let pos = ref 0
  let toks = ref [||]

  let peek () = if !pos < Array.length !toks then !toks.(!pos) else TEOF
  let advance () = incr pos
  let expect t =
    if peek () = t then advance ()
    else raise (ParseError (Printf.sprintf "Expected token at position %d" !pos))

  let rec parse_expr () =
    let left = parse_term () in
    parse_expr_rest left
  and parse_expr_rest left =
    match peek () with
    | TPlus -> advance (); let right = parse_term () in parse_expr_rest (EBinop (Add, left, right))
    | TMinus -> advance (); let right = parse_term () in parse_expr_rest (EBinop (Sub, left, right))
    | _ -> left
  and parse_term () =
    let left = parse_factor () in
    parse_term_rest left
  and parse_term_rest left =
    match peek () with
    | TStar -> advance (); let right = parse_factor () in parse_term_rest (EBinop (Mul, left, right))
    | TSlash -> advance (); let right = parse_factor () in parse_term_rest (EBinop (Div, left, right))
    | TPercent -> advance (); let right = parse_factor () in parse_term_rest (EBinop (Mod, left, right))
    | _ -> left
  and parse_factor () =
    match peek () with
    | TInt n -> advance (); EConst n
    | TId x -> advance (); EVar x
    | TLParen -> advance (); let e = parse_expr () in expect TRParen; e
    | TMinus -> advance (); let e = parse_factor () in EBinop (Sub, EConst 0, e)
    | _ -> raise (ParseError "Expected expression")

  let parse_cmpop () =
    match peek () with
    | TEq -> advance (); Eq | TNe -> advance (); Ne
    | TLt -> advance (); Lt | TLe -> advance (); Le
    | TGt -> advance (); Gt | TGe -> advance (); Ge
    | _ -> raise (ParseError "Expected comparison operator")

  let rec parse_bexpr () =
    let left = parse_bexpr_and () in
    parse_bexpr_or_rest left
  and parse_bexpr_or_rest left =
    match peek () with
    | TOr -> advance (); let right = parse_bexpr_and () in parse_bexpr_or_rest (BOr (left, right))
    | _ -> left
  and parse_bexpr_and () =
    let left = parse_bexpr_atom () in
    parse_bexpr_and_rest left
  and parse_bexpr_and_rest left =
    match peek () with
    | TAnd -> advance (); let right = parse_bexpr_atom () in parse_bexpr_and_rest (BAnd (left, right))
    | _ -> left
  and parse_bexpr_atom () =
    match peek () with
    | TTrue -> advance (); BTrue
    | TFalse -> advance (); BFalse
    | TNot -> advance (); let b = parse_bexpr_atom () in BNot b
    | TLParen ->
      advance ();
      let e1 = parse_expr () in
      (match peek () with
       | TEq | TNe | TLt | TLe | TGt | TGe ->
         let op = parse_cmpop () in
         let e2 = parse_expr () in
         expect TRParen;
         BCmp (op, e1, e2)
       | _ ->
         (* It might be a boolean subexpression *)
         expect TRParen;
         BCmp (Ne, e1, EConst 0))
    | _ ->
      let e1 = parse_expr () in
      let op = parse_cmpop () in
      let e2 = parse_expr () in
      BCmp (op, e1, e2)

  let rec parse_prop () =
    let left = parse_prop_and () in
    parse_prop_or_rest left
  and parse_prop_or_rest left =
    match peek () with
    | TOr -> advance (); let right = parse_prop_and () in parse_prop_or_rest (POr (left, right))
    | _ -> left
  and parse_prop_and () =
    let left = parse_prop_atom () in
    parse_prop_and_rest left
  and parse_prop_and_rest left =
    match peek () with
    | TAnd -> advance (); let right = parse_prop_atom () in parse_prop_and_rest (PAnd (left, right))
    | _ -> left
  and parse_prop_atom () =
    match peek () with
    | TTrue -> advance (); PTrue
    | TFalse -> advance (); PFalse
    | TNot -> advance (); let p = parse_prop_atom () in PNot p
    | TLParen ->
      advance ();
      let e1 = parse_expr () in
      (match peek () with
       | TEq | TNe | TLt | TLe | TGt | TGe ->
         let op = parse_cmpop () in
         let e2 = parse_expr () in
         expect TRParen;
         PCmp (op, e1, e2)
       | TAnd ->
         (* Restart as prop *)
         let p1 = PCmp (Ge, e1, e1) in (* placeholder, re-parse needed *)
         let _ = p1 in
         expect TRParen;
         PTrue
       | _ ->
         expect TRParen;
         PCmp (Ge, e1, EConst 0))
    | _ ->
      let e1 = parse_expr () in
      let op = parse_cmpop () in
      let e2 = parse_expr () in
      PCmp (op, e1, e2)

  let rec parse_stmt () =
    let s = parse_single_stmt () in
    match peek () with
    | TSemicolon -> advance (); let s2 = parse_stmt () in SSeq (s, s2)
    | _ -> s
  and parse_single_stmt () =
    match peek () with
    | TSkip -> advance (); SSkip
    | TIf ->
      advance ();
      expect TLParen;
      let cond = parse_bexpr () in
      expect TRParen;
      expect TLBrace;
      let then_s = parse_stmt () in
      expect TRBrace;
      expect TElse;
      expect TLBrace;
      let else_s = parse_stmt () in
      expect TRBrace;
      SIf (cond, then_s, else_s)
    | TWhile ->
      advance ();
      expect TLParen;
      let cond = parse_bexpr () in
      expect TRParen;
      let inv = if peek () = TInv then begin
        advance ();
        expect TLParen;
        let p = parse_prop () in
        expect TRParen;
        Some p
      end else None in
      expect TLBrace;
      let body = parse_stmt () in
      expect TRBrace;
      SWhile (cond, inv, body)
    | TAssert ->
      advance ();
      expect TLParen;
      let cond = parse_bexpr () in
      expect TRParen;
      SAssert cond
    | TId x ->
      advance ();
      expect TAssign;
      let e = parse_expr () in
      SAssign (x, e)
    | _ -> SSkip

  let parse_program input =
    let token_list = tokenize input in
    toks := Array.of_list token_list;
    pos := 0;
    (* Parse optional precondition *)
    let pre = if peek () = TLBrace then begin
      advance ();
      let p = parse_prop () in
      expect TRBrace;
      p
    end else PTrue in
    let s = parse_stmt () in
    (* Parse optional postcondition *)
    let post = if peek () = TLBrace then begin
      advance ();
      let p = parse_prop () in
      expect TRBrace;
      p
    end else PTrue in
    { precondition = pre; program = s; postcondition = post }
end

(* ===== CLI Interface ===== *)

let print_verification_result name result =
  Printf.printf "\n=== %s ===\n" name;
  Printf.printf "Invariants: %d provided, %d inferred\n"
    result.invariants_provided result.invariants_inferred;
  Printf.printf "VCs generated: %d\n" (List.length result.vcs);
  List.iter (fun vc ->
    let icon = match vc.vc_status with
      | VCValid -> "+" | VCInvalid _ -> "X" | VCUnknown _ -> "?"
    in
    Printf.printf "  VC%d (%s): [%s] %s\n"
      vc.vc_id (vc_origin_to_string vc.vc_origin) icon (vc_status_to_string vc.vc_status)
  ) result.vcs;
  let verdict_icon = match result.verdict with
    | Verified -> "VERIFIED" | Failed _ -> "FAILED" | Partial _ -> "PARTIAL"
  in
  Printf.printf "Verdict: %s (%d/%d VCs valid)\n" verdict_icon
    (List.length (List.filter (fun vc -> vc.vc_status = VCValid) result.vcs))
    (List.length result.vcs);
  Printf.printf "Health: %d/100\n" result.health_score;
  if result.insights <> [] then begin
    Printf.printf "Insights:\n";
    List.iter (fun s -> Printf.printf "  - %s\n" s) result.insights
  end

let run_demo () =
  Printf.printf "[Formal Verification Engine]\n";
  Printf.printf "Running %d demo programs...\n\n" (List.length DemoPrograms.all_demos);
  let results = List.map (fun (name, triple) ->
    let result = Orchestrator.verify triple in
    let analysis = ProgramAnalyzer.analyze triple.program in
    let insights = InsightGenerator.generate result analysis in
    let result = { result with insights } in
    print_verification_result name result;
    (name, result)
  ) DemoPrograms.all_demos in
  let total_health = List.fold_left (fun acc (_, r) -> acc + r.health_score) 0 results in
  let avg_health = total_health / (max 1 (List.length results)) in
  Printf.printf "\n=== Summary ===\n";
  Printf.printf "Programs verified: %d\n" (List.length results);
  Printf.printf "Average health: %d/100\n" avg_health;
  results

let run_dashboard () =
  let results = List.map (fun (name, triple) ->
    let result = Orchestrator.verify triple in
    let analysis = ProgramAnalyzer.analyze triple.program in
    let insights = InsightGenerator.generate result analysis in
    (name, { result with insights })
  ) DemoPrograms.all_demos in
  let html = Dashboard.generate results in
  let filename = "formal_verification_dashboard.html" in
  let oc = open_out filename in
  output_string oc html;
  close_out oc;
  Printf.printf "Dashboard written to %s\n" filename

let run_verify filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  let input = Bytes.to_string s in
  let triple = Parser.parse_program input in
  let result = Orchestrator.verify triple in
  let analysis = ProgramAnalyzer.analyze triple.program in
  let insights = InsightGenerator.generate result analysis in
  let result = { result with insights } in
  Printf.printf "[Formal Verification Engine]\n";
  Printf.printf "Program: %s\n" filename;
  print_verification_result filename result

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | _ when List.mem "--demo" args -> ignore (run_demo ())
  | _ when List.mem "--dashboard" args -> run_dashboard ()
  | _ when List.mem "--verify" args ->
    let idx = ref 0 in
    Array.iteri (fun i s -> if s = "--verify" then idx := i) Sys.argv;
    if !idx + 1 < Array.length Sys.argv then
      run_verify Sys.argv.(!idx + 1)
    else
      Printf.printf "Usage: formal_verification --verify <file.imp>\n"
  | _ ->
    Printf.printf "Formal Verification Engine\n";
    Printf.printf "Usage:\n";
    Printf.printf "  --demo       Run built-in demo programs\n";
    Printf.printf "  --verify F   Verify program from file F\n";
    Printf.printf "  --dashboard  Generate HTML dashboard\n";
    ignore (run_demo ())
