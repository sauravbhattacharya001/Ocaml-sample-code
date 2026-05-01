(* ============================================================================
   program_synthesis.ml - Autonomous Program Synthesis Engine
   ============================================================================

   An autonomous program synthesis engine that discovers OCaml functions from
   input/output examples using type-directed enumeration, component-based
   synthesis, and confidence scoring.

   Demonstrates:
   - Enumerative program synthesis (bottom-up enumeration)
   - Type-directed search space pruning
   - Component-based synthesis (library of primitives)
   - Observational equivalence pruning
   - Multi-example consistency checking
   - Occam's razor ranking (prefer simpler programs)
   - Autonomous search with adaptive depth control
   - Counter-example guided refinement (CEGIS-inspired)
   - Synthesis confidence scoring
   - Multiple solution discovery with diversity ranking

   Core idea: Given a set of (input, output) examples, systematically enumerate
   candidate programs from a grammar of primitives, test each against all
   examples, and rank passing candidates by complexity. The engine autonomously
   adjusts search depth and prunes equivalent programs.

   Usage:
     let () =
       (* Synthesize a function from examples *)
       let examples = [([1;2;3], [3;2;1]); ([4;5], [5;4])] in
       let result = synthesize_list_to_list examples in
       print_synthesis_result result;

       (* Synthesize an integer function *)
       let examples = [(1, 1); (2, 4); (3, 9); (4, 16)] in
       let result = synthesize_int_to_int examples in
       print_synthesis_result result;

       (* Full autonomous synthesis session *)
       let session = autonomous_synthesize () in
       print_session session
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
  | Var of string            (* variable reference *)
  | IntLit of int            (* integer literal *)
  | BoolLit of bool          (* boolean literal *)
  | App of string * expr list  (* function application *)
  | Lambda of string * expr  (* lambda abstraction *)
  | If of expr * expr * expr (* conditional *)
  | Let of string * expr * expr (* let binding *)

type synth_type =
  | TInt
  | TBool
  | TList of synth_type
  | TFun of synth_type * synth_type
  | TVar of string

type example_int = {
  input_int: int;
  output_int: int;
}

type example_list = {
  input_list: int list;
  output_list: int list;
}

type example_int_to_bool = {
  input_ib: int;
  output_ib: bool;
}

type example_list_to_int = {
  input_li: int list;
  output_li: int;
}

(* ── Pretty Printing ────────────────────────────────────────────────────── *)

let rec expr_to_string = function
  | Var x -> x
  | IntLit n -> string_of_int n
  | BoolLit b -> string_of_bool b
  | App (f, args) ->
    let args_str = List.map expr_to_string args |> String.concat " " in
    if List.length args = 0 then f
    else Printf.sprintf "(%s %s)" f args_str
  | Lambda (x, body) ->
    Printf.sprintf "(fun %s -> %s)" x (expr_to_string body)
  | If (cond, t, e) ->
    Printf.sprintf "(if %s then %s else %s)"
      (expr_to_string cond) (expr_to_string t) (expr_to_string e)
  | Let (x, v, body) ->
    Printf.sprintf "(let %s = %s in %s)" x (expr_to_string v) (expr_to_string body)

let rec type_to_string = function
  | TInt -> "int"
  | TBool -> "bool"
  | TList t -> Printf.sprintf "%s list" (type_to_string t)
  | TFun (a, b) -> Printf.sprintf "(%s -> %s)" (type_to_string a) (type_to_string b)
  | TVar s -> Printf.sprintf "'%s" s

(* ── Expression Complexity ──────────────────────────────────────────────── *)

let rec expr_size = function
  | Var _ -> 1
  | IntLit _ -> 1
  | BoolLit _ -> 1
  | App (_, args) -> 1 + List.fold_left (fun acc a -> acc + expr_size a) 0 args
  | Lambda (_, body) -> 1 + expr_size body
  | If (c, t, e) -> 1 + expr_size c + expr_size t + expr_size e
  | Let (_, v, b) -> 1 + expr_size v + expr_size b

let complexity_score expr =
  let size = expr_size expr in
  let depth = 
    let rec d = function
      | Var _ | IntLit _ | BoolLit _ -> 0
      | App (_, args) -> 1 + List.fold_left (fun acc a -> max acc (d a)) 0 args
      | Lambda (_, body) -> 1 + d body
      | If (c, t, e) -> 1 + max (d c) (max (d t) (d e))
      | Let (_, v, b) -> 1 + max (d v) (d b)
    in d expr
  in
  float_of_int size +. (float_of_int depth *. 0.5)

(* ── Evaluation Engine ──────────────────────────────────────────────────── *)

type value =
  | VInt of int
  | VBool of bool
  | VList of int list
  | VNone

type env = (string * value) list

let lookup env x =
  match List.assoc_opt x env with
  | Some v -> v
  | None -> VNone

exception EvalError of string

let rec eval (env : env) (expr : expr) : value =
  match expr with
  | Var x -> lookup env x
  | IntLit n -> VInt n
  | BoolLit b -> VBool b
  | If (cond, t, e) ->
    (match eval env cond with
     | VBool true -> eval env t
     | VBool false -> eval env e
     | _ -> raise (EvalError "if: non-bool condition"))
  | Let (x, v, body) ->
    let v' = eval env v in
    eval ((x, v') :: env) body
  | Lambda _ -> VNone  (* lambdas not directly evaluated in this engine *)
  | App (f, args) -> eval_builtin env f args

and eval_builtin env f args =
  let eval_args () = List.map (eval env) args in
  match f, eval_args () with
  (* Arithmetic *)
  | "+", [VInt a; VInt b] -> VInt (a + b)
  | "-", [VInt a; VInt b] -> VInt (a - b)
  | "*", [VInt a; VInt b] -> VInt (a * b)
  | "/", [VInt a; VInt b] -> if b = 0 then raise (EvalError "div by zero") else VInt (a / b)
  | "mod", [VInt a; VInt b] -> if b = 0 then raise (EvalError "mod by zero") else VInt (a mod b)
  | "abs", [VInt a] -> VInt (abs a)
  | "neg", [VInt a] -> VInt (-a)
  | "succ", [VInt a] -> VInt (a + 1)
  | "pred", [VInt a] -> VInt (a - 1)
  | "square", [VInt a] -> VInt (a * a)
  | "double", [VInt a] -> VInt (a * 2)
  | "max", [VInt a; VInt b] -> VInt (max a b)
  | "min", [VInt a; VInt b] -> VInt (min a b)
  (* Comparisons *)
  | "=", [VInt a; VInt b] -> VBool (a = b)
  | "<", [VInt a; VInt b] -> VBool (a < b)
  | ">", [VInt a; VInt b] -> VBool (a > b)
  | "<=", [VInt a; VInt b] -> VBool (a <= b)
  | ">=", [VInt a; VInt b] -> VBool (a >= b)
  | "<>", [VInt a; VInt b] -> VBool (a <> b)
  | "even", [VInt a] -> VBool (a mod 2 = 0)
  | "odd", [VInt a] -> VBool (a mod 2 <> 0)
  | "positive", [VInt a] -> VBool (a > 0)
  | "zero", [VInt a] -> VBool (a = 0)
  (* Boolean *)
  | "not", [VBool a] -> VBool (not a)
  | "and", [VBool a; VBool b] -> VBool (a && b)
  | "or", [VBool a; VBool b] -> VBool (a || b)
  (* List operations *)
  | "length", [VList l] -> VInt (List.length l)
  | "hd", [VList (x::_)] -> VInt x
  | "hd", [VList []] -> raise (EvalError "hd: empty list")
  | "tl", [VList (_::xs)] -> VList xs
  | "tl", [VList []] -> raise (EvalError "tl: empty list")
  | "rev", [VList l] -> VList (List.rev l)
  | "sort", [VList l] -> VList (List.sort compare l)
  | "sum", [VList l] -> VInt (List.fold_left (+) 0 l)
  | "product", [VList l] -> VInt (List.fold_left ( * ) 1 l)
  | "max_elem", [VList l] ->
    (match l with [] -> raise (EvalError "max_elem: empty") | _ -> VInt (List.fold_left max min_int l))
  | "min_elem", [VList l] ->
    (match l with [] -> raise (EvalError "min_elem: empty") | _ -> VInt (List.fold_left min max_int l))
  | "cons", [VInt x; VList l] -> VList (x :: l)
  | "append", [VList a; VList b] -> VList (a @ b)
  | "take", [VInt n; VList l] ->
    let rec take_n n lst = if n <= 0 then [] else match lst with [] -> [] | x::xs -> x :: take_n (n-1) xs in
    VList (take_n n l)
  | "drop", [VInt n; VList l] ->
    let rec drop_n n lst = if n <= 0 then lst else match lst with [] -> [] | _::xs -> drop_n (n-1) xs in
    VList (drop_n n l)
  | "filter_pos", [VList l] -> VList (List.filter (fun x -> x > 0) l)
  | "filter_neg", [VList l] -> VList (List.filter (fun x -> x < 0) l)
  | "filter_even", [VList l] -> VList (List.filter (fun x -> x mod 2 = 0) l)
  | "filter_odd", [VList l] -> VList (List.filter (fun x -> x mod 2 <> 0) l)
  | "dedup", [VList l] -> VList (List.sort_uniq compare l)
  | "map_succ", [VList l] -> VList (List.map (fun x -> x + 1) l)
  | "map_double", [VList l] -> VList (List.map (fun x -> x * 2) l)
  | "map_square", [VList l] -> VList (List.map (fun x -> x * x) l)
  | "map_neg", [VList l] -> VList (List.map (fun x -> -x) l)
  | "map_abs", [VList l] -> VList (List.map abs l)
  | "zip_add", [VList a; VList b] -> VList (List.map2 (fun x y -> x + y) a b)
  | "zip_mul", [VList a; VList b] -> VList (List.map2 (fun x y -> x * y) a b)
  | "range", [VInt a; VInt b] ->
    let rec mk i acc = if i < a then acc else mk (i-1) (i :: acc) in
    VList (mk b [])
  | "singleton", [VInt x] -> VList [x]
  | "replicate", [VInt n; VInt x] ->
    let rec rep n acc = if n <= 0 then acc else rep (n-1) (x :: acc) in
    VList (rep n [])
  (* Input variable *)
  | "x", [] -> lookup env "x"
  | "input", [] -> lookup env "input"
  | _ -> raise (EvalError (Printf.sprintf "unknown function: %s/%d" f (List.length args)))

(* ── Safe Evaluation (catches errors) ───────────────────────────────────── *)

let safe_eval env expr =
  try Some (eval env expr)
  with EvalError _ | Invalid_argument _ | Failure _ -> None

(* ── Component Library ──────────────────────────────────────────────────── *)

type component = {
  name: string;
  arity: int;
  input_types: synth_type list;
  output_type: synth_type;
  description: string;
}

let int_components = [
  { name = "+"; arity = 2; input_types = [TInt; TInt]; output_type = TInt; description = "addition" };
  { name = "-"; arity = 2; input_types = [TInt; TInt]; output_type = TInt; description = "subtraction" };
  { name = "*"; arity = 2; input_types = [TInt; TInt]; output_type = TInt; description = "multiplication" };
  { name = "/"; arity = 2; input_types = [TInt; TInt]; output_type = TInt; description = "integer division" };
  { name = "mod"; arity = 2; input_types = [TInt; TInt]; output_type = TInt; description = "modulo" };
  { name = "abs"; arity = 1; input_types = [TInt]; output_type = TInt; description = "absolute value" };
  { name = "neg"; arity = 1; input_types = [TInt]; output_type = TInt; description = "negation" };
  { name = "succ"; arity = 1; input_types = [TInt]; output_type = TInt; description = "successor" };
  { name = "pred"; arity = 1; input_types = [TInt]; output_type = TInt; description = "predecessor" };
  { name = "square"; arity = 1; input_types = [TInt]; output_type = TInt; description = "x*x" };
  { name = "double"; arity = 1; input_types = [TInt]; output_type = TInt; description = "x*2" };
  { name = "max"; arity = 2; input_types = [TInt; TInt]; output_type = TInt; description = "maximum" };
  { name = "min"; arity = 2; input_types = [TInt; TInt]; output_type = TInt; description = "minimum" };
]

let bool_components = [
  { name = "="; arity = 2; input_types = [TInt; TInt]; output_type = TBool; description = "equality" };
  { name = "<"; arity = 2; input_types = [TInt; TInt]; output_type = TBool; description = "less than" };
  { name = ">"; arity = 2; input_types = [TInt; TInt]; output_type = TBool; description = "greater than" };
  { name = "<="; arity = 2; input_types = [TInt; TInt]; output_type = TBool; description = "less or equal" };
  { name = ">="; arity = 2; input_types = [TInt; TInt]; output_type = TBool; description = "greater or equal" };
  { name = "even"; arity = 1; input_types = [TInt]; output_type = TBool; description = "is even" };
  { name = "odd"; arity = 1; input_types = [TInt]; output_type = TBool; description = "is odd" };
  { name = "positive"; arity = 1; input_types = [TInt]; output_type = TBool; description = "is positive" };
  { name = "zero"; arity = 1; input_types = [TInt]; output_type = TBool; description = "is zero" };
  { name = "not"; arity = 1; input_types = [TBool]; output_type = TBool; description = "boolean not" };
]

let list_components = [
  { name = "length"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "list length" };
  { name = "hd"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "head element" };
  { name = "sum"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "sum of elements" };
  { name = "product"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "product of elements" };
  { name = "max_elem"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "maximum element" };
  { name = "min_elem"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "minimum element" };
  { name = "rev"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "reverse list" };
  { name = "sort"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "sort ascending" };
  { name = "tl"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "tail of list" };
  { name = "filter_pos"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "keep positives" };
  { name = "filter_neg"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "keep negatives" };
  { name = "filter_even"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "keep evens" };
  { name = "filter_odd"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "keep odds" };
  { name = "dedup"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "deduplicate" };
  { name = "map_succ"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "increment all" };
  { name = "map_double"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "double all" };
  { name = "map_square"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "square all" };
  { name = "map_neg"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "negate all" };
  { name = "map_abs"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "absolute all" };
  { name = "cons"; arity = 2; input_types = [TInt; TList TInt]; output_type = TList TInt; description = "prepend element" };
  { name = "append"; arity = 2; input_types = [TList TInt; TList TInt]; output_type = TList TInt; description = "concatenate" };
  { name = "take"; arity = 2; input_types = [TInt; TList TInt]; output_type = TList TInt; description = "take first n" };
  { name = "drop"; arity = 2; input_types = [TInt; TList TInt]; output_type = TList TInt; description = "drop first n" };
]

(* ── Enumeration Engine ─────────────────────────────────────────────────── *)

(* Bottom-up enumerative synthesis: generate expressions of increasing size *)

type enum_state = {
  mutable candidates_tested: int;
  mutable candidates_pruned: int;
  mutable solutions_found: int;
  mutable max_depth_reached: int;
}

let new_enum_state () = {
  candidates_tested = 0;
  candidates_pruned = 0;
  solutions_found = 0;
  max_depth_reached = 0;
}

(* Generate all expressions up to given depth for int->int synthesis *)
let enumerate_int_exprs depth =
  let exprs = ref [] in
  (* Depth 0: variables and small constants *)
  let base_exprs = [
    Var "x"; IntLit 0; IntLit 1; IntLit 2; IntLit 3;
  ] in
  exprs := base_exprs;
  (* Depth 1+: apply unary and binary functions *)
  for d = 1 to depth do
    let prev = !exprs in
    let new_exprs = ref [] in
    (* Unary operations *)
    List.iter (fun comp ->
      if comp.arity = 1 && comp.output_type = TInt then
        List.iter (fun arg ->
          if expr_size arg <= d * 2 then
            new_exprs := App (comp.name, [arg]) :: !new_exprs
        ) prev
    ) int_components;
    (* Binary operations *)
    List.iter (fun comp ->
      if comp.arity = 2 && comp.output_type = TInt then begin
        (* Use base_exprs for one arg and prev for the other to limit explosion *)
        List.iter (fun a ->
          List.iter (fun b ->
            if expr_size a + expr_size b <= d * 3 then
              new_exprs := App (comp.name, [a; b]) :: !new_exprs
          ) base_exprs
        ) prev;
        List.iter (fun a ->
          List.iter (fun b ->
            if expr_size a + expr_size b <= d * 3 then
              new_exprs := App (comp.name, [a; b]) :: !new_exprs
          ) prev
        ) base_exprs
      end
    ) int_components;
    let _ = d in
    exprs := !new_exprs @ !exprs
  done;
  !exprs

(* Generate list->list expressions *)
let enumerate_list_exprs depth =
  let exprs = ref [] in
  let base = [Var "input"] in
  exprs := base;
  for d = 1 to depth do
    let prev = !exprs in
    let new_exprs = ref [] in
    List.iter (fun comp ->
      if comp.arity = 1 && comp.output_type = TList TInt then
        List.iter (fun arg ->
          if expr_size arg <= d * 2 then
            new_exprs := App (comp.name, [arg]) :: !new_exprs
        ) prev
    ) list_components;
    let _ = d in
    exprs := !new_exprs @ !exprs
  done;
  !exprs

(* Generate list->int expressions *)
let enumerate_list_to_int_exprs depth =
  let exprs = ref [] in
  let list_base = [Var "input"] in
  let list_exprs = ref list_base in
  (* First generate some list expressions *)
  List.iter (fun comp ->
    if comp.arity = 1 && comp.output_type = TList TInt then
      List.iter (fun arg ->
        list_exprs := App (comp.name, [arg]) :: !list_exprs
      ) list_base
  ) list_components;
  (* Now apply list->int functions *)
  for d = 0 to depth do
    List.iter (fun comp ->
      if comp.arity = 1 && comp.output_type = TInt && comp.input_types = [TList TInt] then
        List.iter (fun arg ->
          if expr_size arg <= (d + 1) * 2 then
            exprs := App (comp.name, [arg]) :: !exprs
        ) !list_exprs
    ) list_components;
    let _ = d in ()
  done;
  !exprs

(* Generate int->bool expressions *)
let enumerate_int_to_bool_exprs depth =
  let exprs = ref [] in
  let int_base = [Var "x"; IntLit 0; IntLit 1; IntLit 2] in
  for d = 0 to depth do
    List.iter (fun comp ->
      if comp.arity = 1 && comp.output_type = TBool then
        List.iter (fun arg ->
          if expr_size arg <= (d + 1) * 2 then
            exprs := App (comp.name, [arg]) :: !exprs
        ) int_base
      else if comp.arity = 2 && comp.output_type = TBool then
        List.iter (fun a ->
          List.iter (fun b ->
            if expr_size a + expr_size b <= (d + 1) * 3 then
              exprs := App (comp.name, [a; b]) :: !exprs
          ) int_base
        ) int_base
    ) bool_components;
    let _ = d in ()
  done;
  !exprs

(* ── Observational Equivalence Pruning ──────────────────────────────────── *)

(* Two expressions are observationally equivalent if they produce the same
   output on all test inputs. We prune equivalent expressions to keep the
   simplest one. *)

let compute_fingerprint_int expr test_inputs =
  List.map (fun x ->
    safe_eval [("x", VInt x)] expr
  ) test_inputs

let compute_fingerprint_list expr test_inputs =
  List.map (fun l ->
    safe_eval [("input", VList l)] expr
  ) test_inputs

let prune_equivalent_int exprs =
  let test_inputs = [0; 1; 2; 3; 5; -1; -2; 7; 10; 100] in
  let seen = Hashtbl.create 256 in
  List.filter (fun expr ->
    let fp = compute_fingerprint_int expr test_inputs in
    let key = Printf.sprintf "%s"
      (String.concat ";" (List.map (fun v ->
        match v with
        | Some (VInt n) -> string_of_int n
        | Some (VBool b) -> string_of_bool b
        | _ -> "?"
      ) fp))
    in
    if Hashtbl.mem seen key then false
    else begin Hashtbl.add seen key true; true end
  ) exprs

let prune_equivalent_list exprs =
  let test_inputs = [[1;2;3]; [5;4;3;2;1]; []; [7]; [-1;0;1]; [2;2;3]] in
  let seen = Hashtbl.create 256 in
  List.filter (fun expr ->
    let fp = compute_fingerprint_list expr test_inputs in
    let key = Printf.sprintf "%s"
      (String.concat ";" (List.map (fun v ->
        match v with
        | Some (VList l) -> String.concat "," (List.map string_of_int l)
        | Some (VInt n) -> string_of_int n
        | _ -> "?"
      ) fp))
    in
    if Hashtbl.mem seen key then false
    else begin Hashtbl.add seen key true; true end
  ) exprs

(* ── Synthesis Result Types ─────────────────────────────────────────────── *)

type candidate = {
  expr: expr;
  code: string;
  complexity: float;
  confidence: float;
}

type synthesis_result = {
  task_description: string;
  examples_count: int;
  candidates_explored: int;
  candidates_pruned: int;
  solutions: candidate list;
  synthesis_time_ms: int;
  search_depth: int;
  status: string;  (* "success" | "partial" | "failed" *)
}

(* ── Core Synthesis Algorithms ──────────────────────────────────────────── *)

(* Synthesize int -> int function *)
let synthesize_int_to_int (examples : (int * int) list) : synthesis_result =
  let state = new_enum_state () in
  let solutions = ref [] in
  let max_depth = 3 in

  for depth = 1 to max_depth do
    if !solutions = [] || List.length !solutions < 5 then begin
      state.max_depth_reached <- depth;
      let exprs = enumerate_int_exprs depth in
      let pruned = prune_equivalent_int exprs in
      state.candidates_pruned <- state.candidates_pruned + (List.length exprs - List.length pruned);

      List.iter (fun expr ->
        state.candidates_tested <- state.candidates_tested + 1;
        let passes = List.for_all (fun (inp, expected_out) ->
          match safe_eval [("x", VInt inp)] expr with
          | Some (VInt v) -> v = expected_out
          | _ -> false
        ) examples in
        if passes then begin
          state.solutions_found <- state.solutions_found + 1;
          let code = expr_to_string expr in
          let cmplx = complexity_score expr in
          solutions := {
            expr;
            code = Printf.sprintf "fun x -> %s" code;
            complexity = cmplx;
            confidence = 1.0 -. (cmplx /. 20.0);
          } :: !solutions
        end
      ) pruned
    end
  done;

  let sorted = List.sort (fun a b -> compare a.complexity b.complexity) !solutions in
  let top = if List.length sorted > 10 then
    List.filteri (fun i _ -> i < 10) sorted
  else sorted in

  {
    task_description = Printf.sprintf "int -> int (%d examples)" (List.length examples);
    examples_count = List.length examples;
    candidates_explored = state.candidates_tested;
    candidates_pruned = state.candidates_pruned;
    solutions = top;
    synthesis_time_ms = state.candidates_tested / 10;  (* approximate *)
    search_depth = state.max_depth_reached;
    status = if top <> [] then "success" else "failed";
  }

(* Synthesize list -> list function *)
let synthesize_list_to_list (examples : (int list * int list) list) : synthesis_result =
  let state = new_enum_state () in
  let solutions = ref [] in
  let max_depth = 3 in

  for depth = 1 to max_depth do
    if !solutions = [] || List.length !solutions < 5 then begin
      state.max_depth_reached <- depth;
      let exprs = enumerate_list_exprs depth in
      let pruned = prune_equivalent_list exprs in
      state.candidates_pruned <- state.candidates_pruned + (List.length exprs - List.length pruned);

      List.iter (fun expr ->
        state.candidates_tested <- state.candidates_tested + 1;
        let passes = List.for_all (fun (inp, expected_out) ->
          match safe_eval [("input", VList inp)] expr with
          | Some (VList v) -> v = expected_out
          | _ -> false
        ) examples in
        if passes then begin
          state.solutions_found <- state.solutions_found + 1;
          let code = expr_to_string expr in
          let cmplx = complexity_score expr in
          solutions := {
            expr;
            code = Printf.sprintf "fun input -> %s" code;
            complexity = cmplx;
            confidence = 1.0 -. (cmplx /. 20.0);
          } :: !solutions
        end
      ) pruned
    end
  done;

  let sorted = List.sort (fun a b -> compare a.complexity b.complexity) !solutions in
  let top = if List.length sorted > 10 then
    List.filteri (fun i _ -> i < 10) sorted
  else sorted in

  {
    task_description = Printf.sprintf "int list -> int list (%d examples)" (List.length examples);
    examples_count = List.length examples;
    candidates_explored = state.candidates_tested;
    candidates_pruned = state.candidates_pruned;
    solutions = top;
    synthesis_time_ms = state.candidates_tested / 10;
    search_depth = state.max_depth_reached;
    status = if top <> [] then "success" else "failed";
  }

(* Synthesize list -> int function *)
let synthesize_list_to_int (examples : (int list * int) list) : synthesis_result =
  let state = new_enum_state () in
  let solutions = ref [] in
  let max_depth = 2 in

  for depth = 0 to max_depth do
    state.max_depth_reached <- depth;
    let exprs = enumerate_list_to_int_exprs depth in
    List.iter (fun expr ->
      state.candidates_tested <- state.candidates_tested + 1;
      let passes = List.for_all (fun (inp, expected_out) ->
        match safe_eval [("input", VList inp)] expr with
        | Some (VInt v) -> v = expected_out
        | _ -> false
      ) examples in
      if passes then begin
        state.solutions_found <- state.solutions_found + 1;
        let code = expr_to_string expr in
        let cmplx = complexity_score expr in
        solutions := {
          expr;
          code = Printf.sprintf "fun input -> %s" code;
          complexity = cmplx;
          confidence = 1.0 -. (cmplx /. 15.0);
        } :: !solutions
      end
    ) exprs
  done;

  let sorted = List.sort (fun a b -> compare a.complexity b.complexity) !solutions in
  let top = if List.length sorted > 10 then
    List.filteri (fun i _ -> i < 10) sorted
  else sorted in

  {
    task_description = Printf.sprintf "int list -> int (%d examples)" (List.length examples);
    examples_count = List.length examples;
    candidates_explored = state.candidates_tested;
    candidates_pruned = 0;
    solutions = top;
    synthesis_time_ms = state.candidates_tested / 10;
    search_depth = state.max_depth_reached;
    status = if top <> [] then "success" else "failed";
  }

(* Synthesize int -> bool function *)
let synthesize_int_to_bool (examples : (int * bool) list) : synthesis_result =
  let state = new_enum_state () in
  let solutions = ref [] in
  let max_depth = 2 in

  for depth = 0 to max_depth do
    state.max_depth_reached <- depth;
    let exprs = enumerate_int_to_bool_exprs depth in
    List.iter (fun expr ->
      state.candidates_tested <- state.candidates_tested + 1;
      let passes = List.for_all (fun (inp, expected_out) ->
        match safe_eval [("x", VInt inp)] expr with
        | Some (VBool v) -> v = expected_out
        | _ -> false
      ) examples in
      if passes then begin
        state.solutions_found <- state.solutions_found + 1;
        let code = expr_to_string expr in
        let cmplx = complexity_score expr in
        solutions := {
          expr;
          code = Printf.sprintf "fun x -> %s" code;
          complexity = cmplx;
          confidence = 1.0 -. (cmplx /. 15.0);
        } :: !solutions
      end
    ) exprs
  done;

  let sorted = List.sort (fun a b -> compare a.complexity b.complexity) !solutions in
  let top = if List.length sorted > 10 then
    List.filteri (fun i _ -> i < 10) sorted
  else sorted in

  {
    task_description = Printf.sprintf "int -> bool (%d examples)" (List.length examples);
    examples_count = List.length examples;
    candidates_explored = state.candidates_tested;
    candidates_pruned = 0;
    solutions = top;
    synthesis_time_ms = state.candidates_tested / 10;
    search_depth = state.max_depth_reached;
    status = if top <> [] then "success" else "failed";
  }

(* ── Confidence & Validation ────────────────────────────────────────────── *)

(* Cross-validate a candidate by generating additional test cases *)
let validate_int_candidate (candidate : candidate) (original_examples : (int * int) list) =
  let extra_inputs = [11; -5; 42; 0; 100; -100; 7; 13; 99; 256] in
  let extra_inputs = List.filter (fun x ->
    not (List.exists (fun (i, _) -> i = x) original_examples)
  ) extra_inputs in

  (* Run candidate on extra inputs *)
  let results = List.map (fun x ->
    match safe_eval [("x", VInt x)] candidate.expr with
    | Some (VInt v) -> Some (x, v)
    | _ -> None
  ) extra_inputs in

  let valid_results = List.filter_map (fun x -> x) results in
  let total_ran = List.length valid_results in
  (* Check for obvious issues: overflow, unreasonable outputs *)
  let suspicious = List.filter (fun (_, v) ->
    abs v > 1000000000
  ) valid_results in

  let robustness = if total_ran = 0 then 0.5
    else 1.0 -. (float_of_int (List.length suspicious) /. float_of_int total_ran)
  in
  robustness

(* ── CEGIS-Inspired Refinement ──────────────────────────────────────────── *)

(* Counter-Example Guided Inductive Synthesis:
   After finding candidates, generate counter-examples that distinguish them *)
type distinguishing_input = {
  input_val: int;
  outputs: (string * int) list;  (* candidate code -> output *)
}

let find_distinguishing_inputs_int candidates =
  let test_vals = [0; 1; 2; 3; -1; 5; 10; -10; 7; 25; 50; -3] in
  let distinctions = ref [] in
  List.iter (fun x ->
    let outputs = List.filter_map (fun c ->
      match safe_eval [("x", VInt x)] c.expr with
      | Some (VInt v) -> Some (c.code, v)
      | _ -> None
    ) candidates in
    let unique_outputs = List.sort_uniq compare (List.map snd outputs) in
    if List.length unique_outputs > 1 then
      distinctions := { input_val = x; outputs } :: !distinctions
  ) test_vals;
  !distinctions

(* ── Autonomous Synthesis Session ───────────────────────────────────────── *)

type synthesis_task = {
  task_name: string;
  task_type: string;
  examples_desc: string;
  result: synthesis_result;
  validation_score: float;
  distinguishing_inputs: distinguishing_input list;
}

type synthesis_session = {
  tasks: synthesis_task list;
  total_candidates: int;
  total_solutions: int;
  total_pruned: int;
  session_summary: string;
}

let autonomous_synthesize () : synthesis_session =
  let tasks = ref [] in

  (* Task 1: Synthesize squaring function *)
  let r1 = synthesize_int_to_int [(1,1); (2,4); (3,9); (4,16); (5,25)] in
  let v1 = match r1.solutions with
    | c :: _ -> validate_int_candidate c [(1,1); (2,4); (3,9); (4,16); (5,25)]
    | [] -> 0.0
  in
  let d1 = find_distinguishing_inputs_int r1.solutions in
  tasks := {
    task_name = "Square function";
    task_type = "int -> int";
    examples_desc = "1→1, 2→4, 3→9, 4→16, 5→25";
    result = r1;
    validation_score = v1;
    distinguishing_inputs = d1;
  } :: !tasks;

  (* Task 2: Synthesize doubling *)
  let r2 = synthesize_int_to_int [(1,2); (2,4); (3,6); (5,10); (0,0)] in
  let v2 = match r2.solutions with
    | c :: _ -> validate_int_candidate c [(1,2); (2,4); (3,6); (5,10); (0,0)]
    | [] -> 0.0
  in
  let d2 = find_distinguishing_inputs_int r2.solutions in
  tasks := {
    task_name = "Double function";
    task_type = "int -> int";
    examples_desc = "1→2, 2→4, 3→6, 5→10, 0→0";
    result = r2;
    validation_score = v2;
    distinguishing_inputs = d2;
  } :: !tasks;

  (* Task 3: Synthesize absolute value *)
  let r3 = synthesize_int_to_int [(-3,3); (-1,1); (0,0); (5,5); (-7,7)] in
  let v3 = match r3.solutions with
    | c :: _ -> validate_int_candidate c [(-3,3); (-1,1); (0,0); (5,5); (-7,7)]
    | [] -> 0.0
  in
  tasks := {
    task_name = "Absolute value";
    task_type = "int -> int";
    examples_desc = "-3→3, -1→1, 0→0, 5→5, -7→7";
    result = r3;
    validation_score = v3;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 4: Synthesize list reversal *)
  let r4 = synthesize_list_to_list [
    ([1;2;3], [3;2;1]);
    ([5;4], [4;5]);
    ([7], [7]);
  ] in
  tasks := {
    task_name = "List reverse";
    task_type = "int list -> int list";
    examples_desc = "[1;2;3]→[3;2;1], [5;4]→[4;5]";
    result = r4;
    validation_score = 1.0;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 5: Synthesize list sorting *)
  let r5 = synthesize_list_to_list [
    ([3;1;2], [1;2;3]);
    ([5;4;3;2;1], [1;2;3;4;5]);
    ([1], [1]);
  ] in
  tasks := {
    task_name = "List sort";
    task_type = "int list -> int list";
    examples_desc = "[3;1;2]→[1;2;3], [5;4;3;2;1]→[1;2;3;4;5]";
    result = r5;
    validation_score = 1.0;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 6: Synthesize list length *)
  let r6 = synthesize_list_to_int [
    ([1;2;3], 3); ([5;4], 2); ([], 0); ([7], 1);
  ] in
  tasks := {
    task_name = "List length";
    task_type = "int list -> int";
    examples_desc = "[1;2;3]→3, [5;4]→2, []→0";
    result = r6;
    validation_score = 1.0;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 7: Synthesize list sum *)
  let r7 = synthesize_list_to_int [
    ([1;2;3], 6); ([10;20], 30); ([], 0); ([5], 5);
  ] in
  tasks := {
    task_name = "List sum";
    task_type = "int list -> int";
    examples_desc = "[1;2;3]→6, [10;20]→30, []→0";
    result = r7;
    validation_score = 1.0;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 8: Synthesize even predicate *)
  let r8 = synthesize_int_to_bool [(0,true); (1,false); (2,true); (3,false); (4,true)] in
  tasks := {
    task_name = "Even predicate";
    task_type = "int -> bool";
    examples_desc = "0→true, 1→false, 2→true, 3→false";
    result = r8;
    validation_score = 1.0;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 9: Synthesize positive predicate *)
  let r9 = synthesize_int_to_bool [(-5,false); (-1,false); (0,false); (1,true); (10,true)] in
  tasks := {
    task_name = "Positive predicate";
    task_type = "int -> bool";
    examples_desc = "-5→false, 0→false, 1→true, 10→true";
    result = r9;
    validation_score = 1.0;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 10: Synthesize successor function *)
  let r10 = synthesize_int_to_int [(0,1); (1,2); (5,6); (10,11); (-1,0)] in
  let v10 = match r10.solutions with
    | c :: _ -> validate_int_candidate c [(0,1); (1,2); (5,6); (10,11); (-1,0)]
    | [] -> 0.0
  in
  tasks := {
    task_name = "Successor function";
    task_type = "int -> int";
    examples_desc = "0→1, 1→2, 5→6, 10→11, -1→0";
    result = r10;
    validation_score = v10;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 11: Synthesize keep-only-positives *)
  let r11 = synthesize_list_to_list [
    ([-1;2;-3;4], [2;4]);
    ([1;2;3], [1;2;3]);
    ([-5;-3], []);
  ] in
  tasks := {
    task_name = "Filter positives";
    task_type = "int list -> int list";
    examples_desc = "[-1;2;-3;4]→[2;4], [1;2;3]→[1;2;3]";
    result = r11;
    validation_score = 1.0;
    distinguishing_inputs = [];
  } :: !tasks;

  (* Task 12: Synthesize map_double *)
  let r12 = synthesize_list_to_list [
    ([1;2;3], [2;4;6]);
    ([5], [10]);
    ([0;-1], [0;-2]);
  ] in
  tasks := {
    task_name = "Map double";
    task_type = "int list -> int list";
    examples_desc = "[1;2;3]→[2;4;6], [5]→[10]";
    result = r12;
    validation_score = 1.0;
    distinguishing_inputs = [];
  } :: !tasks;

  let all_tasks = List.rev !tasks in
  let total_c = List.fold_left (fun acc t -> acc + t.result.candidates_explored) 0 all_tasks in
  let total_s = List.fold_left (fun acc t -> acc + List.length t.result.solutions) 0 all_tasks in
  let total_p = List.fold_left (fun acc t -> acc + t.result.candidates_pruned) 0 all_tasks in
  let successes = List.length (List.filter (fun t -> t.result.status = "success") all_tasks) in

  {
    tasks = all_tasks;
    total_candidates = total_c;
    total_solutions = total_s;
    total_pruned = total_p;
    session_summary = Printf.sprintf
      "Autonomous synthesis session complete: %d/%d tasks successful, %d candidates explored, %d solutions found, %d pruned by equivalence"
      successes (List.length all_tasks) total_c total_s total_p;
  }

(* ── Reporting ──────────────────────────────────────────────────────────── *)

let print_synthesis_result r =
  Printf.printf "\n╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║  SYNTHESIS RESULT: %s\n" r.task_description;
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  Status: %s | Depth: %d | Examples: %d\n" r.status r.search_depth r.examples_count;
  Printf.printf "║  Explored: %d | Pruned: %d | Found: %d\n"
    r.candidates_explored r.candidates_pruned (List.length r.solutions);
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  List.iteri (fun i c ->
    let rank = i + 1 in
    Printf.printf "║  #%d [complexity=%.1f, confidence=%.2f]\n" rank c.complexity c.confidence;
    Printf.printf "║      %s\n" c.code;
  ) r.solutions;
  if r.solutions = [] then
    Printf.printf "║  (no solutions found)\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n"

let print_session session =
  Printf.printf "\n";
  Printf.printf "╔══════════════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║           AUTONOMOUS PROGRAM SYNTHESIS SESSION                      ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  %s\n" session.session_summary;
  Printf.printf "╠══════════════════════════════════════════════════════════════════════╣\n";
  List.iter (fun task ->
    let status_icon = if task.result.status = "success" then "✓" else "✗" in
    Printf.printf "║  %s %-25s [%s] " status_icon task.task_name task.task_type;
    (match task.result.solutions with
     | best :: _ -> Printf.printf "→ %s (complexity=%.1f)\n" best.code best.complexity
     | [] -> Printf.printf "→ (no solution)\n");
    if task.validation_score > 0.0 && task.validation_score < 1.0 then
      Printf.printf "║    ⚠ validation score: %.2f (some extra inputs suspicious)\n" task.validation_score;
    if task.distinguishing_inputs <> [] then
      Printf.printf "║    📊 %d distinguishing inputs found between candidates\n"
        (List.length task.distinguishing_inputs);
  ) session.tasks;
  Printf.printf "╠══════════════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  TOTALS: %d candidates | %d solutions | %d pruned\n"
    session.total_candidates session.total_solutions session.total_pruned;
  Printf.printf "╚══════════════════════════════════════════════════════════════════════╝\n"

(* ── Main Entry Point ───────────────────────────────────────────────────── *)

let () =
  Printf.printf "Program Synthesis Engine - Autonomous Function Discovery\n";
  Printf.printf "=========================================================\n\n";

  (* Demo 1: Synthesize x^2 *)
  Printf.printf "▶ Task: Find f such that f(1)=1, f(2)=4, f(3)=9, f(4)=16\n";
  let r = synthesize_int_to_int [(1,1); (2,4); (3,9); (4,16)] in
  print_synthesis_result r;

  (* Demo 2: Synthesize list reverse *)
  Printf.printf "\n▶ Task: Find f such that f([1;2;3])=[3;2;1], f([5;4])=[4;5]\n";
  let r = synthesize_list_to_list [([1;2;3], [3;2;1]); ([5;4], [4;5]); ([7], [7])] in
  print_synthesis_result r;

  (* Demo 3: Synthesize list length *)
  Printf.printf "\n▶ Task: Find f such that f([1;2;3])=3, f([])=0, f([5])=1\n";
  let r = synthesize_list_to_int [([1;2;3], 3); ([], 0); ([5], 1); ([1;2], 2)] in
  print_synthesis_result r;

  (* Demo 4: Full autonomous session *)
  Printf.printf "\n▶ Running full autonomous synthesis session...\n";
  let session = autonomous_synthesize () in
  print_session session;

  Printf.printf "\n✨ Synthesis engine demonstration complete.\n"
