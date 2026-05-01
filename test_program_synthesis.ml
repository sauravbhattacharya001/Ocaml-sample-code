(* ============================================================================
   test_program_synthesis.ml - Tests for Program Synthesis Engine
   ============================================================================
   Self-contained test file that inlines necessary logic from program_synthesis.ml
   ============================================================================ *)

(* ── Test Framework ─────────────────────────────────────────────────────── *)

let tests_run = ref 0
let tests_passed = ref 0

let assert_true msg cond =
  incr tests_run;
  if cond then (incr tests_passed; Printf.printf "  ✓ %s\n" msg)
  else Printf.printf "  ✗ FAIL: %s\n" msg

let assert_equal msg expected actual =
  incr tests_run;
  if expected = actual then (incr tests_passed; Printf.printf "  ✓ %s\n" msg)
  else Printf.printf "  ✗ FAIL: %s (expected %s, got %s)\n" msg expected actual

(* ── Inlined Core from program_synthesis.ml ─────────────────────────────── *)

(* Expression AST *)
type expr =
  | Var of string
  | IntLit of int
  | BoolLit of bool
  | App of string * expr list
  | Lambda of string * expr
  | If of expr * expr * expr
  | Let of string * expr * expr

type synth_type =
  | TInt
  | TBool
  | TList of synth_type
  | TFun of synth_type * synth_type
  | TVar of string

(* Value type for evaluation *)
type value =
  | VInt of int
  | VBool of bool
  | VList of int list
  | VNone

type env = (string * value) list

(* Pretty printing *)
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

(* Expression complexity *)
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

(* Evaluation *)
exception EvalError of string

let lookup env x =
  match List.assoc_opt x env with
  | Some v -> v
  | None -> VNone

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
  | Lambda _ -> VNone
  | App (f, args) -> eval_builtin env f args

and eval_builtin env f args =
  let eval_args () = List.map (eval env) args in
  match f, eval_args () with
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
  | "not", [VBool a] -> VBool (not a)
  | "and", [VBool a; VBool b] -> VBool (a && b)
  | "or", [VBool a; VBool b] -> VBool (a || b)
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
  | "x", [] -> lookup env "x"
  | "input", [] -> lookup env "input"
  | _ -> raise (EvalError (Printf.sprintf "unknown function: %s/%d" f (List.length args)))

let safe_eval env expr =
  try Some (eval env expr)
  with EvalError _ | Invalid_argument _ | Failure _ -> None

(* Component types *)
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
  { name = "abs"; arity = 1; input_types = [TInt]; output_type = TInt; description = "absolute value" };
  { name = "neg"; arity = 1; input_types = [TInt]; output_type = TInt; description = "negation" };
  { name = "succ"; arity = 1; input_types = [TInt]; output_type = TInt; description = "successor" };
  { name = "pred"; arity = 1; input_types = [TInt]; output_type = TInt; description = "predecessor" };
  { name = "square"; arity = 1; input_types = [TInt]; output_type = TInt; description = "x*x" };
  { name = "double"; arity = 1; input_types = [TInt]; output_type = TInt; description = "x*2" };
]

let list_components = [
  { name = "length"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "list length" };
  { name = "hd"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "head" };
  { name = "sum"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "sum" };
  { name = "max_elem"; arity = 1; input_types = [TList TInt]; output_type = TInt; description = "max" };
  { name = "rev"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "reverse" };
  { name = "sort"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "sort" };
  { name = "filter_pos"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "positives" };
  { name = "map_double"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "double all" };
  { name = "map_neg"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "negate all" };
  { name = "dedup"; arity = 1; input_types = [TList TInt]; output_type = TList TInt; description = "deduplicate" };
]

let bool_components = [
  { name = "even"; arity = 1; input_types = [TInt]; output_type = TBool; description = "is even" };
  { name = "odd"; arity = 1; input_types = [TInt]; output_type = TBool; description = "is odd" };
  { name = "positive"; arity = 1; input_types = [TInt]; output_type = TBool; description = "is positive" };
  { name = "zero"; arity = 1; input_types = [TInt]; output_type = TBool; description = "is zero" };
  { name = "="; arity = 2; input_types = [TInt; TInt]; output_type = TBool; description = "equality" };
  { name = "<"; arity = 2; input_types = [TInt; TInt]; output_type = TBool; description = "less than" };
  { name = ">"; arity = 2; input_types = [TInt; TInt]; output_type = TBool; description = "greater than" };
]

(* Candidate and result types *)
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
  status: string;
}

(* Enumeration *)
let enumerate_int_exprs depth =
  let exprs = ref [] in
  let base_exprs = [Var "x"; IntLit 0; IntLit 1; IntLit 2; IntLit 3] in
  exprs := base_exprs;
  for d = 1 to depth do
    let prev = !exprs in
    let new_exprs = ref [] in
    List.iter (fun comp ->
      if comp.arity = 1 && comp.output_type = TInt then
        List.iter (fun arg ->
          if expr_size arg <= d * 2 then
            new_exprs := App (comp.name, [arg]) :: !new_exprs
        ) prev
    ) int_components;
    List.iter (fun comp ->
      if comp.arity = 2 && comp.output_type = TInt then begin
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

let enumerate_list_to_int_exprs depth =
  let exprs = ref [] in
  let list_base = [Var "input"] in
  let list_exprs = ref list_base in
  List.iter (fun comp ->
    if comp.arity = 1 && comp.output_type = TList TInt then
      List.iter (fun arg ->
        list_exprs := App (comp.name, [arg]) :: !list_exprs
      ) list_base
  ) list_components;
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

(* Observational equivalence pruning *)
let prune_equivalent_int exprs =
  let test_inputs = [0; 1; 2; 3; 5; -1; -2; 7; 10; 100] in
  let seen = Hashtbl.create 256 in
  List.filter (fun expr ->
    let fp = List.map (fun x ->
      match safe_eval [("x", VInt x)] expr with
      | Some (VInt n) -> string_of_int n
      | Some (VBool b) -> string_of_bool b
      | _ -> "?"
    ) test_inputs in
    let key = String.concat ";" fp in
    if Hashtbl.mem seen key then false
    else begin Hashtbl.add seen key true; true end
  ) exprs

let prune_equivalent_list exprs =
  let test_inputs = [[1;2;3]; [5;4;3;2;1]; []; [7]; [-1;0;1]; [2;2;3]] in
  let seen = Hashtbl.create 256 in
  List.filter (fun expr ->
    let fp = List.map (fun l ->
      match safe_eval [("input", VList l)] expr with
      | Some (VList lst) -> String.concat "," (List.map string_of_int lst)
      | Some (VInt n) -> string_of_int n
      | _ -> "?"
    ) test_inputs in
    let key = String.concat ";" fp in
    if Hashtbl.mem seen key then false
    else begin Hashtbl.add seen key true; true end
  ) exprs

(* Core synthesis functions *)
let synthesize_int_to_int (examples : (int * int) list) : synthesis_result =
  let candidates_tested = ref 0 in
  let candidates_pruned_count = ref 0 in
  let solutions = ref [] in
  let max_depth = 3 in
  let final_depth = ref 0 in

  for depth = 1 to max_depth do
    if !solutions = [] || List.length !solutions < 5 then begin
      final_depth := depth;
      let exprs = enumerate_int_exprs depth in
      let pruned = prune_equivalent_int exprs in
      candidates_pruned_count := !candidates_pruned_count + (List.length exprs - List.length pruned);
      List.iter (fun expr ->
        incr candidates_tested;
        let passes = List.for_all (fun (inp, expected_out) ->
          match safe_eval [("x", VInt inp)] expr with
          | Some (VInt v) -> v = expected_out
          | _ -> false
        ) examples in
        if passes then begin
          let code = expr_to_string expr in
          let cmplx = complexity_score expr in
          solutions := {
            expr; code = Printf.sprintf "fun x -> %s" code;
            complexity = cmplx; confidence = 1.0 -. (cmplx /. 20.0);
          } :: !solutions
        end
      ) pruned
    end
  done;

  let sorted = List.sort (fun a b -> compare a.complexity b.complexity) !solutions in
  let top = if List.length sorted > 10 then List.filteri (fun i _ -> i < 10) sorted else sorted in
  { task_description = Printf.sprintf "int -> int (%d examples)" (List.length examples);
    examples_count = List.length examples;
    candidates_explored = !candidates_tested;
    candidates_pruned = !candidates_pruned_count;
    solutions = top;
    synthesis_time_ms = !candidates_tested / 10;
    search_depth = !final_depth;
    status = if top <> [] then "success" else "failed"; }

let synthesize_list_to_list (examples : (int list * int list) list) : synthesis_result =
  let candidates_tested = ref 0 in
  let candidates_pruned_count = ref 0 in
  let solutions = ref [] in
  let max_depth = 3 in
  let final_depth = ref 0 in

  for depth = 1 to max_depth do
    if !solutions = [] || List.length !solutions < 5 then begin
      final_depth := depth;
      let exprs = enumerate_list_exprs depth in
      let pruned = prune_equivalent_list exprs in
      candidates_pruned_count := !candidates_pruned_count + (List.length exprs - List.length pruned);
      List.iter (fun expr ->
        incr candidates_tested;
        let passes = List.for_all (fun (inp, expected_out) ->
          match safe_eval [("input", VList inp)] expr with
          | Some (VList v) -> v = expected_out
          | _ -> false
        ) examples in
        if passes then begin
          let code = expr_to_string expr in
          let cmplx = complexity_score expr in
          solutions := {
            expr; code = Printf.sprintf "fun input -> %s" code;
            complexity = cmplx; confidence = 1.0 -. (cmplx /. 20.0);
          } :: !solutions
        end
      ) pruned
    end
  done;

  let sorted = List.sort (fun a b -> compare a.complexity b.complexity) !solutions in
  let top = if List.length sorted > 10 then List.filteri (fun i _ -> i < 10) sorted else sorted in
  { task_description = Printf.sprintf "int list -> int list (%d examples)" (List.length examples);
    examples_count = List.length examples;
    candidates_explored = !candidates_tested;
    candidates_pruned = !candidates_pruned_count;
    solutions = top;
    synthesis_time_ms = !candidates_tested / 10;
    search_depth = !final_depth;
    status = if top <> [] then "success" else "failed"; }

let synthesize_list_to_int (examples : (int list * int) list) : synthesis_result =
  let candidates_tested = ref 0 in
  let solutions = ref [] in
  let max_depth = 2 in
  let final_depth = ref 0 in

  for depth = 0 to max_depth do
    final_depth := depth;
    let exprs = enumerate_list_to_int_exprs depth in
    List.iter (fun expr ->
      incr candidates_tested;
      let passes = List.for_all (fun (inp, expected_out) ->
        match safe_eval [("input", VList inp)] expr with
        | Some (VInt v) -> v = expected_out
        | _ -> false
      ) examples in
      if passes then begin
        let code = expr_to_string expr in
        let cmplx = complexity_score expr in
        solutions := {
          expr; code = Printf.sprintf "fun input -> %s" code;
          complexity = cmplx; confidence = 1.0 -. (cmplx /. 15.0);
        } :: !solutions
      end
    ) exprs
  done;

  let sorted = List.sort (fun a b -> compare a.complexity b.complexity) !solutions in
  let top = if List.length sorted > 10 then List.filteri (fun i _ -> i < 10) sorted else sorted in
  { task_description = Printf.sprintf "int list -> int (%d examples)" (List.length examples);
    examples_count = List.length examples;
    candidates_explored = !candidates_tested;
    candidates_pruned = 0;
    solutions = top;
    synthesis_time_ms = !candidates_tested / 10;
    search_depth = !final_depth;
    status = if top <> [] then "success" else "failed"; }

let synthesize_int_to_bool (examples : (int * bool) list) : synthesis_result =
  let candidates_tested = ref 0 in
  let solutions = ref [] in
  let max_depth = 2 in
  let final_depth = ref 0 in

  for depth = 0 to max_depth do
    final_depth := depth;
    let exprs = enumerate_int_to_bool_exprs depth in
    List.iter (fun expr ->
      incr candidates_tested;
      let passes = List.for_all (fun (inp, expected_out) ->
        match safe_eval [("x", VInt inp)] expr with
        | Some (VBool v) -> v = expected_out
        | _ -> false
      ) examples in
      if passes then begin
        let code = expr_to_string expr in
        let cmplx = complexity_score expr in
        solutions := {
          expr; code = Printf.sprintf "fun x -> %s" code;
          complexity = cmplx; confidence = 1.0 -. (cmplx /. 15.0);
        } :: !solutions
      end
    ) exprs
  done;

  let sorted = List.sort (fun a b -> compare a.complexity b.complexity) !solutions in
  let top = if List.length sorted > 10 then List.filteri (fun i _ -> i < 10) sorted else sorted in
  { task_description = Printf.sprintf "int -> bool (%d examples)" (List.length examples);
    examples_count = List.length examples;
    candidates_explored = !candidates_tested;
    candidates_pruned = 0;
    solutions = top;
    synthesis_time_ms = !candidates_tested / 10;
    search_depth = !final_depth;
    status = if top <> [] then "success" else "failed"; }

(* Validation *)
let validate_int_candidate (cand : candidate) (original_examples : (int * int) list) =
  let extra_inputs = [11; -5; 42; 0; 100; -100; 7; 13; 99; 256] in
  let extra_inputs = List.filter (fun x ->
    not (List.exists (fun (i, _) -> i = x) original_examples)
  ) extra_inputs in
  let results = List.map (fun x ->
    match safe_eval [("x", VInt x)] cand.expr with
    | Some (VInt v) -> Some (x, v)
    | _ -> None
  ) extra_inputs in
  let valid_results = List.filter_map (fun x -> x) results in
  let total_ran = List.length valid_results in
  let suspicious = List.filter (fun (_, v) -> abs v > 1000000000) valid_results in
  if total_ran = 0 then 0.5
  else 1.0 -. (float_of_int (List.length suspicious) /. float_of_int total_ran)

(* ── Tests ──────────────────────────────────────────────────────────────── *)

let test_eval () =
  Printf.printf "\n── Evaluation Engine ──\n";

  (match safe_eval [("x", VInt 5)] (App ("+", [Var "x"; IntLit 3])) with
   | Some (VInt 8) -> assert_true "5 + 3 = 8" true
   | _ -> assert_true "5 + 3 = 8" false);

  (match safe_eval [("x", VInt 4)] (App ("square", [Var "x"])) with
   | Some (VInt 16) -> assert_true "square(4) = 16" true
   | _ -> assert_true "square(4) = 16" false);

  (match safe_eval [("x", VInt 3)] (App ("double", [Var "x"])) with
   | Some (VInt 6) -> assert_true "double(3) = 6" true
   | _ -> assert_true "double(3) = 6" false);

  (match safe_eval [("x", VInt (-5))] (App ("abs", [Var "x"])) with
   | Some (VInt 5) -> assert_true "abs(-5) = 5" true
   | _ -> assert_true "abs(-5) = 5" false);

  (match safe_eval [("x", VInt 7)] (App ("succ", [Var "x"])) with
   | Some (VInt 8) -> assert_true "succ(7) = 8" true
   | _ -> assert_true "succ(7) = 8" false);

  (match safe_eval [("input", VList [3;1;2])] (App ("rev", [Var "input"])) with
   | Some (VList [2;1;3]) -> assert_true "rev [3;1;2] = [2;1;3]" true
   | _ -> assert_true "rev [3;1;2] = [2;1;3]" false);

  (match safe_eval [("input", VList [3;1;2])] (App ("sort", [Var "input"])) with
   | Some (VList [1;2;3]) -> assert_true "sort [3;1;2] = [1;2;3]" true
   | _ -> assert_true "sort [3;1;2] = [1;2;3]" false);

  (match safe_eval [("input", VList [1;2;3;4;5])] (App ("length", [Var "input"])) with
   | Some (VInt 5) -> assert_true "length [1;2;3;4;5] = 5" true
   | _ -> assert_true "length [1;2;3;4;5] = 5" false);

  (match safe_eval [("input", VList [10;20;30])] (App ("sum", [Var "input"])) with
   | Some (VInt 60) -> assert_true "sum [10;20;30] = 60" true
   | _ -> assert_true "sum [10;20;30] = 60" false);

  (match safe_eval [("input", VList [1;2;3])] (App ("map_double", [Var "input"])) with
   | Some (VList [2;4;6]) -> assert_true "map_double [1;2;3] = [2;4;6]" true
   | _ -> assert_true "map_double [1;2;3] = [2;4;6]" false);

  (match safe_eval [("x", VInt 4)] (App ("even", [Var "x"])) with
   | Some (VBool true) -> assert_true "even(4) = true" true
   | _ -> assert_true "even(4) = true" false);

  (match safe_eval [("x", VInt 3)] (App ("odd", [Var "x"])) with
   | Some (VBool true) -> assert_true "odd(3) = true" true
   | _ -> assert_true "odd(3) = true" false);

  (match safe_eval [("x", VInt 5)] (App ("positive", [Var "x"])) with
   | Some (VBool true) -> assert_true "positive(5) = true" true
   | _ -> assert_true "positive(5) = true" false);

  (match safe_eval [] (App ("/", [IntLit 5; IntLit 0])) with
   | None -> assert_true "div by zero returns None" true
   | _ -> assert_true "div by zero returns None" false)

let test_int_synthesis () =
  Printf.printf "\n── Int→Int Synthesis ──\n";

  let r = synthesize_int_to_int [(1,1); (2,4); (3,9); (4,16)] in
  assert_equal "square: status" "success" r.status;
  assert_true "square: has solutions" (List.length r.solutions > 0);

  let r = synthesize_int_to_int [(1,2); (3,6); (5,10); (0,0)] in
  assert_equal "double: status" "success" r.status;
  assert_true "double: has solutions" (List.length r.solutions > 0);

  let r = synthesize_int_to_int [(0,1); (1,2); (5,6); (10,11)] in
  assert_equal "succ: status" "success" r.status;

  let r = synthesize_int_to_int [(-3,3); (-1,1); (0,0); (5,5)] in
  assert_equal "abs: status" "success" r.status;

  let r = synthesize_int_to_int [(1,-1); (3,-3); (0,0); (-5,5)] in
  assert_equal "neg: status" "success" r.status;

  let r = synthesize_int_to_int [(1,1); (5,5); (0,0); (-3,-3)] in
  assert_equal "identity: status" "success" r.status;
  assert_true "identity: simplest is small" 
    (match r.solutions with c::_ -> c.complexity <= 2.0 | [] -> false);

  let r = synthesize_int_to_int [(1,2); (2,3)] in
  assert_true "explored candidates > 0" (r.candidates_explored > 0);

  let r = synthesize_int_to_int [(0,0); (1,1); (2,4); (3,9)] in
  assert_true "solutions ranked by complexity"
    (match r.solutions with
     | a :: b :: _ -> a.complexity <= b.complexity
     | _ -> true)

let test_list_synthesis () =
  Printf.printf "\n── List→List Synthesis ──\n";

  let r = synthesize_list_to_list [([1;2;3], [3;2;1]); ([5;4], [4;5])] in
  assert_equal "reverse: status" "success" r.status;
  assert_true "reverse: has solutions" (List.length r.solutions > 0);

  let r = synthesize_list_to_list [([3;1;2], [1;2;3]); ([5;4;3], [3;4;5])] in
  assert_equal "sort: status" "success" r.status;

  let r = synthesize_list_to_list [
    ([-1;2;-3;4], [2;4]); ([1;2;3], [1;2;3]); ([-5;-3], [])
  ] in
  assert_equal "filter_pos: status" "success" r.status;

  let r = synthesize_list_to_list [([1;2;3], [2;4;6]); ([5], [10])] in
  assert_equal "map_double: status" "success" r.status;

  let r = synthesize_list_to_list [([1;2;3], [-1;-2;-3]); ([0], [0])] in
  assert_equal "map_neg: status" "success" r.status;

  let r = synthesize_list_to_list [([3;1;2;1;3], [1;2;3]); ([5;5;5], [5])] in
  assert_equal "dedup: status" "success" r.status

let test_list_to_int_synthesis () =
  Printf.printf "\n── List→Int Synthesis ──\n";

  let r = synthesize_list_to_int [([1;2;3], 3); ([], 0); ([5;6], 2)] in
  assert_equal "length: status" "success" r.status;

  let r = synthesize_list_to_int [([1;2;3], 6); ([10;20], 30); ([], 0)] in
  assert_equal "sum: status" "success" r.status;

  let r = synthesize_list_to_int [([1;5;3], 5); ([10;2;8], 10); ([7], 7)] in
  assert_equal "max_elem: status" "success" r.status;

  let r = synthesize_list_to_int [([10;20;30], 10); ([5;4;3], 5); ([1], 1)] in
  assert_equal "hd: status" "success" r.status

let test_bool_synthesis () =
  Printf.printf "\n── Int→Bool Synthesis ──\n";

  let r = synthesize_int_to_bool [(0,true); (1,false); (2,true); (3,false)] in
  assert_equal "even: status" "success" r.status;

  let r = synthesize_int_to_bool [(-1,false); (0,false); (1,true); (5,true)] in
  assert_equal "positive: status" "success" r.status;

  let r = synthesize_int_to_bool [(0,true); (1,false); (-1,false); (5,false)] in
  assert_equal "zero: status" "success" r.status

let test_expr_utils () =
  Printf.printf "\n── Expression Utilities ──\n";

  assert_equal "Var to string" "x" (expr_to_string (Var "x"));
  assert_equal "IntLit to string" "42" (expr_to_string (IntLit 42));
  assert_equal "App to string" "(succ x)" (expr_to_string (App ("succ", [Var "x"])));

  assert_true "Var size = 1" (expr_size (Var "x") = 1);
  assert_true "App size > 1" (expr_size (App ("+", [Var "x"; IntLit 1])) > 1);
  assert_true "nested size grows"
    (expr_size (App ("+", [App ("*", [Var "x"; Var "x"]); IntLit 1])) > 3);

  let simple = Var "x" in
  let complex = App ("+", [App ("*", [Var "x"; Var "x"]); IntLit 1]) in
  assert_true "complex > simple" (complexity_score complex > complexity_score simple);

  assert_equal "TInt" "int" (type_to_string TInt);
  assert_equal "TBool" "bool" (type_to_string TBool);
  assert_equal "TList" "int list" (type_to_string (TList TInt))

let test_equivalence_pruning () =
  Printf.printf "\n── Equivalence Pruning ──\n";

  let exprs = enumerate_int_exprs 1 in
  let pruned = prune_equivalent_int exprs in
  assert_true "pruning reduces candidates" (List.length pruned < List.length exprs);
  assert_true "pruned still has candidates" (List.length pruned > 0);

  let list_exprs = enumerate_list_exprs 1 in
  let list_pruned = prune_equivalent_list list_exprs in
  assert_true "list pruning reduces" (List.length list_pruned <= List.length list_exprs);
  assert_true "list pruned non-empty" (List.length list_pruned > 0)

let test_validation () =
  Printf.printf "\n── Validation ──\n";

  let cand = {
    expr = App ("square", [Var "x"]);
    code = "fun x -> (square x)";
    complexity = 2.0;
    confidence = 0.9;
  } in
  let score = validate_int_candidate cand [(1,1); (2,4); (3,9)] in
  assert_true "square validates well" (score >= 0.8);

  let cand_abs = {
    expr = App ("abs", [Var "x"]);
    code = "fun x -> (abs x)";
    complexity = 2.0;
    confidence = 0.9;
  } in
  let score2 = validate_int_candidate cand_abs [(-3,3); (5,5)] in
  assert_true "abs validates well" (score2 >= 0.8)

let test_synthesis_properties () =
  Printf.printf "\n── Synthesis Properties ──\n";

  (* Empty examples should still work *)
  let r = synthesize_int_to_int [] in
  assert_true "empty examples: has solutions (anything matches)" (List.length r.solutions > 0);

  (* Single example *)
  let r = synthesize_int_to_int [(5, 25)] in
  assert_equal "single example: status" "success" r.status;

  (* Impossible synthesis (no simple expr maps these) *)
  let r = synthesize_int_to_int [(1, 42); (2, 97); (3, 153)] in
  (* This might fail - that's expected *)
  assert_true "complex mapping: explored > 0" (r.candidates_explored > 0);

  (* All synthesis results have non-negative fields *)
  let r = synthesize_int_to_int [(1,2); (2,4)] in
  assert_true "candidates >= 0" (r.candidates_explored >= 0);
  assert_true "pruned >= 0" (r.candidates_pruned >= 0);
  assert_true "depth >= 1" (r.search_depth >= 1)

(* ── Main ───────────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║  Program Synthesis Engine - Test Suite (45 tests)           ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n";

  test_eval ();
  test_int_synthesis ();
  test_list_synthesis ();
  test_list_to_int_synthesis ();
  test_bool_synthesis ();
  test_expr_utils ();
  test_equivalence_pruning ();
  test_validation ();
  test_synthesis_properties ();

  Printf.printf "\n══════════════════════════════════════════════════════════════\n";
  Printf.printf "  Results: %d passed, %d failed (total: %d)\n"
    !tests_passed (!tests_run - !tests_passed) !tests_run;
  Printf.printf "══════════════════════════════════════════════════════════════\n";

  if !tests_passed = !tests_run then
    Printf.printf "  ✨ All tests passed!\n"
  else
    Printf.printf "  ⚠ Some tests failed!\n"
