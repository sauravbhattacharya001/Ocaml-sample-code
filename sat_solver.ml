(* SAT Solver using the DPLL algorithm *)
(* Demonstrates: algebraic data types, pattern matching, backtracking,
   unit propagation, pure literal elimination, recursive problem solving *)

(* A literal is a positive or negative variable *)
type literal =
  | Pos of int   (* positive occurrence of variable *)
  | Neg of int   (* negated occurrence of variable *)

(* A clause is a disjunction (OR) of literals *)
type clause = literal list

(* A formula in CNF is a conjunction (AND) of clauses *)
type formula = clause list

(* An assignment maps variables to boolean values *)
module IntMap = Map.Make(Int)
type assignment = bool IntMap.t

(* --- Literal utilities --- *)

let var_of = function Pos v | Neg v -> v

let is_positive = function Pos _ -> true | Neg _ -> false

let eval_literal assign lit =
  match IntMap.find_opt (var_of lit) assign with
  | None -> None  (* unassigned *)
  | Some b -> Some (if is_positive lit then b else not b)

(* --- Formula utilities --- *)

(* Collect all variables in the formula *)
let variables (f : formula) : int list =
  let module IntSet = Set.Make(Int) in
  List.fold_left (fun acc clause ->
    List.fold_left (fun acc lit -> IntSet.add (var_of lit) acc) acc clause
  ) IntSet.empty f
  |> IntSet.elements

(* Evaluate a clause under a partial assignment *)
(* Returns: Some true (satisfied), Some false (falsified), None (undetermined) *)
let eval_clause assign clause =
  let rec aux has_unknown = function
    | [] -> if has_unknown then None else Some false
    | lit :: rest ->
      match eval_literal assign lit with
      | Some true -> Some true    (* one true literal satisfies the clause *)
      | Some false -> aux has_unknown rest
      | None -> aux true rest
  in
  aux false clause

(* Evaluate the entire formula *)
let eval_formula assign formula =
  let rec aux = function
    | [] -> Some true
    | clause :: rest ->
      match eval_clause assign clause with
      | Some false -> Some false  (* one false clause falsifies everything *)
      | None ->
        (match aux rest with
         | Some false -> Some false
         | _ -> None)
      | Some true -> aux rest
  in
  aux formula

(* --- DPLL optimizations --- *)

(* Unit propagation: find unit clauses (single unassigned literal)
   and force their assignment *)
let find_unit_literal assign formula =
  let rec search = function
    | [] -> None
    | clause :: rest ->
      (* Check if clause is already satisfied *)
      match eval_clause assign clause with
      | Some true -> search rest  (* skip satisfied clauses *)
      | Some false -> None        (* contradiction — will be caught by DPLL *)
      | None ->
        (* Find unassigned literals in this clause *)
        let unassigned = List.filter (fun lit ->
          eval_literal assign lit = None
        ) clause in
        (match unassigned with
         | [lit] -> Some lit  (* unit clause found *)
         | _ -> search rest)
  in
  search formula

(* Pure literal elimination: if a variable appears only positive or only
   negative, assign it to satisfy all its occurrences *)
let find_pure_literal assign formula =
  let module IntMap2 = Map.Make(Int) in
  (* Track polarity of each unassigned variable *)
  (* 1 = only positive, -1 = only negative, 0 = both *)
  let polarities = List.fold_left (fun acc clause ->
    match eval_clause assign clause with
    | Some true -> acc  (* skip satisfied clauses *)
    | _ ->
      List.fold_left (fun acc lit ->
        if eval_literal assign lit <> None then acc  (* skip assigned *)
        else
          let v = var_of lit in
          let pol = if is_positive lit then 1 else -1 in
          match IntMap2.find_opt v acc with
          | None -> IntMap2.add v pol acc
          | Some p -> if p = pol then acc
                      else IntMap2.add v 0 acc
      ) acc clause
  ) IntMap2.empty formula in
  (* Find first pure literal *)
  IntMap2.fold (fun v pol acc ->
    match acc with
    | Some _ -> acc
    | None ->
      if pol = 1 then Some (Pos v)
      else if pol = -1 then Some (Neg v)
      else None
  ) polarities None

(* Choose an unassigned variable for branching *)
let choose_variable assign formula =
  (* Simple heuristic: pick the most frequent unassigned variable *)
  let counts = Hashtbl.create 16 in
  List.iter (fun clause ->
    match eval_clause assign clause with
    | Some true -> ()  (* skip satisfied clauses *)
    | _ ->
      List.iter (fun lit ->
        if eval_literal assign lit = None then begin
          let v = var_of lit in
          let c = try Hashtbl.find counts v with Not_found -> 0 in
          Hashtbl.replace counts v (c + 1)
        end
      ) clause
  ) formula;
  let best = Hashtbl.fold (fun v c (bv, bc) ->
    if c > bc then (Some v, c) else (bv, bc)
  ) counts (None, 0) in
  fst best

(* --- DPLL Algorithm --- *)

type result =
  | Satisfiable of assignment
  | Unsatisfiable

let solve (formula : formula) : result =
  let stats_propagations = ref 0 in
  let stats_decisions = ref 0 in

  let rec dpll assign =
    (* Check current state *)
    match eval_formula assign formula with
    | Some true -> Satisfiable assign
    | Some false -> Unsatisfiable
    | None ->
      (* Try unit propagation *)
      match find_unit_literal assign formula with
      | Some lit ->
        incr stats_propagations;
        let v = var_of lit in
        let b = is_positive lit in
        dpll (IntMap.add v b assign)
      | None ->
        (* Try pure literal elimination *)
        match find_pure_literal assign formula with
        | Some lit ->
          incr stats_propagations;
          let v = var_of lit in
          let b = is_positive lit in
          dpll (IntMap.add v b assign)
        | None ->
          (* Branch on an unassigned variable *)
          match choose_variable assign formula with
          | None -> Unsatisfiable  (* no variables left, but not satisfied *)
          | Some v ->
            incr stats_decisions;
            (* Try true first, then false *)
            match dpll (IntMap.add v true assign) with
            | Satisfiable _ as sat -> sat
            | Unsatisfiable -> dpll (IntMap.add v false assign)
  in
  let result = dpll IntMap.empty in
  Printf.printf "  [stats] propagations: %d, decisions: %d\n"
    !stats_propagations !stats_decisions;
  result

(* --- DIMACS CNF parser --- *)
(* Parses the standard DIMACS format used by SAT competition *)

let parse_dimacs (input : string) : formula =
  let lines = String.split_on_char '\n' input in
  List.fold_left (fun acc line ->
    let line = String.trim line in
    if line = "" || line.[0] = 'c' || line.[0] = 'p' then acc
    else
      let tokens = String.split_on_char ' ' line
        |> List.filter (fun s -> s <> "")
        |> List.map int_of_string in
      (* Each line ends with 0 as terminator *)
      let lits = List.filter (fun n -> n <> 0) tokens
        |> List.map (fun n ->
          if n > 0 then Pos n else Neg (abs n)) in
      if lits = [] then acc else lits :: acc
  ) [] lines
  |> List.rev

(* --- Pretty printing --- *)

let string_of_literal = function
  | Pos v -> Printf.sprintf "x%d" v
  | Neg v -> Printf.sprintf "¬x%d" v

let string_of_clause c =
  "(" ^ String.concat " ∨ " (List.map string_of_literal c) ^ ")"

let string_of_formula f =
  String.concat " ∧ " (List.map string_of_clause f)

let print_assignment assign =
  IntMap.iter (fun v b ->
    Printf.printf "  x%d = %b\n" v b
  ) assign

let print_result = function
  | Satisfiable assign ->
    print_endline "  SATISFIABLE ✓";
    print_assignment assign
  | Unsatisfiable ->
    print_endline "  UNSATISFIABLE ✗"

(* --- Verify a solution --- *)
let verify formula assign =
  List.for_all (fun clause ->
    List.exists (fun lit ->
      match eval_literal assign lit with
      | Some true -> true
      | _ -> false
    ) clause
  ) formula

(* --- Formula generators for testing --- *)

(* Generate a random k-SAT formula *)
let random_ksat ~k ~num_vars ~num_clauses =
  Random.self_init ();
  List.init num_clauses (fun _ ->
    List.init k (fun _ ->
      let v = 1 + Random.int num_vars in
      if Random.bool () then Pos v else Neg v
    )
  )

(* Pigeonhole principle: n+1 pigeons into n holes (always UNSAT) *)
let pigeonhole n =
  (* Variable (i,j) = pigeon i is in hole j, encoded as (i-1)*n + j *)
  let var i j = (i - 1) * n + j in
  (* Each pigeon must be in at least one hole *)
  let pigeon_clauses = List.init (n + 1) (fun i ->
    let i = i + 1 in
    List.init n (fun j -> Pos (var i (j + 1)))
  ) in
  (* No two pigeons in the same hole *)
  let hole_clauses = List.init n (fun j ->
    let j = j + 1 in
    let pairs = ref [] in
    for i1 = 1 to n + 1 do
      for i2 = i1 + 1 to n + 1 do
        pairs := [Neg (var i1 j); Neg (var i2 j)] :: !pairs
      done
    done;
    !pairs
  ) |> List.flatten in
  pigeon_clauses @ hole_clauses

(* === Examples === *)

let () =
  print_endline "╔══════════════════════════════════════╗";
  print_endline "║   DPLL SAT Solver in OCaml           ║";
  print_endline "╚══════════════════════════════════════╝";
  print_newline ();

  (* Example 1: Simple satisfiable formula *)
  (* (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ ¬x3) *)
  print_endline "Example 1: Simple 3-variable formula";
  let f1 = [
    [Pos 1; Pos 2];
    [Neg 1; Pos 3];
    [Neg 2; Neg 3];
  ] in
  Printf.printf "  Formula: %s\n" (string_of_formula f1);
  let r1 = solve f1 in
  print_result r1;
  (match r1 with
   | Satisfiable a ->
     Printf.printf "  Verified: %b\n" (verify f1 a)
   | _ -> ());
  print_newline ();

  (* Example 2: Unsatisfiable formula *)
  (* (x1) ∧ (¬x1) *)
  print_endline "Example 2: Trivially unsatisfiable";
  let f2 = [[Pos 1]; [Neg 1]] in
  Printf.printf "  Formula: %s\n" (string_of_formula f2);
  let _r2 = solve f2 in
  print_result _r2;
  print_newline ();

  (* Example 3: Graph coloring as SAT *)
  (* Color a triangle with 2 colors (UNSAT) *)
  print_endline "Example 3: Triangle 2-coloring (UNSAT)";
  print_endline "  Can we color a triangle with 2 colors? (No!)";
  (* var(node, color): node 1-3, color 1-2 → var = (node-1)*2 + color *)
  let vc n c = (n - 1) * 2 + c in
  let f3 =
    (* Each node gets at least one color *)
    [[Pos (vc 1 1); Pos (vc 1 2)];
     [Pos (vc 2 1); Pos (vc 2 2)];
     [Pos (vc 3 1); Pos (vc 3 2)]] @
    (* Adjacent nodes can't share a color *)
    (* Edge 1-2 *) [[Neg (vc 1 1); Neg (vc 2 1)]; [Neg (vc 1 2); Neg (vc 2 2)]] @
    (* Edge 2-3 *) [[Neg (vc 2 1); Neg (vc 3 1)]; [Neg (vc 2 2); Neg (vc 3 2)]] @
    (* Edge 1-3 *) [[Neg (vc 1 1); Neg (vc 3 1)]; [Neg (vc 1 2); Neg (vc 3 2)]]
  in
  let _r3 = solve f3 in
  print_result _r3;
  print_newline ();

  (* Example 4: Graph coloring — triangle with 3 colors (SAT) *)
  print_endline "Example 4: Triangle 3-coloring (SAT)";
  let vc3 n c = (n - 1) * 3 + c in
  let f4 =
    (* Each node gets at least one color *)
    [[Pos (vc3 1 1); Pos (vc3 1 2); Pos (vc3 1 3)];
     [Pos (vc3 2 1); Pos (vc3 2 2); Pos (vc3 2 3)];
     [Pos (vc3 3 1); Pos (vc3 3 2); Pos (vc3 3 3)]] @
    (* Adjacent nodes can't share color *)
    List.concat_map (fun (a, b) ->
      List.init 3 (fun c -> [Neg (vc3 a (c+1)); Neg (vc3 b (c+1))])
    ) [(1,2); (2,3); (1,3)]
  in
  let r4 = solve f4 in
  print_result r4;
  (match r4 with
   | Satisfiable a ->
     Printf.printf "  Verified: %b\n" (verify f4 a)
   | _ -> ());
  print_newline ();

  (* Example 5: DIMACS format parsing *)
  print_endline "Example 5: DIMACS format parsing";
  let dimacs = "c Example DIMACS\np cnf 3 2\n1 -3 0\n2 3 -1 0\n" in
  let f5 = parse_dimacs dimacs in
  Printf.printf "  Parsed: %s\n" (string_of_formula f5);
  let r5 = solve f5 in
  print_result r5;
  print_newline ();

  (* Example 6: Pigeonhole principle (3 pigeons, 2 holes) *)
  print_endline "Example 6: Pigeonhole principle (3 pigeons → 2 holes)";
  print_endline "  Always UNSAT — can't fit 3 pigeons in 2 holes!";
  let f6 = pigeonhole 2 in
  Printf.printf "  Clauses: %d\n" (List.length f6);
  let _r6 = solve f6 in
  print_result _r6;
  print_newline ();

  (* Example 7: Random 3-SAT *)
  print_endline "Example 7: Random 3-SAT (20 vars, 60 clauses)";
  let f7 = random_ksat ~k:3 ~num_vars:20 ~num_clauses:60 in
  Printf.printf "  Variables: %d, Clauses: %d\n"
    (List.length (variables f7)) (List.length f7);
  let r7 = solve f7 in
  print_result r7;
  (match r7 with
   | Satisfiable a ->
     Printf.printf "  Verified: %b\n" (verify f7 a)
   | _ -> ());
  print_newline ();

  print_endline "Done! The DPLL algorithm uses:";
  print_endline "  • Unit propagation — forced assignments from single-literal clauses";
  print_endline "  • Pure literal elimination — variables appearing with one polarity";
  print_endline "  • Backtracking search — try assignments, undo on contradiction";
  print_endline "  • Most-frequent variable heuristic — pick the busiest variable to branch on"
