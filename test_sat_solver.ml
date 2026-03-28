(* Tests for the DPLL SAT Solver *)

(* Inline the SAT solver types and functions since OCaml doesn't have a
   module system that works with simple file compilation without dune/mli *)

type literal =
  | Pos of int
  | Neg of int

type clause = literal list
type formula = clause list

module IntMap = Map.Make(Int)
type assignment = bool IntMap.t

let var_of = function Pos v | Neg v -> v
let is_positive = function Pos _ -> true | Neg _ -> false

let eval_literal assign lit =
  match IntMap.find_opt (var_of lit) assign with
  | None -> None
  | Some b -> Some (if is_positive lit then b else not b)

let variables (f : formula) : int list =
  let module IntSet = Set.Make(Int) in
  List.fold_left (fun acc clause ->
    List.fold_left (fun acc lit -> IntSet.add (var_of lit) acc) acc clause
  ) IntSet.empty f
  |> IntSet.elements

let eval_clause assign clause =
  let rec aux has_unknown = function
    | [] -> if has_unknown then None else Some false
    | lit :: rest ->
      match eval_literal assign lit with
      | Some true -> Some true
      | Some false -> aux has_unknown rest
      | None -> aux true rest
  in
  aux false clause

let eval_formula assign formula =
  let rec aux = function
    | [] -> Some true
    | clause :: rest ->
      match eval_clause assign clause with
      | Some false -> Some false
      | None ->
        (match aux rest with
         | Some false -> Some false
         | _ -> None)
      | Some true -> aux rest
  in
  aux formula

let find_unit_literal assign formula =
  let rec search = function
    | [] -> None
    | clause :: rest ->
      match eval_clause assign clause with
      | Some true -> search rest
      | Some false -> None
      | None ->
        let unassigned = List.filter (fun lit ->
          eval_literal assign lit = None
        ) clause in
        (match unassigned with
         | [lit] -> Some lit
         | _ -> search rest)
  in
  search formula

let find_pure_literal assign formula =
  let module IntMap2 = Map.Make(Int) in
  let polarities = List.fold_left (fun acc clause ->
    match eval_clause assign clause with
    | Some true -> acc
    | _ ->
      List.fold_left (fun acc lit ->
        if eval_literal assign lit <> None then acc
        else
          let v = var_of lit in
          let pol = if is_positive lit then 1 else -1 in
          match IntMap2.find_opt v acc with
          | None -> IntMap2.add v pol acc
          | Some p -> if p = pol then acc
                      else IntMap2.add v 0 acc
      ) acc clause
  ) IntMap2.empty formula in
  IntMap2.fold (fun v pol acc ->
    match acc with
    | Some _ -> acc
    | None ->
      if pol = 1 then Some (Pos v)
      else if pol = -1 then Some (Neg v)
      else None
  ) polarities None

let choose_variable assign formula =
  let counts = Hashtbl.create 16 in
  List.iter (fun clause ->
    match eval_clause assign clause with
    | Some true -> ()
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

type result =
  | Satisfiable of assignment
  | Unsatisfiable

let solve (formula : formula) : result =
  let rec dpll assign =
    match eval_formula assign formula with
    | Some true -> Satisfiable assign
    | Some false -> Unsatisfiable
    | None ->
      match find_unit_literal assign formula with
      | Some lit ->
        let v = var_of lit in
        let b = is_positive lit in
        dpll (IntMap.add v b assign)
      | None ->
        match find_pure_literal assign formula with
        | Some lit ->
          let v = var_of lit in
          let b = is_positive lit in
          dpll (IntMap.add v b assign)
        | None ->
          match choose_variable assign formula with
          | None -> Unsatisfiable
          | Some v ->
            match dpll (IntMap.add v true assign) with
            | Satisfiable _ as sat -> sat
            | Unsatisfiable -> dpll (IntMap.add v false assign)
  in
  dpll IntMap.empty

let verify formula assign =
  List.for_all (fun clause ->
    List.exists (fun lit ->
      match eval_literal assign lit with
      | Some true -> true
      | _ -> false
    ) clause
  ) formula

let parse_dimacs (input : string) : formula =
  let lines = String.split_on_char '\n' input in
  List.fold_left (fun acc line ->
    let line = String.trim line in
    if line = "" || line.[0] = 'c' || line.[0] = 'p' then acc
    else
      let tokens = String.split_on_char ' ' line
        |> List.filter (fun s -> s <> "")
        |> List.map int_of_string in
      let lits = List.filter (fun n -> n <> 0) tokens
        |> List.map (fun n ->
          if n > 0 then Pos n else Neg (abs n)) in
      if lits = [] then acc else lits :: acc
  ) [] lines
  |> List.rev

let pigeonhole n =
  let var i j = (i - 1) * n + j in
  let pigeon_clauses = List.init (n + 1) (fun i ->
    let i = i + 1 in
    List.init n (fun j -> Pos (var i (j + 1)))
  ) in
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

let random_ksat ~k ~num_vars ~num_clauses =
  List.init num_clauses (fun _ ->
    List.init k (fun _ ->
      let v = 1 + Random.int num_vars in
      if Random.bool () then Pos v else Neg v
    )
  )

(* ===== Test harness ===== *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_true name cond =
  if cond then (
    incr tests_passed;
    Printf.printf "  PASS: %s\n" name
  ) else (
    incr tests_failed;
    Printf.printf "  FAIL: %s\n" name
  )

let assert_equal name expected actual =
  assert_true name (expected = actual)

(* ===== Tests ===== *)

let test_eval_literal () =
  Printf.printf "\n--- eval_literal ---\n";
  let assign = IntMap.singleton 1 true in
  assert_equal "Pos var=true -> Some true" (Some true) (eval_literal assign (Pos 1));
  assert_equal "Neg var=true -> Some false" (Some false) (eval_literal assign (Neg 1));
  assert_equal "unassigned -> None" None (eval_literal assign (Pos 2));
  let assign2 = IntMap.singleton 3 false in
  assert_equal "Pos var=false -> Some false" (Some false) (eval_literal assign2 (Pos 3));
  assert_equal "Neg var=false -> Some true" (Some true) (eval_literal assign2 (Neg 3))

let test_eval_clause () =
  Printf.printf "\n--- eval_clause ---\n";
  let assign = IntMap.add 1 true (IntMap.singleton 2 false) in
  (* (x1 | x2) with x1=T, x2=F -> true *)
  assert_equal "one true literal" (Some true) (eval_clause assign [Pos 1; Pos 2]);
  (* (~x1 | x2) with x1=T, x2=F -> false *)
  assert_equal "all false" (Some false) (eval_clause assign [Neg 1; Pos 2]);
  (* (x1 | x3) with x1=T, x3=? -> true *)
  assert_equal "true + unknown" (Some true) (eval_clause assign [Pos 1; Pos 3]);
  (* (~x1 | x3) with x1=T, x3=? -> unknown *)
  assert_equal "false + unknown" None (eval_clause assign [Neg 1; Pos 3]);
  (* empty clause -> false *)
  assert_equal "empty clause" (Some false) (eval_clause assign [])

let test_eval_formula () =
  Printf.printf "\n--- eval_formula ---\n";
  let assign = IntMap.add 1 true (IntMap.singleton 2 true) in
  (* (x1) & (x2) -> true *)
  assert_equal "all satisfied" (Some true) (eval_formula assign [[Pos 1]; [Pos 2]]);
  (* (x1) & (~x1) -> false *)
  assert_equal "contradiction" (Some false) (eval_formula assign [[Pos 1]; [Neg 1]]);
  (* (x1) & (x3) -> unknown *)
  assert_equal "partial" None (eval_formula assign [[Pos 1]; [Pos 3]]);
  (* empty formula -> true *)
  assert_equal "empty formula" (Some true) (eval_formula assign [])

let test_unit_propagation () =
  Printf.printf "\n--- unit propagation ---\n";
  let assign = IntMap.singleton 1 false in
  (* clause (x1 | x2) with x1=false -> unit clause, must set x2 *)
  let f = [[Pos 1; Pos 2]] in
  (match find_unit_literal assign f with
   | Some (Pos 2) -> assert_true "finds unit literal x2" true
   | _ -> assert_true "finds unit literal x2" false);
  (* no unit clause when both unassigned *)
  (match find_unit_literal IntMap.empty [[Pos 1; Pos 2]] with
   | None -> assert_true "no unit in 2-literal clause" true
   | _ -> assert_true "no unit in 2-literal clause" false);
  (* single-literal clause is always unit *)
  (match find_unit_literal IntMap.empty [[Neg 5]] with
   | Some (Neg 5) -> assert_true "single-literal clause is unit" true
   | _ -> assert_true "single-literal clause is unit" false)

let test_pure_literal () =
  Printf.printf "\n--- pure literal elimination ---\n";
  (* x1 appears only positive *)
  let f = [[Pos 1; Pos 2]; [Pos 1; Neg 2]] in
  (match find_pure_literal IntMap.empty f with
   | Some (Pos 1) -> assert_true "x1 is pure positive" true
   | _ -> assert_true "x1 is pure positive" false);
  (* x1 appears both ways -> not pure *)
  let f2 = [[Pos 1]; [Neg 1; Pos 2]] in
  (match find_pure_literal IntMap.empty f2 with
   | Some (Pos 2) -> assert_true "x2 pure, x1 not" true
   | _ -> assert_true "x2 pure, x1 not" false)

let test_solve_simple_sat () =
  Printf.printf "\n--- solve: simple SAT ---\n";
  let f = [[Pos 1; Pos 2]; [Neg 1; Pos 3]; [Neg 2; Neg 3]] in
  match solve f with
  | Satisfiable a ->
    assert_true "satisfiable" true;
    assert_true "solution verifies" (verify f a)
  | Unsatisfiable ->
    assert_true "satisfiable" false

let test_solve_trivial_unsat () =
  Printf.printf "\n--- solve: trivial UNSAT ---\n";
  let f = [[Pos 1]; [Neg 1]] in
  match solve f with
  | Unsatisfiable -> assert_true "unsatisfiable" true
  | Satisfiable _ -> assert_true "unsatisfiable" false

let test_solve_single_var () =
  Printf.printf "\n--- solve: single variable ---\n";
  match solve [[Pos 1]] with
  | Satisfiable a ->
    assert_true "sat with single clause" true;
    assert_equal "x1 = true" (Some true) (IntMap.find_opt 1 a)
  | Unsatisfiable ->
    assert_true "sat with single clause" false

let test_solve_empty_formula () =
  Printf.printf "\n--- solve: empty formula ---\n";
  match solve [] with
  | Satisfiable _ -> assert_true "empty formula is SAT" true
  | Unsatisfiable -> assert_true "empty formula is SAT" false

let test_pigeonhole_unsat () =
  Printf.printf "\n--- pigeonhole principle ---\n";
  (* 3 pigeons, 2 holes -> UNSAT *)
  let f = pigeonhole 2 in
  (match solve f with
   | Unsatisfiable -> assert_true "3 pigeons 2 holes UNSAT" true
   | Satisfiable _ -> assert_true "3 pigeons 2 holes UNSAT" false);
  (* 2 pigeons, 2 holes -> SAT *)
  (* Build manually: each pigeon in at least one hole, no sharing *)
  let var i j = (i - 1) * 2 + j in
  let f2 =
    [[Pos (var 1 1); Pos (var 1 2)];
     [Pos (var 2 1); Pos (var 2 2)];
     [Neg (var 1 1); Neg (var 2 1)];
     [Neg (var 1 2); Neg (var 2 2)]]
  in
  (match solve f2 with
   | Satisfiable a -> assert_true "2 pigeons 2 holes SAT" (verify f2 a)
   | Unsatisfiable -> assert_true "2 pigeons 2 holes SAT" false)

let test_graph_coloring () =
  Printf.printf "\n--- graph coloring ---\n";
  let vc n c = (n - 1) * 3 + c in
  (* Triangle with 3 colors -> SAT *)
  let f =
    [[Pos (vc 1 1); Pos (vc 1 2); Pos (vc 1 3)];
     [Pos (vc 2 1); Pos (vc 2 2); Pos (vc 2 3)];
     [Pos (vc 3 1); Pos (vc 3 2); Pos (vc 3 3)]] @
    List.concat_map (fun (a, b) ->
      List.init 3 (fun c -> [Neg (vc a (c+1)); Neg (vc b (c+1))])
    ) [(1,2); (2,3); (1,3)]
  in
  (match solve f with
   | Satisfiable a ->
     assert_true "triangle 3-color SAT" true;
     assert_true "triangle 3-color verifies" (verify f a)
   | Unsatisfiable ->
     assert_true "triangle 3-color SAT" false);
  (* Triangle with 2 colors -> UNSAT *)
  let vc2 n c = (n - 1) * 2 + c in
  let f2 =
    [[Pos (vc2 1 1); Pos (vc2 1 2)];
     [Pos (vc2 2 1); Pos (vc2 2 2)];
     [Pos (vc2 3 1); Pos (vc2 3 2)]] @
    List.concat_map (fun (a, b) ->
      List.init 2 (fun c -> [Neg (vc2 a (c+1)); Neg (vc2 b (c+1))])
    ) [(1,2); (2,3); (1,3)]
  in
  (match solve f2 with
   | Unsatisfiable -> assert_true "triangle 2-color UNSAT" true
   | Satisfiable _ -> assert_true "triangle 2-color UNSAT" false)

let test_dimacs_parser () =
  Printf.printf "\n--- DIMACS parser ---\n";
  let input = "c comment\np cnf 3 2\n1 -3 0\n2 3 -1 0\n" in
  let f = parse_dimacs input in
  assert_equal "parses 2 clauses" 2 (List.length f);
  (match solve f with
   | Satisfiable a ->
     assert_true "parsed formula SAT" true;
     assert_true "parsed formula verifies" (verify f a)
   | Unsatisfiable ->
     assert_true "parsed formula SAT" false)

let test_verify () =
  Printf.printf "\n--- verify ---\n";
  let f = [[Pos 1; Pos 2]; [Neg 1]] in
  let good = IntMap.add 1 false (IntMap.singleton 2 true) in
  assert_true "correct assignment verifies" (verify f good);
  let bad = IntMap.add 1 true (IntMap.singleton 2 false) in
  assert_true "wrong assignment fails" (not (verify f bad))

let test_random_ksat () =
  Printf.printf "\n--- random k-SAT ---\n";
  Random.init 42;
  let f = random_ksat ~k:3 ~num_vars:10 ~num_clauses:20 in
  assert_equal "generates 20 clauses" 20 (List.length f);
  assert_true "each clause has 3 literals"
    (List.for_all (fun c -> List.length c = 3) f);
  (* Solve it - just check it doesn't crash *)
  (match solve f with
   | Satisfiable a -> assert_true "random SAT verifies" (verify f a)
   | Unsatisfiable -> assert_true "random formula solved (UNSAT)" true)

let test_variables () =
  Printf.printf "\n--- variables ---\n";
  let f = [[Pos 1; Neg 3]; [Pos 2; Pos 1]] in
  let vars = variables f in
  assert_equal "finds 3 variables" 3 (List.length vars);
  assert_true "contains 1" (List.mem 1 vars);
  assert_true "contains 2" (List.mem 2 vars);
  assert_true "contains 3" (List.mem 3 vars)

let () =
  Printf.printf "=== SAT Solver Tests ===\n";
  test_eval_literal ();
  test_eval_clause ();
  test_eval_formula ();
  test_unit_propagation ();
  test_pure_literal ();
  test_solve_simple_sat ();
  test_solve_trivial_unsat ();
  test_solve_single_var ();
  test_solve_empty_formula ();
  test_pigeonhole_unsat ();
  test_graph_coloring ();
  test_dimacs_parser ();
  test_verify ();
  test_random_ksat ();
  test_variables ();
  Printf.printf "\n=== Results: %d passed, %d failed ===\n"
    !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
