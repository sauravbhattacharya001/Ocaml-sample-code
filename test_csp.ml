(* Tests for the CSP solver *)
(* Run: ocamlfind ocamlopt -package ounit2 -linkpkg csp.ml test_csp.ml -o test_csp && ./test_csp *)
(* Or standalone: ocamlfind ocamlopt csp.ml test_csp.ml -o test_csp && ./test_csp *)

(* We use a lightweight inline test framework since ounit2 may not be installed *)

let test_count = ref 0
let pass_count = ref 0
let fail_count = ref 0

let assert_true msg cond =
  incr test_count;
  if cond then incr pass_count
  else begin
    incr fail_count;
    Printf.printf "  FAIL: %s\n" msg
  end

let assert_eq msg expected actual =
  assert_true (Printf.sprintf "%s: expected %d, got %d" msg expected actual)
    (expected = actual)

let assert_some msg = function
  | Some _ -> assert_true msg true
  | None -> assert_true (msg ^ " (expected Some, got None)") false

let assert_none msg = function
  | None -> assert_true msg true
  | Some _ -> assert_true (msg ^ " (expected None, got Some)") false

(* --- Construction tests --- *)

let test_make_csp () =
  print_endline "  Construction tests:";
  let csp = Csp.make_csp ~n_vars:3 ~lo:1 ~hi:3 in
  assert_eq "3 variables" 3 (List.length csp.variables);
  assert_eq "domain size 3" 3
    (Csp.IntSet.cardinal (Csp.IntMap.find 0 csp.domains));
  assert_eq "no constraints" 0 (List.length csp.constraints)

let test_add_neq () =
  let csp = Csp.make_csp ~n_vars:2 ~lo:1 ~hi:3 in
  let csp = Csp.add_neq csp 0 1 in
  (* add_neq adds both forward and reverse *)
  assert_eq "2 constraints (fwd+rev)" 2 (List.length csp.constraints)

let test_add_all_different () =
  let csp = Csp.make_csp ~n_vars:4 ~lo:1 ~hi:4 in
  let csp = Csp.add_all_different csp [0; 1; 2; 3] in
  (* C(4,2) = 6 pairs, each adds 2 constraints = 12 *)
  assert_eq "12 constraints for 4-var alldiff" 12 (List.length csp.constraints)

(* --- Consistency tests --- *)

let test_is_consistent () =
  print_endline "  Consistency tests:";
  let csp = Csp.make_csp ~n_vars:2 ~lo:1 ~hi:3 in
  let csp = Csp.add_neq csp 0 1 in
  let assign = Csp.IntMap.singleton 0 1 in
  assert_true "value 2 consistent with var0=1"
    (Csp.is_consistent csp assign 1 2);
  assert_true "value 1 inconsistent with var0=1"
    (not (Csp.is_consistent csp assign 1 1))

(* --- AC-3 tests --- *)

let test_ac3_basic () =
  print_endline "  AC-3 tests:";
  let csp = Csp.make_csp ~n_vars:2 ~lo:1 ~hi:1 in
  let csp = Csp.add_neq csp 0 1 in
  (* Both variables have domain {1}, but must differ -> inconsistent *)
  let result = Csp.ac3 csp csp.domains in
  assert_none "AC-3 detects inconsistency" result

let test_ac3_reduces_domain () =
  (* var0 in {1}, var1 in {1,2}, var0 != var1 -> var1 reduced to {2} *)
  let csp = Csp.make_csp ~n_vars:2 ~lo:1 ~hi:2 in
  let domains = Csp.IntMap.add 0 (Csp.IntSet.singleton 1) csp.domains in
  let csp = Csp.add_neq csp 0 1 in
  match Csp.ac3 csp domains with
  | None -> assert_true "AC-3 should succeed" false
  | Some (domains', _) ->
    let d1 = Csp.IntMap.find 1 domains' in
    assert_eq "var1 domain reduced to 1 element" 1 (Csp.IntSet.cardinal d1);
    assert_true "var1 domain is {2}" (Csp.IntSet.mem 2 d1)

(* --- Forward checking tests --- *)

let test_forward_check () =
  print_endline "  Forward checking tests:";
  let csp = Csp.make_csp ~n_vars:3 ~lo:1 ~hi:3 in
  let csp = Csp.add_neq csp 0 1 in
  let csp = Csp.add_neq csp 0 2 in
  let assign = Csp.IntMap.singleton 0 1 in
  match Csp.forward_check csp csp.domains assign 0 1 with
  | None -> assert_true "FC should not wipe out" false
  | Some domains' ->
    let d1 = Csp.IntMap.find 1 domains' in
    let d2 = Csp.IntMap.find 2 domains' in
    assert_true "var1 domain excludes 1" (not (Csp.IntSet.mem 1 d1));
    assert_true "var2 domain excludes 1" (not (Csp.IntSet.mem 1 d2));
    assert_eq "var1 domain size 2" 2 (Csp.IntSet.cardinal d1)

let test_forward_check_wipeout () =
  (* var0 in {1}, var1 in {1}, var0 != var1 -> FC wipes out var1 *)
  let csp = Csp.make_csp ~n_vars:2 ~lo:1 ~hi:1 in
  let csp = Csp.add_neq csp 0 1 in
  let assign = Csp.IntMap.singleton 0 1 in
  let result = Csp.forward_check csp csp.domains assign 0 1 in
  assert_none "FC detects wipeout" result

(* --- N-Queens tests --- *)

let test_4_queens () =
  print_endline "  N-Queens tests:";
  let csp = Csp.n_queens 4 in
  let (sol, stats) = Csp.solve csp in
  assert_some "4-Queens has solution" sol;
  assert_true "explored some nodes" (stats.nodes_explored > 0);
  (match sol with
   | Some s ->
     (* Verify no two queens share row, column, or diagonal *)
     let valid = ref true in
     for i = 0 to 3 do
       for j = i + 1 to 3 do
         let ci = Csp.IntMap.find i s in
         let cj = Csp.IntMap.find j s in
         if ci = cj || abs (ci - cj) = j - i then
           valid := false
       done
     done;
     assert_true "4-Queens solution is valid" !valid
   | None -> ())

let test_8_queens () =
  let csp = Csp.n_queens 8 in
  let (sol, _) = Csp.solve csp in
  assert_some "8-Queens has solution" sol

let test_8_queens_all () =
  let all = Csp.solve_all (Csp.n_queens 8) in
  assert_eq "8-Queens has 92 solutions" 92 (List.length all)

let test_3_queens_no_solution () =
  let csp = Csp.n_queens 3 in
  let (sol, _) = Csp.solve csp in
  assert_none "3-Queens has no solution" sol

let test_1_queen () =
  let csp = Csp.n_queens 1 in
  let (sol, _) = Csp.solve csp in
  assert_some "1-Queen has solution" sol

(* --- Graph Coloring tests --- *)

let test_triangle_2_colors () =
  print_endline "  Graph Coloring tests:";
  (* Triangle needs 3 colors, not 2 *)
  let csp = Csp.graph_coloring ~n_nodes:3 ~n_colors:2
    ~edges:[(0,1); (1,2); (0,2)] in
  let (sol, _) = Csp.solve csp in
  assert_none "Triangle not 2-colorable" sol

let test_triangle_3_colors () =
  let csp = Csp.graph_coloring ~n_nodes:3 ~n_colors:3
    ~edges:[(0,1); (1,2); (0,2)] in
  let (sol, _) = Csp.solve csp in
  assert_some "Triangle is 3-colorable" sol;
  (match sol with
   | Some s ->
     let c0 = Csp.IntMap.find 0 s in
     let c1 = Csp.IntMap.find 1 s in
     let c2 = Csp.IntMap.find 2 s in
     assert_true "all different colors" (c0 <> c1 && c1 <> c2 && c0 <> c2)
   | None -> ())

let test_bipartite_2_colors () =
  (* K2,2 is bipartite -> 2-colorable *)
  let csp = Csp.graph_coloring ~n_nodes:4 ~n_colors:2
    ~edges:[(0,2); (0,3); (1,2); (1,3)] in
  let (sol, _) = Csp.solve csp in
  assert_some "K2,2 is 2-colorable" sol

let test_petersen_3_colors () =
  let edges = [
    (0,1); (0,4); (0,5); (1,2); (1,6); (2,3); (2,7);
    (3,4); (3,8); (4,9); (5,7); (5,8); (6,8); (6,9); (7,9)
  ] in
  let csp = Csp.graph_coloring ~n_nodes:10 ~n_colors:3 ~edges in
  let (sol, _) = Csp.solve csp in
  assert_some "Petersen graph is 3-colorable" sol

(* --- Sudoku tests --- *)

let test_sudoku () =
  print_endline "  Sudoku tests:";
  let grid = [|
    [| 5; 3; 0; 0; 7; 0; 0; 0; 0 |];
    [| 6; 0; 0; 1; 9; 5; 0; 0; 0 |];
    [| 0; 9; 8; 0; 0; 0; 0; 6; 0 |];
    [| 8; 0; 0; 0; 6; 0; 0; 0; 3 |];
    [| 4; 0; 0; 8; 0; 3; 0; 0; 1 |];
    [| 7; 0; 0; 0; 2; 0; 0; 0; 6 |];
    [| 0; 6; 0; 0; 0; 0; 2; 8; 0 |];
    [| 0; 0; 0; 4; 1; 9; 0; 0; 5 |];
    [| 0; 0; 0; 0; 8; 0; 0; 7; 9 |]
  |] in
  let csp = Csp.sudoku grid in
  let (sol, _) = Csp.solve csp in
  assert_some "Sudoku has solution" sol;
  (match sol with
   | Some s ->
     (* Verify givens preserved *)
     assert_eq "cell(0,0)=5" 5 (Csp.IntMap.find (Csp.sudoku_var 0 0) s);
     assert_eq "cell(0,1)=3" 3 (Csp.IntMap.find (Csp.sudoku_var 0 1) s);
     assert_eq "cell(0,4)=7" 7 (Csp.IntMap.find (Csp.sudoku_var 0 4) s);
     (* Verify all rows have 1-9 *)
     let valid = ref true in
     for row = 0 to 8 do
       let vals = List.init 9 (fun col ->
         Csp.IntMap.find (Csp.sudoku_var row col) s) in
       let sorted = List.sort compare vals in
       if sorted <> [1;2;3;4;5;6;7;8;9] then valid := false
     done;
     assert_true "All rows have 1-9" !valid;
     (* Verify all columns *)
     let valid = ref true in
     for col = 0 to 8 do
       let vals = List.init 9 (fun row ->
         Csp.IntMap.find (Csp.sudoku_var row col) s) in
       let sorted = List.sort compare vals in
       if sorted <> [1;2;3;4;5;6;7;8;9] then valid := false
     done;
     assert_true "All columns have 1-9" !valid
   | None -> ())

(* --- Heuristic comparison tests --- *)

let test_heuristics_reduce_search () =
  print_endline "  Heuristic comparison tests:";
  let csp = Csp.n_queens 8 in
  let (_, s_naive) = Csp.solve ~use_ac3:false ~use_fc:false ~use_lcv:false csp in
  let (_, s_smart) = Csp.solve ~use_ac3:true ~use_fc:true ~use_lcv:true csp in
  assert_true "Heuristics explore fewer nodes"
    (s_smart.nodes_explored <= s_naive.nodes_explored)

let test_solve_all_with_limit () =
  print_endline "  Solve-all limit tests:";
  let all = Csp.solve_all ~max_solutions:5 (Csp.n_queens 8) in
  assert_eq "max_solutions=5 returns 5" 5 (List.length all)

(* --- Helpers tests --- *)

let test_neighbors () =
  print_endline "  Helper tests:";
  let csp = Csp.make_csp ~n_vars:3 ~lo:1 ~hi:3 in
  let csp = Csp.add_neq csp 0 1 in
  let csp = Csp.add_neq csp 0 2 in
  let nbrs = Csp.neighbors csp 0 in
  assert_eq "var0 has 2 neighbors" 2 (List.length nbrs)

let test_constraints_on () =
  let csp = Csp.make_csp ~n_vars:3 ~lo:1 ~hi:3 in
  let csp = Csp.add_neq csp 0 1 in
  let csp = Csp.add_neq csp 1 2 in
  let cs = Csp.constraints_on csp 1 in
  (* var1 involved in both constraints, each has fwd+rev -> 4 total *)
  assert_eq "var1 has 4 constraint refs" 4 (List.length cs)

let test_render_queens () =
  let assignment = Csp.IntMap.of_seq (List.to_seq [(0,1); (1,3); (2,0); (3,2)]) in
  let board = Csp.render_queens 4 assignment in
  assert_true "board contains Q" (String.contains board 'Q');
  assert_true "board contains ." (String.contains board '.')

let test_empty_csp () =
  (* CSP with 1 variable, domain {1}, no constraints -> trivial *)
  let csp = Csp.make_csp ~n_vars:1 ~lo:1 ~hi:1 in
  let (sol, _) = Csp.solve csp in
  assert_some "Trivial CSP solvable" sol

let () =
  print_endline "\n=== CSP Solver Tests ===\n";
  test_make_csp ();
  test_add_neq ();
  test_add_all_different ();
  test_is_consistent ();
  test_ac3_basic ();
  test_ac3_reduces_domain ();
  test_forward_check ();
  test_forward_check_wipeout ();
  test_4_queens ();
  test_8_queens ();
  test_8_queens_all ();
  test_3_queens_no_solution ();
  test_1_queen ();
  test_triangle_2_colors ();
  test_triangle_3_colors ();
  test_bipartite_2_colors ();
  test_petersen_3_colors ();
  test_sudoku ();
  test_heuristics_reduce_search ();
  test_solve_all_with_limit ();
  test_neighbors ();
  test_constraints_on ();
  test_render_queens ();
  test_empty_csp ();
  Printf.printf "\n=== Results: %d/%d passed" !pass_count !test_count;
  if !fail_count > 0 then
    Printf.printf ", %d FAILED" !fail_count;
  print_endline " ==="
