(* test_constraint.ml — Tests for CSP Solver *)

(* ── Inline the CSP module ─────────────────────────────────── *)

module CSP = struct
  type variable = string
  type domain = int list
  type constraint_t = {
    scope : variable list;
    test  : int list -> bool;
  }
  type t = {
    variables   : variable list;
    domains     : (variable, domain) Hashtbl.t;
    constraints : constraint_t list;
    neighbors   : (variable, variable list) Hashtbl.t;
  }
  type assignment = (variable * int) list

  let create () = {
    variables   = [];
    domains     = Hashtbl.create 16;
    constraints = [];
    neighbors   = Hashtbl.create 16;
  }

  let add_variable name domain csp =
    Hashtbl.replace csp.domains name domain;
    if not (Hashtbl.mem csp.neighbors name) then
      Hashtbl.replace csp.neighbors name [];
    { csp with variables = name :: csp.variables }

  let add_constraint scope test csp =
    let c = { scope; test } in
    List.iter (fun v ->
      List.iter (fun u ->
        if u <> v then begin
          let cur = try Hashtbl.find csp.neighbors v with Not_found -> [] in
          if not (List.mem u cur) then
            Hashtbl.replace csp.neighbors v (u :: cur)
        end
      ) scope
    ) scope;
    { csp with constraints = c :: csp.constraints }

  let add_all_different vars csp =
    let rec pairs = function
      | [] -> []
      | x :: rest -> List.map (fun y -> (x, y)) rest @ pairs rest
    in
    List.fold_left (fun csp (a, b) ->
      add_constraint [a; b] (function
        | [x; y] -> x <> y
        | _ -> false
      ) csp
    ) csp (pairs vars)

  let copy_domains doms =
    let d = Hashtbl.create (Hashtbl.length doms) in
    Hashtbl.iter (fun k v -> Hashtbl.replace d k v) doms;
    d

  let domain_sizes csp =
    List.map (fun v ->
      let dom = try Hashtbl.find csp.domains v with Not_found -> [] in
      (v, List.length dom)
    ) csp.variables

  let binary_constraints_for csp xi xj =
    List.filter (fun c ->
      List.length c.scope = 2 &&
      List.mem xi c.scope && List.mem xj c.scope
    ) csp.constraints

  let revise domains constraints xi xj =
    let di = try Hashtbl.find domains xi with Not_found -> [] in
    let dj = try Hashtbl.find domains xj with Not_found -> [] in
    let revised = ref false in
    let new_di = List.filter (fun vi ->
      let has_support = List.exists (fun vj ->
        List.for_all (fun c ->
          let args = List.map (fun s ->
            if s = xi then vi else if s = xj then vj else 0
          ) c.scope in
          c.test args
        ) constraints
      ) dj in
      if not has_support then (revised := true; false)
      else true
    ) di in
    if !revised then
      Hashtbl.replace domains xi new_di;
    !revised

  let ac3 csp domains =
    let queue = Queue.create () in
    List.iter (fun v ->
      let nbrs = try Hashtbl.find csp.neighbors v with Not_found -> [] in
      List.iter (fun u -> Queue.push (v, u) queue) nbrs
    ) csp.variables;
    let result = ref true in
    while not (Queue.is_empty queue) && !result do
      let (xi, xj) = Queue.pop queue in
      let constraints = binary_constraints_for csp xi xj in
      if constraints <> [] && revise domains constraints xi xj then begin
        let di = try Hashtbl.find domains xi with Not_found -> [] in
        if di = [] then
          result := false
        else begin
          let nbrs = try Hashtbl.find csp.neighbors xi with Not_found -> [] in
          List.iter (fun xk ->
            if xk <> xj then Queue.push (xk, xi) queue
          ) nbrs
        end
      end
    done;
    !result

  let is_consistent assignment csp =
    List.for_all (fun c ->
      let bound = List.filter_map (fun v ->
        List.assoc_opt v assignment
      ) c.scope in
      if List.length bound < List.length c.scope then true
      else c.test bound
    ) csp.constraints

  let select_unassigned assignment domains variables =
    let unassigned = List.filter (fun v ->
      not (List.mem_assoc v assignment)
    ) variables in
    match unassigned with
    | [] -> None
    | _ ->
      let best = List.fold_left (fun acc v ->
        let size = List.length (
          try Hashtbl.find domains v with Not_found -> []
        ) in
        match acc with
        | None -> Some (v, size)
        | Some (_, best_size) ->
          if size < best_size then Some (v, size) else acc
      ) None unassigned in
      Option.map fst best

  let order_domain_values var _assignment csp domains =
    let dom = try Hashtbl.find domains var with Not_found -> [] in
    let nbrs = try Hashtbl.find csp.neighbors var with Not_found -> [] in
    if List.length dom <= 1 || nbrs = [] then dom
    else
      let scored = List.map (fun val_ ->
        let conflicts = List.fold_left (fun acc nbr ->
          let nbr_dom = try Hashtbl.find domains nbr with Not_found -> [] in
          let remaining = List.filter (fun nv ->
            let constraints = binary_constraints_for csp var nbr in
            List.for_all (fun c ->
              let args = List.map (fun s ->
                if s = var then val_ else if s = nbr then nv else 0
              ) c.scope in
              c.test args
            ) constraints
          ) nbr_dom in
          acc + (List.length nbr_dom - List.length remaining)
        ) 0 nbrs in
        (val_, conflicts)
      ) dom in
      List.map fst (List.sort (fun (_, a) (_, b) -> compare a b) scored)

  let rec backtrack csp domains assignment collect_all solutions =
    if List.length assignment = List.length csp.variables then begin
      solutions := assignment :: !solutions;
      collect_all
    end else
      match select_unassigned assignment domains csp.variables with
      | None -> false
      | Some var ->
        let values = order_domain_values var assignment csp domains in
        let found = ref false in
        let i = ref 0 in
        while !i < List.length values && (not !found || collect_all) do
          let value = List.nth values !i in
          let new_assignment = (var, value) :: assignment in
          if is_consistent new_assignment csp then begin
            let new_domains = copy_domains domains in
            Hashtbl.replace new_domains var [value];
            if ac3 csp new_domains then begin
              if backtrack csp new_domains new_assignment collect_all solutions then
                found := true
            end
          end;
          incr i
        done;
        !found

  let solve csp =
    let domains = copy_domains csp.domains in
    if not (ac3 csp domains) then None
    else begin
      let solutions = ref [] in
      let _ = backtrack csp domains [] false solutions in
      match !solutions with
      | [] -> None
      | s :: _ -> Some (List.rev s)
    end

  let solve_all csp =
    let domains = copy_domains csp.domains in
    if not (ac3 csp domains) then []
    else begin
      let solutions = ref [] in
      let _ = backtrack csp domains [] true solutions in
      List.map List.rev !solutions
    end
end

(* ── N-Queens builder ─────────────────────────────────────── *)

module NQueens = struct
  open CSP

  let queen i = Printf.sprintf "Q%d" i

  let make n =
    let csp = ref (create ()) in
    let domain = List.init n Fun.id in
    for i = 0 to n - 1 do
      csp := add_variable (queen i) domain !csp
    done;
    for i = 0 to n - 2 do
      for j = i + 1 to n - 1 do
        let qi = queen i and qj = queen j in
        let diff = j - i in
        csp := add_constraint [qi; qj] (function
          | [ci; cj] -> ci <> cj && abs (ci - cj) <> diff
          | _ -> false
        ) !csp
      done
    done;
    !csp
end

(* ── Test framework ───────────────────────────────────────── *)

let passed = ref 0
let failed = ref 0
let total  = ref 0

let assert_equal ~msg expected actual =
  incr total;
  if expected = actual then incr passed
  else begin
    incr failed;
    Printf.printf "  FAIL: %s — expected %d, got %d\n" msg expected actual
  end

let assert_true ~msg cond =
  incr total;
  if cond then incr passed
  else begin
    incr failed;
    Printf.printf "  FAIL: %s\n" msg
  end

let assert_none ~msg = function
  | None -> incr total; incr passed
  | Some _ -> incr total; incr failed; Printf.printf "  FAIL: %s — expected None\n" msg

let assert_some ~msg = function
  | Some v -> incr total; incr passed; v
  | None -> incr total; incr failed; Printf.printf "  FAIL: %s — expected Some\n" msg; []

let suite name f =
  Printf.printf "--- %s ---\n" name;
  f ()

(* ── Tests ────────────────────────────────────────────────── *)

let test_create_empty () = suite "Create empty CSP" (fun () ->
  let csp = CSP.create () in
  assert_equal ~msg:"no variables" 0 (List.length csp.variables);
  assert_equal ~msg:"no constraints" 0 (List.length csp.constraints);
)

let test_add_variables () = suite "Add variables" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [1; 2; 3] csp in
  let csp = CSP.add_variable "Y" [4; 5] csp in
  assert_equal ~msg:"2 variables" 2 (List.length csp.variables);
  let sizes = CSP.domain_sizes csp in
  let x_size = List.assoc "X" sizes in
  let y_size = List.assoc "Y" sizes in
  assert_equal ~msg:"X domain 3" 3 x_size;
  assert_equal ~msg:"Y domain 2" 2 y_size;
)

let test_simple_binary () = suite "Simple binary constraint" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [1; 2; 3] csp in
  let csp = CSP.add_variable "Y" [1; 2; 3] csp in
  let csp = CSP.add_constraint ["X"; "Y"] (function
    | [x; y] -> x < y
    | _ -> false
  ) csp in
  let sol = CSP.solve csp in
  let sol = assert_some ~msg:"has solution" sol in
  let x = List.assoc "X" sol in
  let y = List.assoc "Y" sol in
  assert_true ~msg:"x < y" (x < y);
)

let test_all_different () = suite "All-different constraint" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "A" [1; 2; 3] csp in
  let csp = CSP.add_variable "B" [1; 2; 3] csp in
  let csp = CSP.add_variable "C" [1; 2; 3] csp in
  let csp = CSP.add_all_different ["A"; "B"; "C"] csp in
  let sols = CSP.solve_all csp in
  (* 3! = 6 permutations *)
  assert_equal ~msg:"6 solutions" 6 (List.length sols);
  (* Each solution has all different values *)
  List.iter (fun sol ->
    let a = List.assoc "A" sol in
    let b = List.assoc "B" sol in
    let c = List.assoc "C" sol in
    assert_true ~msg:"all different" (a <> b && b <> c && a <> c)
  ) sols;
)

let test_unsolvable () = suite "Unsolvable CSP" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [1] csp in
  let csp = CSP.add_variable "Y" [1] csp in
  let csp = CSP.add_all_different ["X"; "Y"] csp in
  assert_none ~msg:"no solution" (CSP.solve csp);
)

let test_single_variable () = suite "Single variable" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [42] csp in
  let sol = assert_some ~msg:"has solution" (CSP.solve csp) in
  assert_equal ~msg:"X = 42" 42 (List.assoc "X" sol);
)

let test_empty_domain () = suite "Empty domain" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [] csp in
  assert_none ~msg:"empty domain unsolvable" (CSP.solve csp);
)

let test_4_queens () = suite "4-Queens" (fun () ->
  let csp = NQueens.make 4 in
  let sol = assert_some ~msg:"has solution" (CSP.solve csp) in
  (* Verify no two queens attack each other *)
  for i = 0 to 3 do
    for j = i + 1 to 3 do
      let ci = List.assoc (NQueens.queen i) sol in
      let cj = List.assoc (NQueens.queen j) sol in
      assert_true ~msg:(Printf.sprintf "Q%d,Q%d not same col" i j) (ci <> cj);
      assert_true ~msg:(Printf.sprintf "Q%d,Q%d not diagonal" i j)
        (abs (ci - cj) <> j - i)
    done
  done;
)

let test_4_queens_count () = suite "4-Queens all solutions" (fun () ->
  let sols = CSP.solve_all (NQueens.make 4) in
  assert_equal ~msg:"2 solutions" 2 (List.length sols);
)

let test_8_queens () = suite "8-Queens" (fun () ->
  let csp = NQueens.make 8 in
  let sol = CSP.solve csp in
  assert_true ~msg:"has solution" (sol <> None);
  (match sol with
   | None -> ()
   | Some s ->
     (* Verify valid placement *)
     for i = 0 to 7 do
       let ci = List.assoc (NQueens.queen i) s in
       assert_true ~msg:(Printf.sprintf "Q%d in range" i) (ci >= 0 && ci < 8)
     done);
)

let test_3_queens_impossible () = suite "3-Queens (no solution)" (fun () ->
  let csp = NQueens.make 3 in
  assert_none ~msg:"3-queens unsolvable" (CSP.solve csp);
)

let test_1_queen () = suite "1-Queen" (fun () ->
  let csp = NQueens.make 1 in
  let sol = assert_some ~msg:"trivial" (CSP.solve csp) in
  assert_equal ~msg:"Q0 = 0" 0 (List.assoc "Q0" sol);
)

let test_map_coloring () = suite "Map coloring (Australia)" (fun () ->
  let regions = ["WA"; "NT"; "SA"; "Q"; "NSW"; "V"; "T"] in
  let borders = [
    ("WA", "NT"); ("WA", "SA"); ("NT", "SA"); ("NT", "Q");
    ("SA", "Q"); ("SA", "NSW"); ("SA", "V"); ("Q", "NSW"); ("NSW", "V")
  ] in
  let colors = List.init 3 Fun.id in
  let csp = ref (CSP.create ()) in
  List.iter (fun r -> csp := CSP.add_variable r colors !csp) regions;
  List.iter (fun (a, b) ->
    csp := CSP.add_constraint [a; b] (function
      | [x; y] -> x <> y | _ -> false
    ) !csp
  ) borders;
  let sol = assert_some ~msg:"3-colorable" (CSP.solve !csp) in
  (* Verify no two adjacent regions have same color *)
  List.iter (fun (a, b) ->
    let ca = List.assoc a sol in
    let cb = List.assoc b sol in
    assert_true ~msg:(Printf.sprintf "%s <> %s" a b) (ca <> cb)
  ) borders;
)

let test_map_2_colors_fail () = suite "Map coloring 2 colors (fails)" (fun () ->
  (* Triangle graph needs 3 colors *)
  let regions = ["A"; "B"; "C"] in
  let borders = [("A", "B"); ("B", "C"); ("A", "C")] in
  let colors = List.init 2 Fun.id in
  let csp = ref (CSP.create ()) in
  List.iter (fun r -> csp := CSP.add_variable r colors !csp) regions;
  List.iter (fun (a, b) ->
    csp := CSP.add_constraint [a; b] (function
      | [x; y] -> x <> y | _ -> false
    ) !csp
  ) borders;
  assert_none ~msg:"triangle not 2-colorable" (CSP.solve !csp);
)

let test_is_consistent () = suite "is_consistent" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [1; 2] csp in
  let csp = CSP.add_variable "Y" [1; 2] csp in
  let csp = CSP.add_constraint ["X"; "Y"] (function
    | [x; y] -> x <> y | _ -> false
  ) csp in
  assert_true ~msg:"consistent partial" (CSP.is_consistent [("X", 1)] csp);
  assert_true ~msg:"consistent full" (CSP.is_consistent [("X", 1); ("Y", 2)] csp);
  assert_true ~msg:"inconsistent full" (not (CSP.is_consistent [("X", 1); ("Y", 1)] csp));
)

let test_solve_all_empty () = suite "solve_all on unsolvable" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [1] csp in
  let csp = CSP.add_variable "Y" [1] csp in
  let csp = CSP.add_all_different ["X"; "Y"] csp in
  let sols = CSP.solve_all csp in
  assert_equal ~msg:"0 solutions" 0 (List.length sols);
)

let test_chain_constraints () = suite "Chain constraints X < Y < Z" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [1; 2; 3; 4; 5] csp in
  let csp = CSP.add_variable "Y" [1; 2; 3; 4; 5] csp in
  let csp = CSP.add_variable "Z" [1; 2; 3; 4; 5] csp in
  let csp = CSP.add_constraint ["X"; "Y"] (function
    | [x; y] -> x < y | _ -> false
  ) csp in
  let csp = CSP.add_constraint ["Y"; "Z"] (function
    | [y; z] -> y < z | _ -> false
  ) csp in
  let sols = CSP.solve_all csp in
  (* C(5,3) = 10 strictly increasing triples *)
  assert_equal ~msg:"10 solutions" 10 (List.length sols);
  List.iter (fun sol ->
    let x = List.assoc "X" sol in
    let y = List.assoc "Y" sol in
    let z = List.assoc "Z" sol in
    assert_true ~msg:"x < y < z" (x < y && y < z)
  ) sols;
)

let test_ac3_prunes () = suite "AC-3 prunes infeasible values" (fun () ->
  (* X in {1,2,3}, Y in {1,2,3}, X = Y+1
     After AC-3: X in {2,3}, Y in {1,2} *)
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [1; 2; 3] csp in
  let csp = CSP.add_variable "Y" [1; 2; 3] csp in
  let csp = CSP.add_constraint ["X"; "Y"] (function
    | [x; y] -> x = y + 1 | _ -> false
  ) csp in
  let sols = CSP.solve_all csp in
  assert_equal ~msg:"2 solutions" 2 (List.length sols);
  (* (X=2,Y=1) and (X=3,Y=2) *)
  let valid = List.for_all (fun sol ->
    let x = List.assoc "X" sol in
    let y = List.assoc "Y" sol in
    x = y + 1
  ) sols in
  assert_true ~msg:"all satisfy X=Y+1" valid;
)

let test_multiple_constraints_same_pair () = suite "Multiple constraints on pair" (fun () ->
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" [1; 2; 3; 4; 5] csp in
  let csp = CSP.add_variable "Y" [1; 2; 3; 4; 5] csp in
  (* X < Y AND X + Y = 5 *)
  let csp = CSP.add_constraint ["X"; "Y"] (function
    | [x; y] -> x < y | _ -> false
  ) csp in
  let csp = CSP.add_constraint ["X"; "Y"] (function
    | [x; y] -> x + y = 5 | _ -> false
  ) csp in
  let sols = CSP.solve_all csp in
  (* (1,4) and (2,3) *)
  assert_equal ~msg:"2 solutions" 2 (List.length sols);
)

let test_large_domain () = suite "Large domain pruning" (fun () ->
  (* X, Y each in 1..20, X + Y = 21, X < Y *)
  let dom = List.init 20 (fun i -> i + 1) in
  let csp = CSP.create () in
  let csp = CSP.add_variable "X" dom csp in
  let csp = CSP.add_variable "Y" dom csp in
  let csp = CSP.add_constraint ["X"; "Y"] (function
    | [x; y] -> x + y = 21 | _ -> false
  ) csp in
  let csp = CSP.add_constraint ["X"; "Y"] (function
    | [x; y] -> x < y | _ -> false
  ) csp in
  let sols = CSP.solve_all csp in
  (* (1,20), (2,19), ..., (10,11) = 10 solutions *)
  assert_equal ~msg:"10 solutions" 10 (List.length sols);
)

(* ── Main ─────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== CSP Solver Tests ===\n\n";
  test_create_empty ();
  test_add_variables ();
  test_simple_binary ();
  test_all_different ();
  test_unsolvable ();
  test_single_variable ();
  test_empty_domain ();
  test_4_queens ();
  test_4_queens_count ();
  test_8_queens ();
  test_3_queens_impossible ();
  test_1_queen ();
  test_map_coloring ();
  test_map_2_colors_fail ();
  test_is_consistent ();
  test_solve_all_empty ();
  test_chain_constraints ();
  test_ac3_prunes ();
  test_multiple_constraints_same_pair ();
  test_large_domain ();
  Printf.printf "\n=== Results: %d/%d passed, %d failed ===\n" !passed !total !failed;
  if !failed > 0 then exit 1
