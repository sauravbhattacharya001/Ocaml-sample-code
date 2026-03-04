(* Constraint Satisfaction Problem (CSP) Solver *)
(* Demonstrates: backtracking search, arc consistency (AC-3),
   constraint propagation, domain reduction, variable ordering heuristics
   (MRV / degree), value ordering (LCV), forward checking.

   Applications: Sudoku, N-Queens, graph coloring, scheduling.

   Key concepts:
   - A CSP has variables, each with a finite domain of possible values
   - Constraints restrict which combinations of values are allowed
   - Backtracking systematically tries assignments, pruning dead ends
   - Arc consistency preemptively removes impossible values
   - Heuristics (MRV, LCV) dramatically reduce search space *)

(* --- Core types --- *)

module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

(** A variable is identified by an integer. *)
type variable = int

(** A domain is a set of possible values for a variable. *)
type domain = IntSet.t

(** A binary constraint between two variables.
    [satisfied a b] returns true if assigning [a] to var1 and [b] to var2
    is consistent. *)
type constraint_fn = int -> int -> bool

(** A binary constraint record. *)
type binary_constraint = {
  var1 : variable;
  var2 : variable;
  check : constraint_fn;
}

(** A CSP problem definition. *)
type csp = {
  variables : variable list;
  domains : domain IntMap.t;
  constraints : binary_constraint list;
}

(** An assignment maps variables to values. *)
type assignment = int IntMap.t

(** Search statistics. *)
type stats = {
  nodes_explored : int;
  backtracks : int;
  arc_revisions : int;
  solutions_found : int;
}

let empty_stats = {
  nodes_explored = 0;
  backtracks = 0;
  arc_revisions = 0;
  solutions_found = 0;
}

(* --- CSP construction helpers --- *)

(** Create a CSP with the given variable count and uniform domain [lo..hi]. *)
let make_csp ~n_vars ~lo ~hi : csp =
  let vars = List.init n_vars (fun i -> i) in
  let dom = IntSet.of_list (List.init (hi - lo + 1) (fun i -> i + lo)) in
  let domains = List.fold_left (fun m v -> IntMap.add v dom m) IntMap.empty vars in
  { variables = vars; domains; constraints = [] }

(** Add a binary constraint to a CSP. *)
let add_constraint csp c1 c2 check =
  let fwd = { var1 = c1; var2 = c2; check } in
  let rev = { var1 = c2; var2 = c1; check = (fun a b -> check b a) } in
  { csp with constraints = fwd :: rev :: csp.constraints }

(** Add a "not equal" constraint between two variables. *)
let add_neq csp v1 v2 =
  add_constraint csp v1 v2 (fun a b -> a <> b)

(** Add an "all different" constraint across a list of variables. *)
let add_all_different csp vars =
  let rec pairs = function
    | [] -> []
    | x :: rest -> List.map (fun y -> (x, y)) rest @ pairs rest
  in
  List.fold_left (fun csp (v1, v2) -> add_neq csp v1 v2) csp (pairs vars)

(** Get neighbors of a variable (connected by any constraint). *)
let neighbors csp var =
  List.fold_left (fun acc c ->
    if c.var1 = var then IntSet.add c.var2 acc
    else if c.var2 = var then IntSet.add c.var1 acc
    else acc
  ) IntSet.empty csp.constraints
  |> IntSet.elements

(* --- Consistency checking --- *)

(** Check if assigning [value] to [var] is consistent with current assignment. *)
let is_consistent csp assignment var value =
  List.for_all (fun c ->
    if c.var1 = var then
      match IntMap.find_opt c.var2 assignment with
      | None -> true
      | Some v2 -> c.check value v2
    else if c.var2 = var then
      match IntMap.find_opt c.var1 assignment with
      | None -> true
      | Some v1 -> c.check v1 value
    else true
  ) csp.constraints

(* --- Arc Consistency (AC-3) --- *)

(** Revise the domain of var1 w.r.t. var2 under constraint c.
    Removes values from var1's domain that have no support in var2's domain.
    Returns (revised_domain, was_revised). *)
let revise domains c =
  let d1 = IntMap.find c.var1 domains in
  let d2 = IntMap.find c.var2 domains in
  let revised = IntSet.filter (fun x ->
    IntSet.exists (fun y -> c.check x y) d2
  ) d1 in
  if IntSet.cardinal revised < IntSet.cardinal d1 then
    (IntMap.add c.var1 revised domains, true)
  else
    (domains, false)

(** AC-3 algorithm: enforce arc consistency across all constraints.
    Returns None if any domain becomes empty (inconsistency detected),
    or Some (reduced_domains, revision_count). *)
let ac3 csp domains =
  let queue = Queue.create () in
  List.iter (fun c -> Queue.push c queue) csp.constraints;
  let rec loop domains revisions =
    if Queue.is_empty queue then Some (domains, revisions)
    else
      let c = Queue.pop queue in
      let (domains', was_revised) = revise domains c in
      if was_revised then begin
        let d1 = IntMap.find c.var1 domains' in
        if IntSet.is_empty d1 then None
        else begin
          List.iter (fun c2 ->
            if c2.var2 = c.var1 && c2.var1 <> c.var2 then
              Queue.push c2 queue
          ) csp.constraints;
          loop domains' (revisions + 1)
        end
      end else
        loop domains (revisions)
  in
  loop domains 0

(* --- Variable ordering heuristics --- *)

(** Minimum Remaining Values (MRV): choose the variable with the smallest
    domain. Ties broken by degree heuristic (most constraints). *)
let select_mrv csp domains assignment =
  let unassigned = List.filter
    (fun v -> not (IntMap.mem v assignment)) csp.variables in
  match unassigned with
  | [] -> None
  | _ ->
    let scored = List.map (fun v ->
      let dom_size = IntSet.cardinal (IntMap.find v domains) in
      let degree = List.length (
        List.filter (fun c ->
          (c.var1 = v && not (IntMap.mem c.var2 assignment)) ||
          (c.var2 = v && not (IntMap.mem c.var1 assignment))
        ) csp.constraints
      ) in
      (v, dom_size, -degree)
    ) unassigned in
    let best = List.fold_left (fun ((_, s1, d1) as acc) ((_, s2, d2) as cur) ->
      if s2 < s1 || (s2 = s1 && d2 < d1) then cur else acc
    ) (List.hd scored) (List.tl scored) in
    let (v, _, _) = best in
    Some v

(** Least Constraining Value (LCV): order values by how many options
    they leave for neighboring variables (most options first). *)
let order_lcv csp domains assignment var =
  let dom = IntMap.find var domains in
  let vals = IntSet.elements dom in
  let scored = List.map (fun value ->
    let ruled_out = List.fold_left (fun acc c ->
      let neighbor =
        if c.var1 = var then Some c.var2
        else if c.var2 = var then Some c.var1
        else None
      in
      match neighbor with
      | None -> acc
      | Some n ->
        if IntMap.mem n assignment then acc
        else
          let n_dom = IntMap.find n domains in
          let eliminated = IntSet.cardinal n_dom -
            IntSet.cardinal (IntSet.filter (fun nv ->
              if c.var1 = var then c.check value nv
              else c.check nv value
            ) n_dom) in
          acc + eliminated
    ) 0 csp.constraints in
    (value, ruled_out)
  ) vals in
  List.sort (fun (_, a) (_, b) -> compare a b) scored
  |> List.map fst

(* --- Forward checking --- *)

(** After assigning [value] to [var], prune domains of unassigned neighbors.
    Returns None if any neighbor's domain becomes empty. *)
let forward_check csp domains assignment var value =
  List.fold_left (fun acc c ->
    match acc with
    | None -> None
    | Some domains ->
      let neighbor =
        if c.var1 = var then Some (c.var2, fun _v nv -> c.check value nv)
        else if c.var2 = var then Some (c.var1, fun nv _v -> c.check nv value)
        else None
      in
      match neighbor with
      | None -> Some domains
      | Some (n, check_fn) ->
        if IntMap.mem n assignment then Some domains
        else
          let n_dom = IntMap.find n domains in
          let pruned = IntSet.filter (fun nv -> check_fn nv value) n_dom in
          if IntSet.is_empty pruned then None
          else Some (IntMap.add n pruned domains)
  ) (Some domains) csp.constraints

(* --- Backtracking solver --- *)

(** Solve a CSP using backtracking with MRV, LCV, forward checking, and AC-3.
    Returns the first solution found, or None. *)
let solve ?(use_ac3=true) ?(use_fc=true) ?(use_lcv=true) csp =
  let initial_domains, initial_revisions =
    if use_ac3 then
      match ac3 csp csp.domains with
      | None -> (csp.domains, 0)
      | Some (d, r) -> (d, r)
    else (csp.domains, 0)
  in
  let stats = ref { empty_stats with arc_revisions = initial_revisions } in
  let rec backtrack assignment domains =
    stats := { !stats with nodes_explored = !stats.nodes_explored + 1 };
    if IntMap.cardinal assignment = List.length csp.variables then
      Some assignment
    else
      match select_mrv csp domains assignment with
      | None -> None
      | Some var ->
        let values =
          if use_lcv then order_lcv csp domains assignment var
          else IntSet.elements (IntMap.find var domains)
        in
        let rec try_values = function
          | [] ->
            stats := { !stats with backtracks = !stats.backtracks + 1 };
            None
          | value :: rest ->
            if is_consistent csp assignment var value then begin
              let assignment' = IntMap.add var value assignment in
              let result =
                if use_fc then
                  match forward_check csp domains assignment' var value with
                  | None -> None
                  | Some domains' -> backtrack assignment' domains'
                else
                  backtrack assignment' domains
              in
              match result with
              | Some _ as sol -> sol
              | None -> try_values rest
            end else
              try_values rest
        in
        try_values values
  in
  let solution = backtrack IntMap.empty initial_domains in
  (solution, !stats)

(** Find all solutions to a CSP. *)
let solve_all ?(use_ac3=true) ?(use_fc=true) ?(max_solutions=max_int) csp =
  let initial_domains =
    if use_ac3 then
      match ac3 csp csp.domains with
      | None -> csp.domains
      | Some (d, _) -> d
    else csp.domains
  in
  let solutions = ref [] in
  let count = ref 0 in
  let rec backtrack assignment domains =
    if !count >= max_solutions then ()
    else if IntMap.cardinal assignment = List.length csp.variables then begin
      solutions := assignment :: !solutions;
      incr count
    end else
      match select_mrv csp domains assignment with
      | None -> ()
      | Some var ->
        let values = IntSet.elements (IntMap.find var domains) in
        List.iter (fun value ->
          if !count < max_solutions && is_consistent csp assignment var value then
            let assignment' = IntMap.add var value assignment in
            match forward_check csp domains assignment' var value with
            | None -> ()
            | Some domains' -> backtrack assignment' domains'
        ) values
  in
  backtrack IntMap.empty initial_domains;
  List.rev !solutions

(* --- Application: N-Queens --- *)

(** Create an N-Queens CSP.
    Variables 0..n-1 represent rows; values represent column placement. *)
let n_queens n =
  let csp = make_csp ~n_vars:n ~lo:0 ~hi:(n - 1) in
  let rec add_pairs csp i =
    if i >= n then csp
    else
      let rec add_j csp j =
        if j >= n then csp
        else
          let diff = j - i in
          let csp = add_constraint csp i j (fun ci cj ->
            ci <> cj &&
            abs (ci - cj) <> diff
          ) in
          add_j csp (j + 1)
      in
      add_pairs (add_j csp (i + 1)) (i + 1)
  in
  add_pairs csp 0

(** Render an N-Queens solution as a board string. *)
let render_queens n assignment =
  let buf = Buffer.create (n * (n + 1)) in
  for row = 0 to n - 1 do
    let col = IntMap.find row assignment in
    for c = 0 to n - 1 do
      Buffer.add_char buf (if c = col then 'Q' else '.');
    done;
    Buffer.add_char buf '\n'
  done;
  Buffer.contents buf

(* --- Application: Graph Coloring --- *)

(** Create a graph coloring CSP.
    [n_nodes] nodes, [n_colors] colors, [edges] as (i, j) pairs. *)
let graph_coloring ~n_nodes ~n_colors ~edges =
  let csp = make_csp ~n_vars:n_nodes ~lo:0 ~hi:(n_colors - 1) in
  List.fold_left (fun csp (i, j) -> add_neq csp i j) csp edges

(** Render a graph coloring as a string. *)
let render_coloring n_nodes assignment color_names =
  let buf = Buffer.create 256 in
  for i = 0 to n_nodes - 1 do
    let c = IntMap.find i assignment in
    let name = if c < Array.length color_names then color_names.(c)
               else Printf.sprintf "Color%d" c in
    Buffer.add_string buf (Printf.sprintf "  Node %d: %s\n" i name)
  done;
  Buffer.contents buf

(* --- Application: Sudoku --- *)

(** Variable index for Sudoku: row * 9 + col. *)
let sudoku_var row col = row * 9 + col

(** Create a Sudoku CSP from a 9x9 grid (0 = empty). *)
let sudoku grid =
  let csp = make_csp ~n_vars:81 ~lo:1 ~hi:9 in
  let domains = Array.fold_left (fun (domains, idx) row ->
    Array.fold_left (fun (domains, idx) value ->
      if value > 0 then
        (IntMap.add idx (IntSet.singleton value) domains, idx + 1)
      else
        (domains, idx + 1)
    ) (domains, idx) row
  ) (csp.domains, 0) grid |> fst in
  let csp = { csp with domains } in
  let csp = List.fold_left (fun csp row ->
    let vars = List.init 9 (fun col -> sudoku_var row col) in
    add_all_different csp vars
  ) csp (List.init 9 (fun i -> i)) in
  let csp = List.fold_left (fun csp col ->
    let vars = List.init 9 (fun row -> sudoku_var row col) in
    add_all_different csp vars
  ) csp (List.init 9 (fun i -> i)) in
  let csp = List.fold_left (fun csp box ->
    let br = (box / 3) * 3 in
    let bc = (box mod 3) * 3 in
    let vars = List.init 9 (fun i ->
      sudoku_var (br + i / 3) (bc + i mod 3)
    ) in
    add_all_different csp vars
  ) csp (List.init 9 (fun i -> i)) in
  csp

(** Render a Sudoku solution as a formatted grid. *)
let render_sudoku assignment =
  let buf = Buffer.create 256 in
  for row = 0 to 8 do
    if row > 0 && row mod 3 = 0 then
      Buffer.add_string buf "  ------+-------+------\n";
    Buffer.add_string buf "  ";
    for col = 0 to 8 do
      if col > 0 && col mod 3 = 0 then
        Buffer.add_string buf "| ";
      let v = IntMap.find (sudoku_var row col) assignment in
      Buffer.add_string buf (Printf.sprintf "%d " v)
    done;
    Buffer.add_char buf '\n'
  done;
  Buffer.contents buf

(* --- Demo / CLI --- *)

let () =
  print_endline "=== CSP Solver ===";
  print_endline "Constraint Satisfaction Problems: backtracking + AC-3 + MRV + LCV\n";

  print_endline "--- 8-Queens ---";
  let csp8 = n_queens 8 in
  let t0 = Sys.time () in
  let (solution, stats) = solve csp8 in
  let elapsed = Sys.time () -. t0 in
  (match solution with
   | Some s ->
     print_string (render_queens 8 s);
     Printf.printf "  Nodes: %d, Backtracks: %d, Time: %.4fs\n"
       stats.nodes_explored stats.backtracks elapsed
   | None -> print_endline "  No solution found.");
  print_newline ();

  let t0 = Sys.time () in
  let all_sols = solve_all (n_queens 8) in
  let elapsed = Sys.time () -. t0 in
  Printf.printf "  Total 8-Queens solutions: %d (%.4fs)\n\n"
    (List.length all_sols) elapsed;

  print_endline "--- 12-Queens ---";
  let t0 = Sys.time () in
  let (solution, stats) = solve (n_queens 12) in
  let elapsed = Sys.time () -. t0 in
  (match solution with
   | Some _ ->
     Printf.printf "  Found solution! Nodes: %d, Backtracks: %d, Time: %.4fs\n"
       stats.nodes_explored stats.backtracks elapsed
   | None -> print_endline "  No solution found.");
  print_newline ();

  print_endline "--- Graph Coloring (Petersen graph, 3 colors) ---";
  let edges = [
    (0,1); (0,4); (0,5);
    (1,2); (1,6);
    (2,3); (2,7);
    (3,4); (3,8);
    (4,9);
    (5,7); (5,8);
    (6,8); (6,9);
    (7,9)
  ] in
  let csp_color = graph_coloring ~n_nodes:10 ~n_colors:3 ~edges in
  let t0 = Sys.time () in
  let (solution, stats) = solve csp_color in
  let elapsed = Sys.time () -. t0 in
  let color_names = [| "Red"; "Green"; "Blue" |] in
  (match solution with
   | Some s ->
     print_string (render_coloring 10 s color_names);
     Printf.printf "  Nodes: %d, Backtracks: %d, AC-3 revisions: %d, Time: %.4fs\n"
       stats.nodes_explored stats.backtracks stats.arc_revisions elapsed
   | None -> print_endline "  No 3-coloring found.");
  print_newline ();

  print_endline "--- Sudoku ---";
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
  let csp_sudoku = sudoku grid in
  let t0 = Sys.time () in
  let (solution, stats) = solve csp_sudoku in
  let elapsed = Sys.time () -. t0 in
  (match solution with
   | Some s ->
     print_string (render_sudoku s);
     Printf.printf "  Nodes: %d, Backtracks: %d, AC-3 revisions: %d, Time: %.4fs\n"
       stats.nodes_explored stats.backtracks stats.arc_revisions elapsed
   | None -> print_endline "  No solution found.");
  print_newline ();

  print_endline "--- Heuristic comparison (8-Queens) ---";
  let csp8 = n_queens 8 in
  let (_, s1) = solve ~use_ac3:false ~use_fc:false ~use_lcv:false csp8 in
  let (_, s2) = solve ~use_ac3:true ~use_fc:true ~use_lcv:true csp8 in
  Printf.printf "  Without heuristics: %d nodes, %d backtracks\n"
    s1.nodes_explored s1.backtracks;
  Printf.printf "  With AC-3+FC+LCV:  %d nodes, %d backtracks\n"
    s2.nodes_explored s2.backtracks;
  print_newline ();

  print_endline "=== Summary ===";
  print_endline "CSP solver with:";
  print_endline "  - Backtracking search with configurable heuristics";
  print_endline "  - AC-3 (arc consistency) preprocessing";
  print_endline "  - MRV (Minimum Remaining Values) variable ordering";
  print_endline "  - LCV (Least Constraining Value) value ordering";
  print_endline "  - Forward checking (domain pruning on assignment)";
  print_endline "  - Applications: N-Queens, graph coloring, Sudoku"
