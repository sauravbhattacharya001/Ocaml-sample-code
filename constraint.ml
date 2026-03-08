(* constraint.ml — Constraint Satisfaction Problem Solver *)
(* A general-purpose CSP solver with arc consistency (AC-3) and        *)
(* backtracking search with constraint propagation.                    *)
(*                                                                     *)
(* Demonstrates: functors, modules, backtracking search, fixed-point   *)
(* iteration, domain reduction, heuristic variable/value ordering.     *)
(*                                                                     *)
(* Built-in solvers for classic problems:                              *)
(*   - Sudoku (9×9 with box constraints)                               *)
(*   - N-Queens (mutual non-attack)                                    *)
(*   - Map/graph coloring (adjacent ≠ same color)                      *)
(*                                                                     *)
(* CSP API:                                                            *)
(*   create, add_variable, add_constraint, add_all_different,          *)
(*   solve, solve_all, is_consistent, domain_sizes, pp                 *)

module CSP = struct

  (* ── Types ──────────────────────────────────────────────── *)

  type variable = string

  type domain = int list

  (** A constraint is a predicate over a subset of variables.
      [scope] lists the variable names; [test] receives values
      in the same order and returns true if satisfied. *)
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

  (* ── Construction ───────────────────────────────────────── *)

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

  (** Add a constraint. Automatically updates neighbor maps. *)
  let add_constraint scope test csp =
    let c = { scope; test } in
    (* Update neighbor adjacency for AC-3 *)
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

  (** Convenience: add an all-different constraint over [vars]. *)
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

  (* ── Domain helpers ─────────────────────────────────────── *)

  (** Deep copy domains hashtable *)
  let copy_domains doms =
    let d = Hashtbl.create (Hashtbl.length doms) in
    Hashtbl.iter (fun k v -> Hashtbl.replace d k v) doms;
    d

  let domain_sizes csp =
    List.map (fun v ->
      let dom = try Hashtbl.find csp.domains v with Not_found -> [] in
      (v, List.length dom)
    ) csp.variables

  (* ── AC-3 (Arc Consistency) ─────────────────────────────── *)

  (** Get binary constraints between two specific variables *)
  let binary_constraints_for csp xi xj =
    List.filter (fun c ->
      List.length c.scope = 2 &&
      List.mem xi c.scope && List.mem xj c.scope
    ) csp.constraints

  (** Revise: remove values from domain of [xi] that have no
      consistent support in domain of [xj] under any binary
      constraint between them. Returns true if domain changed. *)
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

  (** AC-3 algorithm: enforce arc consistency across all arcs.
      Returns false if any domain becomes empty (unsolvable). *)
  let ac3 csp domains =
    (* Initialize queue with all arcs *)
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

  (* ── Consistency check ──────────────────────────────────── *)

  (** Check if a (partial) assignment satisfies all constraints
      whose scope is fully assigned. *)
  let is_consistent assignment csp =
    List.for_all (fun c ->
      let bound = List.filter_map (fun v ->
        List.assoc_opt v assignment
      ) c.scope in
      if List.length bound < List.length c.scope then true (* partial — skip *)
      else c.test bound
    ) csp.constraints

  (* ── Backtracking search with AC-3 propagation ─────────── *)

  (** MRV heuristic: pick unassigned variable with smallest domain *)
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

  (** LCV heuristic: order domain values by how many options they
      leave for neighboring variables (most options first). *)
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

  (** Core backtracking with forward checking via AC-3. *)
  let rec backtrack csp domains assignment collect_all solutions =
    if List.length assignment = List.length csp.variables then begin
      solutions := assignment :: !solutions;
      collect_all  (* return true to continue searching if collect_all *)
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
            (* Forward check: copy domains, assign, propagate *)
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

  (* ── Public API ─────────────────────────────────────────── *)

  (** Find one solution, or None. *)
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

  (** Find all solutions. *)
  let solve_all csp =
    let domains = copy_domains csp.domains in
    if not (ac3 csp domains) then []
    else begin
      let solutions = ref [] in
      let _ = backtrack csp domains [] true solutions in
      List.map List.rev !solutions
    end

  (** Pretty-print a CSP summary. *)
  let pp csp =
    Printf.printf "CSP: %d variables, %d constraints\n"
      (List.length csp.variables) (List.length csp.constraints);
    List.iter (fun (v, s) ->
      Printf.printf "  %s: domain size %d\n" v s
    ) (domain_sizes csp)

  (** Pretty-print an assignment. *)
  let pp_assignment assignment =
    List.iter (fun (v, value) ->
      Printf.printf "  %s = %d\n" v value
    ) (List.sort (fun (a, _) (b, _) -> compare a b) assignment)
end

(* ── Sudoku solver ────────────────────────────────────────── *)

module Sudoku = struct
  open CSP

  let cell r c = Printf.sprintf "R%dC%d" r c

  (** Build a Sudoku CSP from a 9×9 grid.
      0 means empty; 1-9 are given values. *)
  let of_grid (grid : int array array) =
    let csp = ref (create ()) in
    (* Add variables with domains *)
    for r = 0 to 8 do
      for c = 0 to 8 do
        let name = cell r c in
        let domain =
          if grid.(r).(c) <> 0 then [grid.(r).(c)]
          else [1; 2; 3; 4; 5; 6; 7; 8; 9]
        in
        csp := add_variable name domain !csp
      done
    done;
    (* Row constraints: all-different per row *)
    for r = 0 to 8 do
      let vars = List.init 9 (fun c -> cell r c) in
      csp := add_all_different vars !csp
    done;
    (* Column constraints *)
    for c = 0 to 8 do
      let vars = List.init 9 (fun r -> cell r c) in
      csp := add_all_different vars !csp
    done;
    (* Box constraints (3×3) *)
    for br = 0 to 2 do
      for bc = 0 to 2 do
        let vars = List.init 9 (fun i ->
          cell (br * 3 + i / 3) (bc * 3 + i mod 3)
        ) in
        csp := add_all_different vars !csp
      done
    done;
    !csp

  (** Parse a Sudoku from a string of 81 characters (0 or . for empty). *)
  let of_string s =
    let grid = Array.init 9 (fun r ->
      Array.init 9 (fun c ->
        let ch = s.[r * 9 + c] in
        if ch = '.' || ch = '0' then 0
        else Char.code ch - Char.code '0'
      )
    ) in
    of_grid grid

  (** Print a solved Sudoku grid from assignment. *)
  let pp_solution assignment =
    for r = 0 to 8 do
      if r mod 3 = 0 && r > 0 then
        Printf.printf "------+-------+------\n";
      for c = 0 to 8 do
        if c mod 3 = 0 && c > 0 then Printf.printf "| ";
        let v = try List.assoc (cell r c) assignment with Not_found -> 0 in
        Printf.printf "%d " v
      done;
      Printf.printf "\n"
    done
end

(* ── N-Queens solver ──────────────────────────────────────── *)

module NQueens = struct
  open CSP

  let queen i = Printf.sprintf "Q%d" i

  (** Build an N-Queens CSP.
      Variable Q_i = column of queen in row i. *)
  let make n =
    let csp = ref (create ()) in
    let domain = List.init n Fun.id in
    (* Add variables: one queen per row *)
    for i = 0 to n - 1 do
      csp := add_variable (queen i) domain !csp
    done;
    (* Constraints: no two queens on same column or diagonal *)
    for i = 0 to n - 2 do
      for j = i + 1 to n - 1 do
        let qi = queen i and qj = queen j in
        let diff = j - i in
        csp := add_constraint [qi; qj] (function
          | [ci; cj] ->
            ci <> cj                          (* not same column *)
            && abs (ci - cj) <> diff          (* not same diagonal *)
          | _ -> false
        ) !csp
      done
    done;
    !csp

  (** Print a board from the assignment. *)
  let pp_board n assignment =
    for r = 0 to n - 1 do
      let col = try List.assoc (queen r) assignment with Not_found -> -1 in
      for c = 0 to n - 1 do
        Printf.printf "%s " (if c = col then "Q" else ".")
      done;
      Printf.printf "\n"
    done
end

(* ── Map coloring solver ──────────────────────────────────── *)

module MapColoring = struct
  open CSP

  (** Build a graph coloring CSP.
      [regions]: list of region names.
      [borders]: list of (region, region) adjacency pairs.
      [n_colors]: number of colors (encoded as 0..n-1). *)
  let make regions borders n_colors =
    let colors = List.init n_colors Fun.id in
    let csp = ref (create ()) in
    List.iter (fun r ->
      csp := add_variable r colors !csp
    ) regions;
    List.iter (fun (a, b) ->
      csp := add_constraint [a; b] (function
        | [x; y] -> x <> y
        | _ -> false
      ) !csp
    ) borders;
    !csp

  let color_name = function
    | 0 -> "Red" | 1 -> "Green" | 2 -> "Blue"
    | 3 -> "Yellow" | 4 -> "Orange" | n -> Printf.sprintf "Color%d" n
end

(* ── Cryptarithmetic solver ───────────────────────────────── *)

module Cryptarithmetic = struct
  open CSP

  (** Solve SEND + MORE = MONEY.
      Each letter maps to a unique digit 0-9.
      Leading letters (S, M) cannot be 0. *)
  let send_more_money () =
    let letters = ["S"; "E"; "N"; "D"; "M"; "O"; "R"; "Y"] in
    let csp = ref (create ()) in
    (* S and M can't be 0 *)
    List.iter (fun l ->
      let domain = if l = "S" || l = "M" then
        List.init 9 (fun i -> i + 1)
      else
        List.init 10 Fun.id
      in
      csp := add_variable l domain !csp
    ) letters;
    (* All different *)
    csp := add_all_different letters !csp;
    (* SEND + MORE = MONEY *)
    csp := add_constraint letters (function
      | [s; e; n; d; m; o; r; y] ->
        let send = s * 1000 + e * 100 + n * 10 + d in
        let more = m * 1000 + o * 100 + r * 10 + e in
        let money = m * 10000 + o * 1000 + n * 100 + e * 10 + y in
        send + more = money
      | _ -> false
    ) !csp;
    !csp
end

(* ── Demo ─────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Constraint Satisfaction Problem Solver ===\n\n";

  (* ── 4-Queens ── *)
  Printf.printf "--- 4-Queens ---\n";
  let queens_csp = NQueens.make 4 in
  CSP.pp queens_csp;
  (match CSP.solve queens_csp with
   | None -> Printf.printf "No solution found.\n"
   | Some sol ->
     Printf.printf "Solution:\n";
     NQueens.pp_board 4 sol);
  let all_4q = CSP.solve_all (NQueens.make 4) in
  Printf.printf "Total 4-Queens solutions: %d (expected 2)\n\n" (List.length all_4q);

  (* ── 8-Queens ── *)
  Printf.printf "--- 8-Queens ---\n";
  let q8 = NQueens.make 8 in
  (match CSP.solve q8 with
   | None -> Printf.printf "No solution found.\n"
   | Some sol ->
     Printf.printf "Solution:\n";
     NQueens.pp_board 8 sol);
  Printf.printf "\n";

  (* ── Map coloring (Australia) ── *)
  Printf.printf "--- Map Coloring (Australia) ---\n";
  let regions = ["WA"; "NT"; "SA"; "Q"; "NSW"; "V"; "T"] in
  let borders = [
    ("WA", "NT"); ("WA", "SA"); ("NT", "SA"); ("NT", "Q");
    ("SA", "Q"); ("SA", "NSW"); ("SA", "V"); ("Q", "NSW"); ("NSW", "V")
  ] in
  let map_csp = MapColoring.make regions borders 3 in
  (match CSP.solve map_csp with
   | None -> Printf.printf "No 3-coloring found.\n"
   | Some sol ->
     Printf.printf "3-coloring:\n";
     List.iter (fun (v, c) ->
       Printf.printf "  %s: %s\n" v (MapColoring.color_name c)
     ) (List.sort (fun (a, _) (b, _) -> compare a b) sol));
  Printf.printf "\n";

  (* ── Sudoku ── *)
  Printf.printf "--- Sudoku ---\n";
  let puzzle =
    "530070000" ^
    "600195000" ^
    "098000060" ^
    "800060003" ^
    "400803001" ^
    "700020006" ^
    "060000280" ^
    "000419005" ^
    "000080079"
  in
  let sudoku_csp = Sudoku.of_string puzzle in
  Printf.printf "Puzzle:\n";
  Sudoku.pp_solution (List.init 81 (fun i ->
    let r = i / 9 and c = i mod 9 in
    let ch = puzzle.[i] in
    let v = if ch = '0' then 0 else Char.code ch - Char.code '0' in
    (Sudoku.cell r c, v)
  ));
  Printf.printf "\n";
  (match CSP.solve sudoku_csp with
   | None -> Printf.printf "No solution found.\n"
   | Some sol ->
     Printf.printf "Solution:\n";
     Sudoku.pp_solution sol);
  Printf.printf "\n";

  (* ── Cryptarithmetic: SEND + MORE = MONEY ── *)
  Printf.printf "--- SEND + MORE = MONEY ---\n";
  let crypto_csp = Cryptarithmetic.send_more_money () in
  (match CSP.solve crypto_csp with
   | None -> Printf.printf "No solution found.\n"
   | Some sol ->
     let get l = List.assoc l sol in
     let send = get "S" * 1000 + get "E" * 100 + get "N" * 10 + get "D" in
     let more = get "M" * 1000 + get "O" * 100 + get "R" * 10 + get "E" in
     let money = get "M" * 10000 + get "O" * 1000 + get "N" * 100 + get "E" * 10 + get "Y" in
     Printf.printf "  %d + %d = %d\n" send more money;
     CSP.pp_assignment sol);

  Printf.printf "\n=== Done ===\n"
