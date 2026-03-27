(* Dancing Links (Algorithm X) - Exact Cover Problem Solver
   
   Implements Donald Knuth's Algorithm X using the Dancing Links (DLX) technique.
   Efficiently solves exact cover problems where we need to find a subset of rows
   in a binary matrix such that each column has exactly one 1.
   
   Applications: Sudoku solving, pentomino tiling, N-Queens, polyomino packing.
   
   The key insight: doubly-linked lists allow O(1) removal and restoration of nodes,
   making backtracking extremely efficient.
*)

(* A cell in the dancing links structure *)
type cell = {
  mutable left: int;
  mutable right: int;
  mutable up: int;
  mutable down: int;
  mutable col_header: int;   (* index of column header *)
  mutable row_id: int;       (* which row this cell belongs to, -1 for headers *)
  mutable size: int;         (* only used by column headers: count of 1s *)
}

type dlx = {
  cells: cell array;
  mutable num_cells: int;
  num_cols: int;
  root: int;  (* index of root header *)
}

let make_cell () = {
  left = 0; right = 0; up = 0; down = 0;
  col_header = 0; row_id = -1; size = 0;
}

(* Build the DLX structure from a binary matrix (list of rows, each row is list of 1-based column indices) *)
let create ~num_cols ~(rows : int list list) : dlx =
  (* Estimate max cells: root + headers + all entries *)
  let total_entries = List.fold_left (fun acc r -> acc + List.length r) 0 rows in
  let max_cells = 1 + num_cols + total_entries + 1 in
  let cells = Array.init max_cells (fun _ -> make_cell ()) in
  let n = ref 0 in
  let alloc () =
    let i = !n in
    incr n;
    cells.(i) <- make_cell ();
    i
  in
  (* Root node *)
  let root = alloc () in
  cells.(root).left <- root;
  cells.(root).right <- root;
  cells.(root).up <- root;
  cells.(root).down <- root;
  cells.(root).row_id <- -1;
  (* Column headers *)
  let col_headers = Array.init num_cols (fun _ ->
    let h = alloc () in
    cells.(h).col_header <- h;
    cells.(h).row_id <- -1;
    cells.(h).size <- 0;
    (* Insert to the left of root (i.e., at end of header row) *)
    let prev = cells.(root).left in
    cells.(h).left <- prev;
    cells.(h).right <- root;
    cells.(prev).right <- h;
    cells.(root).left <- h;
    (* Vertical: point to self *)
    cells.(h).up <- h;
    cells.(h).down <- h;
    h
  ) in
  (* Add rows *)
  List.iteri (fun row_idx cols ->
    let first = ref (-1) in
    List.iter (fun c ->
      let col_0 = c - 1 in (* convert to 0-based *)
      if col_0 >= 0 && col_0 < num_cols then begin
        let h = col_headers.(col_0) in
        let nd = alloc () in
        cells.(nd).col_header <- h;
        cells.(nd).row_id <- row_idx;
        (* Insert at bottom of column *)
        let prev_up = cells.(h).up in
        cells.(nd).up <- prev_up;
        cells.(nd).down <- h;
        cells.(prev_up).down <- nd;
        cells.(h).up <- nd;
        cells.(h).size <- cells.(h).size + 1;
        (* Horizontal linking *)
        if !first = -1 then begin
          first := nd;
          cells.(nd).left <- nd;
          cells.(nd).right <- nd
        end else begin
          let f = !first in
          let prev_left = cells.(f).left in
          cells.(nd).left <- prev_left;
          cells.(nd).right <- f;
          cells.(prev_left).right <- nd;
          cells.(f).left <- nd
        end
      end
    ) cols
  ) rows;
  { cells; num_cells = !n; num_cols; root }

(* Cover a column: remove it from the header list and remove all rows that have a 1 in this column *)
let cover dlx col =
  let c = dlx.cells in
  (* Remove column header from header row *)
  c.(c.(col).right).left <- c.(col).left;
  c.(c.(col).left).right <- c.(col).right;
  (* For each row in this column *)
  let i = ref c.(col).down in
  while !i <> col do
    (* For each cell in this row (except the column we're covering) *)
    let j = ref c.(!i).right in
    while !j <> !i do
      c.(c.(!j).down).up <- c.(!j).up;
      c.(c.(!j).up).down <- c.(!j).down;
      c.(c.(!j).col_header).size <- c.(c.(!j).col_header).size - 1;
      j := c.(!j).right
    done;
    i := c.(!i).down
  done

(* Uncover a column: reverse of cover *)
let uncover dlx col =
  let c = dlx.cells in
  let i = ref c.(col).up in
  while !i <> col do
    let j = ref c.(!i).left in
    while !j <> !i do
      c.(c.(!j).col_header).size <- c.(c.(!j).col_header).size + 1;
      c.(c.(!j).down).up <- !j;
      c.(c.(!j).up).down <- !j;
      j := c.(!j).left
    done;
    i := c.(!i).up
  done;
  c.(c.(col).right).left <- col;
  c.(c.(col).left).right <- col

(* Choose the column with the fewest 1s (S heuristic) *)
let choose_column dlx =
  let c = dlx.cells in
  let best = ref (-1) in
  let best_size = ref max_int in
  let j = ref c.(dlx.root).right in
  while !j <> dlx.root do
    if c.(!j).size < !best_size then begin
      best := !j;
      best_size := c.(!j).size
    end;
    j := c.(!j).right
  done;
  !best

(* Solve: find all exact covers. Returns list of solutions, each solution is a list of row indices. *)
let solve ?(max_solutions=max_int) dlx =
  let solutions = ref [] in
  let count = ref 0 in
  let partial = ref [] in
  let rec search () =
    if !count >= max_solutions then ()
    else if dlx.cells.(dlx.root).right = dlx.root then begin
      (* All columns covered — found a solution *)
      solutions := (List.rev !partial) :: !solutions;
      incr count
    end else begin
      let col = choose_column dlx in
      if col = -1 || dlx.cells.(col).size = 0 then ()  (* dead end *)
      else begin
        cover dlx col;
        let r = ref dlx.cells.(col).down in
        while !r <> col && !count < max_solutions do
          partial := dlx.cells.(!r).row_id :: !partial;
          (* Cover all other columns in this row *)
          let j = ref dlx.cells.(!r).right in
          while !j <> !r do
            cover dlx dlx.cells.(!j).col_header;
            j := dlx.cells.(!j).right
          done;
          search ();
          (* Uncover *)
          let j = ref dlx.cells.(!r).left in
          while !j <> !r do
            uncover dlx dlx.cells.(!j).col_header;
            j := dlx.cells.(!j).left
          done;
          partial := List.tl !partial;
          r := dlx.cells.(!r).down
        done;
        uncover dlx col
      end
    end
  in
  search ();
  List.rev !solutions

(* Convenience: solve and return first solution, or None *)
let solve_first dlx =
  match solve ~max_solutions:1 dlx with
  | [s] -> Some s
  | _ -> None

(* Count all solutions without storing them *)
let count_solutions dlx =
  let count = ref 0 in
  let rec search () =
    if dlx.cells.(dlx.root).right = dlx.root then
      incr count
    else begin
      let col = choose_column dlx in
      if col = -1 || dlx.cells.(col).size = 0 then ()
      else begin
        cover dlx col;
        let r = ref dlx.cells.(col).down in
        while !r <> col do
          let j = ref dlx.cells.(!r).right in
          while !j <> !r do
            cover dlx dlx.cells.(!j).col_header;
            j := dlx.cells.(!j).right
          done;
          search ();
          let j = ref dlx.cells.(!r).left in
          while !j <> !r do
            uncover dlx dlx.cells.(!j).col_header;
            j := dlx.cells.(!j).left
          done;
          r := dlx.cells.(!r).down
        done;
        uncover dlx col
      end
    end
  in
  search ();
  !count

(* === Sudoku Solver using DLX === *)

(* Encode a standard 9x9 Sudoku as an exact cover problem with 324 columns:
   - Columns 0-80: cell (r,c) is filled  (9*9 = 81)
   - Columns 81-161: row r has digit d   (9*9 = 81)  
   - Columns 162-242: col c has digit d  (9*9 = 81)
   - Columns 243-323: box b has digit d  (9*9 = 81)
   
   Each possible placement (r, c, d) creates one row with exactly 4 ones.
*)

let sudoku_solve (grid : int array array) : int array array option =
  let rows = ref [] in
  let row_info = ref [] in  (* (r, c, d) for each row *)
  for r = 0 to 8 do
    for c = 0 to 8 do
      let box = (r / 3) * 3 + (c / 3) in
      let digits = if grid.(r).(c) <> 0 then [grid.(r).(c)] else List.init 9 (fun i -> i + 1) in
      List.iter (fun d ->
        let d0 = d - 1 in
        let cols = [
          r * 9 + c + 1;                (* cell constraint, 1-based *)
          81 + r * 9 + d0 + 1;          (* row-digit constraint *)
          162 + c * 9 + d0 + 1;         (* col-digit constraint *)
          243 + box * 9 + d0 + 1;       (* box-digit constraint *)
        ] in
        rows := cols :: !rows;
        row_info := (r, c, d) :: !row_info
      ) digits
    done
  done;
  let rows_arr = Array.of_list (List.rev !rows) in
  let info_arr = Array.of_list (List.rev !row_info) in
  let dlx = create ~num_cols:324 ~rows:(Array.to_list rows_arr) in
  match solve_first dlx with
  | None -> None
  | Some sol ->
    let result = Array.init 9 (fun _ -> Array.make 9 0) in
    List.iter (fun row_idx ->
      let (r, c, d) = info_arr.(row_idx) in
      result.(r).(c) <- d
    ) sol;
    Some result

(* === N-Queens using DLX === *)

(* N-Queens as exact cover with secondary columns.
   We use a simplified version: N row constraints (primary) + N col constraints (primary)
   + (2N-1) diagonal constraints (secondary, handled by making them optional).
   
   For simplicity, we solve the simpler version where we just need one queen per row
   and one per column, with diagonal constraints as extras.
*)

let nqueens_solve n =
  (* Columns: 0..n-1 = rows, n..2n-1 = cols, 2n..4n-2 = diag1, 4n-1..6n-3 = diag2 *)
  (* Only row and col constraints are primary (must be covered) *)
  (* We'll handle this by using all as primary for now — works for small N *)
  let num_cols = 2 * n in  (* just row + col constraints *)
  let rows = ref [] in
  let info = ref [] in
  for r = 0 to n - 1 do
    for c = 0 to n - 1 do
      rows := [r + 1; n + c + 1] :: !rows;
      info := (r, c) :: !info
    done
  done;
  let rows_list = List.rev !rows in
  let info_arr = Array.of_list (List.rev !info) in
  let dlx = create ~num_cols ~rows:rows_list in
  (* Get all solutions and filter for diagonal conflicts *)
  let all_sols = solve dlx in
  let valid = List.filter (fun sol ->
    let positions = List.map (fun ri -> info_arr.(ri)) sol in
    let no_diag_conflict = List.for_all (fun (r1, c1) ->
      List.for_all (fun (r2, c2) ->
        (r1 = r2 && c1 = c2) || abs (r1 - r2) <> abs (c1 - c2)
      ) positions
    ) positions in
    no_diag_conflict
  ) all_sols in
  List.map (fun sol -> List.map (fun ri -> info_arr.(ri)) sol) valid

let nqueens_count n = List.length (nqueens_solve n)

(* === Pretty Printing === *)

let print_solution rows row_data =
  Printf.printf "Solution (rows selected):";
  List.iter (fun r -> Printf.printf " %d" r) rows;
  print_newline ();
  match row_data with
  | Some data ->
    List.iter (fun r ->
      Printf.printf "  Row %d: %s\n" r data.(r)
    ) rows
  | None -> ()

let print_sudoku grid =
  Array.iteri (fun r row ->
    if r mod 3 = 0 && r > 0 then
      print_endline "------+-------+------";
    Array.iteri (fun c v ->
      if c mod 3 = 0 && c > 0 then print_string "| ";
      if v = 0 then print_string ". "
      else Printf.printf "%d " v
    ) row;
    print_newline ()
  ) grid

let print_queens n positions =
  let board = Array.init n (fun _ -> Array.make n '.') in
  List.iter (fun (r, c) -> board.(r).(c) <- 'Q') positions;
  Array.iter (fun row ->
    Array.iter (fun c -> Printf.printf "%c " c) row;
    print_newline ()
  ) board

(* === Demo === *)

let () =
  print_endline "=== Dancing Links (Algorithm X) ===\n";
  
  (* Example 1: Simple exact cover *)
  print_endline "--- Example 1: Simple Exact Cover ---";
  print_endline "Matrix:";
  print_endline "  Col:  1 2 3 4 5 6 7";
  print_endline "  Row 0: 1 0 0 1 0 0 1";
  print_endline "  Row 1: 1 0 0 1 0 0 0";
  print_endline "  Row 2: 0 0 0 1 1 0 1";
  print_endline "  Row 3: 0 0 1 0 1 1 0";
  print_endline "  Row 4: 0 1 1 0 0 1 1";
  print_endline "  Row 5: 0 1 0 0 0 0 1";
  let rows = [
    [1; 4; 7];
    [1; 4];
    [4; 5; 7];
    [3; 5; 6];
    [2; 3; 6; 7];
    [2; 7];
  ] in
  let dlx = create ~num_cols:7 ~rows in
  let solutions = solve dlx in
  Printf.printf "Found %d solution(s):\n" (List.length solutions);
  List.iter (fun sol ->
    Printf.printf "  Rows: %s\n" (String.concat ", " (List.map string_of_int sol))
  ) solutions;
  
  (* Example 2: Sudoku *)
  print_endline "\n--- Example 2: Sudoku Solver ---";
  let puzzle = [|
    [|5;3;0;0;7;0;0;0;0|];
    [|6;0;0;1;9;5;0;0;0|];
    [|0;9;8;0;0;0;0;6;0|];
    [|8;0;0;0;6;0;0;0;3|];
    [|4;0;0;8;0;3;0;0;1|];
    [|7;0;0;0;2;0;0;0;6|];
    [|0;6;0;0;0;0;2;8;0|];
    [|0;0;0;4;1;9;0;0;5|];
    [|0;0;0;0;8;0;0;7;9|];
  |] in
  print_endline "Puzzle:";
  print_sudoku puzzle;
  (match sudoku_solve puzzle with
   | Some solution ->
     print_endline "\nSolved:";
     print_sudoku solution
   | None ->
     print_endline "No solution found!");
  
  (* Example 3: N-Queens *)
  print_endline "\n--- Example 3: N-Queens ---";
  for n = 4 to 8 do
    let count = nqueens_count n in
    Printf.printf "%d-Queens: %d solutions\n" n count
  done;
  print_endline "\nFirst 4-Queens solution:";
  (match nqueens_solve 4 with
   | sol :: _ -> print_queens 4 sol
   | [] -> print_endline "No solution!");
  
  print_endline "\n=== Done ==="
