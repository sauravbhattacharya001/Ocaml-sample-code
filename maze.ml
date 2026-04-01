(* maze.ml — Maze Generation & Solving
 *
 * Demonstrates:
 *   - Recursive backtracking (DFS) maze generation
 *   - BFS, DFS, and A* maze solving
 *   - ASCII art visualization with path rendering
 *   - Functional data structures (sets, maps, priority queues)
 *
 * Usage:
 *   ocamlfind ocamlopt -package str -linkpkg maze.ml -o maze && ./maze
 *   # or simply: ocaml maze.ml
 *
 * The program generates a random maze and solves it with three
 * different algorithms, printing each solution path.
 *)

(* ── Types ────────────────────────────────────────────────────── *)

type cell = { row : int; col : int }

module CellSet = Set.Make(struct
  type t = cell
  let compare a b =
    let c = compare a.row b.row in
    if c <> 0 then c else compare a.col b.col
end)

module CellMap = Map.Make(struct
  type t = cell
  let compare a b =
    let c = compare a.row b.row in
    if c <> 0 then c else compare a.col b.col
end)

(* A maze is a set of open passages between adjacent cells. *)
type maze = {
  rows : int;
  cols : int;
  passages : (cell * cell) list;  (* bidirectional edges *)
}

(* ── Utility ──────────────────────────────────────────────────── *)

let neighbors rows cols { row; col } =
  [ { row = row - 1; col };
    { row = row + 1; col };
    { row; col = col - 1 };
    { row; col = col + 1 } ]
  |> List.filter (fun c ->
    c.row >= 0 && c.row < rows && c.col >= 0 && c.col < cols)

let shuffle lst =
  let arr = Array.of_list lst in
  let n = Array.length arr in
  for i = n - 1 downto 1 do
    let j = Random.int (i + 1) in
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp
  done;
  Array.to_list arr

(* Canonical edge: smaller cell first *)
let edge a b =
  if compare (a.row, a.col) (b.row, b.col) <= 0 then (a, b) else (b, a)

(* ── Maze Generation: Recursive Backtracker (DFS) ────────────── *)

let generate rows cols =
  Random.self_init ();
  let visited = Hashtbl.create (rows * cols) in
  let passages = ref [] in
  let rec carve cell =
    Hashtbl.replace visited cell true;
    let nbrs = shuffle (neighbors rows cols cell) in
    List.iter (fun n ->
      if not (Hashtbl.mem visited n) then begin
        passages := (edge cell n) :: !passages;
        carve n
      end
    ) nbrs
  in
  carve { row = 0; col = 0 };
  { rows; cols; passages = !passages }

(* ── Adjacency lookup ─────────────────────────────────────────── *)

let build_adj maze =
  let tbl = Hashtbl.create (maze.rows * maze.cols) in
  let add a b =
    let cur = try Hashtbl.find tbl a with Not_found -> [] in
    Hashtbl.replace tbl a (b :: cur)
  in
  List.iter (fun (a, b) -> add a b; add b a) maze.passages;
  tbl

(* ── Solver: BFS ──────────────────────────────────────────────── *)

let solve_bfs adj start goal =
  let visited = Hashtbl.create 64 in
  let parent = Hashtbl.create 64 in
  let q = Queue.create () in
  Queue.push start q;
  Hashtbl.replace visited start true;
  let found = ref false in
  while not (Queue.is_empty q) && not !found do
    let cur = Queue.pop q in
    if cur = goal then found := true
    else begin
      let nbrs = try Hashtbl.find adj cur with Not_found -> [] in
      List.iter (fun n ->
        if not (Hashtbl.mem visited n) then begin
          Hashtbl.replace visited n true;
          Hashtbl.replace parent n cur;
          Queue.push n q
        end
      ) nbrs
    end
  done;
  (* reconstruct path *)
  if not !found then []
  else begin
    let path = ref [goal] in
    let cur = ref goal in
    while !cur <> start do
      cur := Hashtbl.find parent !cur;
      path := !cur :: !path
    done;
    !path
  end

(* ── Solver: DFS ──────────────────────────────────────────────── *)

let solve_dfs adj start goal =
  let visited = Hashtbl.create 64 in
  let rec dfs cur path =
    if cur = goal then Some (List.rev (cur :: path))
    else begin
      Hashtbl.replace visited cur true;
      let nbrs = try Hashtbl.find adj cur with Not_found -> [] in
      List.fold_left (fun acc n ->
        match acc with
        | Some _ -> acc
        | None ->
          if Hashtbl.mem visited n then None
          else dfs n (cur :: path)
      ) None nbrs
    end
  in
  match dfs start [] with Some p -> p | None -> []

(* ── Solver: A* ───────────────────────────────────────────────── *)

(* Simple priority queue as sorted list — fine for small mazes *)
module PQ = struct
  type 'a t = (int * 'a) list ref

  let create () = ref []

  let push pq priority item =
    let rec insert = function
      | [] -> [(priority, item)]
      | ((p, _) as hd) :: tl ->
        if priority <= p then (priority, item) :: hd :: tl
        else hd :: insert tl
    in
    pq := insert !pq

  let pop pq =
    match !pq with
    | [] -> failwith "empty"
    | (_, item) :: tl -> pq := tl; item

  let is_empty pq = !pq = []
end

let manhattan a b = abs (a.row - b.row) + abs (a.col - b.col)

let solve_astar adj start goal =
  let g_score = Hashtbl.create 64 in
  let parent = Hashtbl.create 64 in
  let closed = Hashtbl.create 64 in
  let pq = PQ.create () in
  Hashtbl.replace g_score start 0;
  PQ.push pq (manhattan start goal) start;
  let found = ref false in
  while not (PQ.is_empty pq) && not !found do
    let cur = PQ.pop pq in
    if cur = goal then found := true
    else if not (Hashtbl.mem closed cur) then begin
      Hashtbl.replace closed cur true;
      let cur_g = Hashtbl.find g_score cur in
      let nbrs = try Hashtbl.find adj cur with Not_found -> [] in
      List.iter (fun n ->
        let tentative = cur_g + 1 in
        let prev = try Hashtbl.find g_score n with Not_found -> max_int in
        if tentative < prev then begin
          Hashtbl.replace g_score n tentative;
          Hashtbl.replace parent n cur;
          PQ.push pq (tentative + manhattan n goal) n
        end
      ) nbrs
    end
  done;
  if not !found then []
  else begin
    let path = ref [goal] in
    let cur = ref goal in
    while !cur <> start do
      cur := Hashtbl.find parent !cur;
      path := !cur :: !path
    done;
    !path
  end

(* ── ASCII Rendering ──────────────────────────────────────────── *)

let render maze path =
  let h = maze.rows * 2 + 1 in
  let w = maze.cols * 2 + 1 in
  let grid = Array.init h (fun r ->
    Array.init w (fun c ->
      if r mod 2 = 0 || c mod 2 = 0 then '#' else ' '
    )
  ) in
  (* Open passages *)
  let passage_set = Hashtbl.create (List.length maze.passages) in
  List.iter (fun (a, b) ->
    Hashtbl.replace passage_set (edge a b) true
  ) maze.passages;
  List.iter (fun (a, b) ->
    let wr = a.row + b.row + 1 in
    let wc = a.col + b.col + 1 in
    grid.(wr).(wc) <- ' '
  ) maze.passages;
  (* Mark path *)
  let path_set = Hashtbl.create (List.length path) in
  List.iter (fun c -> Hashtbl.replace path_set c true) path;
  List.iter (fun c ->
    grid.(c.row * 2 + 1).(c.col * 2 + 1) <- '.'
  ) path;
  (* Mark passages on path *)
  let rec mark_path_passages = function
    | [] | [_] -> ()
    | a :: (b :: _ as rest) ->
      let wr = a.row + b.row + 1 in
      let wc = a.col + b.col + 1 in
      grid.(wr).(wc) <- '.';
      mark_path_passages rest
  in
  mark_path_passages path;
  (* Start and goal markers *)
  (match path with
   | s :: _ ->
     grid.(s.row * 2 + 1).(s.col * 2 + 1) <- 'S';
     let g = List.nth path (List.length path - 1) in
     grid.(g.row * 2 + 1).(g.col * 2 + 1) <- 'E'
   | [] -> ());
  (* Print *)
  Array.iter (fun row ->
    Array.iter (fun c -> print_char c) row;
    print_newline ()
  ) grid

(* ── Main ─────────────────────────────────────────────────────── *)

let () =
  let rows = 12 in
  let cols = 20 in
  let maze = generate rows cols in
  let adj = build_adj maze in
  let start = { row = 0; col = 0 } in
  let goal = { row = rows - 1; col = cols - 1 } in

  Printf.printf "=== Maze (%d×%d) ===\n\n" rows cols;
  render maze [];
  print_newline ();

  let solvers = [
    ("BFS (shortest path)", solve_bfs adj start goal);
    ("DFS (first path found)", solve_dfs adj start goal);
    ("A* (optimal path)", solve_astar adj start goal);
  ] in

  List.iter (fun (name, path) ->
    Printf.printf "--- %s (length: %d) ---\n\n" name (List.length path);
    render maze path;
    print_newline ()
  ) solvers;

  (* Compare path lengths *)
  Printf.printf "=== Summary ===\n";
  List.iter (fun (name, path) ->
    Printf.printf "  %-30s  %d steps\n" name (List.length path)
  ) solvers
