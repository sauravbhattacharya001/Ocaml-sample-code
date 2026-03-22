(* astar.ml - A* Pathfinding Algorithm
 *
 * A generic A* search implementation with multiple heuristics,
 * grid-based pathfinding, and ASCII visualization.
 *
 * Features:
 * - Generic A* over any graph with custom heuristics
 * - Grid-based pathfinding with obstacles
 * - Manhattan, Euclidean, and Chebyshev distance heuristics
 * - Path visualization on ASCII grids
 * - Diagonal movement support
 *)

(* ---------- Priority Queue (min-heap) ---------- *)

module PQ = struct
  type 'a t = {
    mutable data : (float * 'a) array;
    mutable size : int;
  }

  let create () = { data = Array.make 16 (0.0, Obj.magic 0); size = 0 }

  let swap h i j =
    let tmp = h.data.(i) in
    h.data.(i) <- h.data.(j);
    h.data.(j) <- tmp

  let sift_up h idx =
    let i = ref idx in
    while !i > 0 do
      let parent = (!i - 1) / 2 in
      if fst h.data.(!i) < fst h.data.(parent) then begin
        swap h !i parent;
        i := parent
      end else
        i := -1  (* break *)
    done

  let sift_down h idx =
    let i = ref idx in
    let continue_ = ref true in
    while !continue_ do
      let left = 2 * !i + 1 in
      let right = 2 * !i + 2 in
      let smallest = ref !i in
      if left < h.size && fst h.data.(left) < fst h.data.(!smallest) then
        smallest := left;
      if right < h.size && fst h.data.(right) < fst h.data.(!smallest) then
        smallest := right;
      if !smallest <> !i then begin
        swap h !i !smallest;
        i := !smallest
      end else
        continue_ := false
    done

  let push h priority value =
    if h.size >= Array.length h.data then begin
      let new_data = Array.make (h.size * 2) (0.0, Obj.magic 0) in
      Array.blit h.data 0 new_data 0 h.size;
      h.data <- new_data
    end;
    h.data.(h.size) <- (priority, value);
    h.size <- h.size + 1;
    sift_up h (h.size - 1)

  let pop h =
    if h.size = 0 then None
    else begin
      let result = h.data.(0) in
      h.size <- h.size - 1;
      if h.size > 0 then begin
        h.data.(0) <- h.data.(h.size);
        sift_down h 0
      end;
      Some result
    end

  let is_empty h = h.size = 0
end

(* ---------- Coordinate type ---------- *)

type coord = { row : int; col : int }

let coord_equal a b = a.row = b.row && a.col = b.col

(* ---------- Heuristics ---------- *)

type heuristic = Manhattan | Euclidean | Chebyshev | Diagonal

let manhattan a b =
  float_of_int (abs (a.row - b.row) + abs (a.col - b.col))

let euclidean a b =
  let dr = float_of_int (a.row - b.row) in
  let dc = float_of_int (a.col - b.col) in
  sqrt (dr *. dr +. dc *. dc)

let chebyshev a b =
  float_of_int (max (abs (a.row - b.row)) (abs (a.col - b.col)))

let diagonal a b =
  let dx = abs (a.row - b.row) in
  let dy = abs (a.col - b.col) in
  let mn = min dx dy in
  float_of_int (dx + dy) +. (sqrt 2.0 -. 2.0) *. float_of_int mn

let heuristic_fn = function
  | Manhattan -> manhattan
  | Euclidean -> euclidean
  | Chebyshev -> chebyshev
  | Diagonal -> diagonal

let heuristic_name = function
  | Manhattan -> "Manhattan"
  | Euclidean -> "Euclidean"
  | Chebyshev -> "Chebyshev"
  | Diagonal -> "Diagonal"

(* ---------- Grid ---------- *)

type cell = Open | Wall | Start | Goal

type grid = {
  rows : int;
  cols : int;
  cells : cell array array;
  start : coord;
  goal : coord;
}

let make_grid rows cols walls start goal =
  let cells = Array.init rows (fun r ->
    Array.init cols (fun c ->
      let p = { row = r; col = c } in
      if coord_equal p start then Start
      else if coord_equal p goal then Goal
      else if List.exists (coord_equal p) walls then Wall
      else Open
    )
  ) in
  { rows; cols; cells; start; goal }

let is_passable grid coord =
  coord.row >= 0 && coord.row < grid.rows &&
  coord.col >= 0 && coord.col < grid.cols &&
  grid.cells.(coord.row).(coord.col) <> Wall

(* 4-directional neighbors *)
let neighbors4 grid p =
  let dirs = [| {row= -1; col=0}; {row=1; col=0};
                {row=0; col= -1}; {row=0; col=1} |] in
  Array.to_list dirs
  |> List.map (fun d -> { row = p.row + d.row; col = p.col + d.col })
  |> List.filter (is_passable grid)

(* 8-directional neighbors *)
let neighbors8 grid p =
  let dirs = [|
    {row= -1; col= -1}; {row= -1; col=0}; {row= -1; col=1};
    {row=0; col= -1};                       {row=0; col=1};
    {row=1; col= -1};  {row=1; col=0};  {row=1; col=1};
  |] in
  Array.to_list dirs
  |> List.map (fun d -> { row = p.row + d.row; col = p.col + d.col })
  |> List.filter (is_passable grid)

let move_cost a b =
  if a.row <> b.row && a.col <> b.col then sqrt 2.0  (* diagonal *)
  else 1.0

(* ---------- A* Algorithm ---------- *)

type astar_result = {
  path : coord list;
  cost : float;
  nodes_explored : int;
}

let coord_key c = (c.row, c.col)

let astar ~neighbors ~heuristic ~start ~goal =
  let h = heuristic_fn heuristic in
  let open_set = PQ.create () in
  let came_from = Hashtbl.create 64 in
  let g_score = Hashtbl.create 64 in
  let explored = ref 0 in
  Hashtbl.replace g_score (coord_key start) 0.0;
  PQ.push open_set (h start goal) start;
  let found = ref false in
  while not (PQ.is_empty open_set) && not !found do
    match PQ.pop open_set with
    | None -> ()
    | Some (_f, current) ->
      if coord_equal current goal then
        found := true
      else begin
        incr explored;
        let g_current =
          try Hashtbl.find g_score (coord_key current)
          with Not_found -> infinity
        in
        List.iter (fun neighbor ->
          let tentative_g = g_current +. move_cost current neighbor in
          let prev_g =
            try Hashtbl.find g_score (coord_key neighbor)
            with Not_found -> infinity
          in
          if tentative_g < prev_g then begin
            Hashtbl.replace came_from (coord_key neighbor) current;
            Hashtbl.replace g_score (coord_key neighbor) tentative_g;
            let f = tentative_g +. h neighbor goal in
            PQ.push open_set f neighbor
          end
        ) (neighbors current)
      end
  done;
  if !found then begin
    (* reconstruct path *)
    let path = ref [goal] in
    let cur = ref goal in
    while not (coord_equal !cur start) do
      cur := Hashtbl.find came_from (coord_key !cur);
      path := !cur :: !path
    done;
    let cost =
      try Hashtbl.find g_score (coord_key goal)
      with Not_found -> infinity
    in
    Some { path = !path; cost; nodes_explored = !explored }
  end else
    None

(* ---------- Visualization ---------- *)

let visualize_grid grid path =
  let on_path = Hashtbl.create 64 in
  List.iter (fun c -> Hashtbl.replace on_path (coord_key c) true) path;
  Printf.printf "\n    ";
  for c = 0 to grid.cols - 1 do
    Printf.printf "%d " (c mod 10)
  done;
  Printf.printf "\n    ";
  for _ = 0 to grid.cols - 1 do
    Printf.printf "--"
  done;
  Printf.printf "\n";
  for r = 0 to grid.rows - 1 do
    Printf.printf "%2d| " r;
    for c = 0 to grid.cols - 1 do
      let p = { row = r; col = c } in
      let ch =
        if coord_equal p grid.start then "S "
        else if coord_equal p grid.goal then "G "
        else if Hashtbl.mem on_path (coord_key p) then "* "
        else match grid.cells.(r).(c) with
        | Wall -> "# "
        | _ -> ". "
      in
      print_string ch
    done;
    print_newline ()
  done

let print_result grid result heur =
  match result with
  | None ->
    Printf.printf "\n[%s] No path found!\n" (heuristic_name heur)
  | Some r ->
    Printf.printf "\n[%s] Path found!\n" (heuristic_name heur);
    Printf.printf "  Cost: %.2f\n" r.cost;
    Printf.printf "  Steps: %d\n" (List.length r.path - 1);
    Printf.printf "  Nodes explored: %d\n" r.nodes_explored;
    visualize_grid grid r.path

(* ---------- Demo ---------- *)

let () =
  Printf.printf "=== A* Pathfinding Algorithm ===\n";
  Printf.printf "================================\n\n";

  (* Demo 1: Simple grid with walls *)
  Printf.printf "--- Demo 1: Simple Maze ---\n";
  let walls = [
    {row=1; col=3}; {row=2; col=3}; {row=3; col=3}; {row=4; col=3};
    {row=1; col=7}; {row=2; col=7}; {row=3; col=7};
    {row=5; col=5}; {row=5; col=6}; {row=5; col=7}; {row=5; col=8};
    {row=3; col=0}; {row=3; col=1};
  ] in
  let start = { row = 0; col = 0 } in
  let goal = { row = 7; col = 9 } in
  let grid = make_grid 8 10 walls start goal in

  Printf.printf "\nGrid (%d x %d):\n" grid.rows grid.cols;
  visualize_grid grid [];

  (* Try with different heuristics *)
  List.iter (fun heur ->
    let result = astar
      ~neighbors:(neighbors4 grid)
      ~heuristic:heur
      ~start ~goal
    in
    print_result grid result heur
  ) [Manhattan; Euclidean; Chebyshev];

  (* Demo 2: 8-directional movement *)
  Printf.printf "\n--- Demo 2: Diagonal Movement ---\n";
  let result = astar
    ~neighbors:(neighbors8 grid)
    ~heuristic:Diagonal
    ~start ~goal
  in
  print_result grid result Diagonal;

  (* Demo 3: No path possible *)
  Printf.printf "\n--- Demo 3: Blocked Path ---\n";
  let blocking_walls = [
    {row=0; col=2}; {row=1; col=2}; {row=2; col=2};
    {row=2; col=1}; {row=2; col=0};
  ] in
  let small_grid = make_grid 3 5 blocking_walls
    {row=0; col=0} {row=2; col=4} in
  let result = astar
    ~neighbors:(neighbors4 small_grid)
    ~heuristic:Manhattan
    ~start:{row=0; col=0}
    ~goal:{row=2; col=4}
  in
  print_result small_grid result Manhattan;

  (* Demo 4: Heuristic comparison *)
  Printf.printf "\n--- Demo 4: Heuristic Efficiency Comparison ---\n";
  let big_walls = [
    {row=2; col=2}; {row=3; col=2}; {row=4; col=2}; {row=5; col=2};
    {row=5; col=3}; {row=5; col=4}; {row=5; col=5};
    {row=2; col=5}; {row=3; col=5}; {row=2; col=8}; {row=3; col=8};
    {row=4; col=8}; {row=5; col=8}; {row=6; col=8};
    {row=7; col=3}; {row=7; col=4}; {row=7; col=5};
    {row=7; col=6}; {row=7; col=7};
  ] in
  let big_grid = make_grid 10 12 big_walls
    {row=0; col=0} {row=9; col=11} in

  Printf.printf "\nGrid layout:\n";
  visualize_grid big_grid [];

  Printf.printf "\n  %-12s  %6s  %5s  %8s\n"
    "Heuristic" "Cost" "Steps" "Explored";
  Printf.printf "  %-12s  %6s  %5s  %8s\n"
    "----------" "------" "-----" "--------";
  List.iter (fun heur ->
    let result = astar
      ~neighbors:(neighbors4 big_grid)
      ~heuristic:heur
      ~start:{row=0; col=0}
      ~goal:{row=9; col=11}
    in
    match result with
    | None -> Printf.printf "  %-12s  No path found\n" (heuristic_name heur)
    | Some r ->
      Printf.printf "  %-12s  %6.2f  %5d  %8d\n"
        (heuristic_name heur) r.cost (List.length r.path - 1) r.nodes_explored
  ) [Manhattan; Euclidean; Chebyshev];

  Printf.printf "\n=== A* Demo Complete ===\n"
