(* Cellular Automata -- Game of Life, Elementary (Rule 110 etc.), Langton's Ant, Wireworld
 *
 * Demonstrates:
 *   - 2D grid simulations with toroidal wrapping
 *   - 1D elementary automata (Wolfram rules)
 *   - Agent-based automata (Langton's Ant)
 *   - Multi-state automata (Wireworld for logic circuits)
 *   - ASCII rendering and RLE pattern loading
 *   - Functional grid transforms, pattern analysis
 *
 * Usage:
 *   ocaml cellular_automata.ml
 *)

(* ── Grid2D: generic 2D grid with toroidal wrapping ─────────────────── *)

module Grid2D = struct
  type 'a t = {
    width  : int;
    height : int;
    cells  : 'a array array;
  }

  let create w h default =
    { width = w; height = h;
      cells = Array.init h (fun _ -> Array.make w default) }

  let get g x y =
    let x' = ((x mod g.width) + g.width) mod g.width in
    let y' = ((y mod g.height) + g.height) mod g.height in
    g.cells.(y').(x')

  let set g x y v =
    let x' = ((x mod g.width) + g.width) mod g.width in
    let y' = ((y mod g.height) + g.height) mod g.height in
    g.cells.(y').(x') <- v

  let copy g =
    { g with cells = Array.init g.height (fun y -> Array.copy g.cells.(y)) }

  let map f g =
    let g' = copy g in
    for y = 0 to g.height - 1 do
      for x = 0 to g.width - 1 do
        g'.cells.(y).(x) <- f x y g.cells.(y).(x)
      done
    done;
    g'

  let fold f acc g =
    let r = ref acc in
    for y = 0 to g.height - 1 do
      for x = 0 to g.width - 1 do
        r := f !r x y g.cells.(y).(x)
      done
    done;
    !r

  let count pred g =
    fold (fun n _ _ v -> if pred v then n + 1 else n) 0 g

  let neighbors8 g x y =
    let dirs = [(-1,-1);(0,-1);(1,-1);(-1,0);(1,0);(-1,1);(0,1);(1,1)] in
    List.map (fun (dx,dy) -> get g (x+dx) (y+dy)) dirs

  let neighbors4 g x y =
    let dirs = [(0,-1);(-1,0);(1,0);(0,1)] in
    List.map (fun (dx,dy) -> get g (x+dx) (y+dy)) dirs

  let to_string char_of g =
    let buf = Buffer.create (g.width * g.height) in
    for y = 0 to g.height - 1 do
      for x = 0 to g.width - 1 do
        Buffer.add_char buf (char_of g.cells.(y).(x))
      done;
      if y < g.height - 1 then Buffer.add_char buf '\n'
    done;
    Buffer.contents buf

  let of_string_grid lines cell_of =
    let h = List.length lines in
    if h = 0 then create 0 0 (cell_of '.') else
    let w = List.fold_left (fun m l -> max m (String.length l)) 0 lines in
    let g = create w h (cell_of '.') in
    List.iteri (fun y line ->
      String.iteri (fun x c -> if x < w then set g x y (cell_of c)) line
    ) lines;
    g
end

(* ── Game of Life ────────────────────────────────────────────────────── *)

module Life = struct
  type cell = Dead | Alive

  let char_of = function Dead -> '.' | Alive -> '#'
  let cell_of = function '#' | 'O' | '*' -> Alive | _ -> Dead

  let create w h = Grid2D.create w h Dead

  let step g =
    Grid2D.map (fun x y cell ->
      let alive_count =
        List.length (List.filter (fun c -> c = Alive) (Grid2D.neighbors8 g x y))
      in
      match cell, alive_count with
      | Alive, (2 | 3) -> Alive
      | Dead, 3         -> Alive
      | _               -> Dead
    ) g

  let population g = Grid2D.count (fun c -> c = Alive) g

  let run g steps =
    let rec go g n =
      if n >= steps then g
      else go (step g) (n + 1)
    in
    go g 0

  let to_string g = Grid2D.to_string char_of g

  let of_strings lines = Grid2D.of_string_grid lines cell_of

  (* Common patterns *)
  let glider () =
    of_strings [".#."; "..#"; "###"]

  let blinker () =
    of_strings ["###"]

  let block () =
    of_strings ["##"; "##"]

  let beacon () =
    of_strings ["##.."; "##.."; "..##"; "..##"]

  let r_pentomino () =
    of_strings [".##"; "##."; ".#."]

  (* Place a pattern onto a grid at (ox, oy) *)
  let place ~onto pattern ox oy =
    let g = Grid2D.copy onto in
    for y = 0 to pattern.Grid2D.height - 1 do
      for x = 0 to pattern.Grid2D.width - 1 do
        let cell = Grid2D.get pattern x y in
        if cell = Alive then Grid2D.set g (ox + x) (oy + y) Alive
      done
    done;
    g

  (* Detect if grid is static (period-1) *)
  let is_still g =
    let g' = step g in
    let same = ref true in
    for y = 0 to g.Grid2D.height - 1 do
      for x = 0 to g.Grid2D.width - 1 do
        if Grid2D.get g x y <> Grid2D.get g' x y then same := false
      done
    done;
    !same

  (* Detect oscillation period (up to max_period) *)
  let detect_period ?(max_period=100) g =
    let states = Hashtbl.create 16 in
    let rec go g n =
      if n > max_period then None
      else begin
        let s = to_string g in
        match Hashtbl.find_opt states s with
        | Some prev -> Some (n - prev)
        | None ->
          Hashtbl.add states s n;
          go (step g) (n + 1)
      end
    in
    go g 0

  (* RLE decoder (basic subset) *)
  let of_rle s =
    let lines = ref [] in
    let row = Buffer.create 64 in
    let i = ref 0 in
    let len = String.length s in
    while !i < len do
      let c = s.[!i] in
      if c = '!' then i := len
      else if c = '$' then begin
        lines := Buffer.contents row :: !lines;
        Buffer.clear row;
        incr i
      end else if c = 'b' || c = 'o' then begin
        Buffer.add_char row (if c = 'o' then '#' else '.');
        incr i
      end else if c >= '0' && c <= '9' then begin
        let n = ref 0 in
        while !i < len && s.[!i] >= '0' && s.[!i] <= '9' do
          n := !n * 10 + (Char.code s.[!i] - 48);
          incr i
        done;
        if !i < len && (s.[!i] = 'b' || s.[!i] = 'o') then begin
          let ch = if s.[!i] = 'o' then '#' else '.' in
          for _ = 1 to !n do Buffer.add_char row ch done;
          incr i
        end else if !i < len && s.[!i] = '$' then begin
          lines := Buffer.contents row :: !lines;
          Buffer.clear row;
          for _ = 2 to !n do lines := "" :: !lines done;
          incr i
        end
      end else incr i
    done;
    if Buffer.length row > 0 then lines := Buffer.contents row :: !lines;
    of_strings (List.rev !lines)
end

(* ── Elementary Cellular Automata (1D, Wolfram rules) ────────────────── *)

module Elementary = struct
  type row = bool array

  let create_row size =
    let r = Array.make size false in
    r.(size / 2) <- true;
    r

  let create_random size =
    Array.init size (fun _ -> Random.bool ())

  let step rule row =
    let n = Array.length row in
    Array.init n (fun i ->
      let l = if i > 0 then row.(i-1) else row.(n-1) in
      let c = row.(i) in
      let r = if i < n-1 then row.(i+1) else row.(0) in
      let idx = (if l then 4 else 0) + (if c then 2 else 0) + (if r then 1 else 0) in
      (rule lsr idx) land 1 = 1
    )

  let run rule row steps =
    let rows = Array.make (steps + 1) row in
    for i = 1 to steps do
      rows.(i) <- step rule rows.(i-1)
    done;
    rows

  let row_to_string row =
    String.init (Array.length row) (fun i -> if row.(i) then '#' else ' ')

  let to_string rows =
    Array.to_list rows
    |> List.map row_to_string
    |> String.concat "\n"

  let population row =
    Array.fold_left (fun n b -> if b then n + 1 else n) 0 row

  (* Check if a rule is class 1 (dies to all same), class 2, 3, or 4 *)
  let classify_rule rule steps size =
    let row = create_random size in
    let rows = run rule row steps in
    let last = rows.(steps) in
    let pop = population last in
    if pop = 0 || pop = size then "Class 1 (uniform)"
    else begin
      let prev = rows.(steps - 1) in
      if last = prev then "Class 2 (periodic/stable)"
      else "Class 3/4 (complex/chaotic)"
    end
end

(* ── Langton's Ant ───────────────────────────────────────────────────── *)

module LangtonsAnt = struct
  type direction = North | East | South | West

  type ant = {
    x : int;
    y : int;
    dir : direction;
  }

  let turn_right = function
    | North -> East | East -> South | South -> West | West -> North

  let turn_left = function
    | North -> West | West -> South | South -> East | East -> North

  let move_forward ant =
    match ant.dir with
    | North -> { ant with y = ant.y - 1 }
    | South -> { ant with y = ant.y + 1 }
    | East  -> { ant with x = ant.x + 1 }
    | West  -> { ant with x = ant.x - 1 }

  let step grid ant =
    let g = Grid2D.copy grid in
    let wx = ((ant.x mod g.Grid2D.width) + g.Grid2D.width) mod g.Grid2D.width in
    let wy = ((ant.y mod g.Grid2D.height) + g.Grid2D.height) mod g.Grid2D.height in
    let cell = Grid2D.get g wx wy in
    let ant' =
      if cell then { (move_forward { ant with dir = turn_left ant.dir }) with x = ant.x; y = ant.y }
      else { (move_forward { ant with dir = turn_right ant.dir }) with x = ant.x; y = ant.y }
    in
    Grid2D.set g wx wy (not cell);
    let ant'' = move_forward (if cell then { ant with dir = turn_left ant.dir }
                              else { ant with dir = turn_right ant.dir }) in
    (g, ant'')

  let run width height steps =
    let grid = Grid2D.create width height false in
    let ant = { x = width / 2; y = height / 2; dir = North } in
    let rec go g a n =
      if n >= steps then (g, a, n)
      else let (g', a') = step g a in go g' a' (n + 1)
    in
    go grid ant 0

  let to_string grid ant =
    let ant_char = function
      | North -> '^' | South -> 'v' | East -> '>' | West -> '<'
    in
    Grid2D.to_string (fun b -> if b then '#' else '.') grid
    |> fun s ->
      let wx = ((ant.x mod grid.Grid2D.width) + grid.Grid2D.width) mod grid.Grid2D.width in
      let wy = ((ant.y mod grid.Grid2D.height) + grid.Grid2D.height) mod grid.Grid2D.height in
      let lines = String.split_on_char '\n' s |> Array.of_list in
      if wy >= 0 && wy < Array.length lines then begin
        let line = Bytes.of_string lines.(wy) in
        if wx >= 0 && wx < Bytes.length line then
          Bytes.set line wx (ant_char ant.dir);
        lines.(wy) <- Bytes.to_string line
      end;
      Array.to_list lines |> String.concat "\n"
end

(* ── Wireworld ───────────────────────────────────────────────────────── *)

module Wireworld = struct
  type cell = Empty | Head | Tail | Conductor

  let char_of = function
    | Empty -> ' ' | Head -> 'H' | Tail -> 't' | Conductor -> '.'

  let cell_of = function
    | 'H' -> Head | 't' -> Tail | '.' -> Conductor | _ -> Empty

  let step g =
    Grid2D.map (fun x y cell ->
      match cell with
      | Empty -> Empty
      | Head  -> Tail
      | Tail  -> Conductor
      | Conductor ->
        let heads = List.length (List.filter (fun c -> c = Head) (Grid2D.neighbors8 g x y)) in
        if heads = 1 || heads = 2 then Head else Conductor
    ) g

  let run g steps =
    let rec go g n =
      if n >= steps then g
      else go (step g) (n + 1)
    in
    go g 0

  let to_string g = Grid2D.to_string char_of g

  let of_strings lines = Grid2D.of_string_grid lines cell_of

  (* A simple diode pattern *)
  let diode () =
    of_strings [
      "   .Ht...   ";
      "  .      .  ";
      "   ......   ";
    ]

  (* OR gate *)
  let or_gate () =
    of_strings [
      " Ht.....    ";
      "        .   ";
      " Ht.....    ";
    ]
end

(* ── Pattern Analysis ────────────────────────────────────────────────── *)

module Analysis = struct
  (* Bounding box of alive cells in a Life grid *)
  let bounding_box g =
    let min_x = ref max_int and max_x = ref min_int in
    let min_y = ref max_int and max_y = ref min_int in
    Grid2D.fold (fun () x y cell ->
      if cell = Life.Alive then begin
        if x < !min_x then min_x := x;
        if x > !max_x then max_x := x;
        if y < !min_y then min_y := y;
        if y > !max_y then max_y := y
      end
    ) () g;
    if !min_x > !max_x then None
    else Some (!min_x, !min_y, !max_x, !max_y)

  (* Center of mass *)
  let center_of_mass g =
    let sx = ref 0.0 and sy = ref 0.0 and n = ref 0 in
    Grid2D.fold (fun () x y cell ->
      if cell = Life.Alive then begin
        sx := !sx +. float_of_int x;
        sy := !sy +. float_of_int y;
        incr n
      end
    ) () g;
    if !n = 0 then (0.0, 0.0)
    else (!sx /. float_of_int !n, !sy /. float_of_int !n)

  (* Population over time *)
  let population_trace g steps =
    let trace = Array.make (steps + 1) 0 in
    let g = ref g in
    for i = 0 to steps do
      trace.(i) <- Life.population !g;
      if i < steps then g := Life.step !g
    done;
    trace

  (* ASCII sparkline of population *)
  let sparkline trace =
    let bars = [|'▁';'▂';'▃';'▄';'▅';'▆';'▇';'█'|] in
    let mn = Array.fold_left min max_int trace in
    let mx = Array.fold_left max min_int trace in
    let range = max 1 (mx - mn) in
    String.init (Array.length trace) (fun i ->
      let idx = (trace.(i) - mn) * 7 / range in
      bars.(min 7 (max 0 idx))
    )
end

(* ── Demo ────────────────────────────────────────────────────────────── *)

let () =
  print_endline "=== Cellular Automata ===\n";

  (* Game of Life: Glider *)
  print_endline "── Game of Life: Glider ──";
  let field = Life.create 20 10 in
  let field = Life.place ~onto:field (Life.glider ()) 1 1 in
  Printf.printf "Gen 0 (pop %d):\n%s\n\n" (Life.population field) (Life.to_string field);
  let field10 = Life.run field 10 in
  Printf.printf "Gen 10 (pop %d):\n%s\n\n" (Life.population field10) (Life.to_string field10);

  (* Period detection *)
  let blinker = Life.blinker () in
  (match Life.detect_period blinker with
   | Some p -> Printf.printf "Blinker period: %d\n" p
   | None   -> print_endline "Blinker: no period found");
  Printf.printf "Block is still life: %b\n\n" (Life.is_still (Life.block ()));

  (* Population trace with sparkline *)
  let field_big = Life.create 40 40 in
  let field_big = Life.place ~onto:field_big (Life.r_pentomino ()) 18 18 in
  let trace = Analysis.population_trace field_big 80 in
  Printf.printf "R-pentomino population (80 gen): %s\n" (Analysis.sparkline trace);
  Printf.printf "  start=%d peak=%d end=%d\n\n"
    trace.(0)
    (Array.fold_left max 0 trace)
    trace.(80);

  (* RLE *)
  let glider_rle = Life.of_rle "bo$2bo$3o!" in
  Printf.printf "Glider from RLE:\n%s\n\n" (Life.to_string glider_rle);

  (* Elementary CA: Rule 110 *)
  print_endline "── Elementary CA: Rule 110 ──";
  let row = Elementary.create_row 61 in
  let rows = Elementary.run 110 row 20 in
  print_endline (Elementary.to_string rows);
  Printf.printf "\nRule 110 classification: %s\n\n" (Elementary.classify_rule 110 200 101);

  (* Rule 30 *)
  print_endline "── Elementary CA: Rule 30 ──";
  let row30 = Elementary.create_row 41 in
  let rows30 = Elementary.run 30 row30 15 in
  print_endline (Elementary.to_string rows30);
  print_newline ();

  (* Langton's Ant *)
  print_endline "── Langton's Ant (500 steps) ──";
  let (grid, ant, _) = LangtonsAnt.run 25 25 500 in
  let black = Grid2D.count (fun b -> b) grid in
  Printf.printf "Black cells: %d\n%s\n\n" black (LangtonsAnt.to_string grid ant);

  (* Wireworld *)
  print_endline "── Wireworld: Diode ──";
  let ww = Wireworld.diode () in
  Printf.printf "Step 0:\n%s\n" (Wireworld.to_string ww);
  let ww3 = Wireworld.run ww 3 in
  Printf.printf "Step 3:\n%s\n\n" (Wireworld.to_string ww3);

  (* Bounding box & center of mass *)
  let g = Life.place ~onto:(Life.create 10 10) (Life.glider ()) 3 3 in
  (match Analysis.bounding_box g with
   | Some (x1,y1,x2,y2) -> Printf.printf "Glider bbox: (%d,%d)-(%d,%d)\n" x1 y1 x2 y2
   | None -> print_endline "Empty grid");
  let (cx,cy) = Analysis.center_of_mass g in
  Printf.printf "Glider center of mass: (%.1f, %.1f)\n" cx cy;

  print_endline "\n✓ All cellular automata demos complete."
