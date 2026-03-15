(* Tests for cellular_automata.ml *)

#use "test_framework.ml";;
#use "cellular_automata.ml"


let test name f =
  try
    f ();
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  with e ->
    incr tests_failed;
    Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string e)

let () =
  print_endline "\n=== Cellular Automata Tests ===\n";

  print_endline "── Grid2D ──";

  test "create and get" (fun () ->
    let g = Grid2D.create 5 5 0 in
    assert (Grid2D.get g 0 0 = 0));

  test "set and get" (fun () ->
    let g = Grid2D.create 5 5 0 in
    Grid2D.set g 2 3 42;
    assert (Grid2D.get g 2 3 = 42));

  test "toroidal wrapping" (fun () ->
    let g = Grid2D.create 5 5 0 in
    Grid2D.set g 0 0 1;
    assert (Grid2D.get g 5 5 = 1);
    assert (Grid2D.get g (-5) (-5) = 1));

  test "copy independence" (fun () ->
    let g = Grid2D.create 3 3 0 in
    Grid2D.set g 1 1 1;
    let g2 = Grid2D.copy g in
    Grid2D.set g2 1 1 99;
    assert (Grid2D.get g 1 1 = 1));

  test "count" (fun () ->
    let g = Grid2D.create 3 3 false in
    Grid2D.set g 0 0 true;
    Grid2D.set g 2 2 true;
    assert (Grid2D.count (fun b -> b) g = 2));

  test "neighbors8 count" (fun () ->
    let g = Grid2D.create 3 3 1 in
    let n = Grid2D.neighbors8 g 1 1 in
    assert (List.length n = 8));

  test "neighbors4 count" (fun () ->
    let n = Grid2D.neighbors4 (Grid2D.create 3 3 0) 1 1 in
    assert (List.length n = 4));

  test "fold sum" (fun () ->
    let g = Grid2D.create 2 2 1 in
    let s = Grid2D.fold (fun acc _ _ v -> acc + v) 0 g in
    assert (s = 4));

  test "of_string_grid roundtrip" (fun () ->
    let g = Grid2D.of_string_grid ["ab";"cd"] (fun c -> c) in
    assert (Grid2D.get g 0 0 = 'a');
    assert (Grid2D.get g 1 1 = 'd'));

  print_endline "\n── Game of Life ──";

  test "block is still life" (fun () ->
    assert (Life.is_still (Life.block ())));

  test "blinker period 2" (fun () ->
    match Life.detect_period (Life.blinker ()) with
    | Some 2 -> ()
    | Some n -> failwith (Printf.sprintf "got period %d" n)
    | None -> failwith "no period");

  test "glider moves" (fun () ->
    let g = Life.create 20 20 in
    let g = Life.place ~onto:g (Life.glider ()) 1 1 in
    let g4 = Life.run g 4 in
    assert (Life.population g = Life.population g4);
    let (cx0,cy0) = Analysis.center_of_mass g in
    let (cx4,cy4) = Analysis.center_of_mass g4 in
    assert (cx4 > cx0 && cy4 > cy0));

  test "empty grid stays empty" (fun () ->
    let g = Life.create 5 5 in
    let g1 = Life.step g in
    assert (Life.population g1 = 0));

  test "beacon period 2" (fun () ->
    match Life.detect_period (Life.beacon ()) with
    | Some 2 -> ()
    | _ -> failwith "beacon should have period 2");

  test "r_pentomino population grows" (fun () ->
    let g = Life.create 40 40 in
    let g = Life.place ~onto:g (Life.r_pentomino ()) 18 18 in
    let pop0 = Life.population g in
    let g50 = Life.run g 50 in
    assert (Life.population g50 > pop0));

  test "place preserves pattern" (fun () ->
    let g = Life.create 10 10 in
    let p = Life.glider () in
    let g = Life.place ~onto:g p 3 3 in
    assert (Grid2D.get g 4 3 = Life.Alive));

  test "RLE glider decode" (fun () ->
    let g = Life.of_rle "bo$2bo$3o!" in
    assert (Life.population g = 5));

  test "population_trace length" (fun () ->
    let g = Life.create 10 10 in
    let t = Analysis.population_trace g 20 in
    assert (Array.length t = 21));

  test "sparkline non-empty" (fun () ->
    let t = [|1;2;3;4;5|] in
    assert (String.length (Analysis.sparkline t) = 5));

  test "bounding_box empty" (fun () ->
    let g = Life.create 5 5 in
    assert (Analysis.bounding_box g = None));

  test "bounding_box glider" (fun () ->
    let g = Life.create 10 10 in
    let g = Life.place ~onto:g (Life.glider ()) 2 3 in
    match Analysis.bounding_box g with
    | Some (2,3,4,5) -> ()
    | Some (x1,y1,x2,y2) -> failwith (Printf.sprintf "got (%d,%d,%d,%d)" x1 y1 x2 y2)
    | None -> failwith "none");

  print_endline "\n── Elementary CA ──";

  test "create_row center bit" (fun () ->
    let r = Elementary.create_row 11 in
    assert (r.(5) = true);
    assert (r.(0) = false));

  test "rule 0 kills everything" (fun () ->
    let r = Elementary.create_row 11 in
    let r1 = Elementary.step 0 r in
    assert (Elementary.population r1 = 0));

  test "rule 255 fills everything" (fun () ->
    let r = Elementary.create_row 11 in
    let r1 = Elementary.step 255 r in
    assert (Elementary.population r1 = 11));

  test "rule 110 run" (fun () ->
    let r = Elementary.create_row 21 in
    let rows = Elementary.run 110 r 10 in
    assert (Array.length rows = 11);
    assert (Elementary.population rows.(10) > 0));

  test "row_to_string length" (fun () ->
    let r = Elementary.create_row 15 in
    assert (String.length (Elementary.row_to_string r) = 15));

  test "classify_rule returns string" (fun () ->
    let s = Elementary.classify_rule 110 50 31 in
    assert (String.length s > 0));

  print_endline "\n── Langton's Ant ──";

  test "ant runs without crash" (fun () ->
    let (_, _, steps) = LangtonsAnt.run 15 15 100 in
    assert (steps = 100));

  test "ant creates black cells" (fun () ->
    let (grid, _, _) = LangtonsAnt.run 20 20 200 in
    assert (Grid2D.count (fun b -> b) grid > 0));

  test "ant to_string has ant char" (fun () ->
    let (grid, ant, _) = LangtonsAnt.run 10 10 5 in
    let s = LangtonsAnt.to_string grid ant in
    assert (String.contains s '^' || String.contains s 'v' ||
            String.contains s '<' || String.contains s '>'));

  test "turn_right cycle" (fun () ->
    let open LangtonsAnt in
    assert (turn_right (turn_right (turn_right (turn_right North))) = North));

  test "turn_left cycle" (fun () ->
    let open LangtonsAnt in
    assert (turn_left (turn_left (turn_left (turn_left East))) = East));

  print_endline "\n── Wireworld ──";

  test "head becomes tail" (fun () ->
    let g = Grid2D.create 3 1 Wireworld.Empty in
    Grid2D.set g 1 0 Wireworld.Head;
    let g' = Wireworld.step g in
    assert (Grid2D.get g' 1 0 = Wireworld.Tail));

  test "tail becomes conductor" (fun () ->
    let g = Grid2D.create 3 1 Wireworld.Empty in
    Grid2D.set g 1 0 Wireworld.Tail;
    let g' = Wireworld.step g in
    assert (Grid2D.get g' 1 0 = Wireworld.Conductor));

  test "conductor with 1 head neighbor becomes head" (fun () ->
    let g = Grid2D.create 3 1 Wireworld.Empty in
    Grid2D.set g 0 0 Wireworld.Head;
    Grid2D.set g 1 0 Wireworld.Conductor;
    let g' = Wireworld.step g in
    assert (Grid2D.get g' 1 0 = Wireworld.Head));

  test "conductor with 0 heads stays conductor" (fun () ->
    let g = Grid2D.create 3 1 Wireworld.Empty in
    Grid2D.set g 1 0 Wireworld.Conductor;
    let g' = Wireworld.step g in
    assert (Grid2D.get g' 1 0 = Wireworld.Conductor));

  test "conductor with 3 heads stays conductor" (fun () ->
    let g = Wireworld.of_strings ["HHH";"H.H"] in
    let g' = Wireworld.step g in
    (* center of top row has >2 head neighbors *)
    assert (Grid2D.get g' 1 1 = Wireworld.Conductor));

  test "diode creates valid grid" (fun () ->
    let g = Wireworld.diode () in
    assert (g.Grid2D.width > 0 && g.Grid2D.height > 0));

  test "or_gate creates valid grid" (fun () ->
    let g = Wireworld.or_gate () in
    assert (g.Grid2D.width > 0));

  test "wireworld run multiple steps" (fun () ->
    let g = Wireworld.diode () in
    let g5 = Wireworld.run g 5 in
    assert (g5.Grid2D.width = g.Grid2D.width));

  test "wireworld to_string" (fun () ->
    let g = Wireworld.of_strings ["H.t"] in
    let s = Wireworld.to_string g in
    assert (String.contains s 'H'));

  test "empty stays empty" (fun () ->
    let g = Grid2D.create 3 3 Wireworld.Empty in
    let g' = Wireworld.step g in
    assert (Grid2D.count (fun c -> c <> Wireworld.Empty) g' = 0));

  print_endline "\n── Analysis ──";

  test "center_of_mass single cell" (fun () ->
    let g = Life.create 10 10 in
    Grid2D.set g 5 5 Life.Alive;
    let (cx, cy) = Analysis.center_of_mass g in
    assert (cx = 5.0 && cy = 5.0));

  (* Summary *)
  test_summary ()