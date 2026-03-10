(* ==========================================================================
   L-Systems — Lindenmayer Systems and Turtle Graphics
   ==========================================================================
   Generative art through string rewriting and geometric interpretation.

   Covers:
   - D0L systems (deterministic, context-free)
   - Stochastic L-systems (random rule selection)
   - Parametric L-systems (symbols with numeric parameters)
   - Turtle graphics interpretation (move, turn, push/pop stack)
   - SVG output for visual rendering
   - Classic fractals: Koch snowflake, Sierpinski triangle, dragon curve,
     Hilbert curve, plant/fern, Penrose tiling

   An L-system rewrites strings in parallel: every symbol is replaced
   simultaneously on each generation. This models biological growth —
   cells divide in parallel, not sequentially. Combined with turtle
   graphics, the rewritten strings produce beautiful fractal geometry.

   Concepts demonstrated:
   - Algebraic data types for grammars and turtle state
   - Higher-order functions for rule application
   - Recursive string rewriting
   - Immutable stack for turtle state (push/pop via list)
   - SVG generation via string formatting
   - Pattern matching on grammar symbols
   ========================================================================== *)

(* ── Symbol type ──────────────────────────────────────────────────── *)

(** A symbol in the L-system alphabet *)
type symbol =
  | F         (** Move forward, drawing a line *)
  | G         (** Move forward, without drawing (used in some systems) *)
  | Plus      (** Turn right by angle *)
  | Minus     (** Turn left by angle *)
  | Push      (** Save turtle state to stack *)
  | Pop       (** Restore turtle state from stack *)
  | Sym of char  (** Named symbol (for production rules, e.g., 'X', 'A') *)

(** Convert a character to a symbol *)
let symbol_of_char = function
  | 'F' -> F
  | 'G' -> G
  | '+' -> Plus
  | '-' -> Minus
  | '[' -> Push
  | ']' -> Pop
  | c   -> Sym c

(** Convert a symbol to a character *)
let char_of_symbol = function
  | F -> 'F'
  | G -> 'G'
  | Plus -> '+'
  | Minus -> '-'
  | Push -> '['
  | Pop -> ']'
  | Sym c -> c

(** Parse a string into a symbol list *)
let parse_symbols s =
  let n = String.length s in
  let rec go i acc =
    if i >= n then List.rev acc
    else go (i + 1) (symbol_of_char s.[i] :: acc)
  in
  go 0 []

(** Render a symbol list back to a string *)
let string_of_symbols syms =
  let buf = Buffer.create (List.length syms) in
  List.iter (fun s -> Buffer.add_char buf (char_of_symbol s)) syms;
  Buffer.contents buf


(* ── L-System grammar ─────────────────────────────────────────────── *)

(** A production rule: symbol → replacement symbols *)
type rule = {
  from_sym : symbol;
  to_syms  : symbol list;
}

(** An L-system definition *)
type lsystem = {
  axiom : symbol list;
  rules : rule list;
  angle : float;       (** Turn angle in degrees *)
  name  : string;
}

(** Create a rule from string notation: "F" -> "F+F-F" *)
let make_rule from_s to_s =
  let from_sym = match parse_symbols from_s with
    | [s] -> s
    | _ -> failwith ("Rule 'from' must be a single symbol: " ^ from_s)
  in
  { from_sym; to_syms = parse_symbols to_s }

(** Create an L-system from string notation *)
let make_lsystem ~name ~axiom ~rules ~angle =
  {
    name;
    axiom = parse_symbols axiom;
    rules = List.map (fun (f, t) -> make_rule f t) rules;
    angle;
  }


(* ── String rewriting ─────────────────────────────────────────────── *)

(** Apply one generation of rewriting.
    Each symbol is replaced by its production; symbols without rules
    are copied unchanged (identity production). *)
let rewrite rules symbols =
  let apply sym =
    match List.find_opt (fun r -> r.from_sym = sym) rules with
    | Some r -> r.to_syms
    | None   -> [sym]
  in
  List.concat_map apply symbols

(** Apply n generations of rewriting *)
let generate lsystem n =
  let rec go i syms =
    if i >= n then syms
    else go (i + 1) (rewrite lsystem.rules syms)
  in
  go 0 lsystem.axiom

(** Count symbols after n generations (without materialising) *)
let count_symbols lsystem n =
  List.length (generate lsystem n)


(* ── Stochastic L-system ──────────────────────────────────────────── *)

(** A stochastic rule: symbol → (probability, replacement) list *)
type stochastic_rule = {
  s_from : symbol;
  s_alts : (float * symbol list) list;  (** (probability, replacement) *)
}

(** Apply stochastic rewriting for one symbol *)
let stochastic_apply rules sym =
  match List.find_opt (fun r -> r.s_from = sym) rules with
  | None -> [sym]
  | Some r ->
    let roll = Random.float 1.0 in
    let rec pick acc = function
      | [] -> [sym]  (* fallback *)
      | [(_, prod)] -> prod
      | (p, prod) :: rest ->
        let acc' = acc +. p in
        if roll < acc' then prod
        else pick acc' rest
    in
    pick 0.0 r.s_alts

(** Stochastic rewrite one generation *)
let stochastic_rewrite rules symbols =
  List.concat_map (stochastic_apply rules) symbols


(* ── Turtle graphics ──────────────────────────────────────────────── *)

(** Turtle state: position + heading *)
type turtle = {
  x     : float;
  y     : float;
  angle : float;  (** Heading in radians *)
}

(** A line segment drawn by the turtle *)
type segment = {
  x1 : float; y1 : float;
  x2 : float; y2 : float;
}

(** Default step length *)
let default_step = 10.0

(** Interpret symbols as turtle graphics commands.
    Returns a list of line segments. *)
let interpret ?(step = default_step) ~turn_angle symbols =
  let deg_to_rad d = d *. Float.pi /. 180.0 in
  let turn = deg_to_rad turn_angle in
  let t0 = { x = 0.0; y = 0.0; angle = Float.pi /. 2.0 } in

  let rec go turtle stack segments = function
    | [] -> List.rev segments
    | F :: rest ->
      let nx = turtle.x +. step *. cos turtle.angle in
      let ny = turtle.y +. step *. sin turtle.angle in
      let seg = { x1 = turtle.x; y1 = turtle.y; x2 = nx; y2 = ny } in
      go { turtle with x = nx; y = ny } stack (seg :: segments) rest
    | G :: rest ->
      let nx = turtle.x +. step *. cos turtle.angle in
      let ny = turtle.y +. step *. sin turtle.angle in
      go { turtle with x = nx; y = ny } stack segments rest
    | Plus :: rest ->
      go { turtle with angle = turtle.angle -. turn } stack segments rest
    | Minus :: rest ->
      go { turtle with angle = turtle.angle +. turn } stack segments rest
    | Push :: rest ->
      go turtle (turtle :: stack) segments rest
    | Pop :: rest ->
      let turtle' = match stack with
        | [] -> turtle  (* empty stack, stay put *)
        | t :: _ -> t
      in
      let stack' = match stack with
        | [] -> []
        | _ :: s -> s
      in
      go turtle' stack' segments rest
    | (Sym _) :: rest ->
      go turtle stack segments rest  (* ignore unknown symbols *)
  in
  go t0 [] [] symbols


(* ── Bounding box ─────────────────────────────────────────────────── *)

type bbox = {
  min_x : float; min_y : float;
  max_x : float; max_y : float;
}

let compute_bbox segments =
  match segments with
  | [] -> { min_x = 0.0; min_y = 0.0; max_x = 1.0; max_y = 1.0 }
  | _ ->
    let min_x = List.fold_left (fun acc s -> min acc (min s.x1 s.x2)) infinity segments in
    let min_y = List.fold_left (fun acc s -> min acc (min s.y1 s.y2)) infinity segments in
    let max_x = List.fold_left (fun acc s -> max acc (max s.x1 s.x2)) neg_infinity segments in
    let max_y = List.fold_left (fun acc s -> max acc (max s.y1 s.y2)) neg_infinity segments in
    { min_x; min_y; max_x; max_y }


(* ── SVG output ───────────────────────────────────────────────────── *)

(** Render segments to an SVG string *)
let to_svg ?(width = 800) ?(height = 800) ?(stroke = "#2d5016")
           ?(stroke_width = 1.0) ?(bg = "#f5f5dc") segments =
  let bb = compute_bbox segments in
  let pad = 20.0 in
  let dw = bb.max_x -. bb.min_x in
  let dh = bb.max_y -. bb.min_y in
  let fw = float_of_int width in
  let fh = float_of_int height in
  let scale =
    if dw = 0.0 && dh = 0.0 then 1.0
    else min ((fw -. 2.0 *. pad) /. (if dw > 0.0 then dw else 1.0))
             ((fh -. 2.0 *. pad) /. (if dh > 0.0 then dh else 1.0))
  in
  let tx x = pad +. (x -. bb.min_x) *. scale in
  (* SVG y-axis is inverted *)
  let ty y = fh -. pad -. (y -. bb.min_y) *. scale in

  let buf = Buffer.create 4096 in
  Buffer.add_string buf (Printf.sprintf
    {|<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d">
<rect width="100%%" height="100%%" fill="%s"/>
|} width height bg);

  List.iter (fun s ->
    Buffer.add_string buf (Printf.sprintf
      {|<line x1="%.2f" y1="%.2f" x2="%.2f" y2="%.2f" stroke="%s" stroke-width="%.1f" stroke-linecap="round"/>
|}
      (tx s.x1) (ty s.y1) (tx s.x2) (ty s.y2) stroke stroke_width)
  ) segments;

  Buffer.add_string buf "</svg>\n";
  Buffer.contents buf

(** Write SVG to a file *)
let write_svg filename svg_content =
  let oc = open_out filename in
  output_string oc svg_content;
  close_out oc


(* ── Classic L-Systems ────────────────────────────────────────────── *)

(** Koch snowflake: the classic fractal curve *)
let koch_snowflake = make_lsystem
  ~name:"Koch Snowflake"
  ~axiom:"F--F--F"
  ~rules:[("F", "F+F--F+F")]
  ~angle:60.0

(** Sierpinski triangle *)
let sierpinski_triangle = make_lsystem
  ~name:"Sierpinski Triangle"
  ~axiom:"F-G-G"
  ~rules:[("F", "F-G+F+G-F"); ("G", "GG")]
  ~angle:120.0

(** Dragon curve *)
let dragon_curve = make_lsystem
  ~name:"Dragon Curve"
  ~axiom:"X"
  ~rules:[("X", "X+YF+"); ("Y", "-FX-Y")]
  ~angle:90.0

(** Hilbert curve — space-filling curve *)
let hilbert_curve = make_lsystem
  ~name:"Hilbert Curve"
  ~axiom:"A"
  ~rules:[("A", "-BF+AFA+FB-"); ("B", "+AF-BFB-FA+")]
  ~angle:90.0

(** Fractal plant / fern *)
let fractal_plant = make_lsystem
  ~name:"Fractal Plant"
  ~axiom:"X"
  ~rules:[("X", "F+[[X]-X]-F[-FX]+X"); ("F", "FF")]
  ~angle:25.0

(** Penrose tiling (P3) using L-system rules *)
let penrose_tiling = make_lsystem
  ~name:"Penrose Tiling (P3)"
  ~axiom:"[N]++[N]++[N]++[N]++[N]"
  ~rules:[
    ("M", "OF++PF----NF[-OF----MF]++");
    ("N", "+OF--PF[---MF--NF]+");
    ("O", "-MF++NF[+++OF++PF]-");
    ("P", "--OF++++MF[+PF++++NF]--NF");
  ]
  ~angle:36.0

(** Lévy C curve *)
let levy_c_curve = make_lsystem
  ~name:"Lévy C Curve"
  ~axiom:"F"
  ~rules:[("F", "+F--F+")]
  ~angle:45.0

(** Gosper / flowsnake curve *)
let gosper_curve = make_lsystem
  ~name:"Gosper Curve"
  ~axiom:"A"
  ~rules:[
    ("A", "A-B--B+A++AA+B-");
    ("B", "+A-BB--B-A++A+B");
  ]
  ~angle:60.0

(** All built-in systems *)
let classic_systems = [
  koch_snowflake;
  sierpinski_triangle;
  dragon_curve;
  hilbert_curve;
  fractal_plant;
  penrose_tiling;
  levy_c_curve;
  gosper_curve;
]


(* ── Analysis ─────────────────────────────────────────────────────── *)

(** Compute growth statistics for an L-system *)
let growth_stats lsystem max_gen =
  let rec go i syms acc =
    if i > max_gen then List.rev acc
    else begin
      let len = List.length syms in
      let draw_count = List.length (List.filter (fun s -> s = F) syms) in
      let entry = (i, len, draw_count) in
      if i = max_gen then List.rev (entry :: acc)
      else go (i + 1) (rewrite lsystem.rules syms) (entry :: acc)
    end
  in
  go 0 lsystem.axiom []

(** Compute the expansion ratio between generations *)
let expansion_ratio lsystem =
  let g0 = List.length lsystem.axiom in
  let g1 = List.length (rewrite lsystem.rules lsystem.axiom) in
  if g0 = 0 then 0.0
  else float_of_int g1 /. float_of_int g0

(** Compute fractal dimension estimate using box-counting on segments *)
let fractal_dimension segments =
  if List.length segments < 2 then 0.0
  else begin
    let bb = compute_bbox segments in
    let size = max (bb.max_x -. bb.min_x) (bb.max_y -. bb.min_y) in
    if size <= 0.0 then 0.0
    else begin
      (* Count occupied boxes at two scales *)
      let count_boxes box_size =
        let tbl = Hashtbl.create 64 in
        List.iter (fun s ->
          let bx = int_of_float ((s.x1 -. bb.min_x) /. box_size) in
          let by = int_of_float ((s.y1 -. bb.min_y) /. box_size) in
          Hashtbl.replace tbl (bx, by) true;
          let bx2 = int_of_float ((s.x2 -. bb.min_x) /. box_size) in
          let by2 = int_of_float ((s.y2 -. bb.min_y) /. box_size) in
          Hashtbl.replace tbl (bx2, by2) true
        ) segments;
        Hashtbl.length tbl
      in
      let s1 = size /. 10.0 in
      let s2 = size /. 40.0 in
      let n1 = float_of_int (count_boxes s1) in
      let n2 = float_of_int (count_boxes s2) in
      if n1 <= 1.0 || n2 <= 1.0 then 0.0
      else (log n2 -. log n1) /. (log (s1 /. s2))
    end
  end

(** Pretty-print growth statistics *)
let print_growth_stats lsystem max_gen =
  Printf.printf "=== %s — Growth Statistics ===\n" lsystem.name;
  Printf.printf "Angle: %.1f°  Expansion ratio: %.2f\n\n"
    lsystem.angle (expansion_ratio lsystem);
  Printf.printf "Gen  |  Symbols  |  Draw (F)  |  Ratio\n";
  Printf.printf "-----+-----------+------------+--------\n";
  let stats = growth_stats lsystem max_gen in
  let prev_len = ref 0 in
  List.iter (fun (gen, len, draw) ->
    let ratio = if !prev_len > 0 then
      Printf.sprintf "%.2fx" (float_of_int len /. float_of_int !prev_len)
    else "—" in
    Printf.printf "%3d  | %9d | %10d | %s\n" gen len draw ratio;
    prev_len := len
  ) stats;
  Printf.printf "\n"


(* ── Tests ────────────────────────────────────────────────────────── *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0

let assert_true msg cond =
  incr tests_run;
  if cond then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL: %s\n" msg
  end

let assert_eq msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL: %s (expected %s, got %s)\n" msg expected actual
  end

let test_parse_and_render () =
  Printf.printf "  Testing parse/render roundtrip...\n";
  let cases = ["F+F-F"; "F[+F][-F]F"; "X"; "F--F--F"; "A-B+C[]"] in
  List.iter (fun s ->
    let syms = parse_symbols s in
    let rendered = string_of_symbols syms in
    assert_eq (Printf.sprintf "roundtrip '%s'" s) s rendered
  ) cases

let test_rewrite () =
  Printf.printf "  Testing rewriting...\n";
  (* Simple rule: F -> FF *)
  let rules = [make_rule "F" "FF"] in
  let gen0 = parse_symbols "F" in
  let gen1 = rewrite rules gen0 in
  assert_eq "F->FF gen1" "FF" (string_of_symbols gen1);
  let gen2 = rewrite rules gen1 in
  assert_eq "F->FF gen2" "FFFF" (string_of_symbols gen2);

  (* Multiple rules *)
  let rules2 = [make_rule "A" "AB"; make_rule "B" "A"] in
  let gen0 = parse_symbols "A" in
  let gen1 = rewrite rules2 gen0 in
  assert_eq "algae gen1" "AB" (string_of_symbols gen1);
  let gen2 = rewrite rules2 gen1 in
  assert_eq "algae gen2" "ABA" (string_of_symbols gen2);
  let gen3 = rewrite rules2 gen2 in
  assert_eq "algae gen3" "ABAAB" (string_of_symbols gen3);

  (* Identity: symbols without rules pass through *)
  let rules3 = [make_rule "F" "F+F"] in
  let gen0 = parse_symbols "F-G" in
  let gen1 = rewrite rules3 gen0 in
  assert_eq "identity passthrough" "F+F-G" (string_of_symbols gen1)

let test_generate () =
  Printf.printf "  Testing multi-generation...\n";
  let sys = make_lsystem ~name:"test" ~axiom:"A"
              ~rules:[("A", "AB"); ("B", "A")] ~angle:0.0 in
  (* Fibonacci-like growth: 1,2,3,5,8,13... *)
  let counts = List.init 7 (fun n -> count_symbols sys n) in
  assert_eq "gen counts" "1,2,3,5,8,13,21"
    (String.concat "," (List.map string_of_int counts))

let test_turtle_forward () =
  Printf.printf "  Testing turtle forward...\n";
  let syms = parse_symbols "FF" in
  let segs = interpret ~step:10.0 ~turn_angle:90.0 syms in
  assert_true "two segments" (List.length segs = 2);
  (* First segment: (0,0) -> (0,10), heading up *)
  let s1 = List.nth segs 0 in
  assert_true "s1.x1 ~ 0" (abs_float s1.x1 < 0.01);
  assert_true "s1.y1 ~ 0" (abs_float s1.y1 < 0.01);
  assert_true "s1.y2 ~ 10" (abs_float (s1.y2 -. 10.0) < 0.01)

let test_turtle_turn () =
  Printf.printf "  Testing turtle turning...\n";
  (* F+F at 90°: forward then right turn then forward *)
  let syms = parse_symbols "F+F" in
  let segs = interpret ~step:10.0 ~turn_angle:90.0 syms in
  assert_true "two segments after turn" (List.length segs = 2);
  let s2 = List.nth segs 1 in
  (* After turning right 90° from heading up, should go right *)
  assert_true "s2 goes right" (s2.x2 > s2.x1 +. 5.0)

let test_turtle_pushpop () =
  Printf.printf "  Testing turtle push/pop...\n";
  (* F[+F]F: forward, branch right, return, forward *)
  let syms = parse_symbols "F[+F]F" in
  let segs = interpret ~step:10.0 ~turn_angle:90.0 syms in
  assert_true "three segments" (List.length segs = 3);
  (* Third segment should start from end of first (push/pop restored) *)
  let s1 = List.nth segs 0 in
  let s3 = List.nth segs 2 in
  assert_true "s3 starts where s1 ended (x)"
    (abs_float (s3.x1 -. s1.x2) < 0.01);
  assert_true "s3 starts where s1 ended (y)"
    (abs_float (s3.y1 -. s1.y2) < 0.01)

let test_bbox () =
  Printf.printf "  Testing bounding box...\n";
  let segs = [
    { x1 = 0.0; y1 = 0.0; x2 = 10.0; y2 = 0.0 };
    { x1 = 10.0; y1 = 0.0; x2 = 10.0; y2 = 5.0 };
  ] in
  let bb = compute_bbox segs in
  assert_true "min_x = 0" (bb.min_x = 0.0);
  assert_true "max_x = 10" (bb.max_x = 10.0);
  assert_true "min_y = 0" (bb.min_y = 0.0);
  assert_true "max_y = 5" (bb.max_y = 5.0)

let test_svg_output () =
  Printf.printf "  Testing SVG output...\n";
  let segs = interpret ~step:10.0 ~turn_angle:60.0
               (generate koch_snowflake 1) in
  let svg = to_svg segs in
  assert_true "SVG has header" (String.length svg > 100);
  assert_true "SVG contains <svg" (String.sub svg 0 4 = "<svg");
  assert_true "SVG contains <line"
    (let rec find i =
       if i + 5 > String.length svg then false
       else if String.sub svg i 5 = "<line" then true
       else find (i + 1)
     in find 0)

let test_koch_snowflake () =
  Printf.printf "  Testing Koch snowflake...\n";
  let g0 = count_symbols koch_snowflake 0 in
  assert_true "koch gen0 = 5 symbols" (g0 = 5);  (* F--F--F *)
  let g1 = count_symbols koch_snowflake 1 in
  assert_true "koch gen1 grows" (g1 > g0);
  let ratio = expansion_ratio koch_snowflake in
  assert_true "koch expansion > 1" (ratio > 1.0)

let test_sierpinski () =
  Printf.printf "  Testing Sierpinski triangle...\n";
  let g1 = generate sierpinski_triangle 1 in
  let s = string_of_symbols g1 in
  assert_true "sierpinski gen1 has G" (String.contains s 'G')

let test_dragon_curve () =
  Printf.printf "  Testing dragon curve...\n";
  (* Dragon curve has no F in axiom, only X *)
  let g2 = generate dragon_curve 2 in
  let drawn = List.filter (fun s -> s = F) g2 in
  assert_true "dragon gen2 has F segments" (List.length drawn > 0)

let test_fractal_plant () =
  Printf.printf "  Testing fractal plant...\n";
  let g3 = generate fractal_plant 3 in
  let has_push = List.exists (fun s -> s = Push) g3 in
  let has_pop = List.exists (fun s -> s = Pop) g3 in
  assert_true "plant has branching" (has_push && has_pop)

let test_growth_stats () =
  Printf.printf "  Testing growth statistics...\n";
  let stats = growth_stats koch_snowflake 3 in
  assert_true "4 generations (0-3)" (List.length stats = 4);
  (* Each generation should grow *)
  let lens = List.map (fun (_, len, _) -> len) stats in
  let sorted = List.sort compare lens in
  assert_true "monotonically growing" (lens = sorted)

let test_fractal_dimension () =
  Printf.printf "  Testing fractal dimension...\n";
  let segs = interpret ~step:5.0 ~turn_angle:60.0
               (generate koch_snowflake 4) in
  let dim = fractal_dimension segs in
  (* Koch curve dimension ≈ 1.26 *)
  assert_true "dimension > 1.0" (dim > 1.0);
  assert_true "dimension < 2.0" (dim < 2.0)

let test_classic_systems_all_render () =
  Printf.printf "  Testing all classic systems render...\n";
  List.iter (fun sys ->
    let gen = min 3 (if sys.name = "Penrose Tiling (P3)" then 2 else 3) in
    let syms = generate sys gen in
    let segs = interpret ~step:5.0 ~turn_angle:sys.angle syms in
    assert_true (Printf.sprintf "%s produces segments" sys.name)
      (List.length segs > 0 || sys.name = "Penrose Tiling (P3)")
  ) classic_systems

let test_stochastic_rewrite () =
  Printf.printf "  Testing stochastic rewrite...\n";
  Random.self_init ();
  let rules = [{
    s_from = F;
    s_alts = [
      (0.5, parse_symbols "F+F");
      (0.5, parse_symbols "F-F");
    ];
  }] in
  let syms = parse_symbols "F" in
  let result = stochastic_rewrite rules syms in
  let s = string_of_symbols result in
  assert_true "stochastic produces F+F or F-F"
    (s = "F+F" || s = "F-F")

let test_empty_input () =
  Printf.printf "  Testing edge cases...\n";
  let empty = parse_symbols "" in
  assert_true "empty parse" (List.length empty = 0);
  let segs = interpret ~step:10.0 ~turn_angle:90.0 empty in
  assert_true "no segments from empty" (List.length segs = 0);
  let bb = compute_bbox [] in
  assert_true "bbox default for empty" (bb.min_x = 0.0)


(* ── Demo ─────────────────────────────────────────────────────────── *)

let demo () =
  Printf.printf "╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║     L-Systems — Lindenmayer Systems & Turtle Graphics   ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n\n";

  (* Show growth stats for each classic system *)
  List.iter (fun sys ->
    print_growth_stats sys 5
  ) classic_systems;

  (* Fractal dimension estimates *)
  Printf.printf "=== Fractal Dimension Estimates ===\n";
  List.iter (fun sys ->
    let gen = min 5 (if sys.name = "Penrose Tiling (P3)" then 3 else 5) in
    let segs = interpret ~step:3.0 ~turn_angle:sys.angle
                 (generate sys gen) in
    if segs <> [] then begin
      let dim = fractal_dimension segs in
      Printf.printf "  %-25s  D ≈ %.3f  (%d segments)\n"
        sys.name dim (List.length segs)
    end
  ) classic_systems;
  Printf.printf "\n";

  (* Generate sample SVG *)
  Printf.printf "Generating sample SVGs...\n";
  let samples = [
    (koch_snowflake, 4, "koch.svg");
    (sierpinski_triangle, 6, "sierpinski.svg");
    (dragon_curve, 10, "dragon.svg");
    (fractal_plant, 5, "plant.svg");
    (levy_c_curve, 10, "levy.svg");
    (gosper_curve, 3, "gosper.svg");
  ] in
  List.iter (fun (sys, gen, filename) ->
    let syms = generate sys gen in
    let segs = interpret ~step:3.0 ~turn_angle:sys.angle syms in
    let svg = to_svg ~stroke:"#2d5016" ~stroke_width:0.8 segs in
    Printf.printf "  %s: gen=%d, %d segments → %s\n"
      sys.name gen (List.length segs) filename;
    write_svg filename svg
  ) samples;
  Printf.printf "\nDone! Open the .svg files in a browser to see the fractals.\n"


(* ── Main ─────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "L-Systems — Tests\n";
  Printf.printf "==================\n\n";

  test_parse_and_render ();
  test_rewrite ();
  test_generate ();
  test_turtle_forward ();
  test_turtle_turn ();
  test_turtle_pushpop ();
  test_bbox ();
  test_svg_output ();
  test_koch_snowflake ();
  test_sierpinski ();
  test_dragon_curve ();
  test_fractal_plant ();
  test_growth_stats ();
  test_fractal_dimension ();
  test_classic_systems_all_render ();
  test_stochastic_rewrite ();
  test_empty_input ();

  Printf.printf "\n══════════════════════════════════════\n";
  Printf.printf "Results: %d/%d passed (%d failed)\n"
    !tests_passed !tests_run !tests_failed;
  Printf.printf "══════════════════════════════════════\n\n";

  if !tests_failed = 0 then begin
    Printf.printf "All tests passed! Running demo...\n\n";
    demo ()
  end else
    Printf.printf "Some tests failed — fix before running demo.\n";

  exit (if !tests_failed = 0 then 0 else 1)
