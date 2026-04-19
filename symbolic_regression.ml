(* Symbolic Regression via Genetic Programming
   =============================================
   Discovers mathematical formulas from data using evolutionary computation.
   Features: expression trees, tournament selection, subtree crossover/mutation,
   parsimony pressure, algebraic simplification, ASCII plotting, interactive REPL.

   Compile: ocamlfind ocamlopt symbolic_regression.ml -o symbolic_regression
       or: ocamlfind ocamlc symbolic_regression.ml -o symbolic_regression
   Run: ./symbolic_regression
*)

let () = Random.self_init ()

(* === Expression Tree === *)

type expr =
  | Const of float
  | Var of string
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Sin of expr
  | Cos of expr
  | Exp of expr
  | Log of expr
  | Abs of expr
  | Sqrt of expr

(* === Parameters === *)

type params = {
  mutable pop_size : int;
  mutable generations : int;
  mutable max_depth : int;
  mutable tournament_size : int;
  mutable crossover_rate : float;
  mutable mutation_rate : float;
  mutable elitism : int;
  mutable parsimony : float;
}

let default_params () = {
  pop_size = 200;
  generations = 50;
  max_depth = 6;
  tournament_size = 5;
  crossover_rate = 0.7;
  mutation_rate = 0.2;
  elitism = 2;
  parsimony = 0.001;
}

let params = default_params ()

(* === Utilities === *)

let protected_div a b = if Float.abs b < 1e-10 then 1.0 else a /. b
let protected_log x = if x <= 0.0 then 0.0 else Float.log x
let protected_sqrt x = if x < 0.0 then Float.sqrt (Float.abs x) else Float.sqrt x
let protected_exp x = let r = Float.exp (Float.min x 20.0) in if Float.is_finite r then r else 1e8

let rec size = function
  | Const _ | Var _ -> 1
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> 1 + size a + size b
  | Sin a | Cos a | Exp a | Log a | Abs a | Sqrt a -> 1 + size a

let rec depth = function
  | Const _ | Var _ -> 1
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> 1 + max (depth a) (depth b)
  | Sin a | Cos a | Exp a | Log a | Abs a | Sqrt a -> 1 + depth a

(* === Random Tree Generation === *)

let variables = [| "x" |]

let random_const () = (Random.float 10.0) -. 5.0

let random_terminal () =
  if Random.float 1.0 < 0.5 then Var variables.(Random.int (Array.length variables))
  else Const (Float.round ~digits:2 (random_const ()))

let random_function e1 e2 =
  match Random.int 4 with
  | 0 -> Add (e1, e2)
  | 1 -> Sub (e1, e2)
  | 2 -> Mul (e1, e2)
  | _ -> Div (e1, e2)

let random_unary e =
  match Random.int 5 with
  | 0 -> Sin e
  | 1 -> Cos e
  | 2 -> Exp e
  | 3 -> Log e
  | _ -> Abs e

let rec grow max_d d =
  if d >= max_d then random_terminal ()
  else if d < 2 || Random.float 1.0 < 0.7 then begin
    if Random.float 1.0 < 0.15 then random_unary (grow max_d (d + 1))
    else random_function (grow max_d (d + 1)) (grow max_d (d + 1))
  end else random_terminal ()

let rec full max_d d =
  if d >= max_d then random_terminal ()
  else if Random.float 1.0 < 0.15 then random_unary (full max_d (d + 1))
  else random_function (full max_d (d + 1)) (full max_d (d + 1))

let ramped_half_and_half max_d =
  let d = 2 + Random.int (max (max_d - 1) 1) in
  if Random.bool () then grow d 0 else full d 0

(* === Evaluation === *)

let eval_expr env expr =
  let lookup v = try List.assoc v env with Not_found -> 0.0 in
  let rec ev = function
    | Const c -> c
    | Var v -> lookup v
    | Add (a, b) -> ev a +. ev b
    | Sub (a, b) -> ev a -. ev b
    | Mul (a, b) -> ev a *. ev b
    | Div (a, b) -> protected_div (ev a) (ev b)
    | Sin a -> Float.sin (ev a)
    | Cos a -> Float.cos (ev a)
    | Exp a -> protected_exp (ev a)
    | Log a -> protected_log (ev a)
    | Abs a -> Float.abs (ev a)
    | Sqrt a -> protected_sqrt (ev a)
  in
  let r = ev expr in
  if Float.is_finite r then r else 1e8

(* === Fitness === *)

let mse data expr =
  let n = Array.length data in
  if n = 0 then Float.infinity
  else begin
    let sum = ref 0.0 in
    for i = 0 to n - 1 do
      let (x, y) = data.(i) in
      let pred = eval_expr [("x", x)] expr in
      let err = pred -. y in
      sum := !sum +. err *. err
    done;
    !sum /. float_of_int n
  end

let fitness data expr =
  let m = mse data expr in
  m +. params.parsimony *. float_of_int (size expr)

(* === Genetic Operators === *)

let rec count_nodes = function
  | Const _ | Var _ -> 1
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) -> 1 + count_nodes a + count_nodes b
  | Sin a | Cos a | Exp a | Log a | Abs a | Sqrt a -> 1 + count_nodes a

let rec get_node expr idx =
  if idx = 0 then expr
  else match expr with
    | Const _ | Var _ -> expr
    | Sin a | Cos a | Exp a | Log a | Abs a | Sqrt a -> get_node a (idx - 1)
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) ->
      let la = count_nodes a in
      if idx - 1 < la then get_node a (idx - 1)
      else get_node b (idx - 1 - la)

let rec set_node expr idx replacement =
  if idx = 0 then replacement
  else match expr with
    | Const _ | Var _ -> expr
    | Sin a -> Sin (set_node a (idx - 1) replacement)
    | Cos a -> Cos (set_node a (idx - 1) replacement)
    | Exp a -> Exp (set_node a (idx - 1) replacement)
    | Log a -> Log (set_node a (idx - 1) replacement)
    | Abs a -> Abs (set_node a (idx - 1) replacement)
    | Sqrt a -> Sqrt (set_node a (idx - 1) replacement)
    | Add (a, b) ->
      let la = count_nodes a in
      if idx - 1 < la then Add (set_node a (idx - 1) replacement, b)
      else Add (a, set_node b (idx - 1 - la) replacement)
    | Sub (a, b) ->
      let la = count_nodes a in
      if idx - 1 < la then Sub (set_node a (idx - 1) replacement, b)
      else Sub (a, set_node b (idx - 1 - la) replacement)
    | Mul (a, b) ->
      let la = count_nodes a in
      if idx - 1 < la then Mul (set_node a (idx - 1) replacement, b)
      else Mul (a, set_node b (idx - 1 - la) replacement)
    | Div (a, b) ->
      let la = count_nodes a in
      if idx - 1 < la then Div (set_node a (idx - 1) replacement, b)
      else Div (a, set_node b (idx - 1 - la) replacement)

let crossover p1 p2 =
  let n1 = count_nodes p1 in
  let n2 = count_nodes p2 in
  let i1 = Random.int n1 in
  let i2 = Random.int n2 in
  let subtree = get_node p2 i2 in
  let child = set_node p1 i1 subtree in
  if depth child > params.max_depth + 2 then p1 else child

let point_mutation expr =
  let n = count_nodes expr in
  let idx = Random.int n in
  let node = get_node expr idx in
  let replacement = match node with
    | Const _ -> Const (Float.round ~digits:2 (random_const ()))
    | Var _ -> random_terminal ()
    | _ -> grow 3 0
  in
  set_node expr idx replacement

let subtree_mutation expr =
  let n = count_nodes expr in
  let idx = Random.int n in
  let new_subtree = grow 3 0 in
  set_node expr idx new_subtree

let mutate expr =
  if Random.bool () then point_mutation expr else subtree_mutation expr

(* === Selection === *)

let tournament_select pop fitnesses =
  let best = ref 0 in
  let best_f = ref Float.infinity in
  for _ = 1 to params.tournament_size do
    let i = Random.int (Array.length pop) in
    if fitnesses.(i) < !best_f then begin
      best := i;
      best_f := fitnesses.(i)
    end
  done;
  pop.(!best)

(* === Pretty Printing === *)

let rec to_string = function
  | Const c ->
    if Float.equal c (Float.round c) then Printf.sprintf "%.0f" c
    else Printf.sprintf "%.2f" c
  | Var v -> v
  | Add (a, b) -> Printf.sprintf "(%s + %s)" (to_string a) (to_string b)
  | Sub (a, b) -> Printf.sprintf "(%s - %s)" (to_string a) (to_string b)
  | Mul (a, b) -> Printf.sprintf "(%s * %s)" (to_string a) (to_string b)
  | Div (a, b) -> Printf.sprintf "(%s / %s)" (to_string a) (to_string b)
  | Sin a -> Printf.sprintf "sin(%s)" (to_string a)
  | Cos a -> Printf.sprintf "cos(%s)" (to_string a)
  | Exp a -> Printf.sprintf "exp(%s)" (to_string a)
  | Log a -> Printf.sprintf "log(%s)" (to_string a)
  | Abs a -> Printf.sprintf "abs(%s)" (to_string a)
  | Sqrt a -> Printf.sprintf "sqrt(%s)" (to_string a)

(* === Simplification === *)

let rec simplify = function
  | Add (Const 0.0, b) -> simplify b
  | Add (a, Const 0.0) -> simplify a
  | Add (Const a, Const b) -> Const (a +. b)
  | Sub (a, Const 0.0) -> simplify a
  | Sub (Const a, Const b) -> Const (a -. b)
  | Mul (Const 0.0, _) -> Const 0.0
  | Mul (_, Const 0.0) -> Const 0.0
  | Mul (Const 1.0, b) -> simplify b
  | Mul (a, Const 1.0) -> simplify a
  | Mul (Const a, Const b) -> Const (a *. b)
  | Div (a, Const 1.0) -> simplify a
  | Div (Const 0.0, _) -> Const 0.0
  | Div (Const a, Const b) -> Const (protected_div a b)
  | Add (a, b) -> let a' = simplify a and b' = simplify b in
    if a' = a && b' = b then Add (a, b) else simplify (Add (a', b'))
  | Sub (a, b) -> let a' = simplify a and b' = simplify b in
    if a' = a && b' = b then Sub (a, b) else simplify (Sub (a', b'))
  | Mul (a, b) -> let a' = simplify a and b' = simplify b in
    if a' = a && b' = b then Mul (a, b) else simplify (Mul (a', b'))
  | Div (a, b) -> let a' = simplify a and b' = simplify b in
    if a' = a && b' = b then Div (a, b) else simplify (Div (a', b'))
  | Sin a -> Sin (simplify a)
  | Cos a -> Cos (simplify a)
  | Exp a -> Exp (simplify a)
  | Log a -> Log (simplify a)
  | Abs a -> Abs (simplify a)
  | Sqrt a -> Sqrt (simplify a)
  | e -> e

(* === Evolution === *)

type state = {
  mutable data : (float * float) array;
  mutable best : expr option;
  mutable best_fitness : float;
  mutable history : float list;
}

let state = {
  data = [||];
  best = None;
  best_fitness = Float.infinity;
  history = [];
}

let evolve () =
  if Array.length state.data = 0 then begin
    Printf.printf "No data loaded. Use 'data' or 'generate' first.\n%!";
    ()
  end else begin
    let pop = Array.init params.pop_size (fun _ -> ramped_half_and_half params.max_depth) in
    let fitnesses = Array.map (fitness state.data) pop in
    state.history <- [];

    Printf.printf "Evolving %d individuals for %d generations...\n%!" params.pop_size params.generations;

    let best_idx = ref 0 in
    for i = 1 to Array.length fitnesses - 1 do
      if fitnesses.(i) < fitnesses.(!best_idx) then best_idx := i
    done;
    let current_best = ref pop.(!best_idx) in
    let current_best_f = ref fitnesses.(!best_idx) in
    let early_stop = ref false in

    for gen = 1 to params.generations do
      if not !early_stop then begin
        let indices = Array.init params.pop_size (fun i -> i) in
        Array.sort (fun a b -> Float.compare fitnesses.(a) fitnesses.(b)) indices;

        let new_pop = Array.make params.pop_size (Const 0.0) in
        for i = 0 to min (params.elitism - 1) (params.pop_size - 1) do
          new_pop.(i) <- pop.(indices.(i))
        done;

        for i = params.elitism to params.pop_size - 1 do
          let r = Random.float 1.0 in
          if r < params.crossover_rate then begin
            let p1 = tournament_select pop fitnesses in
            let p2 = tournament_select pop fitnesses in
            new_pop.(i) <- crossover p1 p2
          end else if r < params.crossover_rate +. params.mutation_rate then begin
            let p = tournament_select pop fitnesses in
            new_pop.(i) <- mutate p
          end else begin
            new_pop.(i) <- tournament_select pop fitnesses
          end
        done;

        Array.blit new_pop 0 pop 0 params.pop_size;
        for i = 0 to params.pop_size - 1 do
          fitnesses.(i) <- fitness state.data pop.(i)
        done;

        for i = 0 to params.pop_size - 1 do
          if fitnesses.(i) < !current_best_f then begin
            current_best := pop.(i);
            current_best_f := fitnesses.(i)
          end
        done;

        state.history <- !current_best_f :: state.history;

        if gen mod 10 = 0 || gen = 1 then
          Printf.printf "  Gen %3d | Best MSE: %.6f | Size: %d\n%!"
            gen (mse state.data !current_best) (size !current_best);

        if mse state.data !current_best < 1e-6 then begin
          Printf.printf "  Perfect fit found at generation %d!\n%!" gen;
          early_stop := true
        end
      end
    done;

    state.best <- Some !current_best;
    state.best_fitness <- !current_best_f;
    state.history <- List.rev state.history;

    Printf.printf "\nDone! Best formula: %s\n" (to_string !current_best);
    Printf.printf "MSE: %.6f | Size: %d\n%!" (mse state.data !current_best) (size !current_best)
  end

(* === Data Generation === *)

let generate_data f n x_min x_max =
  Array.init n (fun i ->
    let x = x_min +. (x_max -. x_min) *. float_of_int i /. float_of_int (n - 1) in
    (x, f x))

(* === ASCII Plot === *)

let ascii_plot () =
  match state.best with
  | None -> Printf.printf "No model yet. Run 'evolve' first.\n%!"
  | Some expr ->
    let data = state.data in
    if Array.length data = 0 then Printf.printf "No data.\n%!"
    else begin
      let width = 60 and height = 20 in
      let xs = Array.map fst data in
      let ys = Array.map snd data in
      let preds = Array.map (fun (x, _) -> eval_expr [("x", x)] expr) data in
      let all_y = Array.append ys preds in
      let y_min = Array.fold_left Float.min Float.infinity all_y in
      let y_max = Array.fold_left Float.max Float.neg_infinity all_y in
      let x_min = Array.fold_left Float.min Float.infinity xs in
      let x_max = Array.fold_left Float.max Float.neg_infinity xs in
      let dy = if y_max -. y_min < 1e-10 then 1.0 else y_max -. y_min in
      let dx = if x_max -. x_min < 1e-10 then 1.0 else x_max -. x_min in

      let grid = Array.init height (fun _ -> Bytes.make width ' ') in

      Array.iter (fun (x, y) ->
        let col = int_of_float ((x -. x_min) /. dx *. float_of_int (width - 1)) in
        let row = height - 1 - int_of_float ((y -. y_min) /. dy *. float_of_int (height - 1)) in
        let row = max 0 (min (height - 1) row) in
        let col = max 0 (min (width - 1) col) in
        Bytes.set grid.(row) col 'o'
      ) data;

      Array.iteri (fun i (x, _) ->
        let _ = x in
        let y = preds.(i) in
        let col = int_of_float ((fst data.(i) -. x_min) /. dx *. float_of_int (width - 1)) in
        let row = height - 1 - int_of_float ((y -. y_min) /. dy *. float_of_int (height - 1)) in
        let row = max 0 (min (height - 1) row) in
        let col = max 0 (min (width - 1) col) in
        if Bytes.get grid.(row) col = 'o' then Bytes.set grid.(row) col '@'
        else Bytes.set grid.(row) col '*'
      ) data;

      Printf.printf "\n  Data (o) vs Predicted (*), overlap (@)\n";
      Printf.printf "  %8.2f |%s\n" y_max (Bytes.to_string grid.(0));
      for i = 1 to height - 2 do
        Printf.printf "           |%s\n" (Bytes.to_string grid.(i))
      done;
      Printf.printf "  %8.2f |%s\n" y_min (Bytes.to_string grid.(height - 1));
      Printf.printf "           +%s\n" (String.make width '-');
      Printf.printf "            %-8.2f%*s%8.2f\n%!" x_min (width - 16) "" x_max
    end

(* === Parse simple expressions for 'generate' === *)

let eval_simple_expr x str =
  let s = str in
  let pos = ref 0 in
  let len = String.length s in
  let peek () = if !pos < len then Some s.[!pos] else None in
  let advance () = pos := !pos + 1 in
  let skip_spaces () = while !pos < len && s.[!pos] = ' ' do advance () done in

  let rec parse_expr () = parse_add ()
  and parse_add () =
    let left = ref (parse_mul ()) in
    let continue_loop = ref true in
    while !continue_loop do
      skip_spaces ();
      match peek () with
      | Some '+' -> advance (); left := !left +. parse_mul ()
      | Some '-' -> advance (); left := !left -. parse_mul ()
      | _ -> continue_loop := false
    done;
    !left
  and parse_mul () =
    let left = ref (parse_pow ()) in
    let continue_loop = ref true in
    while !continue_loop do
      skip_spaces ();
      match peek () with
      | Some '*' -> advance (); left := !left *. parse_pow ()
      | Some '/' -> advance (); left := protected_div !left (parse_pow ())
      | _ -> continue_loop := false
    done;
    !left
  and parse_pow () =
    let base = parse_unary () in
    skip_spaces ();
    match peek () with
    | Some '^' -> advance (); Float.pow base (parse_unary ())
    | _ -> base
  and parse_unary () =
    skip_spaces ();
    match peek () with
    | Some '-' -> advance (); -. (parse_atom ())
    | _ -> parse_atom ()
  and parse_atom () =
    skip_spaces ();
    match peek () with
    | Some '(' -> advance (); let v = parse_expr () in skip_spaces ();
      (match peek () with Some ')' -> advance () | _ -> ()); v
    | Some 'x' -> advance (); x
    | Some 's' ->
      pos := !pos + 3;
      skip_spaces ();
      (match peek () with Some '(' -> advance () | _ -> ());
      let v = parse_expr () in
      (match peek () with Some ')' -> advance () | _ -> ());
      Float.sin v
    | Some 'c' ->
      pos := !pos + 3;
      skip_spaces ();
      (match peek () with Some '(' -> advance () | _ -> ());
      let v = parse_expr () in
      (match peek () with Some ')' -> advance () | _ -> ());
      Float.cos v
    | _ ->
      let start = !pos in
      while !pos < len && (let c = Char.code s.[!pos] in (c >= 48 && c <= 57) || s.[!pos] = '.') do
        advance ()
      done;
      if !pos > start then float_of_string (String.sub s start (!pos - start))
      else 0.0
  in
  parse_expr ()

(* === REPL === *)

let print_help () =
  Printf.printf "
Symbolic Regression - Genetic Programming REPL
===============================================
Commands:
  data <x1>,<y1>; <x2>,<y2>; ...  Load training data
  generate <expr> [n]              Generate n data points (default 30)
  evolve [gens] [popsize]          Run evolution
  best                             Show best formula
  simplify                         Simplify best expression
  predict <x>                      Evaluate best at x
  plot                             ASCII plot of data vs predicted
  history                          Fitness improvement history
  params                           Show parameters
  set <param> <value>              Set parameter
  demo [1|2|3]                     Run built-in demo
  help                             This help
  quit                             Exit
\n%!"

let run_demo n =
  let (desc, f) = match n with
    | 2 -> ("y = sin(x) * 2", fun x -> Float.sin x *. 2.0)
    | 3 -> ("y = x^3 - 2x + 1", fun x -> x *. x *. x -. 2.0 *. x +. 1.0)
    | _ -> ("y = x^2 + 1", fun x -> x *. x +. 1.0)
  in
  Printf.printf "Demo: %s\n%!" desc;
  state.data <- generate_data f 30 (-3.0) 3.0;
  Printf.printf "Generated 30 data points in [-3, 3]\n%!";
  evolve ()

let trim s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && (s.[!i] = ' ' || s.[!i] = '\t' || s.[!i] = '\r' || s.[!i] = '\n') do incr i done;
  let j = ref (n - 1) in
  while !j >= !i && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\r' || s.[!j] = '\n') do decr j done;
  if !i > !j then "" else String.sub s !i (!j - !i + 1)

let starts_with s prefix =
  String.length s >= String.length prefix &&
  String.sub s 0 (String.length prefix) = prefix

let () =
  Printf.printf "=== Symbolic Regression via Genetic Programming ===\n";
  Printf.printf "Discover mathematical formulas from data.\n";
  Printf.printf "Type 'help' for commands or 'demo' to try it out.\n\n%!";

  let running = ref true in
  while !running do
    Printf.printf "sr> %!";
    match In_channel.input_line stdin with
    | None -> running := false
    | Some line ->
      let cmd = trim line in
      if cmd = "" then ()
      else if cmd = "quit" || cmd = "exit" then running := false
      else if cmd = "help" then print_help ()
      else if starts_with cmd "demo" then begin
        let rest = trim (String.sub cmd 4 (String.length cmd - 4)) in
        let n = if rest = "" then 1 else (try int_of_string rest with _ -> 1) in
        run_demo n
      end
      else if starts_with cmd "generate" then begin
        let rest = trim (String.sub cmd 8 (String.length cmd - 8)) in
        let f x = eval_simple_expr x rest in
        state.data <- generate_data f 30 (-5.0) 5.0;
        Printf.printf "Generated 30 points for: %s\n%!" rest
      end
      else if starts_with cmd "data" then begin
        let rest = trim (String.sub cmd 4 (String.length cmd - 4)) in
        let points = String.split_on_char ';' rest in
        let data = List.filter_map (fun p ->
          let p = trim p in
          if p = "" then None
          else match String.split_on_char ',' p with
            | [x_s; y_s] ->
              (try Some (float_of_string (trim x_s), float_of_string (trim y_s))
               with _ -> None)
            | _ -> None
        ) points in
        state.data <- Array.of_list data;
        Printf.printf "Loaded %d data points.\n%!" (Array.length state.data)
      end
      else if starts_with cmd "evolve" then begin
        let rest = trim (String.sub cmd 6 (String.length cmd - 6)) in
        let parts = String.split_on_char ' ' rest |> List.filter (fun s -> s <> "") in
        (match parts with
         | g :: p :: _ ->
           (try params.generations <- int_of_string g with _ -> ());
           (try params.pop_size <- int_of_string p with _ -> ())
         | [g] -> (try params.generations <- int_of_string g with _ -> ())
         | _ -> ());
        evolve ()
      end
      else if cmd = "best" then begin
        match state.best with
        | None -> Printf.printf "No model yet.\n%!"
        | Some e ->
          Printf.printf "Formula: %s\n" (to_string e);
          Printf.printf "MSE: %.6f | Size: %d | Depth: %d\n%!" (mse state.data e) (size e) (depth e)
      end
      else if cmd = "simplify" then begin
        match state.best with
        | None -> Printf.printf "No model yet.\n%!"
        | Some e ->
          let s = simplify e in
          state.best <- Some s;
          Printf.printf "Simplified: %s\n" (to_string s);
          Printf.printf "Size: %d (was %d)\n%!" (size s) (size e)
      end
      else if starts_with cmd "predict" then begin
        let rest = trim (String.sub cmd 7 (String.length cmd - 7)) in
        match state.best with
        | None -> Printf.printf "No model yet.\n%!"
        | Some e ->
          (try
            let x = float_of_string rest in
            let y = eval_expr [("x", x)] e in
            Printf.printf "f(%g) = %g\n%!" x y
          with _ -> Printf.printf "Usage: predict <x>\n%!")
      end
      else if cmd = "plot" then ascii_plot ()
      else if cmd = "history" then begin
        if state.history = [] then Printf.printf "No history. Run 'evolve' first.\n%!"
        else begin
          Printf.printf "Generation | Best Fitness\n";
          Printf.printf "-----------+-------------\n";
          List.iteri (fun i f ->
            if i mod 5 = 0 || i = List.length state.history - 1 then
              Printf.printf "    %3d    | %.6f\n" (i + 1) f
          ) state.history;
          Printf.printf "%!"
        end
      end
      else if cmd = "params" then begin
        Printf.printf "Population:  %d\n" params.pop_size;
        Printf.printf "Generations: %d\n" params.generations;
        Printf.printf "Max depth:   %d\n" params.max_depth;
        Printf.printf "Tournament:  %d\n" params.tournament_size;
        Printf.printf "Crossover:   %.2f\n" params.crossover_rate;
        Printf.printf "Mutation:    %.2f\n" params.mutation_rate;
        Printf.printf "Elitism:     %d\n" params.elitism;
        Printf.printf "Parsimony:   %.4f\n%!" params.parsimony
      end
      else if starts_with cmd "set" then begin
        let rest = trim (String.sub cmd 3 (String.length cmd - 3)) in
        let parts = String.split_on_char ' ' rest |> List.filter (fun s -> s <> "") in
        match parts with
        | [name; value] -> begin
          try match name with
            | "popsize" | "pop_size" -> params.pop_size <- int_of_string value; Printf.printf "OK\n%!"
            | "generations" | "gens" -> params.generations <- int_of_string value; Printf.printf "OK\n%!"
            | "max_depth" | "depth" -> params.max_depth <- int_of_string value; Printf.printf "OK\n%!"
            | "tournament" -> params.tournament_size <- int_of_string value; Printf.printf "OK\n%!"
            | "crossover" -> params.crossover_rate <- float_of_string value; Printf.printf "OK\n%!"
            | "mutation" -> params.mutation_rate <- float_of_string value; Printf.printf "OK\n%!"
            | "elitism" -> params.elitism <- int_of_string value; Printf.printf "OK\n%!"
            | "parsimony" -> params.parsimony <- float_of_string value; Printf.printf "OK\n%!"
            | _ -> Printf.printf "Unknown param: %s\n%!" name
          with _ -> Printf.printf "Invalid value: %s\n%!" value
        end
        | _ -> Printf.printf "Usage: set <param> <value>\n%!"
      end
      else Printf.printf "Unknown command: %s (type 'help')\n%!" cmd
  done;
  Printf.printf "Goodbye!\n%!"
