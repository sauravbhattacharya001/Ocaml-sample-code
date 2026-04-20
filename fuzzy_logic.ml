(* Fuzzy Logic Controller — Mamdani-style fuzzy inference system
   
   Implements a complete fuzzy logic framework:
   - Membership functions: Triangle, Trapezoid, Gaussian, Sigmoid, Bell
   - Linguistic variables with named fuzzy sets
   - IF-THEN rule engine with AND/OR connectives
   - Mamdani inference: fuzzification → rule eval → implication → aggregation → defuzzification
   - Three defuzzification methods: Centroid, Mean of Maximum, Bisector
   - ASCII plotting of membership functions
   - Sensitivity analysis
   
   Built-in domains:
   1. Temperature Controller (temp → fan speed)
   2. Tipping Calculator (food + service → tip)
   3. Autonomous Braking (distance + speed → brake force)
   
   Usage: ocaml fuzzy_logic.ml
*)

(* ========== Core Types ========== *)

type mf_shape =
  | Triangle of float * float * float
  | Trapezoid of float * float * float * float
  | Gaussian of float * float
  | Sigmoid of float * float
  | Bell of float * float * float

type fuzzy_set = { name: string; shape: mf_shape }

type linguistic_var = {
  var_name: string;
  min_val: float;
  max_val: float;
  sets: fuzzy_set list;
}

type antecedent =
  | Is of string * string
  | And of antecedent * antecedent
  | Or of antecedent * antecedent

type consequent = string * string

type rule = { rule_id: int; ant: antecedent; con: consequent; weight: float }

type defuzz_method = Centroid | MeanOfMax | Bisector

type fis = {
  name: string;
  inputs: linguistic_var list;
  outputs: linguistic_var list;
  rules: rule list;
  method_: defuzz_method;
}

(* ========== Membership Function Evaluation ========== *)

let eval_mf shape x =
  match shape with
  | Triangle (a, b, c) ->
    if x <= a || x >= c then 0.0
    else if x <= b then (x -. a) /. (b -. a)
    else (c -. x) /. (c -. b)
  | Trapezoid (a, b, c, d) ->
    if x <= a || x >= d then 0.0
    else if x >= b && x <= c then 1.0
    else if x < b then (x -. a) /. (b -. a)
    else (d -. x) /. (d -. c)
  | Gaussian (c, s) ->
    exp (-. ((x -. c) ** 2.0) /. (2.0 *. s *. s))
  | Sigmoid (c, a) ->
    1.0 /. (1.0 +. exp (-. a *. (x -. c)))
  | Bell (w, s, c) ->
    1.0 /. (1.0 +. (abs_float ((x -. c) /. w) ** (2.0 *. s)))

(* ========== Fuzzy Operations ========== *)

let fuzzy_and a b = min a b
let fuzzy_or a b = max a b
let _fuzzy_not a = 1.0 -. a

(* ========== Fuzzification ========== *)

let fuzzify var value =
  List.map (fun s -> (s.name, eval_mf s.shape value)) var.sets

(* ========== Rule Evaluation ========== *)

let rec eval_antecedent inputs values ant =
  match ant with
  | Is (var_name, term) ->
    (try
       let var = List.find (fun v -> v.var_name = var_name) inputs in
       let value = List.assoc var_name values in
       let set = List.find (fun s -> s.name = term) var.sets in
       eval_mf set.shape value
     with Not_found -> 0.0)
  | And (a, b) ->
    fuzzy_and (eval_antecedent inputs values a) (eval_antecedent inputs values b)
  | Or (a, b) ->
    fuzzy_or (eval_antecedent inputs values a) (eval_antecedent inputs values b)

(* ========== Inference Engine ========== *)

let infer fis values =
  let rule_strengths = List.map (fun r ->
    let strength = (eval_antecedent fis.inputs values r.ant) *. r.weight in
    (r, strength)
  ) fis.rules in
  let output_var = List.hd fis.outputs in
  let n_points = 200 in
  let step = (output_var.max_val -. output_var.min_val) /. (float_of_int n_points) in
  let aggregated = Array.init (n_points + 1) (fun i ->
    let x = output_var.min_val +. (float_of_int i) *. step in
    let agg = List.fold_left (fun acc (r, strength) ->
      let (_, term) = r.con in
      (try
         let set = List.find (fun s -> s.name = term) output_var.sets in
         let mf_val = eval_mf set.shape x in
         fuzzy_or acc (fuzzy_and strength mf_val)
       with Not_found -> acc)
    ) 0.0 rule_strengths in
    (x, agg)
  ) in
  (aggregated, rule_strengths)

(* ========== Defuzzification ========== *)

let defuzzify_centroid agg =
  let num = Array.fold_left (fun acc (x, m) -> acc +. x *. m) 0.0 agg in
  let den = Array.fold_left (fun acc (_, m) -> acc +. m) 0.0 agg in
  if den = 0.0 then 0.0 else num /. den

let defuzzify_mom agg =
  let max_m = Array.fold_left (fun acc (_, m) -> max acc m) 0.0 agg in
  if max_m = 0.0 then 0.0
  else begin
    let sum = ref 0.0 in
    let count = ref 0 in
    Array.iter (fun (x, m) ->
      if m >= max_m -. 0.001 then (sum := !sum +. x; incr count)
    ) agg;
    if !count = 0 then 0.0 else !sum /. (float_of_int !count)
  end

let defuzzify_bisector agg =
  let total = Array.fold_left (fun acc (_, m) -> acc +. m) 0.0 agg in
  if total = 0.0 then 0.0
  else begin
    let half = total /. 2.0 in
    let running = ref 0.0 in
    let result = ref 0.0 in
    let found = ref false in
    Array.iter (fun (x, m) ->
      if not !found then begin
        running := !running +. m;
        if !running >= half then (result := x; found := true)
      end
    ) agg;
    !result
  end

let defuzzify method_ agg =
  match method_ with
  | Centroid -> defuzzify_centroid agg
  | MeanOfMax -> defuzzify_mom agg
  | Bisector -> defuzzify_bisector agg

(* ========== Built-in Domains ========== *)

let temperature_domain () =
  let temp = {
    var_name = "temperature"; min_val = 0.0; max_val = 100.0;
    sets = [
      { name = "cold"; shape = Trapezoid (0.0, 0.0, 15.0, 30.0) };
      { name = "cool"; shape = Triangle (20.0, 35.0, 50.0) };
      { name = "warm"; shape = Triangle (40.0, 55.0, 70.0) };
      { name = "hot"; shape = Trapezoid (60.0, 75.0, 100.0, 100.0) };
    ]
  } in
  let fan = {
    var_name = "fan_speed"; min_val = 0.0; max_val = 100.0;
    sets = [
      { name = "off"; shape = Trapezoid (0.0, 0.0, 5.0, 15.0) };
      { name = "low"; shape = Triangle (10.0, 30.0, 50.0) };
      { name = "medium"; shape = Triangle (40.0, 55.0, 70.0) };
      { name = "high"; shape = Trapezoid (60.0, 80.0, 100.0, 100.0) };
    ]
  } in
  { name = "Temperature Controller";
    inputs = [temp]; outputs = [fan];
    rules = [
      { rule_id = 1; ant = Is ("temperature", "cold"); con = ("fan_speed", "off"); weight = 1.0 };
      { rule_id = 2; ant = Is ("temperature", "cool"); con = ("fan_speed", "low"); weight = 1.0 };
      { rule_id = 3; ant = Is ("temperature", "warm"); con = ("fan_speed", "medium"); weight = 1.0 };
      { rule_id = 4; ant = Is ("temperature", "hot"); con = ("fan_speed", "high"); weight = 1.0 };
    ];
    method_ = Centroid }

let tipping_domain () =
  let food = {
    var_name = "food"; min_val = 0.0; max_val = 10.0;
    sets = [
      { name = "poor"; shape = Trapezoid (0.0, 0.0, 2.0, 4.0) };
      { name = "average"; shape = Triangle (3.0, 5.0, 7.0) };
      { name = "excellent"; shape = Trapezoid (6.0, 8.0, 10.0, 10.0) };
    ]
  } in
  let service = {
    var_name = "service"; min_val = 0.0; max_val = 10.0;
    sets = [
      { name = "poor"; shape = Trapezoid (0.0, 0.0, 2.0, 4.0) };
      { name = "average"; shape = Triangle (3.0, 5.0, 7.0) };
      { name = "excellent"; shape = Trapezoid (6.0, 8.0, 10.0, 10.0) };
    ]
  } in
  let tip = {
    var_name = "tip"; min_val = 0.0; max_val = 30.0;
    sets = [
      { name = "low"; shape = Triangle (0.0, 5.0, 13.0) };
      { name = "medium"; shape = Triangle (10.0, 15.0, 20.0) };
      { name = "high"; shape = Triangle (17.0, 25.0, 30.0) };
    ]
  } in
  { name = "Tipping Calculator";
    inputs = [food; service]; outputs = [tip];
    rules = [
      { rule_id = 1; ant = Or (Is ("food", "poor"), Is ("service", "poor")); con = ("tip", "low"); weight = 1.0 };
      { rule_id = 2; ant = Is ("service", "average"); con = ("tip", "medium"); weight = 1.0 };
      { rule_id = 3; ant = Or (Is ("food", "excellent"), Is ("service", "excellent")); con = ("tip", "high"); weight = 1.0 };
    ];
    method_ = Centroid }

let braking_domain () =
  let distance = {
    var_name = "distance"; min_val = 0.0; max_val = 100.0;
    sets = [
      { name = "very_close"; shape = Trapezoid (0.0, 0.0, 5.0, 15.0) };
      { name = "close"; shape = Triangle (10.0, 25.0, 40.0) };
      { name = "medium"; shape = Triangle (30.0, 50.0, 70.0) };
      { name = "far"; shape = Trapezoid (60.0, 80.0, 100.0, 100.0) };
    ]
  } in
  let speed = {
    var_name = "speed"; min_val = 0.0; max_val = 200.0;
    sets = [
      { name = "slow"; shape = Trapezoid (0.0, 0.0, 30.0, 60.0) };
      { name = "moderate"; shape = Triangle (40.0, 80.0, 120.0) };
      { name = "fast"; shape = Trapezoid (100.0, 140.0, 200.0, 200.0) };
    ]
  } in
  let brake = {
    var_name = "brake_force"; min_val = 0.0; max_val = 100.0;
    sets = [
      { name = "none"; shape = Trapezoid (0.0, 0.0, 5.0, 15.0) };
      { name = "light"; shape = Triangle (10.0, 30.0, 50.0) };
      { name = "moderate"; shape = Triangle (40.0, 55.0, 70.0) };
      { name = "hard"; shape = Triangle (60.0, 75.0, 90.0) };
      { name = "emergency"; shape = Trapezoid (80.0, 90.0, 100.0, 100.0) };
    ]
  } in
  { name = "Autonomous Braking System";
    inputs = [distance; speed]; outputs = [brake];
    rules = [
      { rule_id = 1; ant = And (Is ("distance", "very_close"), Is ("speed", "fast")); con = ("brake_force", "emergency"); weight = 1.0 };
      { rule_id = 2; ant = And (Is ("distance", "very_close"), Is ("speed", "moderate")); con = ("brake_force", "hard"); weight = 1.0 };
      { rule_id = 3; ant = And (Is ("distance", "very_close"), Is ("speed", "slow")); con = ("brake_force", "moderate"); weight = 1.0 };
      { rule_id = 4; ant = And (Is ("distance", "close"), Is ("speed", "fast")); con = ("brake_force", "hard"); weight = 1.0 };
      { rule_id = 5; ant = And (Is ("distance", "close"), Is ("speed", "moderate")); con = ("brake_force", "moderate"); weight = 1.0 };
      { rule_id = 6; ant = And (Is ("distance", "close"), Is ("speed", "slow")); con = ("brake_force", "light"); weight = 1.0 };
      { rule_id = 7; ant = And (Is ("distance", "medium"), Is ("speed", "fast")); con = ("brake_force", "moderate"); weight = 1.0 };
      { rule_id = 8; ant = And (Is ("distance", "medium"), Is ("speed", "moderate")); con = ("brake_force", "light"); weight = 1.0 };
      { rule_id = 9; ant = And (Is ("distance", "medium"), Is ("speed", "slow")); con = ("brake_force", "none"); weight = 1.0 };
      { rule_id = 10; ant = And (Is ("distance", "far"), Is ("speed", "fast")); con = ("brake_force", "light"); weight = 1.0 };
      { rule_id = 11; ant = And (Is ("distance", "far"), Is ("speed", "moderate")); con = ("brake_force", "none"); weight = 1.0 };
      { rule_id = 12; ant = And (Is ("distance", "far"), Is ("speed", "slow")); con = ("brake_force", "none"); weight = 1.0 };
    ];
    method_ = Centroid }

(* ========== ASCII Plotting ========== *)

let plot_variable var =
  let width = 60 in
  let height = 10 in
  let grid = Array.init height (fun _ -> Array.make width ' ') in
  let step = (var.max_val -. var.min_val) /. (float_of_int (width - 1)) in
  let symbols = [| '/'; '\\'; '^'; '~'; '*'; '#'; '@'; '&' |] in
  List.iteri (fun si s ->
    let sym = symbols.(si mod Array.length symbols) in
    for col = 0 to width - 1 do
      let x = var.min_val +. (float_of_int col) *. step in
      let m = eval_mf s.shape x in
      let row = height - 1 - (int_of_float (m *. (float_of_int (height - 1)) +. 0.5)) in
      if m > 0.01 && row >= 0 && row < height then
        grid.(row).(col) <- sym
    done
  ) var.sets;
  Printf.printf "\n  %s [%.0f - %.0f]\n" var.var_name var.min_val var.max_val;
  Printf.printf "  %s\n" (String.make (width + 6) '-');
  for row = 0 to height - 1 do
    let label = if row = 0 then "1.0" else if row = height / 2 then "0.5" else if row = height - 1 then "0.0" else "   " in
    Printf.printf "  %s |" label;
    for col = 0 to width - 1 do
      Printf.printf "%c" grid.(row).(col)
    done;
    Printf.printf "\n"
  done;
  Printf.printf "      +%s\n" (String.make width '-');
  Printf.printf "       ";
  let label_pos = List.map (fun s ->
    let center = match s.shape with
      | Triangle (_, b, _) -> b
      | Trapezoid (_, b, c, _) -> (b +. c) /. 2.0
      | Gaussian (c, _) -> c
      | Sigmoid (c, _) -> c
      | Bell (_, _, c) -> c
    in
    let col = int_of_float ((center -. var.min_val) /. step) in
    (col, s.name)
  ) var.sets in
  let line = Bytes.make width ' ' in
  List.iter (fun (col, name) ->
    let start = max 0 (min (width - String.length name) col) in
    String.iteri (fun i c -> Bytes.set line (start + i) c) name
  ) label_pos;
  Printf.printf "%s\n" (Bytes.to_string line)

(* ========== Display Helpers ========== *)

let rec string_of_ant = function
  | Is (v, t) -> Printf.sprintf "%s IS %s" v t
  | And (a, b) -> Printf.sprintf "(%s) AND (%s)" (string_of_ant a) (string_of_ant b)
  | Or (a, b) -> Printf.sprintf "(%s) OR (%s)" (string_of_ant a) (string_of_ant b)

let string_of_method = function
  | Centroid -> "centroid"
  | MeanOfMax -> "mean-of-maximum"
  | Bisector -> "bisector"

let method_of_string s =
  match String.lowercase_ascii s with
  | "centroid" | "cog" -> Some Centroid
  | "mom" | "mean-of-maximum" | "meanofmax" -> Some MeanOfMax
  | "bisector" | "bis" -> Some Bisector
  | _ -> None

(* ========== REPL ========== *)

let () =
  Printf.printf "=== Fuzzy Logic Controller ===\n";
  Printf.printf "Mamdani inference | 5 membership functions | 3 domains\n";
  Printf.printf "Type 'help' for commands, 'domains' to list presets.\n\n";
  let current_fis = ref (temperature_domain ()) in
  let running = ref true in
  while !running do
    Printf.printf "fuzzy> %!";
    let line = try input_line stdin with End_of_file -> running := false; "quit" in
    let parts = String.split_on_char ' ' (String.trim line) in
    match parts with
    | ["quit"] | ["exit"] | ["q"] -> running := false
    | ["help"] ->
      Printf.printf "\nCommands:\n";
      Printf.printf "  domain <name>           - Load preset (temperature/tipping/braking)\n";
      Printf.printf "  domains                 - List available domains\n";
      Printf.printf "  vars                    - Show linguistic variables\n";
      Printf.printf "  rules                   - Show fuzzy rules\n";
      Printf.printf "  eval <var>=<val> ...    - Evaluate system with crisp inputs\n";
      Printf.printf "  membership <var> <val>  - Show membership degrees\n";
      Printf.printf "  plot <var>              - ASCII plot of membership functions\n";
      Printf.printf "  defuzz <method>         - Set method (centroid/mom/bisector)\n";
      Printf.printf "  sensitivity <var> <min> <max> <steps> - Sensitivity analysis\n";
      Printf.printf "  alpha <value>           - Show alpha-cut sets\n";
      Printf.printf "  quit                    - Exit\n\n"
    | ["domains"] ->
      Printf.printf "\nAvailable domains:\n";
      Printf.printf "  temperature  - Temperature -> Fan Speed\n";
      Printf.printf "  tipping      - Food + Service -> Tip\n";
      Printf.printf "  braking      - Distance + Speed -> Brake Force\n\n"
    | ["domain"; d] ->
      (match String.lowercase_ascii d with
       | "temperature" | "temp" -> current_fis := temperature_domain (); Printf.printf "Loaded: Temperature Controller\n"
       | "tipping" | "tip" -> current_fis := tipping_domain (); Printf.printf "Loaded: Tipping Calculator\n"
       | "braking" | "brake" -> current_fis := braking_domain (); Printf.printf "Loaded: Autonomous Braking System\n"
       | _ -> Printf.printf "Unknown domain: %s\n" d)
    | ["vars"] ->
      Printf.printf "\n=== %s ===\n" !current_fis.name;
      Printf.printf "Inputs:\n";
      List.iter (fun v ->
        Printf.printf "  %s [%.1f - %.1f]: %s\n" v.var_name v.min_val v.max_val
          (String.concat ", " (List.map (fun s -> s.name) v.sets))
      ) !current_fis.inputs;
      Printf.printf "Outputs:\n";
      List.iter (fun v ->
        Printf.printf "  %s [%.1f - %.1f]: %s\n" v.var_name v.min_val v.max_val
          (String.concat ", " (List.map (fun s -> s.name) v.sets))
      ) !current_fis.outputs;
      Printf.printf "\n"
    | ["rules"] ->
      Printf.printf "\n=== Rules (%d) ===\n" (List.length !current_fis.rules);
      List.iter (fun r ->
        let (ov, ot) = r.con in
        Printf.printf "  R%d: IF %s THEN %s IS %s (w=%.1f)\n"
          r.rule_id (string_of_ant r.ant) ov ot r.weight
      ) !current_fis.rules;
      Printf.printf "\n"
    | "eval" :: assignments ->
      let values = List.filter_map (fun s ->
        match String.split_on_char '=' s with
        | [k; v] -> (try Some (k, float_of_string v) with _ -> None)
        | _ -> None
      ) assignments in
      if values = [] then
        Printf.printf "Usage: eval var1=val1 var2=val2 ...\n"
      else begin
        Printf.printf "\n-- Fuzzification --\n";
        List.iter (fun (vname, value) ->
          try
            let var = List.find (fun v -> v.var_name = vname) !current_fis.inputs in
            let memberships = fuzzify var value in
            Printf.printf "  %s = %.2f: " vname value;
            List.iter (fun (term, deg) ->
              if deg > 0.001 then Printf.printf "%s(%.3f) " term deg
            ) memberships;
            Printf.printf "\n"
          with Not_found -> Printf.printf "  %s: unknown variable\n" vname
        ) values;
        let (agg, rule_strengths) = infer !current_fis values in
        Printf.printf "\n-- Rule Firing --\n";
        List.iter (fun (r, strength) ->
          if strength > 0.001 then begin
            let (ov, ot) = r.con in
            Printf.printf "  R%d: %.3f -> %s IS %s\n" r.rule_id strength ov ot
          end
        ) rule_strengths;
        let result = defuzzify !current_fis.method_ agg in
        let (ov, _) = (List.hd !current_fis.rules).con in
        Printf.printf "\n-- Defuzzification (%s) --\n" (string_of_method !current_fis.method_);
        Printf.printf "  %s = %.2f\n\n" ov result
      end
    | ["membership"; vname; vstr] ->
      (try
         let value = float_of_string vstr in
         let all_vars = !current_fis.inputs @ !current_fis.outputs in
         let var = List.find (fun v -> v.var_name = vname) all_vars in
         Printf.printf "\n  %s = %.2f:\n" vname value;
         List.iter (fun s ->
           let deg = eval_mf s.shape value in
           let bar_len = int_of_float (deg *. 30.0) in
           let bar = String.make bar_len '#' in
           Printf.printf "    %-12s %.3f %s\n" s.name deg bar
         ) var.sets;
         Printf.printf "\n"
       with
       | Not_found -> Printf.printf "Unknown variable: %s\n" vname
       | Failure _ -> Printf.printf "Invalid value: %s\n" vstr)
    | ["plot"; vname] ->
      let all_vars = !current_fis.inputs @ !current_fis.outputs in
      (try
         let var = List.find (fun v -> v.var_name = vname) all_vars in
         plot_variable var
       with Not_found -> Printf.printf "Unknown variable: %s\n" vname)
    | ["defuzz"; m] ->
      (match method_of_string m with
       | Some meth -> current_fis := { !current_fis with method_ = meth };
         Printf.printf "Defuzzification set to: %s\n" (string_of_method meth)
       | None -> Printf.printf "Unknown method. Use: centroid, mom, bisector\n")
    | ["sensitivity"; vname; smin; smax; ssteps] ->
      (try
         let vmin = float_of_string smin in
         let vmax = float_of_string smax in
         let steps = int_of_string ssteps in
         let _ = List.find (fun v -> v.var_name = vname) !current_fis.inputs in
         Printf.printf "\n-- Sensitivity: %s [%.1f to %.1f] --\n" vname vmin vmax;
         let step_size = (vmax -. vmin) /. (float_of_int steps) in
         let (ov, _) = (List.hd !current_fis.rules).con in
         for i = 0 to steps do
           let x = vmin +. (float_of_int i) *. step_size in
           let values = [(vname, x)] in
           let (agg, _) = infer !current_fis values in
           let result = defuzzify !current_fis.method_ agg in
           let bar_len = int_of_float (result /. (List.hd !current_fis.outputs).max_val *. 40.0) in
           let bar = String.make bar_len '#' in
           Printf.printf "  %6.1f -> %5.1f %s\n" x result bar
         done;
         Printf.printf "  (output: %s)\n\n" ov
       with
       | Not_found -> Printf.printf "Unknown variable: %s\n" vname
       | Failure _ -> Printf.printf "Usage: sensitivity <var> <min> <max> <steps>\n")
    | ["alpha"; astr] ->
      (try
         let a = float_of_string astr in
         Printf.printf "\n-- Alpha-cut (a=%.2f) --\n" a;
         let all_vars = !current_fis.inputs @ !current_fis.outputs in
         List.iter (fun var ->
           Printf.printf "  %s: " var.var_name;
           let passing = List.filter (fun s ->
             let n = 100 in
             let step = (var.max_val -. var.min_val) /. (float_of_int n) in
             let found = ref false in
             for i = 0 to n do
               let x = var.min_val +. (float_of_int i) *. step in
               if eval_mf s.shape x >= a then found := true
             done;
             !found
           ) var.sets in
           Printf.printf "%s\n" (String.concat ", " (List.map (fun s -> s.name) passing))
         ) all_vars;
         Printf.printf "\n"
       with Failure _ -> Printf.printf "Usage: alpha <value between 0 and 1>\n")
    | [""] | [] -> ()
    | _ -> Printf.printf "Unknown command. Type 'help' for usage.\n"
  done;
  Printf.printf "Goodbye!\n"
