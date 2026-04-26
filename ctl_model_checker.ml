(* CTL Model Checker
   Computation Tree Logic model checking over Kripke structures.
   Features: fixpoint-based evaluation, CTL formula parser, witness/counterexample
   trace generation, 4 built-in examples, interactive REPL.
   Usage: ocaml ctl_model_checker.ml *)

(* ── Sets and Maps ───────────────────────────────────────────── *)

module SS = Set.Make(String)
module SM = Map.Make(String)

(* ── CTL Formula AST ─────────────────────────────────────────── *)

type formula =
  | Atom of string
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Implies of formula * formula
  | EX of formula
  | EF of formula
  | EG of formula
  | EU of formula * formula
  | AX of formula
  | AF of formula
  | AG of formula
  | AU of formula * formula
  | TT | FF

(* ── Kripke Structure ────────────────────────────────────────── *)

type kripke = {
  states : string list;
  initial : string list;
  transitions : (string * string) list;
  labels : (string * string list) list;
}

(* ── Pretty Printing ─────────────────────────────────────────── *)

let rec pp_formula = function
  | Atom s -> s
  | Not f -> "~" ^ pp_paren f
  | And (a, b) -> pp_paren a ^ " & " ^ pp_paren b
  | Or (a, b) -> pp_paren a ^ " | " ^ pp_paren b
  | Implies (a, b) -> pp_paren a ^ " -> " ^ pp_paren b
  | EX f -> "EX(" ^ pp_formula f ^ ")"
  | EF f -> "EF(" ^ pp_formula f ^ ")"
  | EG f -> "EG(" ^ pp_formula f ^ ")"
  | EU (a, b) -> "E[" ^ pp_formula a ^ " U " ^ pp_formula b ^ "]"
  | AX f -> "AX(" ^ pp_formula f ^ ")"
  | AF f -> "AF(" ^ pp_formula f ^ ")"
  | AG f -> "AG(" ^ pp_formula f ^ ")"
  | AU (a, b) -> "A[" ^ pp_formula a ^ " U " ^ pp_formula b ^ "]"
  | TT -> "true" | FF -> "false"
and pp_paren f = match f with
  | And _ | Or _ | Implies _ -> "(" ^ pp_formula f ^ ")"
  | _ -> pp_formula f

(* ── Tokenizer ───────────────────────────────────────────────── *)

type token =
  | TIdent of string | TLParen | TRParen | TLBrack | TRBrack
  | TNot | TAnd | TOr | TArrow | TU | TEOF

let tokenize s =
  let len = String.length s in
  let i = ref 0 in
  let tokens = ref [] in
  while !i < len do
    let c = s.[!i] in
    match c with
    | ' ' | '\t' | '\n' | '\r' -> incr i
    | '(' -> tokens := TLParen :: !tokens; incr i
    | ')' -> tokens := TRParen :: !tokens; incr i
    | '[' -> tokens := TLBrack :: !tokens; incr i
    | ']' -> tokens := TRBrack :: !tokens; incr i
    | '~' -> tokens := TNot :: !tokens; incr i
    | '&' -> tokens := TAnd :: !tokens; incr i
    | '|' -> tokens := TOr :: !tokens; incr i
    | '-' when !i + 1 < len && s.[!i + 1] = '>' ->
      tokens := TArrow :: !tokens; i := !i + 2
    | _ ->
      let start = !i in
      while !i < len && let c = s.[!i] in
        c <> ' ' && c <> '\t' && c <> '(' && c <> ')' &&
        c <> '[' && c <> ']' && c <> '~' && c <> '&' &&
        c <> '|' && c <> '-' && c <> '\n' && c <> '\r'
      do incr i done;
      let w = String.sub s start (!i - start) in
      tokens := (if w = "U" then TU else TIdent w) :: !tokens
  done;
  List.rev !tokens @ [TEOF]

(* ── Parser ──────────────────────────────────────────────────── *)

let parse_formula s =
  let toks = ref (tokenize s) in
  let peek () = match !toks with t :: _ -> t | [] -> TEOF in
  let advance () = match !toks with _ :: rest -> toks := rest | [] -> () in
  let expect t =
    if peek () = t then advance ()
    else failwith (Printf.sprintf "parse error: unexpected token")
  in
  let rec parse_implies () =
    let lhs = parse_or () in
    if peek () = TArrow then (advance (); Implies (lhs, parse_implies ()))
    else lhs
  and parse_or () =
    let lhs = ref (parse_and ()) in
    while peek () = TOr do advance (); lhs := Or (!lhs, parse_and ()) done;
    !lhs
  and parse_and () =
    let lhs = ref (parse_unary ()) in
    while peek () = TAnd do advance (); lhs := And (!lhs, parse_unary ()) done;
    !lhs
  and parse_unary () =
    match peek () with
    | TNot -> advance (); Not (parse_unary ())
    | TIdent "EX" -> advance (); expect TLParen; let f = parse_implies () in expect TRParen; EX f
    | TIdent "EF" -> advance (); expect TLParen; let f = parse_implies () in expect TRParen; EF f
    | TIdent "EG" -> advance (); expect TLParen; let f = parse_implies () in expect TRParen; EG f
    | TIdent "AX" -> advance (); expect TLParen; let f = parse_implies () in expect TRParen; AX f
    | TIdent "AF" -> advance (); expect TLParen; let f = parse_implies () in expect TRParen; AF f
    | TIdent "AG" -> advance (); expect TLParen; let f = parse_implies () in expect TRParen; AG f
    | TIdent "E" -> advance (); expect TLBrack;
      let a = parse_implies () in expect TU; let b = parse_implies () in
      expect TRBrack; EU (a, b)
    | TIdent "A" -> advance (); expect TLBrack;
      let a = parse_implies () in expect TU; let b = parse_implies () in
      expect TRBrack; AU (a, b)
    | _ -> parse_atom ()
  and parse_atom () =
    match peek () with
    | TLParen -> advance (); let f = parse_implies () in expect TRParen; f
    | TIdent "true" -> advance (); TT
    | TIdent "false" -> advance (); FF
    | TIdent s -> advance (); Atom s
    | _ -> failwith "parse error: expected atom or '('"
  in
  let f = parse_implies () in
  (match peek () with TEOF -> () | _ -> failwith "parse error: trailing tokens");
  f

(* ── Kripke Helpers ──────────────────────────────────────────── *)

let all_states k = List.fold_left (fun s x -> SS.add x s) SS.empty k.states

let successors k st =
  List.fold_left (fun acc (a, b) -> if a = st then SS.add b acc else acc) SS.empty k.transitions

let state_labels k st =
  try List.assoc st k.labels with Not_found -> []

(* ── CTL Model Checking (Fixpoint) ──────────────────────────── *)

let rec check k = function
  | TT -> all_states k
  | FF -> SS.empty
  | Atom p ->
    List.fold_left (fun acc (st, lbl) ->
      if List.mem p lbl then SS.add st acc else acc) SS.empty k.labels
  | Not f -> SS.diff (all_states k) (check k f)
  | And (a, b) -> SS.inter (check k a) (check k b)
  | Or (a, b) -> SS.union (check k a) (check k b)
  | Implies (a, b) -> SS.union (SS.diff (all_states k) (check k a)) (check k b)
  | EX f ->
    let sat_f = check k f in
    List.fold_left (fun acc st ->
      if SS.exists (fun s' -> SS.mem s' sat_f) (successors k st)
      then SS.add st acc else acc) SS.empty k.states
  | EG f -> check_eg k f
  | EU (a, b) -> check_eu k a b
  | EF f -> check_eu k TT f
  | AX f -> check k (Not (EX (Not f)))
  | AF f -> check k (Not (EG (Not f)))
  | AG f -> check k (Not (EF (Not f)))
  | AU (a, b) ->
    let nb = Not b and na = Not a in
    check k (Not (Or (EU (nb, And (na, nb)), EG nb)))

and check_eg k f =
  let sat_f = check k f in
  let z = ref sat_f in
  let changed = ref true in
  while !changed do
    changed := false;
    let z' = SS.filter (fun st ->
      SS.exists (fun s' -> SS.mem s' !z) (successors k st)
    ) !z in
    if SS.cardinal z' < SS.cardinal !z then (z := z'; changed := true)
  done;
  !z

and check_eu k a b =
  let sat_a = check k a and sat_b = check k b in
  let z = ref sat_b in
  let changed = ref true in
  while !changed do
    changed := false;
    let new_states = SS.filter (fun st ->
      SS.mem st sat_a && not (SS.mem st !z) &&
      SS.exists (fun s' -> SS.mem s' !z) (successors k st)
    ) (all_states k) in
    if not (SS.is_empty new_states) then
      (z := SS.union !z new_states; changed := true)
  done;
  !z

(* ── Witness / Counterexample Traces ─────────────────────────── *)

let bfs_path k starts targets =
  let visited = Hashtbl.create 32 in
  let queue = Queue.create () in
  List.iter (fun s ->
    if not (Hashtbl.mem visited s) then begin
      Hashtbl.add visited s None;
      Queue.push s queue
    end) starts;
  let found = ref None in
  while not (Queue.is_empty queue) && !found = None do
    let st = Queue.pop queue in
    if SS.mem st targets then found := Some st
    else
      SS.iter (fun s' ->
        if not (Hashtbl.mem visited s') then begin
          Hashtbl.add visited s' (Some st);
          Queue.push s' queue
        end) (successors k st)
  done;
  match !found with
  | None -> None
  | Some goal ->
    let path = ref [goal] in
    let cur = ref goal in
    let cont = ref true in
    while !cont do
      match Hashtbl.find visited !cur with
      | None -> cont := false
      | Some prev -> path := prev :: !path; cur := prev
    done;
    Some !path

let bfs_path_within k starts within =
  let visited = Hashtbl.create 32 in
  let queue = Queue.create () in
  List.iter (fun s ->
    if SS.mem s within && not (Hashtbl.mem visited s) then begin
      Hashtbl.add visited s None;
      Queue.push s queue
    end) starts;
  let found_cycle = ref None in
  while not (Queue.is_empty queue) && !found_cycle = None do
    let st = Queue.pop queue in
    SS.iter (fun s' ->
      if SS.mem s' within then begin
        if Hashtbl.mem visited s' then begin
          if !found_cycle = None then begin
            let path = ref [st] in
            let cur = ref st in
            let cont = ref true in
            while !cont do
              match Hashtbl.find visited !cur with
              | None -> cont := false
              | Some prev -> path := prev :: !path; cur := prev
            done;
            found_cycle := Some (!path @ [s'])
          end
        end else begin
          Hashtbl.add visited s' (Some st);
          Queue.push s' queue
        end
      end) (successors k st)
  done;
  !found_cycle

let generate_trace k formula sat_set =
  let initial_sat = List.filter (fun s -> SS.mem s sat_set) k.initial in
  let initial_unsat = List.filter (fun s -> not (SS.mem s sat_set)) k.initial in
  match formula with
  | AG _ | AX _ | AU _ | AF _ ->
    if initial_unsat <> [] then
      let violating = SS.diff (all_states k) sat_set in
      match bfs_path k k.initial violating with
      | Some path -> Some (false, path)
      | None -> None
    else None
  | EF _ | EX _ | EU _ ->
    if initial_sat <> [] then
      match bfs_path k initial_sat sat_set with
      | Some path -> Some (true, path)
      | None -> Some (true, [List.hd initial_sat])
    else None
  | EG _ ->
    if initial_sat <> [] then
      match bfs_path_within k initial_sat sat_set with
      | Some path -> Some (true, path)
      | None -> Some (true, [List.hd initial_sat])
    else None
  | _ -> None

(* ── Display ─────────────────────────────────────────────────── *)

let pp_set s =
  "{" ^ String.concat ", " (SS.elements s) ^ "}"

let display_kripke k =
  Printf.printf "  States: %s\n" (String.concat ", " k.states);
  Printf.printf "  Initial: %s\n" (String.concat ", " k.initial);
  Printf.printf "  Transitions:\n";
  List.iter (fun (a, b) -> Printf.printf "    %s -> %s\n" a b) k.transitions;
  Printf.printf "  Labels:\n";
  List.iter (fun (st, lbls) ->
    Printf.printf "    %s: {%s}\n" st (String.concat ", " lbls)) k.labels

let check_and_display k formula_str =
  let f = parse_formula formula_str in
  Printf.printf "Checking: %s\n" (pp_formula f);
  let sat = check k f in
  let all_init_sat = List.for_all (fun s -> SS.mem s sat) k.initial in
  if all_init_sat then
    Printf.printf "Result: SATISFIED in all initial states\n"
  else
    Printf.printf "Result: NOT SATISFIED\n";
  Printf.printf "  Satisfying states: %s\n" (pp_set sat);
  (match generate_trace k f sat with
   | Some (true, path) ->
     Printf.printf "  Witness: %s\n" (String.concat " -> " path)
   | Some (false, path) ->
     Printf.printf "  Counterexample: %s\n" (String.concat " -> " path)
   | None -> ());
  Printf.printf "\n"

(* ── Built-in Examples ───────────────────────────────────────── *)

let example_mutex () =
  let states = ["ii"; "it"; "ic"; "ti"; "tt"; "tc"; "ci"; "ct"] in
  let transitions = [
    ("ii","it"); ("ii","ti");
    ("it","ic"); ("it","tt");
    ("ti","ci"); ("ti","tt");
    ("tt","tc"); ("tt","ct");
    ("ic","ii"); ("ic","tc");
    ("tc","ti"); ("tc","ic");
    ("ci","ii"); ("ci","ct");
    ("ct","ti"); ("ct","ci");
  ] in
  let labels = [
    ("ii", ["idle1"; "idle2"]);
    ("it", ["idle1"; "try2"]);
    ("ic", ["idle1"; "crit2"]);
    ("ti", ["try1"; "idle2"]);
    ("tt", ["try1"; "try2"]);
    ("tc", ["try1"; "crit2"]);
    ("ci", ["crit1"; "idle2"]);
    ("ct", ["crit1"; "try2"]);
  ] in
  { states; initial = ["ii"]; transitions; labels }

let example_traffic () =
  let states = ["red"; "yellow"; "green"] in
  let transitions = [("red","green"); ("green","yellow"); ("yellow","red")] in
  let labels = [("red",["red"]); ("yellow",["yellow"]); ("green",["green"])] in
  { states; initial = ["red"]; transitions; labels }

let example_microwave () =
  let states = ["idle"; "cooking"; "done"; "open_idle"] in
  let transitions = [
    ("idle","cooking"); ("cooking","done"); ("done","idle");
    ("idle","open_idle"); ("open_idle","idle"); ("cooking","open_idle");
  ] in
  let labels = [
    ("idle", ["idle"; "door_closed"]);
    ("cooking", ["cooking"; "door_closed"]);
    ("done", ["done"; "door_closed"]);
    ("open_idle", ["idle"; "door_open"]);
  ] in
  { states; initial = ["idle"]; transitions; labels }

let example_counter () =
  let states = ["s0"; "s1"; "s2"; "s3"] in
  let transitions = [("s0","s1"); ("s1","s2"); ("s2","s3"); ("s3","s0")] in
  let labels = [("s0",["s0";"zero"]); ("s1",["s1"]); ("s2",["s2"]); ("s3",["s3";"max"])] in
  { states; initial = ["s0"]; transitions; labels }

let examples = [|
  ("Mutual Exclusion", example_mutex,
   [| "AG(~(crit1 & crit2))"; "EF(crit1)"; "AG(try1 -> EF(crit1))" |]);
  ("Traffic Light", example_traffic,
   [| "AG(red -> EF(green))"; "AG(green -> AX(yellow))"; "AG(AF(red))" |]);
  ("Microwave", example_microwave,
   [| "AG(cooking -> door_closed)"; "EF(done)"; "AG(idle -> EF(done))" |]);
  ("Simple Counter", example_counter,
   [| "EF(max)"; "AG(EF(zero))"; "AG(s0 -> EX(s1))" |]);
|]

(* ── REPL ────────────────────────────────────────────────────── *)

let trim s =
  let len = String.length s in
  let i = ref 0 and j = ref (len - 1) in
  while !i < len && (s.[!i] = ' ' || s.[!i] = '\t' || s.[!i] = '\r' || s.[!i] = '\n') do incr i done;
  while !j >= !i && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\r' || s.[!j] = '\n') do decr j done;
  if !i > !j then "" else String.sub s !i (!j - !i + 1)

let starts_with prefix s =
  let lp = String.length prefix and ls = String.length s in
  lp <= ls && String.sub s 0 lp = prefix

let split_first s =
  let s = trim s in
  try
    let i = String.index s ' ' in
    (String.sub s 0 i, trim (String.sub s (i+1) (String.length s - i - 1)))
  with Not_found -> (s, "")

let print_help () =
  Printf.printf "Commands:\n";
  Printf.printf "  load N          Load example (1-%d)\n" (Array.length examples);
  Printf.printf "  check FORMULA   Check CTL formula against current model\n";
  Printf.printf "  show            Display current Kripke structure\n";
  Printf.printf "  states          List states and labels\n";
  Printf.printf "  add state S [p1,p2,...]\n";
  Printf.printf "                  Add a state with optional labels\n";
  Printf.printf "  add trans S1 S2 Add a transition\n";
  Printf.printf "  set initial S1 S2 ...\n";
  Printf.printf "                  Set initial states\n";
  Printf.printf "  clear           Reset model\n";
  Printf.printf "  examples        List built-in examples\n";
  Printf.printf "  help            Show this help\n";
  Printf.printf "  quit / exit     Exit\n\n"

let empty_kripke = { states=[]; initial=[]; transitions=[]; labels=[] }

let () =
  Printf.printf "CTL Model Checker -- Kripke Structures\n";
  Printf.printf "Fixpoint evaluation, witness/counterexample generation\n";
  Printf.printf "Type 'help' for commands, 'load 1' for an example\n\n";
  let model = ref empty_kripke in
  let running = ref true in
  while !running do
    Printf.printf "ctl> %!";
    match (try Some (input_line stdin) with End_of_file -> None) with
    | None -> running := false
    | Some line ->
      let line = trim line in
      if line = "" then ()
      else if line = "quit" || line = "exit" then running := false
      else if line = "help" then print_help ()
      else if line = "show" then begin
        if !model.states = [] then
          Printf.printf "  (no model loaded)\n\n"
        else (display_kripke !model; Printf.printf "\n")
      end
      else if line = "states" then begin
        if !model.states = [] then
          Printf.printf "  (no states)\n\n"
        else begin
          List.iter (fun st ->
            let lbls = state_labels !model st in
            let init = if List.mem st !model.initial then " [initial]" else "" in
            Printf.printf "  %s: {%s}%s\n" st (String.concat ", " lbls) init
          ) !model.states;
          Printf.printf "\n"
        end
      end
      else if line = "clear" then begin
        model := empty_kripke;
        Printf.printf "  Model cleared.\n\n"
      end
      else if line = "examples" then begin
        Array.iteri (fun i (name, _, formulas) ->
          Printf.printf "  %d. %s -- sample formulas: %s\n"
            (i+1) name (String.concat ", " (Array.to_list formulas))
        ) examples;
        Printf.printf "\n"
      end
      else if starts_with "load" line then begin
        let (_, arg) = split_first line in
        (try
          let n = int_of_string (trim arg) in
          if n < 1 || n > Array.length examples then
            Printf.printf "  Invalid example number (1-%d)\n\n" (Array.length examples)
          else begin
            let (name, builder, formulas) = examples.(n-1) in
            model := builder ();
            Printf.printf "  Loaded: %s\n" name;
            display_kripke !model;
            Printf.printf "\n  Running sample checks:\n\n";
            Array.iter (fun fs -> check_and_display !model fs) formulas
          end
        with Failure _ -> Printf.printf "  Usage: load N (1-%d)\n\n" (Array.length examples))
      end
      else if starts_with "check" line then begin
        let (_, formula_str) = split_first line in
        if formula_str = "" then
          Printf.printf "  Usage: check FORMULA\n\n"
        else if !model.states = [] then
          Printf.printf "  No model loaded. Use 'load N' first.\n\n"
        else
          (try check_and_display !model formula_str
           with Failure msg -> Printf.printf "  Error: %s\n\n" msg)
      end
      else if starts_with "add state" line then begin
        let rest = trim (String.sub line 9 (String.length line - 9)) in
        let (sname, lbl_str) = split_first rest in
        if sname = "" then
          Printf.printf "  Usage: add state NAME [p1,p2,...]\n\n"
        else begin
          let lbls = if lbl_str = "" then []
            else
              let s = lbl_str in
              let s = if String.length s > 0 && s.[0] = '[' then String.sub s 1 (String.length s - 1) else s in
              let s = if String.length s > 0 && s.[String.length s - 1] = ']' then String.sub s 0 (String.length s - 1) else s in
              List.map trim (String.split_on_char ',' s)
          in
          let k = !model in
          model := {
            states = if List.mem sname k.states then k.states else k.states @ [sname];
            initial = k.initial;
            transitions = k.transitions;
            labels = (sname, lbls) :: List.filter (fun (s,_) -> s <> sname) k.labels;
          };
          Printf.printf "  Added state '%s' with labels {%s}\n\n" sname (String.concat ", " lbls)
        end
      end
      else if starts_with "add trans" line then begin
        let rest = trim (String.sub line 9 (String.length line - 9)) in
        let parts = String.split_on_char ' ' rest in
        let parts = List.filter (fun s -> s <> "") parts in
        match parts with
        | [s1; s2] ->
          let k = !model in
          model := { k with transitions = k.transitions @ [(s1, s2)] };
          Printf.printf "  Added transition %s -> %s\n\n" s1 s2
        | _ -> Printf.printf "  Usage: add trans S1 S2\n\n"
      end
      else if starts_with "set initial" line then begin
        let rest = trim (String.sub line 11 (String.length line - 11)) in
        let parts = List.filter (fun s -> s <> "") (String.split_on_char ' ' rest) in
        if parts = [] then
          Printf.printf "  Usage: set initial S1 S2 ...\n\n"
        else begin
          model := { !model with initial = parts };
          Printf.printf "  Initial states: %s\n\n" (String.concat ", " parts)
        end
      end
      else
        Printf.printf "  Unknown command. Type 'help' for commands.\n\n"
  done;
  Printf.printf "Goodbye!\n"
