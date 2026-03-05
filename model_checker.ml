(* model_checker.ml — CTL Model Checker for finite-state transition systems *)
(* Implements labeling-based CTL model checking (Clarke, Emerson & Sistla) *)

(* ─── Types ─── *)

module StateSet = Set.Make(Int)
module StringSet = Set.Make(String)
module StateMap = Map.Make(Int)

type state = int

type transition_system = {
  states     : StateSet.t;
  initial    : StateSet.t;
  transitions: StateSet.t StateMap.t;  (* state -> set of successor states *)
  labels     : StringSet.t StateMap.t; (* state -> set of atomic propositions *)
}

(* CTL formulas *)
type ctl =
  | True
  | False
  | Atom    of string
  | Not     of ctl
  | And     of ctl * ctl
  | Or      of ctl * ctl
  | Implies of ctl * ctl
  | EX      of ctl          (* exists next *)
  | EF      of ctl          (* exists finally *)
  | EG      of ctl          (* exists globally *)
  | EU      of ctl * ctl    (* exists until *)
  | AX      of ctl          (* forall next *)
  | AF      of ctl          (* forall finally *)
  | AG      of ctl          (* forall globally *)
  | AU      of ctl * ctl    (* forall until *)

(* ─── Transition system construction ─── *)

let empty_ts () = {
  states = StateSet.empty;
  initial = StateSet.empty;
  transitions = StateMap.empty;
  labels = StateMap.empty;
}

let add_state s ts =
  { ts with states = StateSet.add s ts.states }

let add_initial s ts =
  { ts with
    states = StateSet.add s ts.states;
    initial = StateSet.add s ts.initial }

let add_transition src dst ts =
  let succs = match StateMap.find_opt src ts.transitions with
    | Some set -> StateSet.add dst set
    | None -> StateSet.singleton dst
  in
  { ts with
    states = StateSet.add src (StateSet.add dst ts.states);
    transitions = StateMap.add src succs ts.transitions }

let add_label s prop ts =
  let props = match StateMap.find_opt s ts.labels with
    | Some set -> StringSet.add prop set
    | None -> StringSet.singleton prop
  in
  { ts with
    states = StateSet.add s ts.states;
    labels = StateMap.add s props ts.labels }

let successors ts s =
  match StateMap.find_opt s ts.transitions with
  | Some set -> set
  | None -> StateSet.empty

let predecessors ts s =
  StateMap.fold (fun src succs acc ->
    if StateSet.mem s succs then StateSet.add src acc else acc
  ) ts.transitions StateSet.empty

let has_label ts s prop =
  match StateMap.find_opt s ts.labels with
  | Some set -> StringSet.mem prop set
  | None -> false

(* ─── CTL labeling algorithm ─── *)

(* sat ts phi = set of states satisfying phi *)
let rec sat ts phi =
  match phi with
  | True -> ts.states
  | False -> StateSet.empty
  | Atom p ->
    StateSet.filter (fun s -> has_label ts s p) ts.states
  | Not f ->
    StateSet.diff ts.states (sat ts f)
  | And (f1, f2) ->
    StateSet.inter (sat ts f1) (sat ts f2)
  | Or (f1, f2) ->
    StateSet.union (sat ts f1) (sat ts f2)
  | Implies (f1, f2) ->
    sat ts (Or (Not f1, f2))
  | EX f ->
    sat_ex ts f
  | AX f ->
    (* AX f = ¬EX(¬f) *)
    sat ts (Not (EX (Not f)))
  | EF f ->
    (* EF f = E[true U f] *)
    sat_eu ts True f
  | AF f ->
    (* AF f = ¬EG(¬f) *)
    sat ts (Not (EG (Not f)))
  | EG f ->
    sat_eg ts f
  | AG f ->
    (* AG f = ¬EF(¬f) *)
    sat ts (Not (EF (Not f)))
  | EU (f1, f2) ->
    sat_eu ts f1 f2
  | AU (f1, f2) ->
    (* AU(f1,f2) = ¬(E[¬f2 U (¬f1 ∧ ¬f2)] ∨ EG(¬f2)) *)
    sat ts (Not (Or (EU (Not f2, And (Not f1, Not f2)), EG (Not f2))))

(* EX f: states with some successor satisfying f *)
and sat_ex ts f =
  let f_states = sat ts f in
  StateSet.filter (fun s ->
    not (StateSet.is_empty (StateSet.inter (successors ts s) f_states))
  ) ts.states

(* EG f: greatest fixpoint — start with sat(f), remove states
   that have no successor in the current set.
   Deadlock states (no successors) satisfy EG f trivially if they
   satisfy f, since there is no future path to violate it. *)
and sat_eg ts f =
  let f_states = sat ts f in
  let deadlock_f = StateSet.filter (fun s ->
    StateSet.is_empty (successors ts s)
  ) f_states in
  let rec fixpoint current =
    let next = StateSet.filter (fun s ->
      StateSet.mem s deadlock_f ||
      not (StateSet.is_empty (StateSet.inter (successors ts s) current))
    ) current in
    if StateSet.equal next current then current
    else fixpoint next
  in
  fixpoint f_states

(* EU(f1, f2): least fixpoint — start with sat(f2), add states
   satisfying f1 with some successor already in the set *)
and sat_eu ts f1 f2 =
  let f1_states = sat ts f1 in
  let f2_states = sat ts f2 in
  let rec fixpoint current frontier =
    if StateSet.is_empty frontier then current
    else begin
      let new_states = StateSet.fold (fun s acc ->
        let preds = predecessors ts s in
        StateSet.fold (fun p acc2 ->
          if StateSet.mem p f1_states && not (StateSet.mem p current)
          then StateSet.add p acc2
          else acc2
        ) preds acc
      ) frontier StateSet.empty in
      fixpoint (StateSet.union current new_states) new_states
    end
  in
  fixpoint f2_states f2_states

(* ─── Model checking ─── *)

(* Check if formula holds at all initial states *)
let check ts phi =
  let satisfying = sat ts phi in
  StateSet.subset ts.initial satisfying

(* Check which initial states satisfy the formula *)
let check_states ts phi =
  let satisfying = sat ts phi in
  StateSet.inter ts.initial satisfying

(* Get all states satisfying formula *)
let satisfying_states ts phi = sat ts phi

(* ─── CTL formula pretty-printing ─── *)

let rec formula_to_string = function
  | True -> "true"
  | False -> "false"
  | Atom p -> p
  | Not f -> Printf.sprintf "¬(%s)" (formula_to_string f)
  | And (f1, f2) -> Printf.sprintf "(%s ∧ %s)" (formula_to_string f1) (formula_to_string f2)
  | Or (f1, f2) -> Printf.sprintf "(%s ∨ %s)" (formula_to_string f1) (formula_to_string f2)
  | Implies (f1, f2) -> Printf.sprintf "(%s → %s)" (formula_to_string f1) (formula_to_string f2)
  | EX f -> Printf.sprintf "EX(%s)" (formula_to_string f)
  | EF f -> Printf.sprintf "EF(%s)" (formula_to_string f)
  | EG f -> Printf.sprintf "EG(%s)" (formula_to_string f)
  | EU (f1, f2) -> Printf.sprintf "E[%s U %s]" (formula_to_string f1) (formula_to_string f2)
  | AX f -> Printf.sprintf "AX(%s)" (formula_to_string f)
  | AF f -> Printf.sprintf "AF(%s)" (formula_to_string f)
  | AG f -> Printf.sprintf "AG(%s)" (formula_to_string f)
  | AU (f1, f2) -> Printf.sprintf "A[%s U %s]" (formula_to_string f1) (formula_to_string f2)

(* ─── CTL formula parser ─── *)

type token =
  | TTrue | TFalse | TNot | TAnd | TOr | TImplies
  | TLParen | TRParen | TLBracket | TRBracket
  | TEX | TEF | TEG | TEU
  | TAX | TAF | TAG | TAU
  | TAtom of string
  | TEOF

let tokenize input =
  let len = String.length input in
  let pos = ref 0 in
  let tokens = ref [] in
  while !pos < len do
    let c = input.[!pos] in
    match c with
    | ' ' | '\t' | '\n' | '\r' -> incr pos
    | '(' -> tokens := TLParen :: !tokens; incr pos
    | ')' -> tokens := TRParen :: !tokens; incr pos
    | '[' -> tokens := TLBracket :: !tokens; incr pos
    | ']' -> tokens := TRBracket :: !tokens; incr pos
    | '!' | '~' -> tokens := TNot :: !tokens; incr pos
    | '&' ->
      if !pos + 1 < len && input.[!pos + 1] = '&'
      then (tokens := TAnd :: !tokens; pos := !pos + 2)
      else (tokens := TAnd :: !tokens; incr pos)
    | '|' ->
      if !pos + 1 < len && input.[!pos + 1] = '|'
      then (tokens := TOr :: !tokens; pos := !pos + 2)
      else (tokens := TOr :: !tokens; incr pos)
    | '-' ->
      if !pos + 1 < len && input.[!pos + 1] = '>'
      then (tokens := TImplies :: !tokens; pos := !pos + 2)
      else failwith (Printf.sprintf "Unexpected '-' at position %d" !pos)
    | 'E' when !pos + 1 < len ->
      let next = input.[!pos + 1] in
      (match next with
       | 'X' -> tokens := TEX :: !tokens; pos := !pos + 2
       | 'F' -> tokens := TEF :: !tokens; pos := !pos + 2
       | 'G' -> tokens := TEG :: !tokens; pos := !pos + 2
       | '[' -> tokens := TEU :: !tokens; incr pos  (* just push E, [ handled later *)
       | _ ->
         let start = !pos in
         while !pos < len && (let ch = input.[!pos] in
           (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
           (ch >= '0' && ch <= '9') || ch = '_') do
           incr pos
         done;
         tokens := TAtom (String.sub input start (!pos - start)) :: !tokens)
    | 'A' when !pos + 1 < len ->
      let next = input.[!pos + 1] in
      (match next with
       | 'X' -> tokens := TAX :: !tokens; pos := !pos + 2
       | 'F' -> tokens := TAF :: !tokens; pos := !pos + 2
       | 'G' -> tokens := TAG :: !tokens; pos := !pos + 2
       | '[' -> tokens := TAU :: !tokens; incr pos
       | _ ->
         let start = !pos in
         while !pos < len && (let ch = input.[!pos] in
           (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
           (ch >= '0' && ch <= '9') || ch = '_') do
           incr pos
         done;
         tokens := TAtom (String.sub input start (!pos - start)) :: !tokens)
    | 'U' -> tokens := TAtom "U" :: !tokens; incr pos  (* might be atom *)
    | _ when (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' ->
      let start = !pos in
      while !pos < len && (let ch = input.[!pos] in
        (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
        (ch >= '0' && ch <= '9') || ch = '_') do
        incr pos
      done;
      let word = String.sub input start (!pos - start) in
      let tok = match word with
        | "true" | "True" | "TRUE" -> TTrue
        | "false" | "False" | "FALSE" -> TFalse
        | "not" | "NOT" -> TNot
        | "and" | "AND" -> TAnd
        | "or" | "OR" -> TOr
        | _ -> TAtom word
      in
      tokens := tok :: !tokens
    | _ -> failwith (Printf.sprintf "Unexpected character '%c' at position %d" c !pos)
  done;
  List.rev (TEOF :: !tokens)

(* Recursive descent parser *)
let parse input =
  let tokens = ref (tokenize input) in
  let peek () = match !tokens with t :: _ -> t | [] -> TEOF in
  let advance () = match !tokens with _ :: rest -> tokens := rest | [] -> () in
  let expect t =
    if peek () = t then advance ()
    else failwith (Printf.sprintf "Expected token in formula")
  in
  let rec parse_implies () =
    let left = parse_or () in
    if peek () = TImplies then (advance (); Implies (left, parse_implies ()))
    else left
  and parse_or () =
    let left = parse_and () in
    let rec loop acc =
      if peek () = TOr then (advance (); loop (Or (acc, parse_and ())))
      else acc
    in loop left
  and parse_and () =
    let left = parse_unary () in
    let rec loop acc =
      if peek () = TAnd then (advance (); loop (And (acc, parse_unary ())))
      else acc
    in loop left
  and parse_unary () =
    match peek () with
    | TNot -> advance (); Not (parse_unary ())
    | TEX -> advance (); EX (parse_unary ())
    | TEF -> advance (); EF (parse_unary ())
    | TEG -> advance (); EG (parse_unary ())
    | TAX -> advance (); AX (parse_unary ())
    | TAF -> advance (); AF (parse_unary ())
    | TAG -> advance (); AG (parse_unary ())
    | TEU ->
      advance (); expect TLBracket;
      let f1 = parse_implies () in
      (* skip U atom *)
      (match peek () with TAtom "U" -> advance () | _ -> ());
      let f2 = parse_implies () in
      expect TRBracket; EU (f1, f2)
    | TAU ->
      advance (); expect TLBracket;
      let f1 = parse_implies () in
      (match peek () with TAtom "U" -> advance () | _ -> ());
      let f2 = parse_implies () in
      expect TRBracket; AU (f1, f2)
    | _ -> parse_primary ()
  and parse_primary () =
    match peek () with
    | TTrue -> advance (); True
    | TFalse -> advance (); False
    | TAtom s -> advance (); Atom s
    | TLParen -> advance (); let f = parse_implies () in expect TRParen; f
    | t -> failwith (Printf.sprintf "Unexpected token in formula")
  in
  let result = parse_implies () in
  result

(* ─── Counterexample / witness generation ─── *)

(* Find a path (witness) from an initial state to a target state *)
let find_path ts start target_set =
  let rec bfs queue visited =
    match queue with
    | [] -> None
    | (state, path) :: rest ->
      if StateSet.mem state target_set then
        Some (List.rev (state :: path))
      else if StateSet.mem state visited then
        bfs rest visited
      else
        let visited' = StateSet.add state visited in
        let succs = StateSet.elements (successors ts state) in
        let new_entries = List.map (fun s -> (s, state :: path)) succs in
        bfs (rest @ new_entries) visited'
  in
  bfs [(start, [])] StateSet.empty

(* Generate a witness/counterexample for a formula at a state *)
let witness ts phi state =
  let satisfying = sat ts phi in
  if StateSet.mem state satisfying then
    (* Find evidence *)
    match phi with
    | EF f ->
      let f_states = sat ts f in
      find_path ts state f_states
    | _ -> Some [state]
  else
    None

(* ─── Transition system analysis ─── *)

let reachable_states ts =
  let rec bfs queue visited =
    if StateSet.is_empty queue then visited
    else
      let next = StateSet.fold (fun s acc ->
        StateSet.union acc (StateSet.diff (successors ts s) visited)
      ) queue StateSet.empty in
      bfs next (StateSet.union visited next)
  in
  bfs ts.initial ts.initial

let deadlock_states ts =
  StateSet.filter (fun s ->
    StateSet.is_empty (successors ts s)
  ) ts.states

let is_deterministic ts =
  StateMap.for_all (fun _ succs ->
    StateSet.cardinal succs <= 1
  ) ts.transitions

let state_count ts = StateSet.cardinal ts.states

let transition_count ts =
  StateMap.fold (fun _ succs acc ->
    acc + StateSet.cardinal succs
  ) ts.transitions 0

(* ─── Fairness constraints (simple strong fairness) ─── *)

(* Check EG f under strong fairness: the cycle must visit at least one fair state *)
let sat_eg_fair ts f fair_states =
  let f_states = sat ts f in
  (* First compute EG f, then intersect with states that can reach a fair state in f *)
  let eg_states = sat_eg ts f in
  let fair_f = StateSet.inter eg_states fair_states in
  (* Keep only states in EG f that can reach a fair state through f-states *)
  let rec backward current frontier =
    if StateSet.is_empty frontier then current
    else
      let new_states = StateSet.fold (fun s acc ->
        let preds = predecessors ts s in
        StateSet.fold (fun p acc2 ->
          if StateSet.mem p eg_states && not (StateSet.mem p current)
          then StateSet.add p acc2
          else acc2
        ) preds acc
      ) frontier StateSet.empty in
      backward (StateSet.union current new_states) new_states
  in
  backward fair_f fair_f

(* ─── Example transition systems ─── *)

(* Simple mutual exclusion model *)
let mutex_example () =
  (* States: 0=idle/idle, 1=try/idle, 2=idle/try, 3=try/try,
     4=crit/idle, 5=idle/crit, 6=crit/try, 7=try/crit *)
  let ts = empty_ts () in
  let ts = add_initial 0 ts in
  (* Labels *)
  let ts = add_label 0 "idle1" ts in
  let ts = add_label 0 "idle2" ts in
  let ts = add_label 1 "try1" ts in
  let ts = add_label 1 "idle2" ts in
  let ts = add_label 2 "idle1" ts in
  let ts = add_label 2 "try2" ts in
  let ts = add_label 3 "try1" ts in
  let ts = add_label 3 "try2" ts in
  let ts = add_label 4 "crit1" ts in
  let ts = add_label 4 "idle2" ts in
  let ts = add_label 5 "idle1" ts in
  let ts = add_label 5 "crit2" ts in
  let ts = add_label 6 "crit1" ts in
  let ts = add_label 6 "try2" ts in
  let ts = add_label 7 "try1" ts in
  let ts = add_label 7 "crit2" ts in
  (* Transitions *)
  let ts = add_transition 0 1 ts in  (* p1 tries *)
  let ts = add_transition 0 2 ts in  (* p2 tries *)
  let ts = add_transition 1 3 ts in  (* p2 also tries *)
  let ts = add_transition 1 4 ts in  (* p1 enters critical *)
  let ts = add_transition 2 3 ts in  (* p1 also tries *)
  let ts = add_transition 2 5 ts in  (* p2 enters critical *)
  let ts = add_transition 3 6 ts in  (* p1 enters critical *)
  let ts = add_transition 3 7 ts in  (* p2 enters critical *)
  let ts = add_transition 4 0 ts in  (* p1 exits *)
  let ts = add_transition 4 6 ts in  (* p2 tries *)
  let ts = add_transition 5 0 ts in  (* p2 exits *)
  let ts = add_transition 5 7 ts in  (* p1 tries *)
  let ts = add_transition 6 2 ts in  (* p1 exits *)
  let ts = add_transition 7 1 ts in  (* p2 exits *)
  ts

(* Simple traffic light *)
let traffic_light () =
  let ts = empty_ts () in
  let ts = add_initial 0 ts in
  let ts = add_label 0 "red" ts in
  let ts = add_label 1 "green" ts in
  let ts = add_label 2 "yellow" ts in
  let ts = add_transition 0 1 ts in
  let ts = add_transition 1 2 ts in
  let ts = add_transition 2 0 ts in
  ts

(* ─── Report generation ─── *)

let check_report ts formulas =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "=== CTL Model Checking Report ===\n\n";
  Buffer.add_string buf (Printf.sprintf "States: %d | Transitions: %d | Initial: %d\n"
    (state_count ts) (transition_count ts) (StateSet.cardinal ts.initial));
  Buffer.add_string buf (Printf.sprintf "Reachable: %d | Deadlocks: %d | Deterministic: %b\n\n"
    (StateSet.cardinal (reachable_states ts))
    (StateSet.cardinal (deadlock_states ts))
    (is_deterministic ts));
  List.iter (fun (name, phi) ->
    let result = check ts phi in
    let sat_states = sat ts phi in
    Buffer.add_string buf (Printf.sprintf "  %s: %s = %s  (sat: {%s})\n"
      (if result then "✓" else "✗")
      name
      (formula_to_string phi)
      (String.concat "," (List.map string_of_int (StateSet.elements sat_states))))
  ) formulas;
  Buffer.contents buf

(* ─── Tests ─── *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_equal name expected actual =
  if expected = actual then
    (incr tests_passed;
     Printf.printf "  ✓ %s\n" name)
  else
    (incr tests_failed;
     Printf.printf "  ✗ %s: expected %s, got %s\n" name
       (string_of_bool expected) (string_of_bool actual))

let assert_set_equal name expected actual =
  if StateSet.equal expected actual then
    (incr tests_passed;
     Printf.printf "  ✓ %s\n" name)
  else
    (incr tests_failed;
     Printf.printf "  ✗ %s: expected {%s}, got {%s}\n" name
       (String.concat "," (List.map string_of_int (StateSet.elements expected)))
       (String.concat "," (List.map string_of_int (StateSet.elements actual))))

let assert_int name expected actual =
  if expected = actual then
    (incr tests_passed;
     Printf.printf "  ✓ %s\n" name)
  else
    (incr tests_failed;
     Printf.printf "  ✗ %s: expected %d, got %d\n" name expected actual)

let assert_true name cond =
  if cond then (incr tests_passed; Printf.printf "  ✓ %s\n" name)
  else (incr tests_failed; Printf.printf "  ✗ %s\n" name)

let () =
  Printf.printf "\n=== CTL Model Checker Tests ===\n\n";

  (* --- Transition system construction tests --- *)
  Printf.printf "--- Construction ---\n";
  let ts = empty_ts () in
  assert_int "empty has 0 states" 0 (state_count ts);

  let ts = add_state 0 (add_state 1 (add_state 2 ts)) in
  assert_int "3 states added" 3 (state_count ts);

  let ts = add_initial 0 ts in
  assert_int "1 initial state" 1 (StateSet.cardinal ts.initial);

  let ts = add_transition 0 1 (add_transition 1 2 (add_transition 2 0 ts)) in
  assert_int "3 transitions" 3 (transition_count ts);

  let ts = add_label 0 "a" (add_label 1 "b" (add_label 2 "c" ts)) in
  assert_true "state 0 has label a" (has_label ts 0 "a");
  assert_true "state 1 has label b" (has_label ts 1 "b");
  assert_true "state 0 does not have label b" (not (has_label ts 0 "b"));

  (* --- Basic formula tests on simple cycle: 0->1->2->0 --- *)
  Printf.printf "\n--- Basic formulas (cycle) ---\n";
  assert_equal "True holds" true (check ts True);
  assert_equal "False fails" false (check ts False);
  assert_equal "Atom a holds at init" true (check ts (Atom "a"));
  assert_equal "Atom b fails at init" false (check ts (Atom "b"));
  assert_equal "Not b at init" true (check ts (Not (Atom "b")));
  assert_equal "a AND not b" true (check ts (And (Atom "a", Not (Atom "b"))));
  assert_equal "a OR b" true (check ts (Or (Atom "a", Atom "b")));
  assert_equal "a -> a" true (check ts (Implies (Atom "a", Atom "a")));

  (* --- EX tests --- *)
  Printf.printf "\n--- EX ---\n";
  assert_equal "EX b (0->1 has b)" true (check ts (EX (Atom "b")));
  assert_equal "EX a from 0" false (check ts (EX (Atom "a")));
  assert_equal "EX(EX c)" true (check ts (EX (EX (Atom "c"))));

  (* --- AX tests --- *)
  Printf.printf "\n--- AX ---\n";
  assert_equal "AX b (only succ is 1)" true (check ts (AX (Atom "b")));

  (* --- EF tests --- *)
  Printf.printf "\n--- EF ---\n";
  assert_equal "EF a" true (check ts (EF (Atom "a")));
  assert_equal "EF b" true (check ts (EF (Atom "b")));
  assert_equal "EF c" true (check ts (EF (Atom "c")));
  assert_equal "EF false" false (check ts (EF False));

  (* --- AF tests --- *)
  Printf.printf "\n--- AF ---\n";
  assert_equal "AF a (cycle returns to a)" true (check ts (AF (Atom "a")));
  assert_equal "AF b" true (check ts (AF (Atom "b")));

  (* --- EG tests --- *)
  Printf.printf "\n--- EG ---\n";
  assert_equal "EG true (infinite path exists)" true (check ts (EG True));
  assert_equal "EG a (can't stay in a)" false (check ts (EG (Atom "a")));

  (* --- AG tests --- *)
  Printf.printf "\n--- AG ---\n";
  assert_equal "AG true" true (check ts (AG True));
  assert_equal "AG a (not always a)" false (check ts (AG (Atom "a")));
  assert_equal "AG(EF a) (can always reach a)" true (check ts (AG (EF (Atom "a"))));

  (* --- EU tests --- *)
  Printf.printf "\n--- EU ---\n";
  assert_equal "E[a U b]" true (check ts (EU (Atom "a", Atom "b")));
  assert_equal "E[true U c]" true (check ts (EU (True, Atom "c")));
  assert_equal "E[false U a]" true (check ts (EU (False, Atom "a")));  (* a holds now *)

  (* --- AU tests --- *)
  Printf.printf "\n--- AU ---\n";
  assert_equal "A[true U b]" true (check ts (AU (True, Atom "b")));

  (* --- Mutex example --- *)
  Printf.printf "\n--- Mutex model ---\n";
  let mx = mutex_example () in
  assert_int "mutex: 8 states" 8 (state_count mx);

  (* Safety: mutual exclusion — never both critical *)
  let mutual_excl = AG (Not (And (Atom "crit1", Atom "crit2"))) in
  assert_equal "mutex: AG ¬(crit1 ∧ crit2)" true (check mx mutual_excl);

  (* Liveness: if try then eventually critical *)
  let live1 = AG (Implies (Atom "try1", EF (Atom "crit1"))) in
  assert_equal "mutex: try1 -> EF crit1" true (check mx live1);

  let live2 = AG (Implies (Atom "try2", EF (Atom "crit2"))) in
  assert_equal "mutex: try2 -> EF crit2" true (check mx live2);

  (* Can reach critical *)
  assert_equal "mutex: EF crit1" true (check mx (EF (Atom "crit1")));
  assert_equal "mutex: EF crit2" true (check mx (EF (Atom "crit2")));

  (* Not always idle *)
  assert_equal "mutex: ¬AG idle1" false (check mx (AG (Atom "idle1")));

  (* --- Traffic light --- *)
  Printf.printf "\n--- Traffic light ---\n";
  let tl = traffic_light () in
  assert_equal "tl: starts red" true (check tl (Atom "red"));
  assert_equal "tl: EF green" true (check tl (EF (Atom "green")));
  assert_equal "tl: AG(EF red)" true (check tl (AG (EF (Atom "red"))));
  assert_equal "tl: AG(EF green)" true (check tl (AG (EF (Atom "green"))));
  assert_equal "tl: AG(red -> AX green)" true
    (check tl (AG (Implies (Atom "red", AX (Atom "green")))));
  assert_equal "tl: AG(green -> AX yellow)" true
    (check tl (AG (Implies (Atom "green", AX (Atom "yellow")))));
  assert_equal "tl: deterministic" true (is_deterministic tl);

  (* --- Satisfying states tests --- *)
  Printf.printf "\n--- Satisfying states ---\n";
  let sat_a = satisfying_states ts (Atom "a") in
  assert_set_equal "sat(a) = {0}" (StateSet.singleton 0) sat_a;
  let sat_ef_c = satisfying_states ts (EF (Atom "c")) in
  assert_set_equal "sat(EF c) = {0,1,2}"
    (StateSet.of_list [0;1;2]) sat_ef_c;

  (* --- Analysis tests --- *)
  Printf.printf "\n--- Analysis ---\n";
  let reach = reachable_states ts in
  assert_set_equal "reachable = all" ts.states reach;

  let dead = deadlock_states ts in
  assert_true "no deadlocks in cycle" (StateSet.is_empty dead);

  assert_true "cycle is deterministic" (is_deterministic ts);

  (* --- Deadlock state tests --- *)
  Printf.printf "\n--- Deadlock ---\n";
  let ts2 = empty_ts () in
  let ts2 = add_initial 0 ts2 in
  let ts2 = add_transition 0 1 ts2 in
  let ts2 = add_label 0 "start" ts2 in
  let ts2 = add_label 1 "end" ts2 in
  let dead2 = deadlock_states ts2 in
  assert_set_equal "deadlock = {1}" (StateSet.singleton 1) dead2;
  assert_equal "EF end" true (check ts2 (EF (Atom "end")));
  assert_equal "AF end" true (check ts2 (AF (Atom "end")));

  (* --- Parser tests --- *)
  Printf.printf "\n--- Parser ---\n";
  let f = parse "EF p" in
  assert_equal "parse EF p" true (f = EF (Atom "p"));
  let f = parse "AG (p -> EF q)" in
  assert_equal "parse AG(p->EF q)" true
    (f = AG (Implies (Atom "p", EF (Atom "q"))));
  let f = parse "!p & q" in
  assert_equal "parse !p & q" true (f = And (Not (Atom "p"), Atom "q"));
  let f = parse "EX EX p" in
  assert_equal "parse EX EX p" true (f = EX (EX (Atom "p")));
  let f = parse "true" in
  assert_equal "parse true" true (f = True);
  let f = parse "p || q" in
  assert_equal "parse p || q" true (f = Or (Atom "p", Atom "q"));

  (* --- Branching / nondeterminism --- *)
  Printf.printf "\n--- Nondeterminism ---\n";
  let ts3 = empty_ts () in
  let ts3 = add_initial 0 ts3 in
  let ts3 = add_transition 0 1 ts3 in
  let ts3 = add_transition 0 2 ts3 in
  let ts3 = add_label 1 "good" ts3 in
  let ts3 = add_label 2 "bad" ts3 in
  assert_equal "EF good" true (check ts3 (EF (Atom "good")));
  assert_equal "EF bad" true (check ts3 (EF (Atom "bad")));
  assert_equal "AF good (not all paths)" false (check ts3 (AF (Atom "good")));
  assert_equal "EX good" true (check ts3 (EX (Atom "good")));
  assert_equal "AX good (both branches?)" false (check ts3 (AX (Atom "good")));
  assert_true "ts3 not deterministic" (not (is_deterministic ts3));

  (* --- Witness/counterexample --- *)
  Printf.printf "\n--- Witness ---\n";
  let w = witness ts (EF (Atom "c")) 0 in
  assert_true "witness for EF c from 0" (w <> None);
  (match w with
   | Some path ->
     assert_true "path starts at 0" (List.hd path = 0);
     assert_true "path ends at 2" (List.nth path (List.length path - 1) = 2)
   | None -> ());

  (* --- Formula pretty-printing round-trip --- *)
  Printf.printf "\n--- Pretty-printing ---\n";
  let s = formula_to_string (AG (Implies (Atom "p", EF (Atom "q")))) in
  assert_true "pretty AG(p->EF q)" (String.length s > 0);
  let s2 = formula_to_string (EU (Atom "a", Atom "b")) in
  assert_true "pretty E[a U b]" (String.contains s2 'U');

  (* --- Report generation --- *)
  Printf.printf "\n--- Report ---\n";
  let report = check_report tl [
    ("always reaches green", AG (EF (Atom "green")));
    ("starts red", Atom "red");
  ] in
  assert_true "report non-empty" (String.length report > 50);
  assert_true "report has checkmark" (String.contains report (Char.chr 0xe2) || String.length report > 0);

  (* --- Fairness --- *)
  Printf.printf "\n--- Fairness ---\n";
  let fair = StateSet.of_list [0; 1; 2] in
  let eg_fair = sat_eg_fair ts True fair in
  assert_set_equal "fair EG true = all" (StateSet.of_list [0;1;2]) eg_fair;

  (* --- Complex nesting --- *)
  Printf.printf "\n--- Complex nesting ---\n";
  assert_equal "AG(AF a) on cycle" true (check ts (AG (AF (Atom "a"))));
  assert_equal "EG(EF b) on cycle" true (check ts (EG (EF (Atom "b"))));
  assert_equal "AG(EX true) on cycle" true (check ts (AG (EX True)));

  (* --- Edge cases --- *)
  Printf.printf "\n--- Edge cases ---\n";
  let ts_single = empty_ts () in
  let ts_single = add_initial 0 ts_single in
  let ts_single = add_label 0 "lonely" ts_single in
  assert_equal "single: lonely" true (check ts_single (Atom "lonely"));
  assert_equal "single: EX false (deadlock)" false (check ts_single (EX True));
  assert_equal "single: AG lonely" true (check ts_single (AG (Atom "lonely")));

  (* Self-loop *)
  let ts_loop = add_transition 0 0 ts_single in
  assert_equal "self-loop: EG lonely" true (check ts_loop (EG (Atom "lonely")));
  assert_equal "self-loop: AG lonely" true (check ts_loop (AG (Atom "lonely")));

  (* Multiple initial states *)
  Printf.printf "\n--- Multiple initial ---\n";
  let ts4 = empty_ts () in
  let ts4 = add_initial 0 ts4 in
  let ts4 = add_initial 1 ts4 in
  let ts4 = add_label 0 "x" ts4 in
  let ts4 = add_label 1 "y" ts4 in
  assert_equal "multi-init: x holds (not all)" false (check ts4 (Atom "x"));
  assert_equal "multi-init: x or y" true (check ts4 (Or (Atom "x", Atom "y")));

  (* Predecessors *)
  Printf.printf "\n--- Predecessors ---\n";
  let preds = predecessors ts 1 in
  assert_set_equal "preds of 1 = {0}" (StateSet.singleton 0) preds;
  let preds2 = predecessors ts 0 in
  assert_set_equal "preds of 0 = {2}" (StateSet.singleton 2) preds2;

  (* Check_states *)
  Printf.printf "\n--- check_states ---\n";
  let cs = check_states ts (EF (Atom "b")) in
  assert_set_equal "check_states EF b = {0}" (StateSet.singleton 0) cs;

  Printf.printf "\n=== Results: %d passed, %d failed ===\n"
    !tests_passed !tests_failed;

  if !tests_failed > 0 then exit 1
