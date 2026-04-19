(* proof_assistant.ml - Interactive Proof Assistant (Coq-lite)
 *
 * A tactic-based interactive proof assistant for propositional logic.
 * Users manually construct proofs step-by-step using tactics, unlike
 * the automated theorem_prover.ml.
 *
 * Concepts demonstrated:
 * - Tactic-based interactive theorem proving (à la Coq/Lean)
 * - Proof state management with goal stacks
 * - Undo via proof state history
 * - Recursive descent formula parsing
 * - Pretty printing of proof states
 *
 * Example sessions:
 *
 *   > Theorem modus_ponens : P => (P => Q) => Q.
 *   1 goal
 *     ========================
 *     P => (P => Q) => Q
 *   proof> intro HP.
 *   proof> intro HPQ.
 *   proof> apply HPQ.
 *   proof> exact HP.
 *   No more goals. Qed.
 *
 *   > Theorem and_comm : P /\ Q => Q /\ P.
 *   proof> intro H.
 *   proof> destruct H.
 *   proof> split.
 *   proof> exact H2.
 *   proof> exact H1.
 *   No more goals. Qed.
 *
 *   > Theorem or_comm : P \/ Q => Q \/ P.
 *   proof> intro H.
 *   proof> destruct H.
 *   proof> right.
 *   proof> exact H1.
 *   proof> left.
 *   proof> exact H1.
 *   No more goals. Qed.
 *
 *   > Theorem contrapositive : (P => Q) => ~Q => ~P.
 *   proof> intro HPQ.
 *   proof> intro HNQ.
 *   proof> intro HP.
 *   proof> contradiction.
 *   No more goals. Qed.
 *
 * Usage:
 *   ocamlopt proof_assistant.ml -o proof_assistant && ./proof_assistant
 *   (or) ocaml proof_assistant.ml
 *)

(* ===== Formula representation ===== *)

type formula =
  | Var of string
  | Top          (* True *)
  | Bot          (* False *)
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula

let rec formula_to_string f =
  match f with
  | Var s -> s
  | Top -> "True"
  | Bot -> "False"
  | Not p -> "~" ^ formula_atom_str p
  | And (a, b) -> formula_and_str a ^ " /\\ " ^ formula_and_str b
  | Or (a, b) -> formula_or_str a ^ " \\/ " ^ formula_or_str b
  | Imp (a, b) -> formula_or_str a ^ " => " ^ formula_to_string b
  | Iff (a, b) -> formula_or_str a ^ " <=> " ^ formula_or_str b
and formula_atom_str f =
  match f with
  | Var _ | Top | Bot -> formula_to_string f
  | _ -> "(" ^ formula_to_string f ^ ")"
and formula_and_str f =
  match f with
  | And _ | Var _ | Top | Bot | Not _ -> formula_to_string f
  | _ -> "(" ^ formula_to_string f ^ ")"
and formula_or_str f =
  match f with
  | Or _ | And _ | Var _ | Top | Bot | Not _ -> formula_to_string f
  | _ -> "(" ^ formula_to_string f ^ ")"

let rec formula_equal a b =
  match a, b with
  | Var x, Var y -> x = y
  | Top, Top | Bot, Bot -> true
  | Not x, Not y -> formula_equal x y
  | And (a1, a2), And (b1, b2) -> formula_equal a1 b1 && formula_equal a2 b2
  | Or (a1, a2), Or (b1, b2) -> formula_equal a1 b1 && formula_equal a2 b2
  | Imp (a1, a2), Imp (b1, b2) -> formula_equal a1 b1 && formula_equal a2 b2
  | Iff (a1, a2), Iff (b1, b2) -> formula_equal a1 b1 && formula_equal a2 b2
  | _ -> false

(* ===== Formula parser ===== *)

type token =
  | TVar of string | TTrue | TFalse
  | TNot | TAnd | TOr | TImp | TIff
  | TLParen | TRParen | TEOF

let tokenize s =
  let n = String.length s in
  let i = ref 0 in
  let tokens = ref [] in
  while !i < n do
    let c = s.[!i] in
    if c = ' ' || c = '\t' || c = '\n' || c = '\r' then incr i
    else if c = '(' then (tokens := TLParen :: !tokens; incr i)
    else if c = ')' then (tokens := TRParen :: !tokens; incr i)
    else if c = '~' || c = '!' then (tokens := TNot :: !tokens; incr i)
    else if c = '/' && !i + 1 < n && s.[!i+1] = '\\' then
      (tokens := TAnd :: !tokens; i := !i + 2)
    else if c = '\\' && !i + 1 < n && s.[!i+1] = '/' then
      (tokens := TOr :: !tokens; i := !i + 2)
    else if c = '&' && !i + 1 < n && s.[!i+1] = '&' then
      (tokens := TAnd :: !tokens; i := !i + 2)
    else if c = '|' && !i + 1 < n && s.[!i+1] = '|' then
      (tokens := TOr :: !tokens; i := !i + 2)
    else if c = '=' && !i + 1 < n && s.[!i+1] = '>' then
      (tokens := TImp :: !tokens; i := !i + 2)
    else if c = '-' && !i + 1 < n && s.[!i+1] = '>' then
      (tokens := TImp :: !tokens; i := !i + 2)
    else if c = '<' && !i + 2 < n && s.[!i+1] = '=' && s.[!i+2] = '>' then
      (tokens := TIff :: !tokens; i := !i + 3)
    else if c = '<' && !i + 2 < n && s.[!i+1] = '-' && s.[!i+2] = '>' then
      (tokens := TIff :: !tokens; i := !i + 3)
    else if (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') then begin
      let start = !i in
      while !i < n && let ch = s.[!i] in
        (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') ||
        (ch >= '0' && ch <= '9') || ch = '_' do
        incr i
      done;
      let word = String.sub s start (!i - start) in
      match word with
      | "True" | "true" -> tokens := TTrue :: !tokens
      | "False" | "false" -> tokens := TFalse :: !tokens
      | "not" | "Not" | "NOT" -> tokens := TNot :: !tokens
      | "and" | "And" | "AND" -> tokens := TAnd :: !tokens
      | "or" | "Or" | "OR" -> tokens := TOr :: !tokens
      | _ -> tokens := TVar word :: !tokens
    end
    else (incr i) (* skip unknown chars *)
  done;
  List.rev !tokens

(* Recursive descent parser: iff < imp < or < and < not < atom *)
let parse_formula s =
  let tokens = ref (tokenize s) in
  let peek () = match !tokens with t :: _ -> t | [] -> TEOF in
  let advance () = match !tokens with _ :: rest -> tokens := rest | [] -> () in
  let expect t =
    if peek () = t then advance ()
    else failwith "Parse error: unexpected token"
  in
  let rec parse_iff () =
    let lhs = parse_imp () in
    if peek () = TIff then (advance (); Iff (lhs, parse_iff ()))
    else lhs
  and parse_imp () =
    let lhs = parse_or () in
    if peek () = TImp then (advance (); Imp (lhs, parse_imp ()))
    else lhs
  and parse_or () =
    let lhs = ref (parse_and ()) in
    while peek () = TOr do advance (); lhs := Or (!lhs, parse_and ()) done;
    !lhs
  and parse_and () =
    let lhs = ref (parse_not ()) in
    while peek () = TAnd do advance (); lhs := And (!lhs, parse_not ()) done;
    !lhs
  and parse_not () =
    if peek () = TNot then (advance (); Not (parse_not ()))
    else parse_atom ()
  and parse_atom () =
    match peek () with
    | TVar s -> advance (); Var s
    | TTrue -> advance (); Top
    | TFalse -> advance (); Bot
    | TLParen -> advance (); let f = parse_iff () in expect TRParen; f
    | _ -> failwith "Parse error: expected variable or '('"
  in
  let result = parse_iff () in
  result

(* ===== Proof state ===== *)

type hypothesis = { name : string; formula : formula }

type goal = {
  hyps : hypothesis list;
  concl : formula;
  next_h : int;  (* counter for auto-naming hypotheses *)
}

type proof_state = {
  goals : goal list;
  theorem_name : string;
  theorem_formula : formula;
  history : goal list list;  (* previous goal lists for undo *)
}

let fresh_hyp_name g prefix =
  let name = if prefix <> "" then prefix
    else "H" ^ string_of_int g.next_h in
  (name, { g with next_h = g.next_h + 1 })

let find_hyp g name =
  List.find_opt (fun h -> h.name = name) g.hyps

let print_goal_state goals =
  let n = List.length goals in
  if n = 0 then
    print_endline "No more goals."
  else begin
    Printf.printf "%d goal%s\n\n" n (if n > 1 then "s" else "");
    List.iteri (fun i g ->
      if n > 1 then Printf.printf "Goal %d:\n" (i + 1);
      List.iter (fun h ->
        Printf.printf "  %s : %s\n" h.name (formula_to_string h.formula)
      ) g.hyps;
      print_endline "  ========================";
      Printf.printf "  %s\n\n" (formula_to_string g.concl)
    ) goals
  end

(* ===== Tactics ===== *)

type tactic_result =
  | Ok of goal list   (* replacement goals for current goal *)
  | Err of string

let tactic_assumption g =
  if List.exists (fun h -> formula_equal h.formula g.concl) g.hyps
  then Ok []
  else Err "No hypothesis matches the conclusion."

let tactic_intro g name_opt =
  match g.concl with
  | Imp (a, b) ->
    let prefix = match name_opt with Some n -> n | None -> "" in
    let (hname, g') = fresh_hyp_name g prefix in
    Ok [{ g' with hyps = g'.hyps @ [{ name = hname; formula = a }]; concl = b }]
  | Not a ->
    (* ~A is sugar for A => False *)
    let prefix = match name_opt with Some n -> n | None -> "" in
    let (hname, g') = fresh_hyp_name g prefix in
    Ok [{ g' with hyps = g'.hyps @ [{ name = hname; formula = a }]; concl = Bot }]
  | _ -> Err "Goal is not an implication; cannot intro."

let tactic_split g =
  match g.concl with
  | And (a, b) ->
    Ok [{ g with concl = a }; { g with concl = b }]
  | _ -> Err "Goal is not a conjunction; cannot split."

let tactic_left g =
  match g.concl with
  | Or (a, _) -> Ok [{ g with concl = a }]
  | _ -> Err "Goal is not a disjunction; cannot use left."

let tactic_right g =
  match g.concl with
  | Or (_, b) -> Ok [{ g with concl = b }]
  | _ -> Err "Goal is not a disjunction; cannot use right."

let tactic_exact g hname =
  match find_hyp g hname with
  | Some h when formula_equal h.formula g.concl -> Ok []
  | Some _ -> Err (Printf.sprintf "Hypothesis %s does not match the conclusion." hname)
  | None -> Err (Printf.sprintf "No hypothesis named %s." hname)

let tactic_apply g hname =
  match find_hyp g hname with
  | Some h -> begin
    match h.formula with
    | Imp (a, b) when formula_equal b g.concl ->
      Ok [{ g with concl = a }]
    | Imp (_, _) ->
      Err (Printf.sprintf "Conclusion of %s does not match the goal." hname)
    | _ ->
      (* If the hypothesis exactly matches, just close *)
      if formula_equal h.formula g.concl then Ok []
      else Err (Printf.sprintf "%s is not an implication." hname)
    end
  | None -> Err (Printf.sprintf "No hypothesis named %s." hname)

let tactic_contradiction g =
  let found = List.exists (fun h ->
    match h.formula with
    | Not p -> List.exists (fun h2 -> formula_equal h2.formula p) g.hyps
    | _ -> false
  ) g.hyps in
  let found2 = List.exists (fun h ->
    List.exists (fun h2 ->
      match h2.formula with
      | Not p -> formula_equal h.formula p
      | _ -> false
    ) g.hyps
  ) g.hyps in
  let has_bot = List.exists (fun h -> h.formula = Bot) g.hyps in
  if found || found2 || has_bot then Ok []
  else Err "No contradiction found in hypotheses."

let tactic_destruct g hname =
  match find_hyp g hname with
  | None -> Err (Printf.sprintf "No hypothesis named %s." hname)
  | Some h ->
    let other_hyps = List.filter (fun h2 -> h2.name <> hname) g.hyps in
    match h.formula with
    | And (a, b) ->
      let (n1, g1) = fresh_hyp_name { g with hyps = other_hyps } "" in
      let (n2, g2) = fresh_hyp_name g1 "" in
      let new_hyps = g2.hyps @ [{ name = n1; formula = a }; { name = n2; formula = b }] in
      Ok [{ g2 with hyps = new_hyps }]
    | Or (a, b) ->
      let (n1, g1) = fresh_hyp_name { g with hyps = other_hyps } "" in
      let (n2, g2) = fresh_hyp_name { g with hyps = other_hyps; next_h = g1.next_h } "" in
      Ok [
        { g1 with hyps = other_hyps @ [{ name = n1; formula = a }] };
        { g2 with hyps = other_hyps @ [{ name = n2; formula = b }] }
      ]
    | Iff (a, b) ->
      let (n1, g1) = fresh_hyp_name { g with hyps = other_hyps } "" in
      let (n2, g2) = fresh_hyp_name g1 "" in
      let new_hyps = g2.hyps @ [
        { name = n1; formula = Imp (a, b) };
        { name = n2; formula = Imp (b, a) }
      ] in
      Ok [{ g2 with hyps = new_hyps }]
    | _ -> Err (Printf.sprintf "%s is not a conjunction, disjunction, or biconditional." hname)

let tactic_trivial g =
  match g.concl with
  | Top -> Ok []
  | _ ->
    if List.exists (fun h -> formula_equal h.formula g.concl) g.hyps
    then Ok []
    else Err "Goal is not True and no hypothesis matches."

(* ===== Command parsing ===== *)

type command =
  | CmdTheorem of string * formula
  | CmdProof
  | CmdQed
  | CmdShow
  | CmdRestart
  | CmdHelp
  | CmdQuit
  | CmdTactic of string * string option  (* tactic name, optional arg *)

let trim s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && (s.[!i] = ' ' || s.[!i] = '\t') do incr i done;
  let j = ref (n - 1) in
  while !j >= !i && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '.') do decr j done;
  if !i > !j then "" else String.sub s !i (!j - !i + 1)

let parse_command line =
  let s = trim line in
  if s = "" then None
  else if String.length s >= 7 && String.sub s 0 7 = "Theorem" then begin
    (* Theorem name : formula. *)
    let rest = trim (String.sub s 7 (String.length s - 7)) in
    try
      let colon_pos = String.index rest ':' in
      let name = trim (String.sub rest 0 colon_pos) in
      let fstr = trim (String.sub rest (colon_pos + 1)
        (String.length rest - colon_pos - 1)) in
      Some (CmdTheorem (name, parse_formula fstr))
    with _ -> Printf.printf "Error: expected 'Theorem name : formula.'\n"; None
  end
  else if s = "Proof" then Some CmdProof
  else if s = "Qed" then Some CmdQed
  else if s = "Show" then Some CmdShow
  else if s = "Restart" then Some CmdRestart
  else if s = "Help" || s = "help" then Some CmdHelp
  else if s = "Quit" || s = "quit" || s = "exit" then Some CmdQuit
  else begin
    (* Parse as tactic: name [arg] *)
    let parts = String.split_on_char ' ' s in
    match parts with
    | [] -> None
    | [tac] -> Some (CmdTactic (tac, None))
    | tac :: rest -> Some (CmdTactic (tac, Some (String.concat " " rest)))
  end

(* ===== REPL ===== *)

let print_help () =
  print_endline "";
  print_endline "=== Proof Assistant Help ===";
  print_endline "";
  print_endline "Commands:";
  print_endline "  Theorem <name> : <formula>.  Start a new theorem";
  print_endline "  Proof.                       Begin proof mode";
  print_endline "  Qed.                         Finish proof (all goals must be solved)";
  print_endline "  Show.                        Display current proof state";
  print_endline "  Restart.                     Restart current proof";
  print_endline "  Help.                        Show this help";
  print_endline "  Quit.                        Exit";
  print_endline "";
  print_endline "Tactics:";
  print_endline "  assumption       Close goal if conclusion is a hypothesis";
  print_endline "  intro [H]        Introduce antecedent of => as hypothesis";
  print_endline "  split            Split A /\\ B goal into two subgoals";
  print_endline "  left             Prove left side of A \\/ B";
  print_endline "  right            Prove right side of A \\/ B";
  print_endline "  exact H          Close goal using hypothesis H";
  print_endline "  apply H          Apply implication hypothesis H";
  print_endline "  contradiction    Close goal if hypotheses are contradictory";
  print_endline "  destruct H       Case-split on /\\, \\/, or <=>";
  print_endline "  trivial          Close trivially true goals";
  print_endline "  undo             Undo last tactic";
  print_endline "";
  print_endline "Formula syntax:";
  print_endline "  P, Q, R ...      Variables";
  print_endline "  True, False      Constants";
  print_endline "  ~P or not P      Negation";
  print_endline "  P /\\ Q or P && Q  Conjunction";
  print_endline "  P \\/ Q or P || Q  Disjunction";
  print_endline "  P => Q or P -> Q  Implication";
  print_endline "  P <=> Q          Biconditional";
  print_endline ""

type repl_state =
  | Idle
  | InProof of proof_state

let apply_tactic ps tac_name arg =
  match ps.goals with
  | [] -> Printf.printf "No goals to prove.\n"; ps
  | g :: rest ->
    let result = match tac_name with
      | "assumption" -> tactic_assumption g
      | "intro" -> tactic_intro g arg
      | "split" -> tactic_split g
      | "left" -> tactic_left g
      | "right" -> tactic_right g
      | "exact" -> begin match arg with
        | Some a -> tactic_exact g a
        | None -> Err "exact requires a hypothesis name."
        end
      | "apply" -> begin match arg with
        | Some a -> tactic_apply g a
        | None -> Err "apply requires a hypothesis name."
        end
      | "contradiction" | "exfalso" -> tactic_contradiction g
      | "destruct" | "unfold_iff" -> begin match arg with
        | Some a -> tactic_destruct g a
        | None -> Err "destruct requires a hypothesis name."
        end
      | "trivial" -> tactic_trivial g
      | _ -> Err (Printf.sprintf "Unknown tactic: %s" tac_name)
    in
    match result with
    | Err msg -> Printf.printf "Error: %s\n" msg; ps
    | Ok new_goals ->
      let all_goals = new_goals @ rest in
      let ps' = { ps with goals = all_goals; history = ps.goals :: ps.history } in
      print_goal_state all_goals;
      ps'

let () =
  print_endline "== Proof Assistant (Coq-lite) ==";
  print_endline "Type 'Help.' for available commands.\n";
  let state = ref Idle in
  let running = ref true in
  while !running do
    let prompt = match !state with
      | Idle -> "> "
      | InProof _ -> "proof> "
    in
    print_string prompt;
    flush stdout;
    match try Some (input_line stdin) with End_of_file -> None with
    | None -> running := false
    | Some line ->
      match parse_command line with
      | None -> ()
      | Some cmd ->
        match cmd with
        | CmdQuit -> running := false; print_endline "Goodbye!"
        | CmdHelp -> print_help ()
        | CmdTheorem (name, f) ->
          let g = { hyps = []; concl = f; next_h = 0 } in
          let ps = {
            goals = [g];
            theorem_name = name;
            theorem_formula = f;
            history = [];
          } in
          Printf.printf "Theorem %s : %s\n\n" name (formula_to_string f);
          print_goal_state [g];
          state := InProof ps
        | CmdProof -> begin match !state with
          | InProof ps -> print_goal_state ps.goals
          | Idle -> print_endline "No theorem to prove. Use 'Theorem name : formula.' first."
          end
        | CmdQed -> begin match !state with
          | InProof ps ->
            if ps.goals = [] then begin
              Printf.printf "%s is proved!\n\n" ps.theorem_name;
              state := Idle
            end else
              Printf.printf "There are still %d unsolved goal(s).\n" (List.length ps.goals)
          | Idle -> print_endline "Not in proof mode."
          end
        | CmdShow -> begin match !state with
          | InProof ps -> print_goal_state ps.goals
          | Idle -> print_endline "Not in proof mode."
          end
        | CmdRestart -> begin match !state with
          | InProof ps ->
            let g = { hyps = []; concl = ps.theorem_formula; next_h = 0 } in
            let ps' = { ps with goals = [g]; history = [] } in
            print_endline "Proof restarted.\n";
            print_goal_state [g];
            state := InProof ps'
          | Idle -> print_endline "Not in proof mode."
          end
        | CmdTactic (name, arg) -> begin match !state with
          | InProof ps ->
            if name = "undo" then begin
              match ps.history with
              | prev :: rest ->
                let ps' = { ps with goals = prev; history = rest } in
                print_endline "Undone.\n";
                print_goal_state prev;
                state := InProof ps'
              | [] -> print_endline "Nothing to undo."
            end
            else
              state := InProof (apply_tactic ps name arg)
          | Idle -> print_endline "Not in proof mode. Use 'Theorem name : formula.' first."
          end
  done
