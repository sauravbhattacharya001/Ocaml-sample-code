(* argumentation.ml — Dung's Abstract Argumentation Framework
   Formal argumentation for AI reasoning about conflicting arguments.

   Semantics: Grounded, Preferred, Stable, Complete, Admissible, Ideal.

   Features:
   - Framework construction with arguments and attack relations
   - Extension computation under all major semantics
   - Credulous and skeptical acceptance queries
   - Argument status classification (accepted/rejected/undecided)
   - Framework analysis (well-founded, coherent, SCCs, stats)
   - Dispute tree generation for dialectical reasoning
   - ASCII attack graph visualization
   - DOT/Graphviz export
   - 6 built-in example frameworks
   - Interactive REPL

   Usage: ocaml argumentation.ml
*)

(* ── Types ────────────────────────────────────────────────────────── *)

type argument = string
type attack = argument * argument (* attacker, target *)

type framework = {
  args : argument list;
  attacks : attack list;
}

type semantics = Grounded | Preferred | Stable | Complete | Admissible | Ideal

(* ── Set utilities (lists as sets) ────────────────────────────────── *)

let mem x s = List.mem x s
let add x s = if mem x s then s else x :: s
let union s1 s2 = List.fold_left (fun acc x -> add x acc) s1 s2
let inter s1 s2 = List.filter (fun x -> mem x s2) s1
let diff s1 s2 = List.filter (fun x -> not (mem x s2)) s1
let subset s1 s2 = List.for_all (fun x -> mem x s2) s1
let set_eq s1 s2 = subset s1 s2 && subset s2 s1
let remove x s = List.filter (fun y -> y <> x) s

(* ── Framework operations ─────────────────────────────────────────── *)

let create_framework args attacks =
  { args; attacks }

let empty_framework () =
  { args = []; attacks = [] }

let add_argument fw a =
  { fw with args = add a fw.args }

let add_attack fw (a, b) =
  let fw = add_argument (add_argument fw a) b in
  { fw with attacks = add (a, b) fw.attacks }

let remove_argument fw a =
  { args = remove a fw.args;
    attacks = List.filter (fun (x, y) -> x <> a && y <> a) fw.attacks }

let remove_attack fw (a, b) =
  { fw with attacks = List.filter (fun (x, y) -> x <> a || y <> b) fw.attacks }

let attackers_of fw a =
  List.filter_map (fun (x, y) -> if y = a then Some x else None) fw.attacks

let attacked_by fw a =
  List.filter_map (fun (x, y) -> if x = a then Some y else None) fw.attacks

(* ── Conflict-free, defence, admissibility ────────────────────────── *)

let is_conflict_free fw s =
  not (List.exists (fun (a, b) -> mem a s && mem b s) fw.attacks)

let defends fw s a =
  let atks = attackers_of fw a in
  List.for_all (fun att ->
    List.exists (fun d -> mem (d, att) fw.attacks) s
  ) atks

let is_admissible fw s =
  is_conflict_free fw s &&
  List.for_all (defends fw s) s

(* Characteristic function F(S) = { a in Args | S defends a } *)
let characteristic_fn fw s =
  List.filter (defends fw s) fw.args

(* ── Extension computation ────────────────────────────────────────── *)

(* Grounded: least fixed point of F starting from empty set *)
let grounded_extension fw =
  let rec fixpoint s =
    let s' = characteristic_fn fw s in
    let combined = union s s' in
    if set_eq combined s then s
    else fixpoint combined
  in
  fixpoint []

(* Enumerate all subsets up to size n *)
let rec powerset = function
  | [] -> [[]]
  | x :: xs ->
    let rest = powerset xs in
    rest @ List.map (fun s -> x :: s) rest

(* Complete extensions: fixed points of F that are admissible *)
let complete_extensions fw =
  let subsets = powerset fw.args in
  List.filter (fun s ->
    is_admissible fw s && set_eq (characteristic_fn fw s) s
  ) subsets

(* Preferred extensions: maximal complete *)
let preferred_extensions fw =
  let comps = complete_extensions fw in
  List.filter (fun s ->
    not (List.exists (fun s' ->
      s' <> s && subset s s' && not (set_eq s s')
    ) comps)
  ) comps

(* Stable extensions: conflict-free sets attacking all outsiders *)
let stable_extensions fw =
  let subsets = powerset fw.args in
  List.filter (fun s ->
    is_conflict_free fw s &&
    let outside = diff fw.args s in
    List.for_all (fun a ->
      List.exists (fun d -> mem (d, a) fw.attacks) s
    ) outside
  ) subsets

(* All admissible sets *)
let admissible_sets fw =
  let subsets = powerset fw.args in
  List.filter (is_admissible fw) subsets

(* Ideal extension: largest admissible set contained in every preferred *)
let ideal_extension fw =
  let prefs = preferred_extensions fw in
  match prefs with
  | [] -> []
  | _ ->
    let candidates = admissible_sets fw in
    let in_all_prefs s =
      List.for_all (fun p -> subset s p) prefs
    in
    let valid = List.filter in_all_prefs candidates in
    List.fold_left (fun best s ->
      if List.length s > List.length best then s else best
    ) [] valid

(* ── Acceptance queries ───────────────────────────────────────────── *)

let extensions_for fw sem =
  match sem with
  | Grounded -> [grounded_extension fw]
  | Preferred -> preferred_extensions fw
  | Stable -> stable_extensions fw
  | Complete -> complete_extensions fw
  | Admissible -> admissible_sets fw
  | Ideal -> [ideal_extension fw]

let credulous_acceptance fw sem a =
  let exts = extensions_for fw sem in
  List.exists (fun e -> mem a e) exts

let skeptical_acceptance fw sem a =
  let exts = extensions_for fw sem in
  exts <> [] && List.for_all (fun e -> mem a e) exts

type status = Accepted | Rejected | Undecided

let argument_status fw sem a =
  let exts = extensions_for fw sem in
  if exts = [] then Undecided
  else if List.for_all (fun e -> mem a e) exts then Accepted
  else if List.for_all (fun e -> not (mem a e)) exts then Rejected
  else Undecided

let status_string = function
  | Accepted -> "accepted"
  | Rejected -> "rejected"
  | Undecided -> "undecided"

(* ── Framework analysis ───────────────────────────────────────────── *)

let is_well_founded fw =
  set_eq (grounded_extension fw) fw.args

let is_coherent fw =
  let prefs = preferred_extensions fw in
  let stabs = stable_extensions fw in
  List.for_all (fun p -> List.exists (set_eq p) stabs) prefs

let has_empty_grounded fw =
  grounded_extension fw = []

let framework_stats fw =
  let n = List.length fw.args in
  let m = List.length fw.attacks in
  let density = if n <= 1 then 0.0
    else float_of_int m /. float_of_int (n * (n - 1)) in
  (n, m, density)

(* Tarjan's SCC *)
let strongly_connected_components fw =
  let index_counter = ref 0 in
  let stack = ref [] in
  let on_stack = Hashtbl.create 16 in
  let indices = Hashtbl.create 16 in
  let lowlinks = Hashtbl.create 16 in
  let result = ref [] in

  let rec strongconnect v =
    Hashtbl.replace indices v !index_counter;
    Hashtbl.replace lowlinks v !index_counter;
    incr index_counter;
    stack := v :: !stack;
    Hashtbl.replace on_stack v true;

    let succs = attacked_by fw v in
    List.iter (fun w ->
      if not (Hashtbl.mem indices w) then begin
        strongconnect w;
        Hashtbl.replace lowlinks v
          (min (Hashtbl.find lowlinks v) (Hashtbl.find lowlinks w))
      end else if Hashtbl.mem on_stack w && Hashtbl.find on_stack w then
        Hashtbl.replace lowlinks v
          (min (Hashtbl.find lowlinks v) (Hashtbl.find indices w))
    ) succs;

    if Hashtbl.find lowlinks v = Hashtbl.find indices v then begin
      let scc = ref [] in
      let continue = ref true in
      while !continue do
        match !stack with
        | w :: rest ->
          stack := rest;
          Hashtbl.replace on_stack w false;
          scc := w :: !scc;
          if w = v then continue := false
        | [] -> continue := false
      done;
      result := !scc :: !result
    end
  in

  List.iter (fun v ->
    if not (Hashtbl.mem indices v) then strongconnect v
  ) fw.args;
  !result

(* ── Dispute trees ────────────────────────────────────────────────── *)

type dispute_node =
  | Proponent of argument * dispute_node list
  | Opponent of argument * dispute_node list
  | ProponentWin of argument
  | OpponentWin of argument

let build_dispute_tree fw target max_depth =
  let rec pro_move a depth used =
    if depth > max_depth then ProponentWin a
    else
      let atks = attackers_of fw a in
      let atks = diff atks used in
      if atks = [] then ProponentWin a
      else Proponent (a, List.map (fun att ->
        opp_move att (depth + 1) (add a used)
      ) atks)
  and opp_move a depth used =
    if depth > max_depth then OpponentWin a
    else
      let counters = attackers_of fw a in
      let counters = diff counters used in
      if counters = [] then OpponentWin a
      else Opponent (a, List.map (fun c ->
        pro_move c (depth + 1) (add a used)
      ) counters)
  in
  pro_move target 0 []

let rec print_dispute_tree indent node =
  let pad = String.make indent ' ' in
  match node with
  | ProponentWin a ->
    Printf.printf "%s✓ PRO[%s] (unattacked — wins)\n" pad a
  | OpponentWin a ->
    Printf.printf "%s✗ OPP[%s] (no counter — loses)\n" pad a
  | Proponent (a, children) ->
    Printf.printf "%s● PRO[%s] (attacked by:)\n" pad a;
    List.iter (print_dispute_tree (indent + 4)) children
  | Opponent (a, children) ->
    Printf.printf "%s○ OPP[%s] (countered by:)\n" pad a;
    List.iter (print_dispute_tree (indent + 4)) children

(* ── Visualization ────────────────────────────────────────────────── *)

let print_framework fw =
  Printf.printf "Arguments: {%s}\n" (String.concat ", " (List.sort compare fw.args));
  Printf.printf "Attacks:\n";
  List.iter (fun (a, b) ->
    Printf.printf "  %s → %s\n" a b
  ) (List.sort compare fw.attacks);
  let (n, m, d) = framework_stats fw in
  Printf.printf "(%d arguments, %d attacks, density=%.3f)\n" n m d

let print_extension label ext =
  Printf.printf "%s: {%s}\n" label
    (String.concat ", " (List.sort compare ext))

let print_extensions label exts =
  if exts = [] then
    Printf.printf "%s: (none)\n" label
  else begin
    Printf.printf "%s (%d):\n" label (List.length exts);
    List.iteri (fun i e ->
      Printf.printf "  %d. {%s}\n" (i + 1)
        (String.concat ", " (List.sort compare e))
    ) exts
  end

(* DOT export *)
let to_dot fw =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "digraph argumentation {\n";
  Buffer.add_string buf "  rankdir=LR;\n";
  Buffer.add_string buf "  node [shape=ellipse, style=filled, fillcolor=lightblue];\n";
  List.iter (fun a ->
    Buffer.add_string buf (Printf.sprintf "  \"%s\";\n" a)
  ) fw.args;
  List.iter (fun (a, b) ->
    Buffer.add_string buf (Printf.sprintf "  \"%s\" -> \"%s\" [color=red];\n" a b)
  ) fw.attacks;
  Buffer.add_string buf "}\n";
  Buffer.contents buf

(* ASCII attack graph *)
let ascii_graph fw =
  Printf.printf "\n┌─ Attack Graph ─────────────────────────┐\n";
  Printf.printf "│                                        │\n";
  List.iter (fun a ->
    let targets = attacked_by fw a in
    let sources = attackers_of fw a in
    if targets = [] && sources = [] then
      Printf.printf "│  [%s] (isolated)                       \n" a
    else begin
      if targets <> [] then
        Printf.printf "│  [%s] ──attacks──▶ %s\n" a
          (String.concat ", " (List.map (fun t -> "[" ^ t ^ "]") targets));
      if sources <> [] then
        Printf.printf "│  [%s] ◀──attacked by── %s\n" a
          (String.concat ", " (List.map (fun s -> "[" ^ s ^ "]") sources))
    end
  ) (List.sort compare fw.args);
  Printf.printf "│                                        │\n";
  Printf.printf "└────────────────────────────────────────┘\n"

(* ── Built-in examples ────────────────────────────────────────────── *)

let nixon_diamond () =
  create_framework
    ["nixon"; "republican"; "quaker"; "hawk"; "pacifist"]
    [("republican", "pacifist"); ("quaker", "hawk");
     ("hawk", "pacifist"); ("pacifist", "hawk")]

let simple_chain () =
  create_framework
    ["a"; "b"; "c"]
    [("a", "b"); ("b", "c")]

let odd_cycle () =
  create_framework
    ["a"; "b"; "c"]
    [("a", "b"); ("b", "c"); ("c", "a")]

let even_cycle () =
  create_framework
    ["a"; "b"; "c"; "d"]
    [("a", "b"); ("b", "c"); ("c", "d"); ("d", "a")]

let self_attacker () =
  create_framework
    ["a"; "b"]
    [("a", "a"); ("b", "a")]

let policy_debate () =
  create_framework
    ["tax_cut"; "deficit_risk"; "growth"; "inequality";
     "trickle_down"; "evidence_against"]
    [("deficit_risk", "tax_cut"); ("growth", "deficit_risk");
     ("inequality", "tax_cut"); ("trickle_down", "inequality");
     ("evidence_against", "trickle_down"); ("growth", "inequality")]

let examples = [
  ("nixon", "Nixon Diamond — classic undecidability", nixon_diamond);
  ("chain", "Simple chain a→b→c — reinstatement", simple_chain);
  ("odd_cycle", "Odd cycle a→b→c→a", odd_cycle);
  ("even_cycle", "Even cycle a→b→c→d→a", even_cycle);
  ("self_attack", "Self-attacker a→a with defender b→a", self_attacker);
  ("debate", "Policy debate — 6 arguments on tax policy", policy_debate);
]

(* ── Full analysis ────────────────────────────────────────────────── *)

let full_analysis fw =
  Printf.printf "\n═══ Framework Analysis ═══════════════════════\n\n";
  print_framework fw;
  ascii_graph fw;

  Printf.printf "\n── Semantics ──\n";
  print_extension "Grounded" (grounded_extension fw);
  print_extensions "Complete" (complete_extensions fw);
  print_extensions "Preferred" (preferred_extensions fw);
  print_extensions "Stable" (stable_extensions fw);
  print_extension "Ideal" (ideal_extension fw);

  Printf.printf "\n── Argument Status (under preferred) ──\n";
  List.iter (fun a ->
    let st = argument_status fw Preferred a in
    Printf.printf "  %s: %s\n" a (status_string st)
  ) (List.sort compare fw.args);

  Printf.printf "\n── Properties ──\n";
  Printf.printf "  Well-founded: %b\n" (is_well_founded fw);
  Printf.printf "  Coherent: %b\n" (is_coherent fw);
  Printf.printf "  Empty grounded: %b\n" (has_empty_grounded fw);

  let sccs = strongly_connected_components fw in
  Printf.printf "  SCCs (%d): " (List.length sccs);
  List.iter (fun scc ->
    Printf.printf "{%s} " (String.concat "," (List.sort compare scc))
  ) sccs;
  Printf.printf "\n";
  Printf.printf "══════════════════════════════════════════════\n"

(* ── REPL ─────────────────────────────────────────────────────────── *)

let parse_semantics s =
  match String.lowercase_ascii s with
  | "grounded" -> Some Grounded
  | "preferred" -> Some Preferred
  | "stable" -> Some Stable
  | "complete" -> Some Complete
  | "admissible" -> Some Admissible
  | "ideal" -> Some Ideal
  | _ -> None

let print_help () =
  Printf.printf "\n── Argumentation Framework REPL ──\n";
  Printf.printf "  add <arg>              Add argument\n";
  Printf.printf "  attack <a> <b>         Add attack a → b\n";
  Printf.printf "  remove <arg>           Remove argument + attacks\n";
  Printf.printf "  remove_attack <a> <b>  Remove specific attack\n";
  Printf.printf "  show                   Display framework (ASCII graph)\n";
  Printf.printf "  grounded               Compute grounded extension\n";
  Printf.printf "  preferred              Compute preferred extensions\n";
  Printf.printf "  stable                 Compute stable extensions\n";
  Printf.printf "  complete               Compute complete extensions\n";
  Printf.printf "  admissible             List admissible sets\n";
  Printf.printf "  ideal                  Compute ideal extension\n";
  Printf.printf "  status                 Acceptance status (preferred)\n";
  Printf.printf "  credulous <sem> <arg>  Credulous acceptance query\n";
  Printf.printf "  skeptical <sem> <arg>  Skeptical acceptance query\n";
  Printf.printf "  dispute <arg>          Generate dispute tree\n";
  Printf.printf "  analyze                Full framework analysis\n";
  Printf.printf "  dot                    Export DOT format\n";
  Printf.printf "  load <name>            Load built-in example\n";
  Printf.printf "  examples               List available examples\n";
  Printf.printf "  clear                  Reset framework\n";
  Printf.printf "  help                   Show this help\n";
  Printf.printf "  quit                   Exit\n\n"

let split_words s =
  let s = String.trim s in
  let len = String.length s in
  let rec scan i acc cur =
    if i >= len then
      if cur <> "" then List.rev (cur :: acc)
      else List.rev acc
    else if s.[i] = ' ' || s.[i] = '\t' then
      if cur <> "" then scan (i + 1) (cur :: acc) ""
      else scan (i + 1) acc ""
    else
      scan (i + 1) acc (cur ^ String.make 1 s.[i])
  in
  scan 0 [] ""

let () =
  Printf.printf "╔══════════════════════════════════════════════╗\n";
  Printf.printf "║   Dung's Abstract Argumentation Framework   ║\n";
  Printf.printf "║   Formal reasoning about conflicting args   ║\n";
  Printf.printf "╚══════════════════════════════════════════════╝\n";
  Printf.printf "Type 'help' for commands, 'examples' for demos.\n\n";

  let fw = ref (empty_framework ()) in
  let running = ref true in

  while !running do
    Printf.printf "arg> %!";
    let line = try input_line stdin with End_of_file -> running := false; "quit" in
    let words = split_words line in
    match words with
    | [] -> ()
    | ["quit"] | ["exit"] | ["q"] ->
      Printf.printf "Goodbye.\n"; running := false
    | ["help"] | ["h"] -> print_help ()
    | ["add"; a] ->
      fw := add_argument !fw a;
      Printf.printf "Added argument '%s'\n" a
    | ["attack"; a; b] ->
      fw := add_attack !fw (a, b);
      Printf.printf "Added attack %s → %s\n" a b
    | ["remove"; a] ->
      fw := remove_argument !fw a;
      Printf.printf "Removed argument '%s'\n" a
    | ["remove_attack"; a; b] ->
      fw := remove_attack !fw (a, b);
      Printf.printf "Removed attack %s → %s\n" a b
    | ["show"] ->
      print_framework !fw;
      ascii_graph !fw
    | ["grounded"] ->
      print_extension "Grounded" (grounded_extension !fw)
    | ["preferred"] ->
      print_extensions "Preferred" (preferred_extensions !fw)
    | ["stable"] ->
      print_extensions "Stable" (stable_extensions !fw)
    | ["complete"] ->
      print_extensions "Complete" (complete_extensions !fw)
    | ["admissible"] ->
      print_extensions "Admissible" (admissible_sets !fw)
    | ["ideal"] ->
      print_extension "Ideal" (ideal_extension !fw)
    | ["status"] ->
      Printf.printf "Argument status (preferred semantics):\n";
      List.iter (fun a ->
        let st = argument_status !fw Preferred a in
        Printf.printf "  %s: %s\n" a (status_string st)
      ) (List.sort compare !fw.args)
    | ["credulous"; sem_s; a] ->
      (match parse_semantics sem_s with
       | Some sem ->
         let r = credulous_acceptance !fw sem a in
         Printf.printf "Credulous(%s, %s) = %b\n" sem_s a r
       | None -> Printf.printf "Unknown semantics: %s\n" sem_s)
    | ["skeptical"; sem_s; a] ->
      (match parse_semantics sem_s with
       | Some sem ->
         let r = skeptical_acceptance !fw sem a in
         Printf.printf "Skeptical(%s, %s) = %b\n" sem_s a r
       | None -> Printf.printf "Unknown semantics: %s\n" sem_s)
    | ["dispute"; a] ->
      if mem a !fw.args then begin
        Printf.printf "Dispute tree for '%s':\n" a;
        let tree = build_dispute_tree !fw a 6 in
        print_dispute_tree 2 tree
      end else
        Printf.printf "Unknown argument: %s\n" a
    | ["analyze"] -> full_analysis !fw
    | ["dot"] -> Printf.printf "%s" (to_dot !fw)
    | ["load"; name] ->
      (match List.assoc_opt name (List.map (fun (n, _, f) -> (n, f)) examples) with
       | Some f ->
         fw := f ();
         Printf.printf "Loaded '%s'\n" name;
         print_framework !fw
       | None -> Printf.printf "Unknown example: %s (try 'examples')\n" name)
    | ["examples"] ->
      Printf.printf "Built-in examples:\n";
      List.iter (fun (name, desc, _) ->
        Printf.printf "  %-12s  %s\n" name desc
      ) examples
    | ["clear"] ->
      fw := empty_framework ();
      Printf.printf "Framework cleared.\n"
    | _ ->
      Printf.printf "Unknown command. Type 'help' for commands.\n"
  done
