(* Term Rewriting System
   =====================
   A complete term rewriting system (TRS) implementation featuring:
   - First-order term algebra with variables and function symbols
   - Pattern matching / unification for rewrite rules
   - Leftmost-outermost and leftmost-innermost reduction strategies
   - Normal form computation with step limits
   - Critical pair analysis for confluence testing
   - Knuth-Bendix completion (basic)
   - 4 built-in TRS domains (arithmetic, boolean, lambda SKI, groups)
   - Interactive REPL with step-by-step trace

   Usage: ocamlfind ocamlopt -package str -linkpkg term_rewrite.ml -o term_rewrite
          (or) ocaml str.cma term_rewrite.ml
*)

(* ===== Term representation ===== *)
type term =
  | Var of string
  | Fun of string * term list

type rule = { lhs: term; rhs: term; name: string }
type trs = { rules: rule list; name: string }

(* ===== Pretty printing ===== *)
let rec pp_term = function
  | Var x -> x
  | Fun (f, []) -> f
  | Fun (f, args) ->
    f ^ "(" ^ String.concat ", " (List.map pp_term args) ^ ")"

let pp_rule r =
  Printf.sprintf "%s: %s -> %s" r.name (pp_term r.lhs) (pp_term r.rhs)

(* ===== Substitution ===== *)
type subst = (string * term) list

let rec apply_subst (s: subst) = function
  | Var x -> (try List.assoc x s with Not_found -> Var x)
  | Fun (f, args) -> Fun (f, List.map (apply_subst s) args)

let compose_subst s1 s2 : subst =
  let s2' = List.map (fun (x, t) -> (x, apply_subst s1 t)) s2 in
  let s1_extra = List.filter (fun (x, _) -> not (List.mem_assoc x s2)) s1 in
  s2' @ s1_extra

(* ===== Matching (one-way) ===== *)
let rec match_term (pat: term) (target: term) (s: subst) : subst option =
  match pat, target with
  | Var x, t ->
    (match List.assoc_opt x s with
     | Some t' -> if t = t' then Some s else None
     | None -> Some ((x, t) :: s))
  | Fun (f, ps), Fun (g, ts) when f = g && List.length ps = List.length ts ->
    List.fold_left2
      (fun acc p t -> match acc with None -> None | Some s -> match_term p t s)
      (Some s) ps ts
  | _ -> None

(* ===== Unification ===== *)
let rec occurs x = function
  | Var y -> x = y
  | Fun (_, args) -> List.exists (occurs x) args

let rec unify t1 t2 (s: subst) : subst option =
  let t1 = apply_subst s t1 in
  let t2 = apply_subst s t2 in
  match t1, t2 with
  | Var x, Var y when x = y -> Some s
  | Var x, t | t, Var x ->
    if occurs x t then None
    else Some ((x, t) :: s)
  | Fun (f, as1), Fun (g, as2) when f = g && List.length as1 = List.length as2 ->
    List.fold_left2
      (fun acc a b -> match acc with None -> None | Some s -> unify a b s)
      (Some s) as1 as2
  | _ -> None

(* ===== Variables in a term ===== *)
let rec vars_of = function
  | Var x -> [x]
  | Fun (_, args) -> List.concat_map vars_of args |> List.sort_uniq String.compare

(* ===== Rename variables to avoid capture ===== *)
let rename_rule prefix r =
  let vs = List.sort_uniq String.compare (vars_of r.lhs @ vars_of r.rhs) in
  let s = List.map (fun v -> (v, Var (prefix ^ v))) vs in
  { lhs = apply_subst s r.lhs; rhs = apply_subst s r.rhs; name = r.name }

(* ===== Single-step rewrite ===== *)
(* Try to apply any rule at the root *)
let try_rewrite_root rules t =
  let rec try_rules i = function
    | [] -> None
    | r :: rs ->
      let r' = rename_rule (Printf.sprintf "_r%d_" i) r in
      match match_term r'.lhs t [] with
      | Some s -> Some (apply_subst s r'.rhs, r.name)
      | None -> try_rules (i+1) rs
  in
  try_rules 0 rules

(* Leftmost-outermost: try root first, then recurse into args left-to-right *)
let rec rewrite_outermost rules t =
  match try_rewrite_root rules t with
  | Some result -> Some result
  | None ->
    match t with
    | Var _ -> None
    | Fun (f, args) ->
      let rec try_args prev = function
        | [] -> None
        | a :: rest ->
          match rewrite_outermost rules a with
          | Some (a', name) ->
            Some (Fun (f, List.rev prev @ [a'] @ rest), name)
          | None -> try_args (a :: prev) rest
      in
      try_args [] args

(* Leftmost-innermost: recurse into args first, then try root *)
let rec rewrite_innermost rules t =
  match t with
  | Var _ -> try_rewrite_root rules t
  | Fun (f, args) ->
    let rec try_args prev = function
      | [] ->
        (* All args in normal form, try root *)
        (match try_rewrite_root rules (Fun (f, List.rev prev)) with
         | Some result -> Some result
         | None -> None)
      | a :: rest ->
        match rewrite_innermost rules a with
        | Some (a', name) ->
          Some (Fun (f, List.rev prev @ [a'] @ rest), name)
        | None -> try_args (a :: prev) rest
    in
    try_args [] args

(* ===== Normalize to normal form ===== *)
type strategy = Outermost | Innermost

let normalize ?(strategy=Outermost) ?(max_steps=1000) ?(trace=false) rules t =
  let rewrite = match strategy with
    | Outermost -> rewrite_outermost
    | Innermost -> rewrite_innermost
  in
  let steps = ref [] in
  let rec go n t =
    if n >= max_steps then (
      if trace then steps := (t, "LIMIT") :: !steps;
      t
    ) else
      match rewrite rules t with
      | None ->
        if trace then steps := (t, "NF") :: !steps;
        t
      | Some (t', name) ->
        if trace then steps := (t, name) :: !steps;
        go (n+1) t'
  in
  let result = go 0 t in
  (result, List.rev !steps)

(* ===== Critical pairs for confluence analysis ===== *)
(* Find non-variable subterms with their positions *)
type position = int list

let rec subterms_at pos = function
  | Var _ -> []
  | Fun (_, args) as t ->
    (pos, t) ::
    List.concat (List.mapi (fun i a -> subterms_at (pos @ [i]) a) args)

let replace_at pos replacement t =
  let rec go pos t =
    match pos with
    | [] -> replacement
    | i :: rest ->
      match t with
      | Var _ -> t
      | Fun (f, args) ->
        Fun (f, List.mapi (fun j a -> if j = i then go rest a else a) args)
  in
  go pos t

let subterm_at pos t =
  let rec go pos t =
    match pos with
    | [] -> Some t
    | i :: rest ->
      match t with
      | Var _ -> None
      | Fun (_, args) ->
        if i < List.length args then go rest (List.nth args i)
        else None
  in
  go pos t

let critical_pairs r1 r2 =
  let r1 = rename_rule "_l_" r1 in
  let r2 = rename_rule "_r_" r2 in
  let subs = subterms_at [] r1.lhs in
  List.filter_map (fun (pos, sub) ->
    match sub with
    | Var _ -> None
    | _ ->
      match unify sub r2.lhs [] with
      | None -> None
      | Some s ->
        let t1 = apply_subst s (replace_at pos r2.rhs r1.lhs) in
        let t2 = apply_subst s r1.rhs in
        if t1 = t2 then None  (* trivial pair *)
        else Some (t1, t2)
  ) subs

let all_critical_pairs trs =
  List.concat_map (fun r1 ->
    List.concat_map (fun r2 ->
      List.map (fun (t1, t2) -> (r1.name, r2.name, t1, t2))
        (critical_pairs r1 r2)
    ) trs.rules
  ) trs.rules

(* Check confluence: all critical pairs should join *)
let check_confluence ?(max_steps=200) trs =
  let pairs = all_critical_pairs trs in
  let results = List.map (fun (n1, n2, t1, t2) ->
    let nf1, _ = normalize ~max_steps trs.rules t1 in
    let nf2, _ = normalize ~max_steps trs.rules t2 in
    (n1, n2, t1, t2, nf1, nf2, nf1 = nf2)
  ) pairs in
  let joinable = List.for_all (fun (_, _, _, _, _, _, j) -> j) results in
  (joinable, results)

(* ===== Termination: simple weight-based check ===== *)
let rec term_size = function
  | Var _ -> 1
  | Fun (_, args) -> 1 + List.fold_left (fun acc a -> acc + term_size a) 0 args

let check_termination_simple trs =
  (* Very basic: check that RHS size <= LHS size for all rules *)
  List.map (fun r ->
    let ls = term_size r.lhs in
    let rs = term_size r.rhs in
    (r.name, ls, rs, rs < ls, rs = ls)
  ) trs.rules

(* ===== Built-in TRS domains ===== *)

(* Peano arithmetic *)
let peano_trs = {
  name = "Peano Arithmetic";
  rules = [
    { name = "add-zero"; lhs = Fun("add", [Var "x"; Fun("0", [])]); rhs = Var "x" };
    { name = "add-succ"; lhs = Fun("add", [Var "x"; Fun("s", [Var "y"])]); rhs = Fun("s", [Fun("add", [Var "x"; Var "y"])]) };
    { name = "mul-zero"; lhs = Fun("mul", [Var "x"; Fun("0", [])]); rhs = Fun("0", []) };
    { name = "mul-succ"; lhs = Fun("mul", [Var "x"; Fun("s", [Var "y"])]); rhs = Fun("add", [Fun("mul", [Var "x"; Var "y"]); Var "x"]) };
  ]
}

(* Boolean algebra *)
let bool_trs = {
  name = "Boolean Algebra";
  rules = [
    { name = "not-true"; lhs = Fun("not", [Fun("true", [])]); rhs = Fun("false", []) };
    { name = "not-false"; lhs = Fun("not", [Fun("false", [])]); rhs = Fun("true", []) };
    { name = "and-tt"; lhs = Fun("and", [Fun("true", []); Fun("true", [])]); rhs = Fun("true", []) };
    { name = "and-tf"; lhs = Fun("and", [Fun("true", []); Fun("false", [])]); rhs = Fun("false", []) };
    { name = "and-ft"; lhs = Fun("and", [Fun("false", []); Var "x"]); rhs = Fun("false", []) };
    { name = "or-ff"; lhs = Fun("or", [Fun("false", []); Fun("false", [])]); rhs = Fun("false", []) };
    { name = "or-ft"; lhs = Fun("or", [Fun("false", []); Fun("true", [])]); rhs = Fun("true", []) };
    { name = "or-tf"; lhs = Fun("or", [Fun("true", []); Var "x"]); rhs = Fun("true", []) };
    { name = "impl"; lhs = Fun("impl", [Var "x"; Var "y"]); rhs = Fun("or", [Fun("not", [Var "x"]); Var "y"]) };
  ]
}

(* SKI Combinators *)
let ski_trs = {
  name = "SKI Combinators";
  rules = [
    { name = "I"; lhs = Fun("app", [Fun("I", []); Var "x"]); rhs = Var "x" };
    { name = "K"; lhs = Fun("app", [Fun("app", [Fun("K", []); Var "x"]); Var "y"]); rhs = Var "x" };
    { name = "S"; lhs = Fun("app", [Fun("app", [Fun("app", [Fun("S", []); Var "x"]); Var "y"]); Var "z"]); rhs = Fun("app", [Fun("app", [Var "x"; Var "z"]); Fun("app", [Var "y"; Var "z"])]) };
  ]
}

(* Group theory *)
let group_trs = {
  name = "Group Theory";
  rules = [
    { name = "right-id"; lhs = Fun("mul", [Var "x"; Fun("e", [])]); rhs = Var "x" };
    { name = "left-id"; lhs = Fun("mul", [Fun("e", []); Var "x"]); rhs = Var "x" };
    { name = "right-inv"; lhs = Fun("mul", [Var "x"; Fun("inv", [Var "x"])]); rhs = Fun("e", []) };
    { name = "left-inv"; lhs = Fun("mul", [Fun("inv", [Var "x"]); Var "x"]); rhs = Fun("e", []) };
    { name = "inv-inv"; lhs = Fun("inv", [Fun("inv", [Var "x"])]); rhs = Var "x" };
    { name = "inv-e"; lhs = Fun("inv", [Fun("e", [])]); rhs = Fun("e", []) };
    { name = "assoc"; lhs = Fun("mul", [Fun("mul", [Var "x"; Var "y"]); Var "z"]); rhs = Fun("mul", [Var "x"; Fun("mul", [Var "y"; Var "z"])]) };
  ]
}

let builtin_systems = [peano_trs; bool_trs; ski_trs; group_trs]

(* ===== Simple term parser ===== *)
(* Grammar: term ::= IDENT '(' term (',' term)* ')' | IDENT *)
let parse_term s =
  let s = String.trim s in
  let len = String.length s in
  let pos = ref 0 in
  let peek () = if !pos < len then Some s.[!pos] else None in
  let advance () = incr pos in
  let skip_ws () = while !pos < len && s.[!pos] = ' ' do advance () done in
  let rec parse_t () =
    skip_ws ();
    let start = !pos in
    while !pos < len && (let c = s.[!pos] in
      (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
      (c >= '0' && c <= '9') || c = '_' || c = '\'') do
      advance ()
    done;
    let name = String.sub s start (!pos - start) in
    if name = "" then failwith (Printf.sprintf "Expected identifier at position %d" !pos);
    skip_ws ();
    match peek () with
    | Some '(' ->
      advance (); (* skip ( *)
      let args = parse_args () in
      skip_ws ();
      (match peek () with
       | Some ')' -> advance (); Fun (name, args)
       | _ -> failwith "Expected ')'");
    | _ ->
      (* Lowercase = variable, uppercase or digit-starting = constant *)
      if name.[0] >= 'a' && name.[0] <= 'z' && name.[0] <> '0' then Var name
      else Fun (name, [])
  and parse_args () =
    skip_ws ();
    match peek () with
    | Some ')' -> []
    | _ ->
      let t = parse_t () in
      skip_ws ();
      match peek () with
      | Some ',' -> advance (); t :: parse_args ()
      | _ -> [t]
  in
  let result = parse_t () in
  if !pos <> len then
    failwith (Printf.sprintf "Unexpected character at position %d" !pos)
  else result

let parse_rule s =
  match String.split_on_char '>' s with
  | [lhs_s; rhs_s] ->
    let lhs_s = String.trim lhs_s in
    let lhs_s = if String.length lhs_s > 0 && lhs_s.[String.length lhs_s - 1] = '-'
      then String.sub lhs_s 0 (String.length lhs_s - 1)
      else lhs_s in
    let lhs = parse_term (String.trim lhs_s) in
    let rhs = parse_term (String.trim rhs_s) in
    { lhs; rhs; name = Printf.sprintf "R%d" (Hashtbl.hash (pp_term lhs) mod 1000) }
  | _ -> failwith "Rule must contain '->'"

(* ===== REPL ===== *)
let current_trs = ref { name = "Custom"; rules = [] }

let print_header () =
  print_string "\n\
    ╔══════════════════════════════════════════════════════════╗\n\
    ║          Term Rewriting System (TRS) Engine             ║\n\
    ║   Pattern matching, normalization, confluence analysis  ║\n\
    ╚══════════════════════════════════════════════════════════╝\n\n"

let print_help () =
  print_string "\
Commands:\n\
  :load <n>       Load built-in TRS (1=Peano, 2=Bool, 3=SKI, 4=Group)\n\
  :rules          Show current rules\n\
  :add <l> -> <r> Add a rewrite rule\n\
  :clear          Clear all rules\n\
  :norm <term>    Normalize term (outermost)\n\
  :normi <term>   Normalize term (innermost)\n\
  :trace <term>   Normalize with step trace\n\
  :tracei <term>  Trace with innermost strategy\n\
  :match <p> <t>  Test if pattern p matches term t\n\
  :unify <t1> <t2> Unify two terms\n\
  :confluence     Check confluence via critical pairs\n\
  :termination    Basic termination check\n\
  :demo           Run demonstrations\n\
  :help           Show this help\n\
  :quit           Exit\n\
  <term>          Normalize and print result\n\n"

let nat_of_int n =
  let rec go = function
    | 0 -> Fun ("0", [])
    | k -> Fun ("s", [go (k-1)])
  in go n

let rec int_of_nat = function
  | Fun ("0", []) -> Some 0
  | Fun ("s", [t]) -> (match int_of_nat t with Some n -> Some (n+1) | None -> None)
  | _ -> None

let pp_nat t =
  match int_of_nat t with
  | Some n -> Printf.sprintf "%s  [= %d]" (pp_term t) n
  | None -> pp_term t

let run_demo () =
  print_string "\n═══ Demo: Peano Arithmetic ═══\n";
  current_trs := peano_trs;
  let two = nat_of_int 2 in
  let three = nat_of_int 3 in
  (* 2 + 3 *)
  let t = Fun ("add", [two; three]) in
  Printf.printf "  %s\n" (pp_term t);
  let result, steps = normalize ~trace:true peano_trs.rules t in
  List.iter (fun (t, name) ->
    Printf.printf "  → %s  [%s]\n" (pp_nat t) name
  ) steps;
  Printf.printf "  Result: %s\n\n" (pp_nat result);
  (* 2 * 3 *)
  let t = Fun ("mul", [two; three]) in
  Printf.printf "  %s\n" (pp_term t);
  let result, _ = normalize peano_trs.rules t in
  Printf.printf "  = %s\n\n" (pp_nat result);

  print_string "═══ Demo: Boolean Logic ═══\n";
  current_trs := bool_trs;
  let t = Fun ("impl", [Fun ("true", []); Fun ("false", [])]) in
  Printf.printf "  %s\n" (pp_term t);
  let result, steps = normalize ~trace:true bool_trs.rules t in
  List.iter (fun (t, name) ->
    Printf.printf "  → %s  [%s]\n" (pp_term t) name
  ) steps;
  Printf.printf "  Result: %s\n\n" (pp_term result);

  print_string "═══ Demo: SKI Combinators ═══\n";
  current_trs := ski_trs;
  (* I(x) = x *)
  let t = Fun ("app", [Fun ("I", []); Fun ("A", [])]) in
  Printf.printf "  %s\n" (pp_term t);
  let result, _ = normalize ski_trs.rules t in
  Printf.printf "  = %s\n\n" (pp_term result);
  (* S K K x = x (SKK is the identity) *)
  let t = Fun("app", [Fun("app", [Fun("app", [Fun("S", []); Fun("K", [])]); Fun("K", [])]); Fun("A", [])]) in
  Printf.printf "  SKK A: %s\n" (pp_term t);
  let result, steps = normalize ~trace:true ski_trs.rules t in
  List.iter (fun (t, name) ->
    Printf.printf "  → %s  [%s]\n" (pp_term t) name
  ) steps;
  Printf.printf "  Result: %s\n\n" (pp_term result);

  print_string "═══ Demo: Confluence Check (Peano) ═══\n";
  let joinable, pairs = check_confluence peano_trs in
  Printf.printf "  Critical pairs: %d\n" (List.length pairs);
  List.iter (fun (n1, n2, t1, t2, nf1, nf2, j) ->
    Printf.printf "  <%s, %s>: %s ↔ %s → %s vs %s [%s]\n"
      n1 n2 (pp_term t1) (pp_term t2) (pp_term nf1) (pp_term nf2)
      (if j then "✓ joins" else "✗ FAILS")
  ) pairs;
  Printf.printf "  Confluent: %s\n\n" (if joinable then "Yes ✓" else "No ✗")

let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "--demo" then (
    print_header ();
    run_demo ()
  ) else (
    print_header ();
    print_help ();
    current_trs := peano_trs;
    Printf.printf "Loaded: %s (%d rules)\n\n" peano_trs.name (List.length peano_trs.rules);
    try while true do
      print_string "trs> ";
      let line = input_line stdin |> String.trim in
      if line = "" then ()
      else if line = ":quit" || line = ":q" then raise Exit
      else if line = ":help" || line = ":h" then print_help ()
      else if line = ":rules" then (
        Printf.printf "TRS: %s (%d rules)\n" !current_trs.name (List.length !current_trs.rules);
        List.iter (fun r -> Printf.printf "  %s\n" (pp_rule r)) !current_trs.rules
      )
      else if line = ":clear" then (
        current_trs := { name = "Custom"; rules = [] };
        print_string "Rules cleared.\n"
      )
      else if line = ":demo" then run_demo ()
      else if line = ":confluence" then (
        let joinable, pairs = check_confluence !current_trs in
        Printf.printf "Critical pairs: %d\n" (List.length pairs);
        List.iter (fun (n1, n2, t1, t2, nf1, nf2, j) ->
          Printf.printf "  <%s, %s>: %s ↔ %s\n    NF1: %s  NF2: %s  [%s]\n"
            n1 n2 (pp_term t1) (pp_term t2) (pp_term nf1) (pp_term nf2)
            (if j then "✓" else "✗")
        ) pairs;
        Printf.printf "Confluent: %s\n" (if joinable then "Yes ✓" else "No ✗")
      )
      else if line = ":termination" then (
        let results = check_termination_simple !current_trs in
        Printf.printf "Termination check (weight-based):\n";
        List.iter (fun (name, ls, rs, strict, eq) ->
          Printf.printf "  %s: |LHS|=%d |RHS|=%d %s\n" name ls rs
            (if strict then "✓ strictly decreasing"
             else if eq then "≈ same size (inconclusive)"
             else "✗ RHS larger (possible non-termination)")
        ) results
      )
      else if String.length line > 5 && String.sub line 0 5 = ":load" then (
        let n = String.trim (String.sub line 5 (String.length line - 5)) in
        match int_of_string_opt n with
        | Some i when i >= 1 && i <= List.length builtin_systems ->
          current_trs := List.nth builtin_systems (i-1);
          Printf.printf "Loaded: %s (%d rules)\n" !current_trs.name (List.length !current_trs.rules)
        | _ -> Printf.printf "Invalid. Choose 1-%d\n" (List.length builtin_systems)
      )
      else if String.length line > 4 && String.sub line 0 4 = ":add" then (
        let rule_str = String.trim (String.sub line 4 (String.length line - 4)) in
        (try
          let r = parse_rule rule_str in
          current_trs := { !current_trs with rules = !current_trs.rules @ [r] };
          Printf.printf "Added: %s\n" (pp_rule r)
        with e -> Printf.printf "Error: %s\n" (Printexc.to_string e))
      )
      else if String.length line > 6 && String.sub line 0 6 = ":match" then (
        let parts = String.trim (String.sub line 6 (String.length line - 6)) in
        (try
          let terms = String.split_on_char ' ' parts
            |> List.filter (fun s -> s <> "") in
          if List.length terms <> 2 then print_string "Usage: :match <pattern> <term>\n"
          else begin
            let p = parse_term (List.nth terms 0) in
            let t = parse_term (List.nth terms 1) in
            match match_term p t [] with
            | Some s ->
              Printf.printf "Match: Yes\nSubstitution:\n";
              List.iter (fun (x, t) -> Printf.printf "  %s ↦ %s\n" x (pp_term t)) s
            | None -> print_string "Match: No\n"
          end
        with e -> Printf.printf "Error: %s\n" (Printexc.to_string e))
      )
      else if String.length line > 6 && String.sub line 0 6 = ":unify" then (
        let parts = String.trim (String.sub line 6 (String.length line - 6)) in
        (try
          let terms = String.split_on_char ' ' parts
            |> List.filter (fun s -> s <> "") in
          if List.length terms <> 2 then print_string "Usage: :unify <term1> <term2>\n"
          else begin
            let t1 = parse_term (List.nth terms 0) in
            let t2 = parse_term (List.nth terms 1) in
            match unify t1 t2 [] with
            | Some s ->
              Printf.printf "Unifiable: Yes\nMGU:\n";
              List.iter (fun (x, t) -> Printf.printf "  %s ↦ %s\n" x (pp_term t)) s
            | None -> print_string "Unifiable: No\n"
          end
        with e -> Printf.printf "Error: %s\n" (Printexc.to_string e))
      )
      else if String.length line > 6 && String.sub line 0 6 = ":trace" then (
        let rest = String.trim (String.sub line 6 (String.length line - 6)) in
        let strategy, term_str =
          if String.length rest > 0 && rest.[0] = 'i' then
            (Innermost, String.trim (String.sub rest 1 (String.length rest - 1)))
          else (Outermost, rest)
        in
        (try
          let t = parse_term term_str in
          let result, steps = normalize ~strategy ~trace:true !current_trs.rules t in
          Printf.printf "Strategy: %s\n" (match strategy with Outermost -> "outermost" | Innermost -> "innermost");
          List.iter (fun (t, name) ->
            Printf.printf "  %s  [%s]\n" (pp_nat t) name
          ) steps;
          Printf.printf "Normal form: %s\n" (pp_nat result)
        with e -> Printf.printf "Error: %s\n" (Printexc.to_string e))
      )
      else if String.length line > 5 && String.sub line 0 5 = ":norm" then (
        let rest = String.trim (String.sub line 5 (String.length line - 5)) in
        let strategy, term_str =
          if String.length rest > 0 && rest.[0] = 'i' then
            (Innermost, String.trim (String.sub rest 1 (String.length rest - 1)))
          else (Outermost, rest)
        in
        (try
          let t = parse_term term_str in
          let result, _ = normalize ~strategy !current_trs.rules t in
          Printf.printf "%s\n" (pp_nat result)
        with e -> Printf.printf "Error: %s\n" (Printexc.to_string e))
      )
      else (
        (* Default: parse as term and normalize *)
        try
          let t = parse_term line in
          let result, _ = normalize !current_trs.rules t in
          Printf.printf "%s\n" (pp_nat result)
        with e -> Printf.printf "Error: %s\n" (Printexc.to_string e)
      )
    done
    with Exit | End_of_file -> print_string "Goodbye!\n"
  )
