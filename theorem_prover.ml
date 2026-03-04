(* theorem_prover.ml - Propositional Theorem Prover via Natural Deduction
 *
 * A complete automated theorem prover for propositional logic built in OCaml.
 * Uses sequent-style backward proof search with natural deduction rules.
 *
 * Concepts demonstrated:
 * - Algebraic data types for logical formulas and proof trees
 * - Recursive proof search with backtracking
 * - Pattern matching for inference rule application
 * - Immutable set-based context management
 * - Pretty printing of proof trees
 * - Formula parsing from string syntax
 *
 * Supported connectives:
 *   ~P          negation (also: not P, !P)
 *   P /\ Q      conjunction (also: P & Q, P and Q)
 *   P \/ Q      disjunction (also: P | Q, P or Q)
 *   P => Q      implication (also: P -> Q)
 *   P <=> Q     biconditional (also: P <-> Q)
 *   True, False propositional constants
 *
 * Natural deduction rules implemented:
 *   Axiom       P |- P
 *   TrueI       G |- True
 *   FalseE      G |- False  =>  G |- P   (ex falso quodlibet)
 *   AndI        G |- A, G |- B  =>  G |- A /\ B
 *   AndE1       G |- A /\ B  =>  G |- A
 *   AndE2       G |- A /\ B  =>  G |- B
 *   OrI1        G |- A  =>  G |- A \/ B
 *   OrI2        G |- B  =>  G |- A \/ B
 *   OrE         G |- A \/ B, G,A |- C, G,B |- C  =>  G |- C
 *   ImpI        G,A |- B  =>  G |- A => B
 *   ImpE        G |- A => B, G |- A  =>  G |- B
 *   NotI        G,A |- False  =>  G |- ~A
 *   NotE        G |- A, G |- ~A  =>  G |- False
 *   DNE         G |- ~~A  =>  G |- A    (classical logic)
 *
 * Usage:
 *   let f = parse "P => (Q => P)"
 *   let result = prove f         (* Some proof_tree *)
 *   let s = pp_proof result      (* pretty-printed proof *)
 *   let valid = is_tautology f   (* true *)
 *)

(* Formula type *)

type formula =
  | Atom  of string
  | Top                         (* True / verum *)
  | Bot                         (* False / falsum *)
  | Not   of formula
  | And   of formula * formula
  | Or    of formula * formula
  | Imp   of formula * formula
  | Iff   of formula * formula

(* Formula comparison and sets *)

let rec compare_formula a b =
  match a, b with
  | Atom s1, Atom s2 -> String.compare s1 s2
  | Atom _, _ -> -1 | _, Atom _ -> 1
  | Top, Top -> 0
  | Top, _ -> -1 | _, Top -> 1
  | Bot, Bot -> 0
  | Bot, _ -> -1 | _, Bot -> 1
  | Not f1, Not f2 -> compare_formula f1 f2
  | Not _, _ -> -1 | _, Not _ -> 1
  | And (a1,b1), And (a2,b2) ->
    let c = compare_formula a1 a2 in if c <> 0 then c else compare_formula b1 b2
  | And _, _ -> -1 | _, And _ -> 1
  | Or (a1,b1), Or (a2,b2) ->
    let c = compare_formula a1 a2 in if c <> 0 then c else compare_formula b1 b2
  | Or _, _ -> -1 | _, Or _ -> 1
  | Imp (a1,b1), Imp (a2,b2) ->
    let c = compare_formula a1 a2 in if c <> 0 then c else compare_formula b1 b2
  | Imp _, _ -> -1 | _, Imp _ -> 1
  | Iff (a1,b1), Iff (a2,b2) ->
    let c = compare_formula a1 a2 in if c <> 0 then c else compare_formula b1 b2

module FormulaSet = Set.Make(struct
  type t = formula
  let compare = compare_formula
end)

type context = FormulaSet.t

(* Pretty printing *)

let prec = function
  | Atom _ | Top | Bot -> 5
  | Not _  -> 4
  | And _  -> 3
  | Or _   -> 2
  | Imp _  -> 1
  | Iff _  -> 0

let rec pp_formula f =
  match f with
  | Atom s -> s
  | Top -> "True"
  | Bot -> "False"
  | Not g -> "~" ^ paren 4 g
  | And (a, b) -> paren 3 a ^ " /\\ " ^ paren 3 b
  | Or  (a, b) -> paren 2 a ^ " \\/ " ^ paren 2 b
  | Imp (a, b) -> paren 2 a ^ " => " ^ paren 1 b
  | Iff (a, b) -> paren 1 a ^ " <=> " ^ paren 1 b

and paren min_prec f =
  if prec f < min_prec then "(" ^ pp_formula f ^ ")"
  else pp_formula f

(* Formula parser *)

exception Parse_error of string

type token =
  | TAtom of string | TTrue | TFalse
  | TNot | TAnd | TOr | TImp | TIff
  | TLParen | TRParen | TEOF

let tokenize s =
  let n = String.length s in
  let i = ref 0 in
  let tokens = ref [] in
  while !i < n do
    match s.[!i] with
    | ' ' | '\t' | '\n' | '\r' -> incr i
    | '(' -> tokens := TLParen :: !tokens; incr i
    | ')' -> tokens := TRParen :: !tokens; incr i
    | '~' | '!' -> tokens := TNot :: !tokens; incr i
    | '&' -> tokens := TAnd :: !tokens; incr i
    | '|' -> tokens := TOr :: !tokens; incr i
    | '/' ->
      if !i + 1 < n && s.[!i+1] = '\\' then
        (tokens := TAnd :: !tokens; i := !i + 2)
      else raise (Parse_error ("unexpected '/' at position " ^ string_of_int !i))
    | '\\' ->
      if !i + 1 < n && s.[!i+1] = '/' then
        (tokens := TOr :: !tokens; i := !i + 2)
      else raise (Parse_error ("unexpected '\\' at position " ^ string_of_int !i))
    | '-' ->
      if !i + 1 < n && s.[!i+1] = '>' then
        (tokens := TImp :: !tokens; i := !i + 2)
      else raise (Parse_error ("unexpected '-' at position " ^ string_of_int !i))
    | '=' ->
      if !i + 1 < n && s.[!i+1] = '>' then
        (tokens := TImp :: !tokens; i := !i + 2)
      else raise (Parse_error ("unexpected '=' at position " ^ string_of_int !i))
    | '<' ->
      if !i + 2 < n && s.[!i+1] = '=' && s.[!i+2] = '>' then
        (tokens := TIff :: !tokens; i := !i + 3)
      else if !i + 2 < n && s.[!i+1] = '-' && s.[!i+2] = '>' then
        (tokens := TIff :: !tokens; i := !i + 3)
      else raise (Parse_error ("unexpected '<' at position " ^ string_of_int !i))
    | c when (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ->
      let start = !i in
      while !i < n && let c = s.[!i] in
            (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
            (c >= '0' && c <= '9') || c = '_'
      do incr i done;
      let word = String.sub s start (!i - start) in
      let tok = match String.lowercase_ascii word with
        | "true" | "t" | "verum" -> TTrue
        | "false" | "f" | "falsum" -> TFalse
        | "not" -> TNot
        | "and" -> TAnd
        | "or" -> TOr
        | _ -> TAtom word
      in
      tokens := tok :: !tokens
    | c -> raise (Parse_error ("unexpected character '" ^ String.make 1 c ^ "'"))
  done;
  List.rev !tokens

let parse s =
  let toks = ref (tokenize s) in
  let peek () = match !toks with t :: _ -> t | [] -> TEOF in
  let advance () = match !toks with _ :: rest -> toks := rest | [] -> () in
  let expect t =
    if peek () = t then advance ()
    else raise (Parse_error "unexpected token")
  in
  let rec parse_iff () =
    let lhs = parse_imp () in
    match peek () with
    | TIff -> advance (); Iff (lhs, parse_iff ())
    | _ -> lhs
  and parse_imp () =
    let lhs = parse_disj () in
    match peek () with
    | TImp -> advance (); Imp (lhs, parse_imp ())
    | _ -> lhs
  and parse_disj () =
    let lhs = ref (parse_conj ()) in
    while peek () = TOr do advance (); lhs := Or (!lhs, parse_conj ()) done;
    !lhs
  and parse_conj () =
    let lhs = ref (parse_unary ()) in
    while peek () = TAnd do advance (); lhs := And (!lhs, parse_unary ()) done;
    !lhs
  and parse_unary () =
    match peek () with
    | TNot -> advance (); Not (parse_unary ())
    | _ -> parse_atom ()
  and parse_atom () =
    match peek () with
    | TAtom s -> advance (); Atom s
    | TTrue -> advance (); Top
    | TFalse -> advance (); Bot
    | TLParen -> advance (); let f = parse_iff () in expect TRParen; f
    | _ -> raise (Parse_error "unexpected token in atom position")
  in
  let f = parse_iff () in
  if peek () <> TEOF then raise (Parse_error "unexpected tokens after formula");
  f

(* Proof trees *)

type rule_name =
  | Axiom | TrueI | FalseE
  | AndI | AndE1 | AndE2
  | OrI1 | OrI2 | OrE
  | ImpI | ImpE
  | NotI | NotE
  | DNE
  | IffI | IffE1 | IffE2

type proof = {
  rule:     rule_name;
  context:  context;
  goal:     formula;
  premises: proof list;
}

let rule_name_to_string = function
  | Axiom -> "Ax" | TrueI -> "TI" | FalseE -> "FE"
  | AndI -> "/\\I" | AndE1 -> "/\\E1" | AndE2 -> "/\\E2"
  | OrI1 -> "\\/I1" | OrI2 -> "\\/I2" | OrE -> "\\/E"
  | ImpI -> "=>I" | ImpE -> "=>E"
  | NotI -> "~I" | NotE -> "~E"
  | DNE -> "DNE"
  | IffI -> "<=>I" | IffE1 -> "<=>E1" | IffE2 -> "<=>E2"

(* Proof search *)

let prove_sequent ?(fuel=50) (ctx : context) (goal : formula) : proof option =
  let rec search fuel ctx goal =
    if fuel <= 0 then None
    else
      if FormulaSet.mem goal ctx then
        Some { rule = Axiom; context = ctx; goal; premises = [] }
      else if goal = Top then
        Some { rule = TrueI; context = ctx; goal; premises = [] }
      else if FormulaSet.mem Bot ctx then
        Some { rule = FalseE; context = ctx; goal; premises = [] }
      else
        let result = try_intro (fuel - 1) ctx goal in
        match result with
        | Some _ -> result
        | None -> try_elim (fuel - 1) ctx goal

  and try_intro fuel ctx goal =
    match goal with
    | And (a, b) ->
      (match search fuel ctx a with
       | Some pa ->
         (match search fuel ctx b with
          | Some pb -> Some { rule = AndI; context = ctx; goal; premises = [pa; pb] }
          | None -> None)
       | None -> None)
    | Imp (a, b) ->
      let ctx' = FormulaSet.add a ctx in
      (match search fuel ctx' b with
       | Some pb -> Some { rule = ImpI; context = ctx; goal; premises = [pb] }
       | None -> None)
    | Or (a, b) ->
      (match search fuel ctx a with
       | Some pa -> Some { rule = OrI1; context = ctx; goal; premises = [pa] }
       | None ->
         match search fuel ctx b with
         | Some pb -> Some { rule = OrI2; context = ctx; goal; premises = [pb] }
         | None -> try_or_elim fuel ctx goal)
    | Not a ->
      let ctx' = FormulaSet.add a ctx in
      (match search fuel ctx' Bot with
       | Some pf -> Some { rule = NotI; context = ctx; goal; premises = [pf] }
       | None -> None)
    | Iff (a, b) ->
      let ctx_a = FormulaSet.add a ctx in
      let ctx_b = FormulaSet.add b ctx in
      (match search fuel ctx_a b with
       | Some pab ->
         (match search fuel ctx_b a with
          | Some pba -> Some { rule = IffI; context = ctx; goal; premises = [pab; pba] }
          | None -> None)
       | None -> None)
    | _ ->
      if FormulaSet.mem (Not (Not goal)) ctx then
        Some { rule = DNE; context = ctx; goal; premises = [] }
      else
        let ctx' = FormulaSet.add (Not goal) ctx in
        match search (fuel / 2) ctx' Bot with
        | Some pf -> Some { rule = DNE; context = ctx; goal;
                            premises = [{ rule = NotI; context = ctx; goal = Not goal;
                                         premises = [pf] }] }
        | None -> None

  and try_or_elim fuel ctx goal =
    FormulaSet.fold (fun hyp acc ->
      match acc with Some _ -> acc | None ->
      match hyp with
      | Or (a, b) ->
        let ctx_a = FormulaSet.add a (FormulaSet.remove hyp ctx) in
        let ctx_b = FormulaSet.add b (FormulaSet.remove hyp ctx) in
        (match search (fuel / 2) ctx_a goal with
         | Some pa ->
           (match search (fuel / 2) ctx_b goal with
            | Some pb ->
              let por = { rule = Axiom; context = ctx; goal = hyp; premises = [] } in
              Some { rule = OrE; context = ctx; goal; premises = [por; pa; pb] }
            | None -> None)
         | None -> None)
      | _ -> None
    ) ctx None

  and try_elim fuel ctx goal =
    let result = ref None in
    FormulaSet.iter (fun hyp ->
      if !result = None then
        match hyp with
        | And (a, b) ->
          let ctx' = FormulaSet.add a (FormulaSet.add b ctx) in
          if not (FormulaSet.mem a ctx && FormulaSet.mem b ctx) then
            (match search fuel ctx' goal with
             | Some pg ->
               result := Some { rule = AndE1; context = ctx; goal; premises = [pg] }
             | None -> ())
        | _ -> ()
    ) ctx;
    if !result <> None then !result
    else begin
      FormulaSet.iter (fun hyp ->
        if !result = None then
          match hyp with
          | Imp (a, b) when not (FormulaSet.mem b ctx) ->
            (match search (fuel / 3) ctx a with
             | Some pa ->
               let ctx' = FormulaSet.add b ctx in
               (match search (fuel / 2) ctx' goal with
                | Some pg ->
                  let pimp = { rule = Axiom; context = ctx; goal = hyp; premises = [] } in
                  result := Some { rule = ImpE; context = ctx; goal;
                                   premises = [pimp; pa; pg] }
                | None -> ())
             | None -> ())
          | _ -> ()
      ) ctx;
      if !result <> None then !result
      else begin
        FormulaSet.iter (fun hyp ->
          if !result = None then
            match hyp with
            | Iff (a, b) ->
              let ctx' = FormulaSet.add (Imp (a, b)) (FormulaSet.add (Imp (b, a)) ctx) in
              if not (FormulaSet.mem (Imp (a, b)) ctx) then
                (match search fuel ctx' goal with
                 | Some pg ->
                   result := Some { rule = IffE1; context = ctx; goal; premises = [pg] }
                 | None -> ())
            | _ -> ()
        ) ctx;
        if !result <> None then !result
        else begin
          if goal = Bot then begin
            FormulaSet.iter (fun hyp ->
              if !result = None then
                match hyp with
                | Not a when FormulaSet.mem a ctx ->
                  result := Some { rule = NotE; context = ctx; goal = Bot; premises = [] }
                | _ ->
                  if FormulaSet.mem (Not hyp) ctx then
                    result := Some { rule = NotE; context = ctx; goal = Bot; premises = [] }
            ) ctx
          end;
          !result
        end
      end
    end
  in
  search fuel ctx goal

(* High-level API *)

let prove ?(fuel=50) f =
  prove_sequent ~fuel FormulaSet.empty f

let prove_from ?(fuel=50) assumptions goal =
  let ctx = List.fold_left (fun s a -> FormulaSet.add a s) FormulaSet.empty assumptions in
  prove_sequent ~fuel ctx goal

let is_tautology ?(fuel=50) f =
  prove ~fuel f <> None

let entails ?(fuel=50) assumptions goal =
  prove_from ~fuel assumptions goal <> None

(* Proof tree pretty printing *)

let pp_context ctx =
  let elems = FormulaSet.elements ctx in
  match elems with
  | [] -> ""
  | _ -> String.concat ", " (List.map pp_formula elems)

let pp_sequent ctx goal =
  let ctx_str = pp_context ctx in
  if ctx_str = "" then "|- " ^ pp_formula goal
  else ctx_str ^ " |- " ^ pp_formula goal

let pp_proof proof =
  let buf = Buffer.create 256 in
  let rec pp indent p =
    let seq = pp_sequent p.context p.goal in
    let rule = rule_name_to_string p.rule in
    Buffer.add_string buf indent;
    Buffer.add_string buf seq;
    Buffer.add_string buf "  [";
    Buffer.add_string buf rule;
    Buffer.add_string buf "]\n";
    List.iter (pp (indent ^ "  ")) p.premises
  in
  pp "" proof;
  Buffer.contents buf

let rec proof_size p =
  1 + List.fold_left (fun acc sub -> acc + proof_size sub) 0 p.premises

let rec proof_depth p =
  match p.premises with
  | [] -> 1
  | subs -> 1 + List.fold_left (fun acc sub -> max acc (proof_depth sub)) 0 subs

let rules_used proof =
  let rec collect acc p =
    let acc = p.rule :: acc in
    List.fold_left collect acc p.premises
  in
  List.rev (collect [] proof)

(* Formula utilities *)

let rec atoms f =
  match f with
  | Atom s -> [s]
  | Top | Bot -> []
  | Not g -> atoms g
  | And (a, b) | Or (a, b) | Imp (a, b) | Iff (a, b) ->
    List.sort_uniq String.compare (atoms a @ atoms b)

let rec complexity = function
  | Atom _ | Top | Bot -> 0
  | Not f -> 1 + complexity f
  | And (a, b) | Or (a, b) | Imp (a, b) | Iff (a, b) ->
    1 + complexity a + complexity b

let rec subst name replacement f =
  match f with
  | Atom s when s = name -> replacement
  | Atom _ | Top | Bot -> f
  | Not g -> Not (subst name replacement g)
  | And (a, b) -> And (subst name replacement a, subst name replacement b)
  | Or  (a, b) -> Or  (subst name replacement a, subst name replacement b)
  | Imp (a, b) -> Imp (subst name replacement a, subst name replacement b)
  | Iff (a, b) -> Iff (subst name replacement a, subst name replacement b)

let rec nnf = function
  | Atom _ | Top | Bot as f -> f
  | Not (Not f) -> nnf f
  | Not Top -> Bot
  | Not Bot -> Top
  | Not (And (a, b)) -> Or (nnf (Not a), nnf (Not b))
  | Not (Or (a, b)) -> And (nnf (Not a), nnf (Not b))
  | Not (Imp (a, b)) -> And (nnf a, nnf (Not b))
  | Not (Iff (a, b)) -> Or (And (nnf a, nnf (Not b)), And (nnf (Not a), nnf b))
  | Not f -> Not (nnf f)
  | And (a, b) -> And (nnf a, nnf b)
  | Or  (a, b) -> Or  (nnf a, nnf b)
  | Imp (a, b) -> Or (nnf (Not a), nnf b)
  | Iff (a, b) -> And (Or (nnf (Not a), nnf b), Or (nnf (Not b), nnf a))

let rec eval env = function
  | Atom s -> (try List.assoc s env with Not_found -> false)
  | Top -> true
  | Bot -> false
  | Not f -> not (eval env f)
  | And (a, b) -> eval env a && eval env b
  | Or  (a, b) -> eval env a || eval env b
  | Imp (a, b) -> (not (eval env a)) || eval env b
  | Iff (a, b) -> eval env a = eval env b

let truth_table_tautology f =
  let vars = atoms f in
  let n = List.length vars in
  let total = 1 lsl n in
  let rec check i =
    if i >= total then true
    else
      let env = List.mapi (fun j v -> (v, (i lsr j) land 1 = 1)) vars in
      if eval env f then check (i + 1)
      else false
  in
  check 0

let truth_table f =
  let vars = atoms f in
  let n = List.length vars in
  let total = 1 lsl n in
  let rec build i acc =
    if i >= total then List.rev acc
    else
      let env = List.mapi (fun j v -> (v, (i lsr j) land 1 = 1)) vars in
      build (i + 1) ((env, eval env f) :: acc)
  in
  build 0 []

let counterexample f =
  let table = truth_table f in
  try Some (fst (List.find (fun (_, r) -> not r) table))
  with Not_found -> None

(* Named theorem library *)

let classic_theorems = [
  ("identity",          "P => P");
  ("modus_ponens",      "(P => Q) => P => Q");
  ("hypothetical_syll", "(P => Q) => (Q => R) => (P => R)");
  ("contrapositive",    "(P => Q) => (~Q => ~P)");
  ("double_negation",   "~~P => P");
  ("excluded_middle",   "P \\/ ~P");
  ("de_morgan_1",       "~(P /\\ Q) <=> (~P \\/ ~Q)");
  ("de_morgan_2",       "~(P \\/ Q) <=> (~P /\\ ~Q)");
  ("distribution",      "P /\\ (Q \\/ R) <=> (P /\\ Q) \\/ (P /\\ R)");
  ("absorption",        "P => (P \\/ Q)");
  ("peirce",            "((P => Q) => P) => P");
  ("explosion",         "False => P");
  ("and_comm",          "(P /\\ Q) <=> (Q /\\ P)");
  ("or_comm",           "(P \\/ Q) <=> (Q \\/ P)");
  ("imp_trans",         "(P => Q) => (Q => R) => (P => R)");
  ("curry",             "(P /\\ Q => R) <=> (P => Q => R)");
]

let prove_classics ?(fuel=80) () =
  List.map (fun (name, s) ->
    let f = parse s in
    (name, f, prove ~fuel f)
  ) classic_theorems

(* Tests *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let test name check =
    if check () then (incr passed; Printf.printf "  PASS  %s\n" name)
    else (incr failed; Printf.printf "  FAIL  %s\n" name)
  in

  Printf.printf "\n=== Theorem Prover Tests ===\n\n";

  Printf.printf "-- Parsing --\n";

  test "parse atom" (fun () ->
    parse "P" = Atom "P");

  test "parse negation" (fun () ->
    parse "~P" = Not (Atom "P"));

  test "parse conjunction" (fun () ->
    parse "P /\\ Q" = And (Atom "P", Atom "Q"));

  test "parse disjunction" (fun () ->
    parse "P \\/ Q" = Or (Atom "P", Atom "Q"));

  test "parse implication" (fun () ->
    parse "P => Q" = Imp (Atom "P", Atom "Q"));

  test "parse biconditional" (fun () ->
    parse "P <=> Q" = Iff (Atom "P", Atom "Q"));

  test "parse arrow syntax" (fun () ->
    parse "P -> Q" = Imp (Atom "P", Atom "Q"));

  test "parse double arrow syntax" (fun () ->
    parse "P <-> Q" = Iff (Atom "P", Atom "Q"));

  test "parse True/False" (fun () ->
    parse "True" = Top && parse "False" = Bot);

  test "parse precedence" (fun () ->
    parse "~P /\\ Q \\/ R => S" =
      Imp (Or (And (Not (Atom "P"), Atom "Q"), Atom "R"), Atom "S"));

  test "parse right-associative implication" (fun () ->
    parse "P => Q => R" = Imp (Atom "P", Imp (Atom "Q", Atom "R")));

  test "parse parenthesized" (fun () ->
    parse "(P \\/ Q) /\\ R" = And (Or (Atom "P", Atom "Q"), Atom "R"));

  test "parse word operators" (fun () ->
    parse "P and Q or R" = Or (And (Atom "P", Atom "Q"), Atom "R"));

  test "parse not word" (fun () ->
    parse "not P" = Not (Atom "P"));

  test "parse complex" (fun () ->
    let f = parse "(P => Q) => (~Q => ~P)" in
    f = Imp (Imp (Atom "P", Atom "Q"), Imp (Not (Atom "Q"), Not (Atom "P"))));

  Printf.printf "\n-- Pretty Printing --\n";

  test "pp round-trip atom" (fun () ->
    pp_formula (Atom "P") = "P");

  test "pp round-trip complex" (fun () ->
    let s = "P => Q => R" in
    let f = parse s in
    pp_formula f = "P => Q => R");

  test "pp adds parens when needed" (fun () ->
    pp_formula (Imp (Or (Atom "A", Atom "B"), Atom "C")) = "A \\/ B => C");

  test "pp negation precedence" (fun () ->
    pp_formula (Not (And (Atom "A", Atom "B"))) = "~(A /\\ B)");

  Printf.printf "\n-- Formula Utilities --\n";

  test "atoms" (fun () ->
    atoms (parse "P => (Q /\\ R)") = ["P"; "Q"; "R"]);

  test "complexity" (fun () ->
    complexity (parse "P => (Q /\\ R)") = 2);

  test "subst" (fun () ->
    subst "P" (Atom "X") (parse "P => Q") = Imp (Atom "X", Atom "Q"));

  test "nnf pushes negations" (fun () ->
    nnf (parse "~(P /\\ Q)") = Or (Not (Atom "P"), Not (Atom "Q")));

  test "nnf eliminates double negation" (fun () ->
    nnf (parse "~~P") = Atom "P");

  test "nnf converts implication" (fun () ->
    nnf (parse "P => Q") = Or (Not (Atom "P"), Atom "Q"));

  test "eval true formula" (fun () ->
    eval [("P", true); ("Q", false)] (parse "P \\/ Q") = true);

  test "eval false formula" (fun () ->
    eval [("P", false); ("Q", false)] (parse "P /\\ Q") = false);

  test "eval implication" (fun () ->
    eval [("P", false); ("Q", true)] (parse "P => Q") = true);

  Printf.printf "\n-- Truth Table --\n";

  test "truth_table_tautology for P \\/ ~P" (fun () ->
    truth_table_tautology (parse "P \\/ ~P"));

  test "truth_table_tautology false for P" (fun () ->
    not (truth_table_tautology (parse "P")));

  test "truth_table size" (fun () ->
    List.length (truth_table (parse "P /\\ Q")) = 4);

  test "counterexample for non-tautology" (fun () ->
    counterexample (parse "P") <> None);

  test "no counterexample for tautology" (fun () ->
    counterexample (parse "P => P") = None);

  Printf.printf "\n-- Proof Search (basic) --\n";

  test "prove identity P => P" (fun () ->
    is_tautology (parse "P => P"));

  test "prove True" (fun () ->
    is_tautology Top);

  test "prove explosion False => P" (fun () ->
    is_tautology (parse "False => P"));

  test "prove modus ponens schema" (fun () ->
    is_tautology (parse "(P => Q) => P => Q"));

  test "prove and introduction" (fun () ->
    entails [Atom "P"; Atom "Q"] (And (Atom "P", Atom "Q")));

  test "prove and elimination left" (fun () ->
    entails [And (Atom "P", Atom "Q")] (Atom "P"));

  test "prove and elimination right" (fun () ->
    entails [And (Atom "P", Atom "Q")] (Atom "Q"));

  test "prove or introduction left" (fun () ->
    entails [Atom "P"] (Or (Atom "P", Atom "Q")));

  test "prove or introduction right" (fun () ->
    entails [Atom "Q"] (Or (Atom "P", Atom "Q")));

  test "prove implication introduction" (fun () ->
    is_tautology (parse "P => (Q => P)"));

  test "prove negation introduction" (fun () ->
    entails [Imp (Atom "P", Bot)] (Not (Atom "P")));

  Printf.printf "\n-- Proof Search (classical) --\n";

  test "prove excluded middle" (fun () ->
    is_tautology (parse "P \\/ ~P"));

  test "prove double negation elimination" (fun () ->
    is_tautology (parse "~~P => P"));

  test "prove contrapositive" (fun () ->
    is_tautology (parse "(P => Q) => (~Q => ~P)"));

  test "prove hypothetical syllogism" (fun () ->
    is_tautology (parse "(P => Q) => (Q => R) => (P => R)"));

  test "prove de Morgan 1" (fun () ->
    is_tautology (parse "~(P /\\ Q) <=> (~P \\/ ~Q)"));

  test "prove de Morgan 2" (fun () ->
    is_tautology (parse "~(P \\/ Q) <=> (~P /\\ ~Q)"));

  test "prove distribution" (fun () ->
    is_tautology (parse "P /\\ (Q \\/ R) <=> (P /\\ Q) \\/ (P /\\ R)"));

  test "prove absorption" (fun () ->
    is_tautology (parse "P => (P \\/ Q)"));

  test "prove Peirce's law" (fun () ->
    is_tautology (parse "((P => Q) => P) => P"));

  test "prove and commutativity" (fun () ->
    is_tautology (parse "(P /\\ Q) <=> (Q /\\ P)"));

  test "prove or commutativity" (fun () ->
    is_tautology (parse "(P \\/ Q) <=> (Q \\/ P)"));

  test "prove curry/uncurry" (fun () ->
    is_tautology (parse "(P /\\ Q => R) <=> (P => Q => R)"));

  Printf.printf "\n-- Proof Search (non-tautologies) --\n";

  test "P alone is not a tautology" (fun () ->
    not (is_tautology (parse "P")));

  test "P => Q is not a tautology" (fun () ->
    not (is_tautology (parse "P => Q")));

  test "P /\\ Q is not a tautology" (fun () ->
    not (is_tautology (parse "P /\\ Q")));

  test "P /\\ ~P is not a tautology" (fun () ->
    not (is_tautology (parse "P /\\ ~P")));

  Printf.printf "\n-- Proof Properties --\n";

  test "proof_size for identity" (fun () ->
    match prove (parse "P => P") with
    | Some p -> proof_size p >= 1
    | None -> false);

  test "proof_depth for identity" (fun () ->
    match prove (parse "P => P") with
    | Some p -> proof_depth p >= 1
    | None -> false);

  test "rules_used contains ImpI for P => P" (fun () ->
    match prove (parse "P => P") with
    | Some p -> List.mem ImpI (rules_used p)
    | None -> false);

  test "pp_proof produces output" (fun () ->
    match prove (parse "P => P") with
    | Some p -> String.length (pp_proof p) > 0
    | None -> false);

  test "pp_proof contains rule names" (fun () ->
    match prove (parse "P => P") with
    | Some p -> let s = pp_proof p in
      String.length s > 0 && (
        try ignore (String.index s '['); true
        with Not_found -> false)
    | None -> false);

  Printf.printf "\n-- Entailment --\n";

  test "P, P => Q entails Q" (fun () ->
    entails [Atom "P"; Imp (Atom "P", Atom "Q")] (Atom "Q"));

  test "P, Q entails P /\\ Q" (fun () ->
    entails [Atom "P"; Atom "Q"] (And (Atom "P", Atom "Q")));

  test "P \\/ Q, ~P entails Q" (fun () ->
    entails [Or (Atom "P", Atom "Q"); Not (Atom "P")] (Atom "Q"));

  test "P <=> Q, P entails Q" (fun () ->
    entails [Iff (Atom "P", Atom "Q"); Atom "P"] (Atom "Q"));

  test "P <=> Q, Q entails P" (fun () ->
    entails [Iff (Atom "P", Atom "Q"); Atom "Q"] (Atom "P"));

  Printf.printf "\n-- Consistency (prover vs truth table) --\n";

  let consistency_formulas = [
    "P => P";
    "P => (Q => P)";
    "(P => Q) => (~Q => ~P)";
    "P \\/ ~P";
    "~~P => P";
    "P => Q";
    "P /\\ ~P";
    "P \\/ Q";
  ] in
  List.iter (fun s ->
    test (Printf.sprintf "consistency: %s" s) (fun () ->
      let f = parse s in
      is_tautology f = truth_table_tautology f)
  ) consistency_formulas;

  Printf.printf "\n-- Classic Theorems Library --\n";

  test "prove_classics returns all theorems" (fun () ->
    let results = prove_classics () in
    List.length results = List.length classic_theorems);

  test "all classic theorems are provable" (fun () ->
    let results = prove_classics () in
    List.for_all (fun (_, _, p) -> p <> None) results);

  test "all classic theorems match truth tables" (fun () ->
    let results = prove_classics () in
    List.for_all (fun (_, f, _) -> truth_table_tautology f) results);

  Printf.printf "\n=== Results: %d passed, %d failed ===\n" !passed !failed;
  if !failed > 0 then exit 1
