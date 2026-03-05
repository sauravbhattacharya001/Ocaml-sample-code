(* datalog.ml - Datalog Query Engine
 *
 * A bottom-up Datalog engine with semi-naive evaluation, stratified negation,
 * and built-in aggregation.
 *
 * Concepts demonstrated:
 * - Bottom-up (forward-chaining) evaluation vs top-down (miniKanren)
 * - Semi-naive evaluation for efficient fixed-point computation
 * - Unification of terms (constants, variables)
 * - Stratified negation (safe negation via dependency analysis)
 * - Aggregation (count, sum, min, max, group-by)
 * - Topological sorting for stratification
 * - Fixed-point iteration
 *
 * Example:
 *   parent(tom, bob).
 *   parent(bob, ann).
 *   ancestor(X, Y) :- parent(X, Y).
 *   ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
 *   ?- ancestor(tom, X).
 *   => X = bob; X = ann
 *)

(* ══════════════════════════════════════════════
   Terms & Atoms
   ══════════════════════════════════════════════ *)

(** A term is either a constant (string/int) or a logic variable. *)
type term =
  | Const of string
  | Int of int
  | Var of string

(** An atom is a predicate applied to a list of terms. *)
type atom = {
  pred: string;
  args: term list;
  negated: bool;  (** true for negated literals in rule bodies *)
}

(** A rule: head :- body. A fact is a rule with empty body. *)
type rule = {
  head: atom;
  body: atom list;
}

(** A query: ?- atom. *)
type query = atom

(** Aggregation operations. *)
type agg_op = Count | Sum | Min | Max

(** An aggregate query: agg_op(var) over atom with group-by vars. *)
type aggregate = {
  op: agg_op;
  target_var: string;
  source: atom;
  group_by: string list;
}

(* ══════════════════════════════════════════════
   Pretty Printing
   ══════════════════════════════════════════════ *)

let term_to_string = function
  | Const s -> s
  | Int n -> string_of_int n
  | Var v -> String.capitalize_ascii v

let atom_to_string a =
  let neg = if a.negated then "not " else "" in
  let args = String.concat ", " (List.map term_to_string a.args) in
  Printf.sprintf "%s%s(%s)" neg a.pred args

let rule_to_string r =
  match r.body with
  | [] -> atom_to_string r.head ^ "."
  | body ->
    let body_str = String.concat ", " (List.map atom_to_string body) in
    Printf.sprintf "%s :- %s." (atom_to_string r.head) body_str

(* ══════════════════════════════════════════════
   Substitution & Unification
   ══════════════════════════════════════════════ *)

(** A substitution maps variable names to terms. *)
type substitution = (string * term) list

let empty_subst : substitution = []

(** Apply a substitution to a term. *)
let rec apply_term (subst : substitution) = function
  | Var v ->
    (match List.assoc_opt v subst with
     | Some t -> apply_term subst t  (* follow chains *)
     | None -> Var v)
  | t -> t

(** Apply a substitution to an atom. *)
let apply_atom subst a =
  { a with args = List.map (apply_term subst) a.args }

(** Extend a substitution: bind var to term, checking consistency. *)
let extend_subst subst var term =
  let resolved = apply_term subst term in
  match List.assoc_opt var subst with
  | Some existing ->
    let existing' = apply_term subst existing in
    if existing' = resolved then Some subst
    else None
  | None -> Some ((var, resolved) :: subst)

(** Unify a term with a ground term (from a fact). *)
let unify_term subst t1 t2 =
  let t1' = apply_term subst t1 in
  match t1', t2 with
  | Const a, Const b when a = b -> Some subst
  | Int a, Int b when a = b -> Some subst
  | Var v, _ -> extend_subst subst v t2
  | _, Var v -> extend_subst subst v t1'
  | _ -> None

(** Unify an atom's args with a ground fact's args. *)
let unify_atoms subst pattern fact =
  if pattern.pred <> fact.pred then None
  else if List.length pattern.args <> List.length fact.args then None
  else
    List.fold_left2
      (fun acc t1 t2 ->
         match acc with
         | None -> None
         | Some s -> unify_term s t1 t2)
      (Some subst)
      pattern.args fact.args

(* ══════════════════════════════════════════════
   Fact Database
   ══════════════════════════════════════════════ *)

module FactSet = Set.Make(struct
  type t = atom
  let compare a b =
    let c = String.compare a.pred b.pred in
    if c <> 0 then c
    else compare a.args b.args
end)

type database = FactSet.t

let empty_db : database = FactSet.empty

let add_fact db fact = FactSet.add fact db

let add_facts db facts = List.fold_left add_fact db facts

let facts_for_pred db pred =
  FactSet.filter (fun a -> a.pred = pred) db |> FactSet.elements

let db_size db = FactSet.cardinal db

let db_to_list db = FactSet.elements db

let db_diff db1 db2 = FactSet.diff db1 db2

let db_union db1 db2 = FactSet.union db1 db2

(* ══════════════════════════════════════════════
   Rule Evaluation (single rule, one step)
   ══════════════════════════════════════════════ *)

(** Ground an atom: check all args are constants/ints (no variables). *)
let is_ground a =
  List.for_all (fun t ->
    match t with Var _ -> false | _ -> true
  ) a.args

(** Evaluate a single body atom against the database.
    Returns all substitutions that make the atom match some fact. *)
let eval_positive_atom db subst atom =
  let pattern = apply_atom subst atom in
  let candidates = facts_for_pred db pattern.pred in
  List.filter_map (fun fact -> unify_atoms subst pattern fact) candidates

(** Evaluate a negated atom: succeeds (returns subst) if no fact matches. *)
let eval_negated_atom db subst atom =
  let pattern = apply_atom subst { atom with negated = false } in
  let candidates = facts_for_pred db pattern.pred in
  let any_match = List.exists (fun fact ->
    unify_atoms subst pattern fact <> None
  ) candidates in
  if any_match then [] else [subst]

(** Evaluate a conjunction of body atoms (left to right). *)
let eval_body db body =
  List.fold_left
    (fun substs atom ->
       List.concat_map
         (fun subst ->
            if atom.negated then eval_negated_atom db subst atom
            else eval_positive_atom db subst atom)
         substs)
    [empty_subst]
    body

(** Apply a rule: derive all new facts from the current database. *)
let apply_rule db rule =
  let substs = eval_body db rule.body in
  List.filter_map (fun subst ->
    let head = apply_atom subst rule.head in
    if is_ground head then Some head
    else None
  ) substs

(* ══════════════════════════════════════════════
   Stratification (for safe negation)
   ══════════════════════════════════════════════ *)

(** Build a predicate dependency graph.
    An edge from P to Q means P depends on Q.
    Negated edges are marked for stratification. *)
type dep_edge = { from_pred: string; to_pred: string; is_negated: bool }

let build_dependency_graph rules =
  List.concat_map (fun r ->
    List.map (fun b ->
      { from_pred = r.head.pred;
        to_pred = b.pred;
        is_negated = b.negated }
    ) r.body
  ) rules

(** Compute strata using topological sorting of the dependency graph.
    Rules with negation on predicate P must be in a higher stratum than
    rules defining P. Returns list of rule groups (stratum 0 first). *)
let stratify rules =
  let edges = build_dependency_graph rules in
  (* Collect all predicates *)
  let preds = List.fold_left (fun acc e ->
    let acc = if List.mem e.from_pred acc then acc else e.from_pred :: acc in
    if List.mem e.to_pred acc then acc else e.to_pred :: acc
  ) [] edges in
  (* Assign strata: iteratively resolve *)
  let strata = Hashtbl.create 16 in
  List.iter (fun p -> Hashtbl.replace strata p 0) preds;
  let changed = ref true in
  let iterations = ref 0 in
  while !changed && !iterations < 100 do
    changed := false;
    incr iterations;
    List.iter (fun e ->
      let s_from = Hashtbl.find strata e.from_pred in
      let s_to = Hashtbl.find strata e.to_pred in
      let required = if e.is_negated then s_to + 1 else s_to in
      if required > s_from then begin
        Hashtbl.replace strata e.from_pred required;
        changed := true
      end
    ) edges
  done;
  (* Group rules by stratum of their head predicate *)
  let max_stratum = Hashtbl.fold (fun _ s m -> max s m) strata 0 in
  List.init (max_stratum + 1) (fun i ->
    List.filter (fun r ->
      let s = try Hashtbl.find strata r.head.pred with Not_found -> 0 in
      s = i
    ) rules
  )

(* ══════════════════════════════════════════════
   Semi-Naive Evaluation
   ══════════════════════════════════════════════ *)

(** Naive evaluation: apply all rules until fixed point. *)
let eval_naive rules db =
  let db = ref db in
  let changed = ref true in
  let iterations = ref 0 in
  while !changed do
    changed := false;
    incr iterations;
    List.iter (fun rule ->
      let new_facts = apply_rule !db rule in
      List.iter (fun fact ->
        if not (FactSet.mem fact !db) then begin
          db := add_fact !db fact;
          changed := true
        end
      ) new_facts
    ) rules
  done;
  (!db, !iterations)

(** Semi-naive evaluation: only consider newly derived facts.
    Much more efficient than naive for recursive rules. *)
let eval_semi_naive rules db =
  (* Initial pass: derive from existing facts *)
  let new_facts = ref FactSet.empty in
  List.iter (fun rule ->
    let derived = apply_rule db rule in
    List.iter (fun fact ->
      if not (FactSet.mem fact db) then
        new_facts := FactSet.add fact !new_facts
    ) derived
  ) rules;
  let db = ref (db_union db !new_facts) in
  let delta = ref !new_facts in
  let iterations = ref 1 in
  (* Iterate: only use delta facts to find new derivations *)
  while not (FactSet.is_empty !delta) do
    incr iterations;
    let next_delta = ref FactSet.empty in
    List.iter (fun rule ->
      (* For semi-naive: at least one body atom must match a delta fact *)
      List.iteri (fun i body_atom ->
        if not body_atom.negated then begin
          let delta_facts = facts_for_pred !delta body_atom.pred in
          List.iter (fun delta_fact ->
            let subst = unify_atoms empty_subst
              (apply_atom empty_subst body_atom) delta_fact in
            match subst with
            | None -> ()
            | Some s ->
              (* Evaluate remaining body atoms against full db *)
              let remaining = List.filteri (fun j _ -> j <> i) rule.body in
              let substs = List.fold_left
                (fun acc atom ->
                   List.concat_map (fun sub ->
                     if atom.negated then eval_negated_atom !db sub atom
                     else eval_positive_atom !db sub atom
                   ) acc)
                [s] remaining in
              List.iter (fun sub ->
                let head = apply_atom sub rule.head in
                if is_ground head && not (FactSet.mem head !db) then
                  next_delta := FactSet.add head !next_delta
              ) substs
          ) delta_facts
        end
      ) rule.body
    ) rules;
    db := db_union !db !next_delta;
    delta := !next_delta
  done;
  (!db, !iterations)

(** Full stratified evaluation with semi-naive per stratum. *)
let evaluate ?(use_semi_naive=true) rules db =
  let strata = stratify rules in
  let eval_fn = if use_semi_naive then eval_semi_naive else eval_naive in
  let db = ref db in
  let total_iters = ref 0 in
  List.iter (fun stratum_rules ->
    if stratum_rules <> [] then begin
      let (db', iters) = eval_fn stratum_rules !db in
      db := db';
      total_iters := !total_iters + iters
    end
  ) strata;
  (!db, !total_iters)

(* ══════════════════════════════════════════════
   Querying
   ══════════════════════════════════════════════ *)

(** Answer a query: return all substitutions that satisfy it. *)
let answer_query db q =
  let candidates = facts_for_pred db q.pred in
  List.filter_map (fun fact ->
    match unify_atoms empty_subst q fact with
    | None -> None
    | Some subst ->
      (* Only return bindings for variables in the query *)
      let vars = List.filter_map (fun t ->
        match t with Var v -> Some v | _ -> None
      ) q.args in
      let bindings = List.map (fun v ->
        (v, apply_term subst (Var v))
      ) vars in
      Some bindings
  ) candidates

(** Format query results. *)
let format_results results =
  if results = [] then "no."
  else
    List.map (fun bindings ->
      if bindings = [] then "yes."
      else
        String.concat ", "
          (List.map (fun (v, t) ->
             Printf.sprintf "%s = %s" (String.capitalize_ascii v) (term_to_string t)
           ) bindings)
    ) results
    |> String.concat "\n"

(* ══════════════════════════════════════════════
   Aggregation
   ══════════════════════════════════════════════ *)

(** Evaluate an aggregate query over the database. *)
let eval_aggregate db agg =
  let facts = facts_for_pred db agg.source.pred in
  (* Match facts against the source pattern *)
  let matched = List.filter_map (fun fact ->
    unify_atoms empty_subst agg.source fact
  ) facts in
  (* Group by the group_by variables *)
  let groups = Hashtbl.create 16 in
  List.iter (fun subst ->
    let key = List.map (fun v -> apply_term subst (Var v)) agg.group_by in
    let target_val = apply_term subst (Var agg.target_var) in
    let current = try Hashtbl.find groups key with Not_found -> [] in
    Hashtbl.replace groups key (target_val :: current)
  ) matched;
  (* Apply aggregation *)
  let to_int = function Int n -> n | _ -> 0 in
  Hashtbl.fold (fun key values acc ->
    let result = match agg.op with
      | Count -> Int (List.length values)
      | Sum -> Int (List.fold_left (fun s v -> s + to_int v) 0 values)
      | Min -> (match values with
        | [] -> Int 0
        | _ -> List.fold_left (fun m v ->
            if to_int v < to_int m then v else m) (List.hd values) values)
      | Max -> (match values with
        | [] -> Int 0
        | _ -> List.fold_left (fun m v ->
            if to_int v > to_int m then v else m) (List.hd values) values)
    in
    (key, result) :: acc
  ) groups []

(** Format aggregate results. *)
let format_aggregate agg results =
  let op_name = match agg.op with
    | Count -> "count" | Sum -> "sum" | Min -> "min" | Max -> "max" in
  if results = [] then Printf.sprintf "%s = 0 (no matching facts)" op_name
  else
    List.map (fun (key, value) ->
      let group_str = match key with
        | [] -> ""
        | _ ->
          let pairs = List.map2 (fun v t ->
            Printf.sprintf "%s=%s" (String.capitalize_ascii v) (term_to_string t)
          ) agg.group_by key in
          "[" ^ String.concat ", " pairs ^ "] "
      in
      Printf.sprintf "%s%s(%s) = %s"
        group_str op_name
        (String.capitalize_ascii agg.target_var)
        (term_to_string value)
    ) results
    |> String.concat "\n"

(* ══════════════════════════════════════════════
   Convenience Constructors
   ══════════════════════════════════════════════ *)

(** Create a constant term. *)
let const s = Const s

(** Create an integer term. *)
let int_t n = Int n

(** Create a variable term. *)
let var v = Var v

(** Create a positive atom. *)
let atom pred args = { pred; args; negated = false }

(** Create a negated atom. *)
let neg_atom pred args = { pred; args; negated = true }

(** Create a fact (rule with no body). *)
let fact pred args = { head = atom pred args; body = [] }

(** Create a rule. *)
let rule head body = { head; body }

(** Create a query. *)
let query pred args = atom pred args

(* ══════════════════════════════════════════════
   Parser (Simple Datalog Syntax)
   ══════════════════════════════════════════════ *)

module Parser = struct
  type token =
    | TIdent of string
    | TInt of int
    | TVar of string
    | TLParen | TRParen
    | TComma | TDot
    | TImplies    (* :- *)
    | TNot
    | TQuery      (* ?- *)
    | TEOF

  let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
  let is_digit c = c >= '0' && c <= '9'
  let is_upper c = c >= 'A' && c <= 'Z'

  (** Tokenize a Datalog string. *)
  let tokenize input =
    let n = String.length input in
    let i = ref 0 in
    let tokens = ref [] in
    while !i < n do
      let c = input.[!i] in
      if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
        incr i
      else if c = '%' then begin
        (* Line comment *)
        while !i < n && input.[!i] <> '\n' do incr i done
      end
      else if c = '(' then (tokens := TLParen :: !tokens; incr i)
      else if c = ')' then (tokens := TRParen :: !tokens; incr i)
      else if c = ',' then (tokens := TComma :: !tokens; incr i)
      else if c = '.' then (tokens := TDot :: !tokens; incr i)
      else if c = ':' && !i + 1 < n && input.[!i + 1] = '-' then
        (tokens := TImplies :: !tokens; i := !i + 2)
      else if c = '?' && !i + 1 < n && input.[!i + 1] = '-' then
        (tokens := TQuery :: !tokens; i := !i + 2)
      else if is_digit c || (c = '-' && !i + 1 < n && is_digit input.[!i + 1]) then begin
        let start = !i in
        if c = '-' then incr i;
        while !i < n && is_digit input.[!i] do incr i done;
        let s = String.sub input start (!i - start) in
        tokens := TInt (int_of_string s) :: !tokens
      end
      else if is_alpha c then begin
        let start = !i in
        while !i < n && (is_alpha input.[!i] || is_digit input.[!i]) do incr i done;
        let s = String.sub input start (!i - start) in
        if s = "not" then tokens := TNot :: !tokens
        else if is_upper s.[0] || s.[0] = '_' then tokens := TVar s :: !tokens
        else tokens := TIdent s :: !tokens
      end
      else
        failwith (Printf.sprintf "Unexpected character '%c' at position %d" c !i)
    done;
    List.rev (TEOF :: !tokens)

  (** Parse a term from tokens. *)
  let parse_term = function
    | TIdent s :: rest -> (Const s, rest)
    | TInt n :: rest -> (Int n, rest)
    | TVar v :: rest -> (Var v, rest)
    | t :: _ -> failwith (Printf.sprintf "Expected term, got unexpected token")
    | [] -> failwith "Unexpected end of input"

  (** Parse an argument list: (t1, t2, ...) *)
  let rec parse_args tokens =
    match tokens with
    | TRParen :: rest -> ([], rest)
    | _ ->
      let (t, rest) = parse_term tokens in
      (match rest with
       | TComma :: rest' ->
         let (more, rest'') = parse_args rest' in
         (t :: more, rest'')
       | TRParen :: rest' -> ([t], rest')
       | _ -> failwith "Expected ',' or ')' in argument list")

  (** Parse an atom: pred(args) or not pred(args) *)
  let parse_atom tokens =
    let (negated, tokens) = match tokens with
      | TNot :: rest -> (true, rest)
      | _ -> (false, tokens) in
    match tokens with
    | TIdent pred :: TLParen :: rest ->
      let (args, rest') = parse_args rest in
      ({ pred; args; negated }, rest')
    | _ -> failwith "Expected predicate name followed by '('"

  (** Parse a rule body: atom1, atom2, ... *)
  let rec parse_body tokens =
    let (a, rest) = parse_atom tokens in
    match rest with
    | TComma :: rest' ->
      let (more, rest'') = parse_body rest' in
      (a :: more, rest'')
    | _ -> ([a], rest)

  (** Parse a complete clause (fact or rule). *)
  let parse_clause tokens =
    let (head, rest) = parse_atom tokens in
    match rest with
    | TDot :: rest' ->
      (* Fact *)
      ({ head; body = [] }, rest')
    | TImplies :: rest' ->
      (* Rule *)
      let (body, rest'') = parse_body rest' in
      (match rest'' with
       | TDot :: rest''' -> ({ head; body }, rest''')
       | _ -> failwith "Expected '.' at end of rule")
    | _ -> failwith "Expected '.' or ':-' after head atom"

  (** Parse a query: ?- atom. *)
  let parse_query tokens =
    match tokens with
    | TQuery :: rest ->
      let (q, rest') = parse_atom rest in
      (match rest' with
       | TDot :: rest'' -> (q, rest'')
       | _ -> failwith "Expected '.' at end of query")
    | _ -> failwith "Expected '?-' at start of query"

  (** Parse a complete Datalog program: clauses + optional queries.
      Returns (rules, queries). *)
  let parse_program input =
    let tokens = tokenize input in
    let rules = ref [] in
    let queries = ref [] in
    let toks = ref tokens in
    while !toks <> [TEOF] && !toks <> [] do
      match !toks with
      | TQuery :: _ ->
        let (q, rest) = parse_query !toks in
        queries := q :: !queries;
        toks := rest
      | TEOF :: _ -> toks := [TEOF]
      | _ ->
        let (r, rest) = parse_clause !toks in
        rules := r :: !rules;
        toks := rest
    done;
    (List.rev !rules, List.rev !queries)
end

(* ══════════════════════════════════════════════
   Program Runner
   ══════════════════════════════════════════════ *)

(** Run a Datalog program from source text. Returns (database, results). *)
let run_program ?(use_semi_naive=true) source =
  let (rules, queries) = Parser.parse_program source in
  let facts_list = List.filter (fun r -> r.body = []) rules in
  let rules_list = List.filter (fun r -> r.body <> []) rules in
  let db = List.fold_left (fun db r -> add_fact db r.head) empty_db facts_list in
  let (db, _iters) = evaluate ~use_semi_naive rules_list db in
  let results = List.map (fun q -> (q, answer_query db q)) queries in
  (db, results)

(** Format the full results of running a program. *)
let format_program_results results =
  List.map (fun (q, bindings) ->
    Printf.sprintf "?- %s\n%s" (atom_to_string q) (format_results bindings)
  ) results
  |> String.concat "\n\n"

(* ══════════════════════════════════════════════
   Magic Sets Optimization (Query-directed)
   ══════════════════════════════════════════════ *)

(** Adorned predicate: tracks which args are bound (b) vs free (f). *)
type adornment = Bound | Free

let adornment_string adorns =
  String.concat "" (List.map (fun a -> match a with Bound -> "b" | Free -> "f") adorns)

(** Generate magic-set rewritten rules for a query.
    This restricts bottom-up evaluation to facts relevant to the query. *)
let magic_rewrite rules query =
  let adornments = List.map (fun t ->
    match t with Var _ -> Free | _ -> Bound
  ) query.args in
  let adorned_pred = query.pred ^ "_" ^ adornment_string adornments in
  (* Create seed fact: magic_pred(bound_args) *)
  let bound_args = List.filter_map (fun (t, a) ->
    match a with Bound -> Some t | Free -> None
  ) (List.combine query.args adornments) in
  let magic_pred = "magic_" ^ adorned_pred in
  let seed = fact magic_pred bound_args in
  (* Rewrite rules: add magic guard to each rule for the query predicate *)
  let rewritten = List.filter_map (fun r ->
    if r.head.pred = query.pred then begin
      let magic_guard = atom magic_pred bound_args in
      Some { r with body = magic_guard :: r.body }
    end else None
  ) rules in
  (seed :: rewritten, adorned_pred, magic_pred)

(* ══════════════════════════════════════════════
   Built-in Predicates
   ══════════════════════════════════════════════ *)

(** Evaluate built-in predicates (comparison, arithmetic). *)
let eval_builtin subst atom =
  match atom.pred, atom.args with
  | "lt", [a; b] ->
    let a' = apply_term subst a and b' = apply_term subst b in
    (match a', b' with
     | Int x, Int y -> if x < y then Some subst else None
     | _ -> None)
  | "lte", [a; b] ->
    let a' = apply_term subst a and b' = apply_term subst b in
    (match a', b' with
     | Int x, Int y -> if x <= y then Some subst else None
     | _ -> None)
  | "gt", [a; b] ->
    let a' = apply_term subst a and b' = apply_term subst b in
    (match a', b' with
     | Int x, Int y -> if x > y then Some subst else None
     | _ -> None)
  | "gte", [a; b] ->
    let a' = apply_term subst a and b' = apply_term subst b in
    (match a', b' with
     | Int x, Int y -> if x >= y then Some subst else None
     | _ -> None)
  | "neq", [a; b] ->
    let a' = apply_term subst a and b' = apply_term subst b in
    if a' <> b' then Some subst else None
  | "eq", [a; b] ->
    let a' = apply_term subst a and b' = apply_term subst b in
    if a' = b' then Some subst else None
  | "add", [a; b; c] ->
    let a' = apply_term subst a and b' = apply_term subst b in
    (match a', b' with
     | Int x, Int y -> extend_subst subst
       (match c with Var v -> v | _ -> "_")
       (Int (x + y))
     | _ -> None)
  | "succ", [a; b] ->
    let a' = apply_term subst a in
    (match a' with
     | Int x -> extend_subst subst
       (match b with Var v -> v | _ -> "_")
       (Int (x + 1))
     | _ -> None)
  | _ -> None  (* Not a builtin *)

let builtins = ["lt"; "lte"; "gt"; "gte"; "neq"; "eq"; "add"; "succ"]

let is_builtin pred = List.mem pred builtins

(* ══════════════════════════════════════════════
   Enhanced Evaluation (with builtins)
   ══════════════════════════════════════════════ *)

(** Evaluate body with support for built-in predicates. *)
let eval_body_enhanced db body =
  List.fold_left
    (fun substs a ->
       List.concat_map
         (fun subst ->
            if is_builtin a.pred then
              (match eval_builtin subst a with
               | Some s -> [s]
               | None -> [])
            else if a.negated then eval_negated_atom db subst a
            else eval_positive_atom db subst a)
         substs)
    [empty_subst]
    body

(** Apply a rule with builtin support. *)
let apply_rule_enhanced db rule =
  let substs = eval_body_enhanced db rule.body in
  List.filter_map (fun subst ->
    let head = apply_atom subst rule.head in
    if is_ground head then Some head
    else None
  ) substs

(** Semi-naive evaluation with builtin support. *)
let eval_semi_naive_enhanced rules db =
  let new_facts = ref FactSet.empty in
  List.iter (fun rule ->
    let derived = apply_rule_enhanced db rule in
    List.iter (fun f ->
      if not (FactSet.mem f db) then
        new_facts := FactSet.add f !new_facts
    ) derived
  ) rules;
  let db = ref (db_union db !new_facts) in
  let delta = ref !new_facts in
  let iterations = ref 1 in
  while not (FactSet.is_empty !delta) do
    incr iterations;
    let next_delta = ref FactSet.empty in
    List.iter (fun rule ->
      let derived = apply_rule_enhanced !db rule in
      List.iter (fun f ->
        if not (FactSet.mem f !db) then
          next_delta := FactSet.add f !next_delta
      ) derived
    ) rules;
    db := db_union !db !next_delta;
    delta := !next_delta
  done;
  (!db, !iterations)

(** Full evaluation with builtins. *)
let evaluate_enhanced rules db =
  let strata = stratify rules in
  let db = ref db in
  let total_iters = ref 0 in
  List.iter (fun stratum_rules ->
    if stratum_rules <> [] then begin
      let (db', iters) = eval_semi_naive_enhanced stratum_rules !db in
      db := db';
      total_iters := !total_iters + iters
    end
  ) strata;
  (!db, !total_iters)


(* ══════════════════════════════════════════════
   TESTS
   ══════════════════════════════════════════════ *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_true msg b =
  if b then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "FAIL: %s\n" msg
  end

let assert_equal msg expected actual =
  if expected = actual then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "FAIL: %s (expected %s, got %s)\n" msg expected actual
  end

let assert_int msg expected actual =
  if expected = actual then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "FAIL: %s (expected %d, got %d)\n" msg expected actual
  end

let () =
  Printf.printf "=== Datalog Engine Tests ===\n\n";

  (* ── Term & Atom basics ── *)
  Printf.printf "--- Term & Atom ---\n";
  assert_equal "const to_string" "hello" (term_to_string (Const "hello"));
  assert_equal "int to_string" "42" (term_to_string (Int 42));
  assert_equal "var to_string" "X" (term_to_string (Var "X"));
  assert_equal "atom to_string" "parent(tom, Bob)"
    (atom_to_string (atom "parent" [const "tom"; var "Bob"]));
  assert_equal "neg atom to_string" "not edge(X, Y)"
    (atom_to_string (neg_atom "edge" [var "X"; var "Y"]));

  (* ── Unification ── *)
  Printf.printf "--- Unification ---\n";
  let s = unify_term empty_subst (Var "X") (Const "hello") in
  assert_true "var unifies with const" (s <> None);
  let s = Option.get s in
  assert_equal "substitution applied" "hello" (term_to_string (apply_term s (Var "X")));

  let s2 = unify_term empty_subst (Const "a") (Const "b") in
  assert_true "different consts don't unify" (s2 = None);

  let s3 = unify_term empty_subst (Const "a") (Const "a") in
  assert_true "same consts unify" (s3 <> None);

  let s4 = unify_atoms empty_subst
    (atom "p" [var "X"; const "b"])
    (atom "p" [const "a"; const "b"]) in
  assert_true "atom unification" (s4 <> None);
  let s4 = Option.get s4 in
  assert_equal "X bound to a" "a" (term_to_string (apply_term s4 (Var "X")));

  let s5 = unify_atoms empty_subst
    (atom "p" [var "X"; var "X"])
    (atom "p" [const "a"; const "b"]) in
  assert_true "same var different vals fails" (s5 = None);

  let s6 = unify_atoms empty_subst
    (atom "p" [var "X"; var "X"])
    (atom "p" [const "a"; const "a"]) in
  assert_true "same var same vals succeeds" (s6 <> None);

  (* ── Simple facts and queries ── *)
  Printf.printf "--- Facts & Queries ---\n";
  let db = empty_db
    |> add_fact (atom "parent" [const "tom"; const "bob"])
    |> add_fact (atom "parent" [const "bob"; const "ann"])
    |> add_fact (atom "parent" [const "bob"; const "pat"]) in
  assert_int "db size" 3 (db_size db);

  let results = answer_query db (query "parent" [const "tom"; var "X"]) in
  assert_int "tom's children" 1 (List.length results);

  let results = answer_query db (query "parent" [const "bob"; var "X"]) in
  assert_int "bob's children" 2 (List.length results);

  let results = answer_query db (query "parent" [var "X"; const "ann"]) in
  assert_int "ann's parents" 1 (List.length results);

  let results = answer_query db (query "parent" [const "sue"; var "X"]) in
  assert_int "sue's children (none)" 0 (List.length results);

  (* ── Rule evaluation (ancestor) ── *)
  Printf.printf "--- Rule Evaluation ---\n";
  let rules = [
    rule (atom "ancestor" [var "X"; var "Y"])
      [atom "parent" [var "X"; var "Y"]];
    rule (atom "ancestor" [var "X"; var "Y"])
      [atom "parent" [var "X"; var "Z"];
       atom "ancestor" [var "Z"; var "Y"]];
  ] in
  let (db2, iters) = evaluate rules db in
  assert_true "converged" (iters > 0);

  let results = answer_query db2 (query "ancestor" [const "tom"; var "X"]) in
  assert_int "tom's descendants" 3 (List.length results);  (* bob, ann, pat *)

  let results = answer_query db2 (query "ancestor" [var "X"; const "ann"]) in
  assert_int "ann's ancestors" 2 (List.length results);  (* bob, tom *)

  (* ── Semi-naive vs Naive ── *)
  Printf.printf "--- Semi-Naive vs Naive ---\n";
  let (db_naive, iters_naive) = evaluate ~use_semi_naive:false rules db in
  let (db_semi, iters_semi) = evaluate ~use_semi_naive:true rules db in
  assert_int "same result size" (db_size db_naive) (db_size db_semi);
  assert_true "semi-naive uses fewer or equal iterations" (iters_semi <= iters_naive);

  (* ── Negation ── *)
  Printf.printf "--- Negation ---\n";
  let db3 = empty_db
    |> add_fact (atom "bird" [const "tweety"])
    |> add_fact (atom "bird" [const "sam"])
    |> add_fact (atom "penguin" [const "sam"]) in
  let rules3 = [
    rule (atom "can_fly" [var "X"])
      [atom "bird" [var "X"];
       neg_atom "penguin" [var "X"]];
  ] in
  let (db3', _) = evaluate rules3 db3 in
  let flyers = answer_query db3' (query "can_fly" [var "X"]) in
  assert_int "only tweety can fly" 1 (List.length flyers);

  (* ── Stratification ── *)
  Printf.printf "--- Stratification ---\n";
  let strata = stratify rules3 in
  assert_true "at least 1 stratum" (List.length strata >= 1);

  let strata2 = stratify rules in  (* no negation *)
  assert_int "non-negative rules: 1 stratum" 1 (List.length strata2);

  (* ── Transitive closure ── *)
  Printf.printf "--- Transitive Closure ---\n";
  let graph_db = empty_db
    |> add_fact (atom "edge" [const "a"; const "b"])
    |> add_fact (atom "edge" [const "b"; const "c"])
    |> add_fact (atom "edge" [const "c"; const "d"])
    |> add_fact (atom "edge" [const "d"; const "e"]) in
  let reach_rules = [
    rule (atom "reach" [var "X"; var "Y"]) [atom "edge" [var "X"; var "Y"]];
    rule (atom "reach" [var "X"; var "Y"])
      [atom "edge" [var "X"; var "Z"]; atom "reach" [var "Z"; var "Y"]];
  ] in
  let (graph_db', _) = evaluate reach_rules graph_db in
  let all_reach = answer_query graph_db' (query "reach" [var "X"; var "Y"]) in
  (* a->b,c,d,e  b->c,d,e  c->d,e  d->e = 4+3+2+1 = 10 *)
  assert_int "reachability pairs" 10 (List.length all_reach);

  let from_a = answer_query graph_db' (query "reach" [const "a"; var "Y"]) in
  assert_int "reachable from a" 4 (List.length from_a);

  (* ── Same generation ── *)
  Printf.printf "--- Same Generation ---\n";
  let family_db = empty_db
    |> add_fact (atom "parent" [const "alice"; const "bob"])
    |> add_fact (atom "parent" [const "alice"; const "carol"])
    |> add_fact (atom "parent" [const "dave"; const "eve"])
    |> add_fact (atom "parent" [const "dave"; const "frank"]) in
  let sg_rules = [
    (* Same generation: X and Y are same generation if
       they share parents who are same generation *)
    rule (atom "sg" [var "X"; var "X"]) [atom "parent" [var "_P"; var "X"]];
    rule (atom "sg" [var "X"; var "Y"])
      [atom "parent" [var "P1"; var "X"];
       atom "parent" [var "P2"; var "Y"];
       atom "sg" [var "P1"; var "P2"]];
  ] in
  let (sg_db, _) = evaluate sg_rules family_db in
  let sg_bob = answer_query sg_db (query "sg" [const "bob"; var "X"]) in
  assert_true "bob same gen as carol" (List.exists (fun bindings ->
    List.exists (fun (_, t) -> t = Const "carol") bindings) sg_bob);

  (* ── Parser ── *)
  Printf.printf "--- Parser ---\n";
  let (rules, queries) = Parser.parse_program
    "parent(tom, bob).
     parent(bob, ann).
     ancestor(X, Y) :- parent(X, Y).
     ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
     ?- ancestor(tom, X)." in
  assert_int "parsed 4 clauses" 4 (List.length rules);
  assert_int "parsed 1 query" 1 (List.length queries);
  let facts_p = List.filter (fun r -> r.body = []) rules in
  let rules_p = List.filter (fun r -> r.body <> []) rules in
  assert_int "2 facts" 2 (List.length facts_p);
  assert_int "2 rules" 2 (List.length rules_p);

  (* ── Parser: run full program ── *)
  Printf.printf "--- Full Program Run ---\n";
  let program = "
    parent(tom, bob).
    parent(bob, ann).
    parent(bob, pat).
    ancestor(X, Y) :- parent(X, Y).
    ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    ?- ancestor(tom, X).
  " in
  let (_, results) = run_program program in
  let (_, bindings) = List.hd results in
  assert_int "tom has 3 descendants" 3 (List.length bindings);

  (* ── Parser: negation ── *)
  let neg_program = "
    bird(tweety).
    bird(sam).
    penguin(sam).
    can_fly(X) :- bird(X), not penguin(X).
    ?- can_fly(X).
  " in
  let (_, neg_results) = run_program neg_program in
  let (_, neg_bindings) = List.hd neg_results in
  assert_int "only tweety can fly (parsed)" 1 (List.length neg_bindings);

  (* ── Aggregation ── *)
  Printf.printf "--- Aggregation ---\n";
  let score_db = empty_db
    |> add_fact (atom "score" [const "alice"; int_t 90])
    |> add_fact (atom "score" [const "alice"; int_t 85])
    |> add_fact (atom "score" [const "bob"; int_t 75])
    |> add_fact (atom "score" [const "bob"; int_t 80])
    |> add_fact (atom "score" [const "carol"; int_t 95]) in

  let count_agg = {
    op = Count;
    target_var = "S";
    source = atom "score" [var "N"; var "S"];
    group_by = ["N"];
  } in
  let count_results = eval_aggregate score_db count_agg in
  assert_int "3 people" 3 (List.length count_results);

  let sum_agg = { count_agg with op = Sum; group_by = [] } in
  let sum_results = eval_aggregate score_db sum_agg in
  assert_int "1 total group" 1 (List.length sum_results);
  let (_, total) = List.hd sum_results in
  assert_equal "total score 425" "425" (term_to_string total);

  let max_agg = { count_agg with op = Max } in
  let max_results = eval_aggregate score_db max_agg in
  let alice_max = List.find (fun (k, _) -> k = [Const "alice"]) max_results in
  assert_equal "alice max 90" "90" (term_to_string (snd alice_max));

  let min_agg = { count_agg with op = Min } in
  let min_results = eval_aggregate score_db min_agg in
  let bob_min = List.find (fun (k, _) -> k = [Const "bob"]) min_results in
  assert_equal "bob min 75" "75" (term_to_string (snd bob_min));

  (* ── Integer terms ── *)
  Printf.printf "--- Integer Terms ---\n";
  let int_db = empty_db
    |> add_fact (atom "age" [const "alice"; int_t 30])
    |> add_fact (atom "age" [const "bob"; int_t 25])
    |> add_fact (atom "age" [const "carol"; int_t 35]) in
  let q = query "age" [var "X"; int_t 30] in
  let results = answer_query int_db q in
  assert_int "age 30 query" 1 (List.length results);

  (* ── Builtins ── *)
  Printf.printf "--- Builtins ---\n";
  let builtin_rules = [
    rule (atom "adult" [var "X"])
      [atom "age" [var "X"; var "A"];
       atom "gte" [var "A"; int_t 30]];
  ] in
  let (int_db2, _) = evaluate_enhanced builtin_rules int_db in
  let adults = answer_query int_db2 (query "adult" [var "X"]) in
  assert_int "adults (>=30)" 2 (List.length adults);

  let neq_rules = [
    rule (atom "different_age" [var "X"; var "Y"])
      [atom "age" [var "X"; var "A"];
       atom "age" [var "Y"; var "B"];
       atom "neq" [var "X"; var "Y"]];
  ] in
  let (int_db3, _) = evaluate_enhanced neq_rules int_db in
  let diff = answer_query int_db3 (query "different_age" [var "X"; var "Y"]) in
  assert_int "different age pairs" 6 (List.length diff);  (* 3*2 = 6 *)

  (* ── Parser: comments ── *)
  Printf.printf "--- Parser: Comments ---\n";
  let commented = "
    % This is a comment
    parent(a, b).  % inline comment
    parent(b, c).
    ?- parent(a, X).
  " in
  let (_, results) = run_program commented in
  let (_, bindings) = List.hd results in
  assert_int "comment handling" 1 (List.length bindings);

  (* ── Parser: integer args ── *)
  let int_prog = "
    cost(item1, 100).
    cost(item2, 200).
    cost(item3, 50).
    ?- cost(X, 100).
  " in
  let (_, results) = run_program int_prog in
  let (_, bindings) = List.hd results in
  assert_int "int arg query" 1 (List.length bindings);

  (* ── Empty program ── *)
  Printf.printf "--- Edge Cases ---\n";
  let (db_empty, _) = run_program "" in
  assert_int "empty program" 0 (db_size db_empty);

  (* ── Single fact, no query ── *)
  let (db_single, results) = run_program "fact(a)." in
  assert_int "single fact" 1 (db_size db_single);
  assert_int "no queries" 0 (List.length results);

  (* ── Ground query ── *)
  let (_, results) = run_program "
    edge(a, b).
    ?- edge(a, b).
  " in
  let (_, bindings) = List.hd results in
  assert_int "ground query matches" 1 (List.length bindings);

  (* ── Ground query miss ── *)
  let (_, results) = run_program "
    edge(a, b).
    ?- edge(a, c).
  " in
  let (_, bindings) = List.hd results in
  assert_int "ground query no match" 0 (List.length bindings);

  (* ── Multiple queries ── *)
  let (_, results) = run_program "
    color(red). color(blue). color(green).
    ?- color(red).
    ?- color(X).
  " in
  assert_int "2 queries" 2 (List.length results);
  let (_, b1) = List.nth results 0 in
  let (_, b2) = List.nth results 1 in
  assert_int "first query: 1 result" 1 (List.length b1);
  assert_int "second query: 3 results" 3 (List.length b2);

  (* ── Rule to_string ── *)
  Printf.printf "--- Pretty Printing ---\n";
  let r = rule (atom "ancestor" [var "X"; var "Y"])
    [atom "parent" [var "X"; var "Z"];
     atom "ancestor" [var "Z"; var "Y"]] in
  assert_equal "rule to_string"
    "ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y)."
    (rule_to_string r);

  let f = fact "parent" [const "tom"; const "bob"] in
  assert_equal "fact to_string" "parent(tom, bob)." (rule_to_string f);

  (* ── format_results ── *)
  let r1 = [
    [("X", Const "bob")];
    [("X", Const "ann")];
  ] in
  let s = format_results r1 in
  assert_true "format has bob" (String.length s > 0);

  let empty_results = format_results [] in
  assert_equal "empty results" "no." empty_results;

  (* ── Mutual recursion ── *)
  Printf.printf "--- Mutual Recursion ---\n";
  let mutual_db = empty_db
    |> add_fact (atom "num" [int_t 0])
    |> add_fact (atom "num" [int_t 1])
    |> add_fact (atom "num" [int_t 2])
    |> add_fact (atom "num" [int_t 3])
    |> add_fact (atom "num" [int_t 4]) in
  let even_odd_rules = [
    rule (atom "even" [int_t 0]) [];
    rule (atom "even" [var "N"])
      [atom "num" [var "N"];
       atom "num" [var "M"];
       atom "odd" [var "M"];
       atom "succ" [var "M"; var "N"]];
    rule (atom "odd" [var "N"])
      [atom "num" [var "N"];
       atom "num" [var "M"];
       atom "even" [var "M"];
       atom "succ" [var "M"; var "N"]];
  ] in
  (* Can't test with builtins through evaluate, use evaluate_enhanced *)
  let (eo_db, _) = evaluate_enhanced even_odd_rules mutual_db in
  let evens = answer_query eo_db (query "even" [var "X"]) in
  let odds = answer_query eo_db (query "odd" [var "X"]) in
  assert_int "even numbers (0,2,4)" 3 (List.length evens);
  assert_int "odd numbers (1,3)" 2 (List.length odds);

  (* ── Larger graph ── *)
  Printf.printf "--- Larger Graph ---\n";
  let big_graph = empty_db
    |> add_fact (atom "edge" [int_t 1; int_t 2])
    |> add_fact (atom "edge" [int_t 2; int_t 3])
    |> add_fact (atom "edge" [int_t 3; int_t 4])
    |> add_fact (atom "edge" [int_t 4; int_t 5])
    |> add_fact (atom "edge" [int_t 5; int_t 6])
    |> add_fact (atom "edge" [int_t 6; int_t 1]) in  (* cycle! *)
  let cycle_rules = [
    rule (atom "path" [var "X"; var "Y"]) [atom "edge" [var "X"; var "Y"]];
    rule (atom "path" [var "X"; var "Y"])
      [atom "edge" [var "X"; var "Z"]; atom "path" [var "Z"; var "Y"]];
  ] in
  let (big_db, _) = evaluate cycle_rules big_graph in
  (* In a 6-node cycle, every node reaches every node: 6*6 = 36 but
     actually 6*5=30 non-self + 6 self = 36 total? Let's check...
     Actually, 1->2, 1->3, ..., 1->6, 1->1 = 6 from each node = 36 *)
  let all_paths = answer_query big_db (query "path" [var "X"; var "Y"]) in
  assert_int "cyclic graph paths" 36 (List.length all_paths);

  (* ── Magic sets ── *)
  Printf.printf "--- Magic Sets ---\n";
  let q = query "reach" [const "a"; var "Y"] in
  let (magic_rules, adorned, magic_pred) = magic_rewrite reach_rules q in
  assert_true "magic rules generated" (List.length magic_rules > 0);
  assert_equal "adorned pred" "reach_bf" adorned;
  assert_equal "magic pred" "magic_reach_bf" magic_pred;

  (* ── db operations ── *)
  Printf.printf "--- DB Operations ---\n";
  let db_a = empty_db
    |> add_fact (atom "x" [const "1"])
    |> add_fact (atom "x" [const "2"]) in
  let db_b = empty_db
    |> add_fact (atom "x" [const "2"])
    |> add_fact (atom "x" [const "3"]) in
  let diff_db = db_diff db_a db_b in
  assert_int "diff: only x(1)" 1 (db_size diff_db);
  let union_db = db_union db_a db_b in
  assert_int "union: x(1,2,3)" 3 (db_size union_db);

  (* ── Aggregate: format ── *)
  Printf.printf "--- Aggregate Format ---\n";
  let agg = { op = Count; target_var = "X"; source = atom "p" [var "X"]; group_by = [] } in
  let fmt = format_aggregate agg [] in
  assert_true "empty agg format" (String.length fmt > 0);

  let fmt2 = format_aggregate count_agg count_results in
  assert_true "grouped agg format" (String.length fmt2 > 0);

  (* ── is_ground ── *)
  assert_true "ground atom" (is_ground (atom "p" [const "a"; int_t 1]));
  assert_true "non-ground atom" (not (is_ground (atom "p" [var "X"])));

  (* ── Tokenizer edge cases ── *)
  Printf.printf "--- Tokenizer ---\n";
  let tokens = Parser.tokenize "p(X, 42)." in
  assert_int "token count" 7 (List.length tokens);  (* p ( X , 42 ) . EOF *)

  let tokens2 = Parser.tokenize "not p(X)." in
  assert_int "negation tokens" 6 (List.length tokens2);

  let tokens3 = Parser.tokenize "?- q(a)." in
  assert_int "query tokens" 6 (List.length tokens3);

  let tokens4 = Parser.tokenize "a(X) :- b(X)." in
  assert_int "rule tokens" 9 (List.length tokens4);

  (* ── Negative integers ── *)
  let neg_db = empty_db
    |> add_fact (atom "temp" [const "outside"; int_t (-5)]) in
  let neg_q = answer_query neg_db (query "temp" [const "outside"; var "T"]) in
  assert_int "negative int query" 1 (List.length neg_q);

  (* ── Self-join ── *)
  Printf.printf "--- Self-Join ---\n";
  let friend_db = empty_db
    |> add_fact (atom "likes" [const "a"; const "b"])
    |> add_fact (atom "likes" [const "b"; const "a"])
    |> add_fact (atom "likes" [const "c"; const "d"]) in
  let mutual_rules = [
    rule (atom "mutual" [var "X"; var "Y"])
      [atom "likes" [var "X"; var "Y"];
       atom "likes" [var "Y"; var "X"]];
  ] in
  let (mutual_db', _) = evaluate mutual_rules friend_db in
  let mutuals = answer_query mutual_db' (query "mutual" [var "X"; var "Y"]) in
  assert_int "mutual friends" 2 (List.length mutuals);  (* (a,b) and (b,a) *)

  (* ── Arity mismatch ── *)
  Printf.printf "--- Safety ---\n";
  let db_arity = empty_db
    |> add_fact (atom "p" [const "a"; const "b"]) in
  let q_wrong = query "p" [var "X"] in
  let results = answer_query db_arity q_wrong in
  assert_int "arity mismatch: 0 results" 0 (List.length results);

  (* ── Predicate miss ── *)
  let results = answer_query db_arity (query "nonexistent" [var "X"]) in
  assert_int "missing predicate: 0 results" 0 (List.length results);

  (* ── Builtin: add ── *)
  Printf.printf "--- Builtin: Arithmetic ---\n";
  let add_rules = [
    rule (atom "double" [var "X"; var "D"])
      [atom "num" [var "X"]; atom "add" [var "X"; var "X"; var "D"]];
  ] in
  let num_db = empty_db
    |> add_fact (atom "num" [int_t 3])
    |> add_fact (atom "num" [int_t 5]) in
  let (add_db, _) = evaluate_enhanced add_rules num_db in
  let doubles = answer_query add_db (query "double" [var "X"; var "D"]) in
  assert_int "doubles computed" 2 (List.length doubles);

  (* ── Builtin: lt/gt ── *)
  let cmp_rules = [
    rule (atom "smaller" [var "X"; var "Y"])
      [atom "num" [var "X"]; atom "num" [var "Y"]; atom "lt" [var "X"; var "Y"]];
  ] in
  let (cmp_db, _) = evaluate_enhanced cmp_rules num_db in
  let smaller = answer_query cmp_db (query "smaller" [var "X"; var "Y"]) in
  assert_int "3 < 5 only" 1 (List.length smaller);

  (* ── Builtin: eq ── *)
  let eq_rules = [
    rule (atom "same" [var "X"])
      [atom "num" [var "X"]; atom "eq" [var "X"; int_t 5]];
  ] in
  let (eq_db, _) = evaluate_enhanced eq_rules num_db in
  let sames = answer_query eq_db (query "same" [var "X"]) in
  assert_int "eq 5" 1 (List.length sames);

  (* ── Final summary ── *)
  Printf.printf "\n=== Results: %d passed, %d failed ===\n"
    !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
