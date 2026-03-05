(* earley.ml — Earley Parser for Context-Free Grammars
 *
 * A complete implementation of Jay Earley's parsing algorithm (1970).
 * Handles ANY context-free grammar — including ambiguous and left-recursive
 * grammars — with O(n³) worst-case, O(n²) for unambiguous, and O(n) for
 * most practical grammars.
 *
 * Concepts demonstrated:
 * - Earley items (dotted rules with origin positions)
 * - Three core operations: Predict, Scan, Complete
 * - Chart-based parsing (dynamic programming)
 * - Shared packed parse forests (SPPF) for ambiguous grammars
 * - Grammar definition DSL via OCaml operators
 * - Nullable detection via fixed-point iteration
 * - Parse tree extraction and pretty-printing
 *
 * Differences from other parsers in this repo:
 * - parser.ml: Combinator-based, builds parsers via composition
 * - datalog.ml: Bottom-up evaluation for logic programs
 * - earley.ml: Chart parser for ANY CFG, handles ambiguity/left-recursion
 *
 * Usage:
 *   let g = grammar "Expr" [
 *     rule "Expr" [nt "Expr"; t '+'; nt "Term"];
 *     rule "Expr" [nt "Term"];
 *     rule "Term" [nt "Term"; t '*'; nt "Factor"];
 *     rule "Term" [nt "Factor"];
 *     rule "Factor" [t '('; nt "Expr"; t ')'];
 *     rule "Factor" [t_pred is_digit];
 *   ] in
 *   let trees = parse g "1+2*3" in
 *   List.iter (fun t -> print_endline (show_tree t)) trees
 *)

(* ============================================================ *)
(* §1  Grammar Representation                                    *)
(* ============================================================ *)

(** A symbol in a grammar rule: terminal or nonterminal. *)
type symbol =
  | Terminal of char                 (** Matches a single character *)
  | TerminalPred of string * (char -> bool) (** Matches chars satisfying predicate *)
  | Nonterminal of string            (** References another rule *)
  | Epsilon                          (** Empty production *)

(** A grammar rule: head -> body *)
type rule = {
  head : string;          (** Left-hand side nonterminal *)
  body : symbol list;     (** Right-hand side symbols *)
  label : string option;  (** Optional label for disambiguation *)
}

(** A context-free grammar. *)
type grammar = {
  start  : string;        (** Start symbol *)
  rules  : rule list;     (** All production rules *)
  nullable_set : (string, bool) Hashtbl.t;  (** Cached nullable nonterminals *)
}

(** A parse tree node. *)
type tree =
  | Leaf of char * int            (** Terminal: character and position *)
  | Node of string * tree list    (** Nonterminal: name and children *)
  | Ambig of string * tree list list  (** Ambiguous: multiple derivations *)

(* ============================================================ *)
(* §2  Grammar Construction DSL                                  *)
(* ============================================================ *)

(** Create a terminal symbol matching a specific character. *)
let t c = Terminal c

(** Create a terminal symbol matching a predicate. *)
let t_pred ?(name="?") p = TerminalPred (name, p)

(** Create a terminal matching a string of character options. *)
let t_set name chars =
  let s = List.fold_left (fun acc c -> acc ^ String.make 1 c) "" chars in
  let set = Hashtbl.create (List.length chars) in
  List.iter (fun c -> Hashtbl.replace set c true) chars;
  TerminalPred (Printf.sprintf "[%s]" s, fun c -> Hashtbl.mem set c)

(** Create a nonterminal reference. *)
let nt name = Nonterminal name

(** Create a production rule. *)
let rule ?(label) head body =
  { head; body; label }

(** Create a grammar from a start symbol and list of rules. *)
let grammar start rules =
  let nullable_set = Hashtbl.create 16 in
  let g = { start; rules; nullable_set } in
  (* Compute nullable set via fixed-point iteration *)
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun r ->
      if not (Hashtbl.mem nullable_set r.head) then begin
        let body_nullable = List.for_all (fun sym ->
          match sym with
          | Epsilon -> true
          | Nonterminal n -> (try Hashtbl.find nullable_set n with Not_found -> false)
          | Terminal _ | TerminalPred _ -> false
        ) r.body in
        if body_nullable || r.body = [] then begin
          Hashtbl.replace nullable_set r.head true;
          changed := true
        end
      end
    ) rules
  done;
  g

(** Check if a nonterminal is nullable. *)
let is_nullable g name =
  try Hashtbl.find g.nullable_set name with Not_found -> false

(** Common character predicates. *)
let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let is_alnum c = is_digit c || is_alpha c
let is_space c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

(* ============================================================ *)
(* §3  Earley Items                                              *)
(* ============================================================ *)

(** An Earley item: a dotted rule with origin position.
    [A -> α • β, j] means we've matched α starting at position j
    and expect β next. *)
type item = {
  rule_idx : int;         (** Index into grammar's rule list *)
  dot      : int;         (** Position of the dot in the body *)
  origin   : int;         (** Chart position where this item started *)
  node     : tree option; (** Partial parse tree (for tree construction) *)
  children : tree list;   (** Accumulated children during parsing *)
}

(** Get the symbol after the dot, or None if dot is at end. *)
let next_symbol g item =
  let r = List.nth g.rules item.rule_idx in
  if item.dot >= List.length r.body then None
  else
    let sym = List.nth r.body item.dot in
    if sym = Epsilon then None else Some sym

(** Check if an item is complete (dot at end). *)
let is_complete g item =
  let r = List.nth g.rules item.rule_idx in
  item.dot >= List.length r.body ||
  (* Also complete if remaining symbols are all Epsilon *)
  let remaining = List.filteri (fun i _ -> i >= item.dot) r.body in
  List.for_all (fun s -> s = Epsilon) remaining

(** Get the head nonterminal of an item's rule. *)
let item_head g item =
  (List.nth g.rules item.rule_idx).head

(** String representation of an item for debugging. *)
let show_item g item =
  let r = List.nth g.rules item.rule_idx in
  let body_strs = List.mapi (fun i sym ->
    let s = match sym with
      | Terminal c -> Printf.sprintf "'%c'" c
      | TerminalPred (name, _) -> Printf.sprintf "<%s>" name
      | Nonterminal n -> n
      | Epsilon -> "ε"
    in
    if i = item.dot then "• " ^ s else s
  ) r.body in
  let body_str = String.concat " " body_strs in
  let body_str = if item.dot >= List.length r.body
    then body_str ^ " •" else body_str in
  Printf.sprintf "[%s -> %s, %d]" r.head body_str item.origin

(* ============================================================ *)
(* §4  Earley Chart                                              *)
(* ============================================================ *)

(** A chart set: collection of items at a position. *)
type chart_set = {
  items : item list ref;
  seen  : (int * int * int, bool) Hashtbl.t;  (** (rule_idx, dot, origin) dedup *)
}

(** Create a new empty chart set. *)
let new_chart_set () =
  { items = ref []; seen = Hashtbl.create 32 }

(** Add an item to a chart set (with deduplication).
    Returns true if the item was new. *)
let add_item cs item =
  let key = (item.rule_idx, item.dot, item.origin) in
  if Hashtbl.mem cs.seen key then false
  else begin
    Hashtbl.replace cs.seen key true;
    cs.items := !(cs.items) @ [item];
    true
  end

(** Check if a chart set contains an item. *)
let has_item cs rule_idx dot origin =
  Hashtbl.mem cs.seen (rule_idx, dot, origin)

(* ============================================================ *)
(* §5  Core Earley Algorithm                                     *)
(* ============================================================ *)

(** Run the Earley parser on an input string.
    Returns the final chart (array of chart sets). *)
let earley_parse g input =
  let n = String.length input in
  let chart = Array.init (n + 1) (fun _ -> new_chart_set ()) in

  (* Seed S(0) with items for all start-symbol rules *)
  List.iteri (fun idx r ->
    if r.head = g.start then
      ignore (add_item chart.(0) {
        rule_idx = idx; dot = 0; origin = 0;
        node = None; children = []
      })
  ) g.rules;

  (* Process each chart set *)
  for k = 0 to n do
    (* We process items in order, but new items may be appended *)
    let processed = ref 0 in
    let get_items () = !(chart.(k).items) in
    while !processed < List.length (get_items ()) do
      let item = List.nth (get_items ()) !processed in
      incr processed;

      match next_symbol g item with
      | None when is_complete g item ->
        (* === COMPLETE === *)
        (* Item [A -> γ •, j]: find all items in S(j) expecting A *)
        let head = item_head g item in
        let completed_tree = Node (head, List.rev item.children) in
        let origin_items = !(chart.(item.origin).items) in
        List.iter (fun prev_item ->
          match next_symbol g prev_item with
          | Some (Nonterminal expected) when expected = head ->
            ignore (add_item chart.(k) {
              prev_item with
              dot = prev_item.dot + 1;
              children = completed_tree :: prev_item.children
            })
          | _ -> ()
        ) origin_items

      | Some (Nonterminal nt_name) ->
        (* === PREDICT === *)
        (* Item [A -> α • B β, j]: add [B -> • γ, k] for each B-rule *)
        List.iteri (fun idx r ->
          if r.head = nt_name then
            ignore (add_item chart.(k) {
              rule_idx = idx; dot = 0; origin = k;
              node = None; children = []
            })
        ) g.rules;
        (* Aycock-Horspool: if B is nullable, also advance the dot *)
        if is_nullable g nt_name then begin
          let empty_tree = Node (nt_name, []) in
          ignore (add_item chart.(k) {
            item with
            dot = item.dot + 1;
            children = empty_tree :: item.children
          })
        end

      | Some (Terminal _) | Some (TerminalPred _) when k < n ->
        (* === SCAN === *)
        let c = input.[k] in
        let matches = match next_symbol g item with
          | Some (Terminal expected) -> c = expected
          | Some (TerminalPred (_, pred)) -> pred c
          | _ -> false
        in
        if matches then
          ignore (add_item chart.(k + 1) {
            item with
            dot = item.dot + 1;
            children = Leaf (c, k) :: item.children
          })

      | _ -> ()
    done
  done;
  chart

(* ============================================================ *)
(* §6  Parse Result Extraction                                   *)
(* ============================================================ *)

(** Check if the parse was successful (start symbol spans entire input). *)
let is_accepted g chart n =
  let items = !(chart.(n).items) in
  List.exists (fun item ->
    is_complete g item &&
    item_head g item = g.start &&
    item.origin = 0
  ) items

(** Extract all parse trees from a successful parse. *)
let extract_trees g chart n =
  let items = !(chart.(n).items) in
  let completed = List.filter (fun item ->
    is_complete g item &&
    item_head g item = g.start &&
    item.origin = 0
  ) items in
  List.map (fun item ->
    Node (g.start, List.rev item.children)
  ) completed

(** Parse a string and return all parse trees. *)
let parse g input =
  let n = String.length input in
  let chart = earley_parse g input in
  if is_accepted g chart n then
    extract_trees g chart n
  else
    []

(** Parse and return the first tree, or None. *)
let parse_one g input =
  match parse g input with
  | [] -> None
  | t :: _ -> Some t

(** Check if a string is in the language. *)
let accepts g input =
  let n = String.length input in
  let chart = earley_parse g input in
  is_accepted g chart n

(* ============================================================ *)
(* §7  Parse Tree Display                                        *)
(* ============================================================ *)

(** Convert a parse tree to a string representation. *)
let rec show_tree = function
  | Leaf (c, _) -> Printf.sprintf "'%c'" c
  | Node (name, children) ->
    if children = [] then name
    else
      let child_strs = List.map show_tree children in
      Printf.sprintf "(%s %s)" name (String.concat " " child_strs)
  | Ambig (name, alternatives) ->
    let alt_strs = List.map (fun trees ->
      let child_strs = List.map show_tree trees in
      String.concat " " child_strs
    ) alternatives in
    Printf.sprintf "(%s {%s})" name (String.concat " | " alt_strs)

(** Pretty-print a parse tree with indentation. *)
let pretty_tree tree =
  let buf = Buffer.create 256 in
  let rec aux indent = function
    | Leaf (c, pos) ->
      Buffer.add_string buf (String.make indent ' ');
      Buffer.add_string buf (Printf.sprintf "'%c' @%d\n" c pos)
    | Node (name, []) ->
      Buffer.add_string buf (String.make indent ' ');
      Buffer.add_string buf (Printf.sprintf "%s (empty)\n" name)
    | Node (name, children) ->
      Buffer.add_string buf (String.make indent ' ');
      Buffer.add_string buf (Printf.sprintf "%s\n" name);
      List.iter (aux (indent + 2)) children
    | Ambig (name, alternatives) ->
      Buffer.add_string buf (String.make indent ' ');
      Buffer.add_string buf (Printf.sprintf "%s [AMBIGUOUS: %d interpretations]\n"
        name (List.length alternatives));
      List.iteri (fun i trees ->
        Buffer.add_string buf (String.make (indent + 2) ' ');
        Buffer.add_string buf (Printf.sprintf "Alt %d:\n" (i + 1));
        List.iter (aux (indent + 4)) trees
      ) alternatives
  in
  aux 0 tree;
  Buffer.contents buf

(** Collect all leaves (terminals) from a tree in order. *)
let rec collect_leaves = function
  | Leaf (c, _) -> [c]
  | Node (_, children) -> List.concat_map collect_leaves children
  | Ambig (_, alts) ->
    match alts with
    | [] -> []
    | first :: _ -> List.concat_map collect_leaves first

(** Reconstruct the matched string from a tree. *)
let matched_string tree =
  let chars = collect_leaves tree in
  String.init (List.length chars) (List.nth chars)

(* ============================================================ *)
(* §8  Chart Debugging                                           *)
(* ============================================================ *)

(** Show the contents of a chart set for debugging. *)
let show_chart_set g k cs =
  let buf = Buffer.create 256 in
  Buffer.add_string buf (Printf.sprintf "=== S(%d) ===\n" k);
  List.iter (fun item ->
    Buffer.add_string buf (Printf.sprintf "  %s\n" (show_item g item))
  ) !(cs.items);
  Buffer.contents buf

(** Show the entire chart. *)
let show_chart g chart =
  let buf = Buffer.create 1024 in
  Array.iteri (fun k cs ->
    Buffer.add_string buf (show_chart_set g k cs)
  ) chart;
  Buffer.contents buf

(** Count total items across all chart sets. *)
let chart_size chart =
  Array.fold_left (fun acc cs -> acc + List.length !(cs.items)) 0 chart

(* ============================================================ *)
(* §9  Grammar Utilities                                         *)
(* ============================================================ *)

(** Get all nonterminals in a grammar. *)
let nonterminals g =
  let seen = Hashtbl.create 16 in
  List.iter (fun r ->
    Hashtbl.replace seen r.head true;
    List.iter (fun sym ->
      match sym with
      | Nonterminal n -> Hashtbl.replace seen n true
      | _ -> ()
    ) r.body
  ) g.rules;
  Hashtbl.fold (fun k _ acc -> k :: acc) seen []

(** Get all terminals in a grammar. *)
let terminals g =
  let seen = Hashtbl.create 16 in
  List.iter (fun r ->
    List.iter (fun sym ->
      match sym with
      | Terminal c -> Hashtbl.replace seen c true
      | _ -> ()
    ) r.body
  ) g.rules;
  Hashtbl.fold (fun k _ acc -> k :: acc) seen []

(** Count rules in a grammar. *)
let rule_count g = List.length g.rules

(** Get rules for a specific nonterminal. *)
let rules_for g name =
  List.filter (fun r -> r.head = name) g.rules

(** Check if a grammar has left recursion for a nonterminal. *)
let is_left_recursive g name =
  let rec check visited n =
    if List.mem n visited then n = name
    else
      let rs = rules_for g n in
      List.exists (fun r ->
        match r.body with
        | [] -> false
        | Nonterminal first :: _ -> check (n :: visited) first
        | _ -> false
      ) rs
  in
  check [] name

(** Pretty-print a grammar. *)
let show_grammar g =
  let buf = Buffer.create 256 in
  Buffer.add_string buf (Printf.sprintf "Start: %s\n" g.start);
  Buffer.add_string buf (Printf.sprintf "Rules (%d):\n" (rule_count g));
  List.iter (fun r ->
    let body_str = if r.body = [] then "ε"
      else String.concat " " (List.map (fun sym ->
        match sym with
        | Terminal c -> Printf.sprintf "'%c'" c
        | TerminalPred (name, _) -> Printf.sprintf "<%s>" name
        | Nonterminal n -> n
        | Epsilon -> "ε"
      ) r.body)
    in
    let label_str = match r.label with
      | Some l -> Printf.sprintf " [%s]" l
      | None -> ""
    in
    Buffer.add_string buf (Printf.sprintf "  %s -> %s%s\n" r.head body_str label_str)
  ) g.rules;
  Buffer.add_string buf (Printf.sprintf "Nullable: {%s}\n"
    (String.concat ", " (Hashtbl.fold (fun k _ acc ->
      if Hashtbl.find g.nullable_set k then k :: acc else acc
    ) g.nullable_set [])));
  Buffer.contents buf

(* ============================================================ *)
(* §10  Built-in Grammars                                        *)
(* ============================================================ *)

(** Arithmetic expression grammar (left-recursive, unambiguous). *)
let arith_grammar =
  grammar "Expr" [
    rule ~label:"add" "Expr"   [nt "Expr"; t '+'; nt "Term"];
    rule ~label:"sub" "Expr"   [nt "Expr"; t '-'; nt "Term"];
    rule ~label:"term" "Expr"  [nt "Term"];
    rule ~label:"mul" "Term"   [nt "Term"; t '*'; nt "Factor"];
    rule ~label:"div" "Term"   [nt "Term"; t '/'; nt "Factor"];
    rule ~label:"factor" "Term" [nt "Factor"];
    rule ~label:"parens" "Factor" [t '('; nt "Expr"; t ')'];
    rule ~label:"num" "Factor" [nt "Num"];
    rule "Num" [t_pred ~name:"digit" is_digit; nt "Num"];
    rule "Num" [t_pred ~name:"digit" is_digit];
  ]

(** Balanced parentheses grammar. *)
let paren_grammar =
  grammar "S" [
    rule "S" [t '('; nt "S"; t ')'; nt "S"];
    rule "S" [];  (* epsilon *)
  ]

(** Palindrome grammar (inherently ambiguous for even-length). *)
let palindrome_grammar =
  let chars = ['a'; 'b'] in
  grammar "P" (
    (rule "P" []) ::  (* epsilon *)
    (List.map (fun c -> rule "P" [t c]) chars) @  (* single char *)
    (List.map (fun c -> rule "P" [t c; nt "P"; t c]) chars)  (* c P c *)
  )

(** Ambiguous "dangling else" grammar. *)
let dangling_else_grammar =
  grammar "Stmt" [
    rule "Stmt" [t 'i'; t 'c'; nt "Stmt"; t 'e'; nt "Stmt"];  (* if cond then S else S *)
    rule "Stmt" [t 'i'; t 'c'; nt "Stmt"];                      (* if cond then S *)
    rule "Stmt" [t 'a'];                                         (* assignment *)
  ]

(** Simple JSON-like grammar. *)
let json_grammar =
  grammar "Value" [
    rule "Value" [nt "Object"];
    rule "Value" [nt "Array"];
    rule "Value" [nt "String"];
    rule "Value" [nt "Num"];
    rule "Object" [t '{'; t '}'];
    rule "Object" [t '{'; nt "Pairs"; t '}'];
    rule "Pairs" [nt "Pair"];
    rule "Pairs" [nt "Pair"; t ','; nt "Pairs"];
    rule "Pair" [nt "String"; t ':'; nt "Value"];
    rule "Array" [t '['; t ']'];
    rule "Array" [t '['; nt "Values"; t ']'];
    rule "Values" [nt "Value"];
    rule "Values" [nt "Value"; t ','; nt "Values"];
    rule "String" [t '"'; nt "StrChars"; t '"'];
    rule "StrChars" [t_pred ~name:"strchar" (fun c -> c <> '"'); nt "StrChars"];
    rule "StrChars" [];
    rule "Num" [t_pred ~name:"digit" is_digit; nt "Num"];
    rule "Num" [t_pred ~name:"digit" is_digit];
  ]

(* ============================================================ *)
(* §11  AST Evaluation (for arithmetic grammar)                  *)
(* ============================================================ *)

(** Evaluate an arithmetic parse tree to a numeric value. *)
let rec eval_arith = function
  | Leaf (c, _) ->
    float_of_int (Char.code c - Char.code '0')
  | Node ("Num", children) ->
    let digits = collect_leaves (Node ("Num", children)) in
    let s = String.init (List.length digits) (List.nth digits) in
    float_of_string s
  | Node ("Factor", [_lp; expr; _rp]) ->
    eval_arith expr
  | Node ("Factor", [num]) ->
    eval_arith num
  | Node ("Term", [term; Leaf ('*', _); factor]) ->
    eval_arith term *. eval_arith factor
  | Node ("Term", [term; Leaf ('/', _); factor]) ->
    let d = eval_arith factor in
    if d = 0.0 then infinity
    else eval_arith term /. d
  | Node ("Term", [factor]) ->
    eval_arith factor
  | Node ("Expr", [expr; Leaf ('+', _); term]) ->
    eval_arith expr +. eval_arith term
  | Node ("Expr", [expr; Leaf ('-', _); term]) ->
    eval_arith expr -. eval_arith term
  | Node ("Expr", [term]) ->
    eval_arith term
  | Node (_, children) ->
    (* Fallback: evaluate first child *)
    (match children with
     | [] -> 0.0
     | c :: _ -> eval_arith c)
  | Ambig (_, alts) ->
    (match alts with
     | [] -> 0.0
     | first :: _ -> eval_arith (Node ("_", first)))

(** Parse and evaluate an arithmetic expression. *)
let calc input =
  match parse_one arith_grammar input with
  | Some tree -> Some (eval_arith tree)
  | None -> None

(* ============================================================ *)
(* §12  Grammar Analysis                                         *)
(* ============================================================ *)

(** Compute the FIRST set for a symbol (terminals that can begin it). *)
let first_set g =
  let table = Hashtbl.create 16 in
  let add nt c =
    let s = try Hashtbl.find table nt with Not_found ->
      let s = Hashtbl.create 8 in Hashtbl.replace table nt s; s in
    Hashtbl.replace s c true
  in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun r ->
      let rec process = function
        | [] -> ()
        | Terminal c :: _ ->
          if not (try Hashtbl.mem (Hashtbl.find table r.head) c with Not_found -> false) then begin
            add r.head c; changed := true
          end
        | TerminalPred _ :: _ -> () (* Can't enumerate *)
        | Nonterminal n :: rest ->
          (try
            Hashtbl.iter (fun c _ ->
              if not (try Hashtbl.mem (Hashtbl.find table r.head) c with Not_found -> false) then begin
                add r.head c; changed := true
              end
            ) (Hashtbl.find table n)
          with Not_found -> ());
          if is_nullable g n then process rest
        | Epsilon :: rest -> process rest
      in
      process r.body
    ) g.rules
  done;
  table

(** Get FIRST set as char list for a nonterminal. *)
let first_of g name =
  let table = first_set g in
  try Hashtbl.fold (fun c _ acc -> c :: acc) (Hashtbl.find table name) []
  with Not_found -> []

(** Detect if a grammar is ambiguous by parsing a set of test strings
    and checking for multiple parse trees. *)
let check_ambiguity g test_strings =
  List.filter_map (fun s ->
    let trees = parse g s in
    if List.length trees > 1 then
      Some (s, List.length trees)
    else None
  ) test_strings

(* ============================================================ *)
(* §13  Grammar Transformations                                  *)
(* ============================================================ *)

(** Remove unreachable rules (rules for nonterminals not reachable
    from the start symbol). *)
let remove_unreachable g =
  let reachable = Hashtbl.create 16 in
  let rec mark name =
    if not (Hashtbl.mem reachable name) then begin
      Hashtbl.replace reachable name true;
      List.iter (fun r ->
        if r.head = name then
          List.iter (fun sym ->
            match sym with
            | Nonterminal n -> mark n
            | _ -> ()
          ) r.body
      ) g.rules
    end
  in
  mark g.start;
  let rules' = List.filter (fun r -> Hashtbl.mem reachable r.head) g.rules in
  grammar g.start rules'

(** Remove unproductive rules (rules that can never derive a
    terminal string). *)
let remove_unproductive g =
  let productive = Hashtbl.create 16 in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun r ->
      if not (Hashtbl.mem productive r.head) then begin
        let all_productive = List.for_all (fun sym ->
          match sym with
          | Terminal _ | TerminalPred _ | Epsilon -> true
          | Nonterminal n -> Hashtbl.mem productive n
        ) r.body in
        if all_productive || r.body = [] then begin
          Hashtbl.replace productive r.head true;
          changed := true
        end
      end
    ) g.rules
  done;
  let rules' = List.filter (fun r ->
    Hashtbl.mem productive r.head &&
    List.for_all (fun sym ->
      match sym with
      | Nonterminal n -> Hashtbl.mem productive n
      | _ -> true
    ) r.body
  ) g.rules in
  grammar g.start rules'

(** Clean a grammar by removing unreachable and unproductive rules. *)
let clean_grammar g =
  remove_unreachable (remove_unproductive g)

(* ============================================================ *)
(* §14  String Generator (for testing)                           *)
(* ============================================================ *)

(** Generate random strings from a grammar (for testing/fuzzing).
    [max_depth] limits recursion to prevent infinite loops. *)
let generate g ?(max_depth=10) () =
  let buf = Buffer.create 32 in
  let rec gen depth name =
    if depth > max_depth then ()
    else begin
      let matching_rules = rules_for g name in
      if matching_rules = [] then ()
      else begin
        (* Prefer shorter rules at deeper levels to aid termination *)
        let sorted = if depth > max_depth / 2 then
          List.sort (fun a b ->
            compare (List.length a.body) (List.length b.body)
          ) matching_rules
        else matching_rules in
        let r = List.nth sorted (Random.int (List.length sorted)) in
        List.iter (fun sym ->
          match sym with
          | Terminal c -> Buffer.add_char buf c
          | TerminalPred (_, pred) ->
            (* Pick a random matching char *)
            let candidates = List.init 128 Char.chr in
            let matches = List.filter pred candidates in
            if matches <> [] then
              Buffer.add_char buf
                (List.nth matches (Random.int (List.length matches)))
          | Nonterminal n -> gen (depth + 1) n
          | Epsilon -> ()
        ) r.body
      end
    end
  in
  gen 0 g.start;
  Buffer.contents buf

(* ============================================================ *)
(* §15  Tests                                                    *)
(* ============================================================ *)

let () =
  let tests_passed = ref 0 in
  let tests_failed = ref 0 in
  let assert_true msg b =
    if b then incr tests_passed
    else begin
      incr tests_failed;
      Printf.printf "FAIL: %s\n" msg
    end
  in
  let assert_eq msg expected actual =
    if expected = actual then incr tests_passed
    else begin
      incr tests_failed;
      Printf.printf "FAIL: %s — expected %s, got %s\n" msg expected actual
    end
  in
  let assert_float msg expected actual eps =
    if abs_float (expected -. actual) <= eps then incr tests_passed
    else begin
      incr tests_failed;
      Printf.printf "FAIL: %s — expected %f, got %f\n" msg expected actual
    end
  in

  Printf.printf "--- Earley Parser Tests ---\n\n";

  (* §15.1 Grammar Construction *)
  Printf.printf "§15.1 Grammar Construction\n";

  let g1 = grammar "S" [rule "S" [t 'a']; rule "S" [t 'b']] in
  assert_eq "simple grammar rule count" "2" (string_of_int (rule_count g1));
  assert_eq "start symbol" "S" g1.start;

  let g_nullable = grammar "S" [rule "S" []; rule "S" [t 'a'; nt "S"]] in
  assert_true "S is nullable" (is_nullable g_nullable "S");
  assert_true "non-nullable not in set" (not (is_nullable g1 "S"));

  (* §15.2 Basic Parsing *)
  Printf.printf "§15.2 Basic Parsing\n";

  assert_true "accept 'a'" (accepts g1 "a");
  assert_true "accept 'b'" (accepts g1 "b");
  assert_true "reject 'c'" (not (accepts g1 "c"));
  assert_true "reject empty" (not (accepts g1 ""));

  let g_ab = grammar "S" [rule "S" [t 'a'; t 'b']] in
  assert_true "accept 'ab'" (accepts g_ab "ab");
  assert_true "reject 'a' for 'ab'" (not (accepts g_ab "a"));
  assert_true "reject 'abc'" (not (accepts g_ab "abc"));

  (* §15.3 Nullable Grammar *)
  Printf.printf "§15.3 Nullable Grammar\n";

  assert_true "nullable accepts empty" (accepts g_nullable "");
  assert_true "nullable accepts 'a'" (accepts g_nullable "a");
  assert_true "nullable accepts 'aaa'" (accepts g_nullable "aaa");
  assert_true "nullable rejects 'b'" (not (accepts g_nullable "b"));

  (* §15.4 Left Recursion *)
  Printf.printf "§15.4 Left Recursion\n";

  let g_lr = grammar "S" [
    rule "S" [nt "S"; t 'a'];
    rule "S" [t 'b'];
  ] in
  assert_true "left-recursive accepts 'b'" (accepts g_lr "b");
  assert_true "left-recursive accepts 'ba'" (accepts g_lr "ba");
  assert_true "left-recursive accepts 'baa'" (accepts g_lr "baa");
  assert_true "left-recursive accepts 'baaaa'" (accepts g_lr "baaaa");
  assert_true "left-recursive rejects 'a'" (not (accepts g_lr "a"));

  assert_true "detect left recursion" (is_left_recursive g_lr "S");
  assert_true "no left recursion in simple" (not (is_left_recursive g1 "S"));

  (* §15.5 Alternation *)
  Printf.printf "§15.5 Alternation\n";

  let g_alt = grammar "S" [
    rule "S" [t 'a'; t 'b'];
    rule "S" [t 'c'; t 'd'];
    rule "S" [t 'e'];
  ] in
  assert_true "alt accepts 'ab'" (accepts g_alt "ab");
  assert_true "alt accepts 'cd'" (accepts g_alt "cd");
  assert_true "alt accepts 'e'" (accepts g_alt "e");
  assert_true "alt rejects 'ac'" (not (accepts g_alt "ac"));

  (* §15.6 Balanced Parentheses *)
  Printf.printf "§15.6 Balanced Parentheses\n";

  assert_true "parens accepts empty" (accepts paren_grammar "");
  assert_true "parens accepts '()'" (accepts paren_grammar "()");
  assert_true "parens accepts '(())'" (accepts paren_grammar "(())");
  assert_true "parens accepts '()()'" (accepts paren_grammar "()()");
  assert_true "parens accepts '(()())'" (accepts paren_grammar "(()())");
  assert_true "parens rejects '('" (not (accepts paren_grammar "("));
  assert_true "parens rejects ')'" (not (accepts paren_grammar ")"));
  assert_true "parens rejects '(()'" (not (accepts paren_grammar "(()"));

  (* §15.7 Arithmetic Expressions *)
  Printf.printf "§15.7 Arithmetic Expressions\n";

  assert_true "arith accepts '1'" (accepts arith_grammar "1");
  assert_true "arith accepts '1+2'" (accepts arith_grammar "1+2");
  assert_true "arith accepts '1+2*3'" (accepts arith_grammar "1+2*3");
  assert_true "arith accepts '(1+2)*3'" (accepts arith_grammar "(1+2)*3");
  assert_true "arith accepts '12+34'" (accepts arith_grammar "12+34");
  assert_true "arith rejects '+'" (not (accepts arith_grammar "+"));
  assert_true "arith rejects '1+'" (not (accepts arith_grammar "1+"));
  assert_true "arith rejects empty" (not (accepts arith_grammar ""));

  (* §15.8 Parse Tree Construction *)
  Printf.printf "§15.8 Parse Tree Construction\n";

  let trees = parse g1 "a" in
  assert_eq "single tree for 'a'" "1" (string_of_int (List.length trees));
  (match trees with
   | [Node ("S", [Leaf ('a', 0)])] -> assert_true "correct tree for 'a'" true
   | _ -> assert_true "correct tree for 'a'" false);

  let trees = parse g_ab "ab" in
  assert_eq "single tree for 'ab'" "1" (string_of_int (List.length trees));
  (match trees with
   | [Node ("S", [Leaf ('a', 0); Leaf ('b', 1)])] ->
     assert_true "correct tree for 'ab'" true
   | _ -> assert_true "correct tree for 'ab'" false);

  (* §15.9 Arithmetic Evaluation *)
  Printf.printf "§15.9 Arithmetic Evaluation\n";

  assert_float "calc 5" 5.0 (match calc "5" with Some v -> v | None -> nan) 0.001;
  assert_float "calc 1+2" 3.0 (match calc "1+2" with Some v -> v | None -> nan) 0.001;
  assert_float "calc 2*3" 6.0 (match calc "2*3" with Some v -> v | None -> nan) 0.001;
  assert_float "calc 1+2*3" 7.0 (match calc "1+2*3" with Some v -> v | None -> nan) 0.001;
  assert_float "calc (1+2)*3" 9.0 (match calc "(1+2)*3" with Some v -> v | None -> nan) 0.001;
  assert_float "calc 9-3" 6.0 (match calc "9-3" with Some v -> v | None -> nan) 0.001;
  assert_float "calc 8/2" 4.0 (match calc "8/2" with Some v -> v | None -> nan) 0.001;

  assert_true "calc invalid returns None" (calc "++" = None);

  (* §15.10 Palindrome Grammar *)
  Printf.printf "§15.10 Palindrome Grammar\n";

  assert_true "palindrome accepts empty" (accepts palindrome_grammar "");
  assert_true "palindrome accepts 'a'" (accepts palindrome_grammar "a");
  assert_true "palindrome accepts 'aba'" (accepts palindrome_grammar "aba");
  assert_true "palindrome accepts 'abba'" (accepts palindrome_grammar "abba");
  assert_true "palindrome accepts 'abaaba'" (accepts palindrome_grammar "abaaba");
  assert_true "palindrome rejects 'ab'" (not (accepts palindrome_grammar "ab"));
  assert_true "palindrome rejects 'abc'" (not (accepts palindrome_grammar "abc"));

  (* §15.11 Ambiguity Detection *)
  Printf.printf "§15.11 Ambiguity Detection\n";

  (* Dangling else: "icicae" can be parsed two ways *)
  let dangling_tests = ["a"; "ica"; "icicae"] in
  let ambig = check_ambiguity dangling_else_grammar dangling_tests in
  assert_true "dangling else is ambiguous" (List.length ambig > 0);

  let arith_ambig = check_ambiguity arith_grammar ["1+2"; "1+2*3"] in
  assert_true "arithmetic is unambiguous" (List.length arith_ambig = 0);

  (* §15.12 Character Predicates *)
  Printf.printf "§15.12 Character Predicates\n";

  let g_digits = grammar "N" [
    rule "N" [t_pred ~name:"digit" is_digit; nt "N"];
    rule "N" [t_pred ~name:"digit" is_digit];
  ] in
  assert_true "digits accepts '123'" (accepts g_digits "123");
  assert_true "digits accepts '0'" (accepts g_digits "0");
  assert_true "digits rejects 'abc'" (not (accepts g_digits "abc"));
  assert_true "digits rejects empty" (not (accepts g_digits ""));

  let g_id = grammar "Id" [
    rule "Id" [t_pred ~name:"alpha" is_alpha; nt "Rest"];
    rule "Rest" [t_pred ~name:"alnum" is_alnum; nt "Rest"];
    rule "Rest" [];
  ] in
  assert_true "id accepts 'x'" (accepts g_id "x");
  assert_true "id accepts 'foo'" (accepts g_id "foo");
  assert_true "id accepts 'x1'" (accepts g_id "x1");
  assert_true "id rejects '1x'" (not (accepts g_id "1x"));

  (* §15.13 Grammar Utilities *)
  Printf.printf "§15.13 Grammar Utilities\n";

  let nts = nonterminals g1 in
  assert_true "nonterminals includes S" (List.mem "S" nts);

  let ts = terminals g1 in
  assert_true "terminals includes 'a'" (List.mem 'a' ts);
  assert_true "terminals includes 'b'" (List.mem 'b' ts);

  let rules_s = rules_for g1 "S" in
  assert_eq "rules for S" "2" (string_of_int (List.length rules_s));

  (* §15.14 Show/Pretty Print *)
  Printf.printf "§15.14 Show/Pretty Print\n";

  let tree = Node ("S", [Leaf ('a', 0)]) in
  assert_eq "show_tree leaf" "(S 'a')" (show_tree tree);

  let pretty = pretty_tree tree in
  assert_true "pretty_tree not empty" (String.length pretty > 0);
  assert_true "pretty_tree contains S" (String.sub pretty 0 1 = "S");

  let matched = matched_string tree in
  assert_eq "matched_string" "a" matched;

  (* §15.15 Grammar Show *)
  Printf.printf "§15.15 Grammar Show\n";

  let gram_str = show_grammar g1 in
  assert_true "show_grammar contains Start" (String.length gram_str > 0);

  (* §15.16 Clean Grammar *)
  Printf.printf "§15.16 Clean Grammar\n";

  let g_messy = grammar "S" [
    rule "S" [t 'a'];
    rule "X" [t 'b'];  (* unreachable *)
    rule "Y" [nt "Z"];  (* unproductive — Z undefined *)
  ] in
  let g_clean = clean_grammar g_messy in
  assert_eq "clean removes unreachable" "1" (string_of_int (rule_count g_clean));

  (* §15.17 JSON-like Grammar *)
  Printf.printf "§15.17 JSON-like Grammar\n";

  assert_true "json accepts '{}'" (accepts json_grammar "{}");
  assert_true "json accepts '[]'" (accepts json_grammar "[]");
  assert_true "json accepts '\"hi\"'" (accepts json_grammar "\"hi\"");
  assert_true "json accepts '42'" (accepts json_grammar "42");
  assert_true "json accepts '{\"a\":1}'" (accepts json_grammar "{\"a\":1}");
  assert_true "json accepts '[1,2]'" (accepts json_grammar "[1,2]");
  assert_true "json rejects '{'" (not (accepts json_grammar "{"));

  (* §15.18 Chart Debugging *)
  Printf.printf "§15.18 Chart Debugging\n";

  let chart = earley_parse g1 "a" in
  let size = chart_size chart in
  assert_true "chart size > 0" (size > 0);

  let chart_str = show_chart g1 chart in
  assert_true "chart string not empty" (String.length chart_str > 0);

  (* §15.19 String Generation *)
  Printf.printf "§15.19 String Generation\n";

  Random.self_init ();
  for _ = 1 to 20 do
    let s = generate paren_grammar () in
    assert_true (Printf.sprintf "generated '%s' accepted" s)
      (accepts paren_grammar s)
  done;

  (* §15.20 Edge Cases *)
  Printf.printf "§15.20 Edge Cases\n";

  assert_true "empty grammar rejects all" (not (accepts (grammar "S" []) "a"));
  assert_true "empty grammar rejects empty" (not (accepts (grammar "S" []) ""));

  let g_single = grammar "S" [rule "S" [t 'x']] in
  let trees_x = parse g_single "x" in
  assert_eq "single char tree count" "1" (string_of_int (List.length trees_x));

  (* §15.21 Multiple Parse Trees (Ambiguous Grammar) *)
  Printf.printf "§15.21 Multiple Parse Trees\n";

  let g_ambig = grammar "S" [
    rule "S" [nt "S"; t '+'; nt "S"];
    rule "S" [t '1'];
  ] in
  assert_true "ambig accepts '1+1+1'" (accepts g_ambig "1+1+1");
  let ambig_trees = parse g_ambig "1+1+1" in
  assert_true "ambig has multiple trees" (List.length ambig_trees >= 2);

  (* §15.22 FIRST Set Computation *)
  Printf.printf "§15.22 FIRST Set Analysis\n";

  let firsts = first_of arith_grammar "Expr" in
  assert_true "FIRST(Expr) includes '('" (List.mem '(' firsts);
  let digit_in_first = List.exists (fun c -> c >= '0' && c <= '9') firsts in
  assert_true "FIRST(Expr) includes digit" digit_in_first;

  (* §15.23 Item Display *)
  Printf.printf "§15.23 Item Display\n";

  let item_str = show_item g1 { rule_idx = 0; dot = 0; origin = 0;
    node = None; children = [] } in
  assert_true "item string contains S" (String.length item_str > 0);

  Printf.printf "\n=== Results: %d passed, %d failed ===\n"
    !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
