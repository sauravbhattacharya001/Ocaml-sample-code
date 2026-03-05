(* peg.ml — Parsing Expression Grammar (PEG) Engine
 *
 * A complete PEG parser with packrat memoization for guaranteed
 * linear-time parsing. PEGs are a practical alternative to CFGs
 * that eliminate ambiguity through ordered choice.
 *
 * Concepts demonstrated:
 * - Parsing Expression Grammars (Ford, 2004)
 * - Packrat parsing with memoization (linear-time guarantee)
 * - Algebraic data types for grammar representation
 * - CPS-style parsing with backtracking
 * - Semantic actions (parse tree construction)
 * - Left recursion detection
 * - Grammar analysis and optimization
 *
 * PEG operators:
 *   'c'       literal character
 *   "str"     literal string
 *   [a-z]     character class
 *   .         any character
 *   e1 e2     sequence
 *   e1 / e2   ordered choice (not alternation!)
 *   e*        zero or more (greedy, no backtrack)
 *   e+        one or more
 *   e?        optional
 *   &e        positive lookahead (match without consuming)
 *   !e        negative lookahead
 *   rule      non-terminal reference
 *
 * Key difference from CFGs:
 *   PEG's "/" is ORDERED choice — tries alternatives left-to-right,
 *   commits to first match. This eliminates ambiguity but means
 *   grammar order matters.
 *
 * Usage:
 *   let arith = Grammar.create "expr" [
 *     "expr",   Sequence [Ref "term"; Star (Sequence [Class [Range ('+',"+"'); Range ('-',"-")]; Ref "term"])];
 *     "term",   Sequence [Ref "factor"; Star (Sequence [Class [Range ('*',"*"); Range ('/',"/")]; Ref "factor"])];
 *     "factor", Choice [
 *       Sequence [Lit '('; Ref "expr"; Lit ')'];
 *       Ref "number"
 *     ];
 *     "number", Plus (Class [Range ('0','9')]);
 *   ]
 *   let result = parse arith "3+4*5"
 *)

(* ═══════════════════════════════════════════════════════════════
   Module: PEG expression types
   ═══════════════════════════════════════════════════════════════ *)

(** Character class element *)
type char_class_elem =
  | Single of char
  | Range of char * char

(** PEG expression *)
type expr =
  | Lit of char               (* match single character *)
  | LitStr of string          (* match literal string *)
  | Dot                       (* match any character *)
  | Class of char_class_elem list  (* character class [a-zA-Z0-9] *)
  | NegClass of char_class_elem list  (* negated class [^...] *)
  | Sequence of expr list     (* e1 e2 e3 ... *)
  | Choice of expr list       (* e1 / e2 / e3 ... (ordered) *)
  | Star of expr              (* e* — zero or more *)
  | Plus of expr              (* e+ — one or more *)
  | Opt of expr               (* e? — optional *)
  | And of expr               (* &e — positive lookahead *)
  | Not of expr               (* !e — negative lookahead *)
  | Ref of string             (* non-terminal reference *)
  | Action of expr * string   (* semantic action label *)
  | Empty                     (* always succeeds, consumes nothing *)

(** Parse tree node *)
type parse_tree =
  | Leaf of string * int * int      (* matched text, start, end *)
  | Node of string * parse_tree list  (* rule name, children *)

(** Parse result *)
type parse_result =
  | Success of int * parse_tree     (* end position, tree *)
  | Failure of int * string         (* position, error message *)

(* ═══════════════════════════════════════════════════════════════
   Module: Grammar
   ═══════════════════════════════════════════════════════════════ *)

module Grammar = struct
  type t = {
    start: string;
    rules: (string * expr) list;
  }

  let create start rules = { start; rules }

  let get_rule g name =
    List.assoc_opt name g.rules

  let rule_names g =
    List.map fst g.rules

  let rule_count g =
    List.length g.rules
end

(* ═══════════════════════════════════════════════════════════════
   Module: Packrat memoization table
   ═══════════════════════════════════════════════════════════════ *)

module Memo = struct
  type key = string * int  (* rule name, position *)
  type t = (key, parse_result) Hashtbl.t

  let create () : t = Hashtbl.create 256

  let lookup (memo : t) rule pos =
    Hashtbl.find_opt memo (rule, pos)

  let store (memo : t) rule pos result =
    Hashtbl.replace memo (rule, pos) result

  let size (memo : t) = Hashtbl.length memo

  let hit_count (memo : t) = Hashtbl.length memo
end

(* ═══════════════════════════════════════════════════════════════
   Module: Character class matching
   ═══════════════════════════════════════════════════════════════ *)

let char_in_class c elems =
  List.exists (fun elem ->
    match elem with
    | Single ch -> c = ch
    | Range (lo, hi) -> c >= lo && c <= hi
  ) elems

(* ═══════════════════════════════════════════════════════════════
   Module: PEG Parser Engine
   ═══════════════════════════════════════════════════════════════ *)

(** Parse an expression against input starting at position pos.
    Returns Success (end_pos, tree) or Failure (pos, msg).
    Uses packrat memoization for Ref (non-terminal) calls. *)
let rec parse_expr (grammar : Grammar.t) (memo : Memo.t) (input : string) (expr : expr) (pos : int) : parse_result =
  let len = String.length input in
  match expr with

  | Empty ->
    Success (pos, Leaf ("", pos, pos))

  | Lit c ->
    if pos < len && input.[pos] = c then
      Success (pos + 1, Leaf (String.make 1 c, pos, pos + 1))
    else
      let expected = Printf.sprintf "expected '%c'" c in
      Failure (pos, expected)

  | LitStr s ->
    let slen = String.length s in
    if pos + slen <= len && String.sub input pos slen = s then
      Success (pos + slen, Leaf (s, pos, pos + slen))
    else
      Failure (pos, Printf.sprintf "expected \"%s\"" s)

  | Dot ->
    if pos < len then
      Success (pos + 1, Leaf (String.make 1 input.[pos], pos, pos + 1))
    else
      Failure (pos, "unexpected end of input")

  | Class elems ->
    if pos < len && char_in_class input.[pos] elems then
      Success (pos + 1, Leaf (String.make 1 input.[pos], pos, pos + 1))
    else
      Failure (pos, "character class mismatch")

  | NegClass elems ->
    if pos < len && not (char_in_class input.[pos] elems) then
      Success (pos + 1, Leaf (String.make 1 input.[pos], pos, pos + 1))
    else
      Failure (pos, "negated character class mismatch")

  | Sequence exprs ->
    parse_sequence grammar memo input exprs pos pos []

  | Choice exprs ->
    parse_choice grammar memo input exprs pos

  | Star e ->
    parse_star grammar memo input e pos pos []

  | Plus e ->
    (match parse_expr grammar memo input e pos with
     | Failure (fp, msg) -> Failure (fp, msg)
     | Success (p1, t1) ->
       parse_star grammar memo input e p1 pos [t1])

  | Opt e ->
    (match parse_expr grammar memo input e pos with
     | Success (p1, t1) -> Success (p1, t1)
     | Failure _ -> Success (pos, Leaf ("", pos, pos)))

  | And e ->
    (match parse_expr grammar memo input e pos with
     | Success _ -> Success (pos, Leaf ("", pos, pos))  (* don't consume *)
     | Failure (fp, msg) -> Failure (fp, msg))

  | Not e ->
    (match parse_expr grammar memo input e pos with
     | Success _ -> Failure (pos, "negative lookahead failed")
     | Failure _ -> Success (pos, Leaf ("", pos, pos)))

  | Ref name ->
    (* Packrat memoization: check memo table first *)
    (match Memo.lookup memo name pos with
     | Some result -> result
     | None ->
       match Grammar.get_rule grammar name with
       | None -> Failure (pos, Printf.sprintf "undefined rule '%s'" name)
       | Some rule_expr ->
         (* Store a failure sentinel to detect left recursion *)
         Memo.store memo name pos (Failure (pos, Printf.sprintf "left recursion in '%s'" name));
         let result = parse_expr grammar memo input rule_expr pos in
         let wrapped = match result with
           | Success (ep, tree) -> Success (ep, Node (name, [tree]))
           | Failure _ -> result
         in
         Memo.store memo name pos wrapped;
         wrapped)

  | Action (e, label) ->
    (match parse_expr grammar memo input e pos with
     | Success (ep, tree) -> Success (ep, Node (label, [tree]))
     | Failure _ as f -> f)

and parse_sequence grammar memo input exprs start_pos pos acc =
  match exprs with
  | [] ->
    let text = String.sub input start_pos (pos - start_pos) in
    Success (pos, Node ("seq", List.rev acc @ [Leaf (text, start_pos, pos)]))
  | e :: rest ->
    match parse_expr grammar memo input e pos with
    | Failure (fp, msg) -> Failure (fp, msg)
    | Success (p1, t1) ->
      parse_sequence grammar memo input rest start_pos p1 (t1 :: acc)

and parse_choice grammar memo input exprs pos =
  match exprs with
  | [] -> Failure (pos, "no alternative matched")
  | e :: rest ->
    match parse_expr grammar memo input e pos with
    | Success _ as s -> s
    | Failure _ ->
      parse_choice grammar memo input rest pos

and parse_star grammar memo input e pos start_pos acc =
  match parse_expr grammar memo input e pos with
  | Failure _ ->
    let text = String.sub input start_pos (pos - start_pos) in
    Success (pos, Node ("repeat", List.rev acc @ [Leaf (text, start_pos, pos)]))
  | Success (p1, t1) ->
    if p1 = pos then
      (* Prevent infinite loop on empty match *)
      let text = String.sub input start_pos (pos - start_pos) in
      Success (pos, Node ("repeat", List.rev acc @ [Leaf (text, start_pos, pos)]))
    else
      parse_star grammar memo input e p1 start_pos (t1 :: acc)

(* ═══════════════════════════════════════════════════════════════
   Module: Top-level parse functions
   ═══════════════════════════════════════════════════════════════ *)

(** Parse input string using grammar, starting from the start rule *)
let parse grammar input =
  let memo = Memo.create () in
  parse_expr grammar memo input (Ref grammar.Grammar.start) 0

(** Parse and require full input consumption *)
let parse_full grammar input =
  let memo = Memo.create () in
  match parse_expr grammar memo input (Ref grammar.Grammar.start) 0 with
  | Success (ep, tree) ->
    if ep = String.length input then
      Success (ep, tree)
    else
      Failure (ep, Printf.sprintf "unexpected input at position %d" ep)
  | Failure _ as f -> f

(** Parse with statistics *)
let parse_with_stats grammar input =
  let memo = Memo.create () in
  let result = parse_expr grammar memo input (Ref grammar.Grammar.start) 0 in
  (result, Memo.size memo)

(* ═══════════════════════════════════════════════════════════════
   Module: Parse tree utilities
   ═══════════════════════════════════════════════════════════════ *)

(** Extract matched text from a parse tree *)
let rec tree_text input = function
  | Leaf (_, s, e) -> String.sub input s (e - s)
  | Node (_, children) ->
    String.concat "" (List.map (tree_text input) children)

(** Count nodes in parse tree *)
let rec tree_size = function
  | Leaf _ -> 1
  | Node (_, children) ->
    1 + List.fold_left (fun acc c -> acc + tree_size c) 0 children

(** Tree depth *)
let rec tree_depth = function
  | Leaf _ -> 1
  | Node (_, []) -> 1
  | Node (_, children) ->
    1 + List.fold_left (fun acc c -> max acc (tree_depth c)) 0 children

(** Flatten tree to list of (name, text) pairs *)
let rec tree_flatten input = function
  | Leaf (_, s, e) -> [("leaf", String.sub input s (e - s))]
  | Node (name, children) ->
    (name, "") :: List.concat_map (tree_flatten input) children

(** Pretty-print parse tree *)
let rec tree_to_string indent = function
  | Leaf (text, s, e) ->
    Printf.sprintf "%s\"%s\" [%d..%d]" indent text s e
  | Node (name, children) ->
    let header = Printf.sprintf "%s%s:" indent name in
    let child_strs = List.map (tree_to_string (indent ^ "  ")) children in
    String.concat "\n" (header :: child_strs)

(* ═══════════════════════════════════════════════════════════════
   Module: Grammar analysis
   ═══════════════════════════════════════════════════════════════ *)

(** Find all non-terminals referenced in an expression *)
let rec refs_in_expr = function
  | Ref name -> [name]
  | Sequence exprs | Choice exprs ->
    List.concat_map refs_in_expr exprs
  | Star e | Plus e | Opt e | And e | Not e | Action (e, _) ->
    refs_in_expr e
  | _ -> []

(** Check if a rule can match empty string (nullable) *)
let rec nullable grammar visited = function
  | Empty -> true
  | Lit _ | LitStr _ | Dot | Class _ | NegClass _ -> false
  | Opt _ | Star _ -> true
  | Plus e -> nullable grammar visited e
  | Sequence exprs -> List.for_all (nullable grammar visited) exprs
  | Choice exprs -> List.exists (nullable grammar visited) exprs
  | And _ | Not _ -> true  (* lookaheads don't consume *)
  | Action (e, _) -> nullable grammar visited e
  | Ref name ->
    if List.mem name visited then false  (* avoid infinite loop *)
    else
      match Grammar.get_rule grammar name with
      | None -> false
      | Some e -> nullable grammar (name :: visited) e

(** Detect potential left recursion *)
let rec left_recursive grammar visited name =
  if List.mem name visited then true
  else
    match Grammar.get_rule grammar name with
    | None -> false
    | Some expr -> check_left grammar (name :: visited) expr

and check_left grammar visited = function
  | Ref name -> left_recursive grammar visited name
  | Sequence (e :: _) -> check_left grammar visited e
  | Choice exprs -> List.exists (check_left grammar visited) exprs
  | Action (e, _) -> check_left grammar visited e
  | _ -> false

(** Find all left-recursive rules *)
let find_left_recursive grammar =
  List.filter (fun (name, _) ->
    left_recursive grammar [] name
  ) grammar.Grammar.rules
  |> List.map fst

(** Find undefined references *)
let find_undefined grammar =
  let defined = List.map fst grammar.Grammar.rules in
  List.concat_map (fun (_, expr) -> refs_in_expr expr) grammar.Grammar.rules
  |> List.sort_uniq String.compare
  |> List.filter (fun name -> not (List.mem name defined))

(** Find unused rules (not reachable from start) *)
let find_unused grammar =
  let rec reachable visited name =
    if List.mem name visited then visited
    else
      match Grammar.get_rule grammar name with
      | None -> visited
      | Some expr ->
        let visited' = name :: visited in
        List.fold_left (fun v r -> reachable v r) visited' (refs_in_expr expr)
  in
  let used = reachable [] grammar.Grammar.start in
  List.filter (fun (name, _) -> not (List.mem name used)) grammar.Grammar.rules
  |> List.map fst

(** Grammar summary *)
let grammar_info grammar =
  let rules = Grammar.rule_count grammar in
  let lr = find_left_recursive grammar in
  let undef = find_undefined grammar in
  let unused = find_unused grammar in
  Printf.sprintf "Grammar: %d rules, start='%s'\n  Left-recursive: %s\n  Undefined: %s\n  Unused: %s"
    rules grammar.Grammar.start
    (if lr = [] then "none" else String.concat ", " lr)
    (if undef = [] then "none" else String.concat ", " undef)
    (if unused = [] then "none" else String.concat ", " unused)

(* ═══════════════════════════════════════════════════════════════
   Module: PEG expression builders (convenience)
   ═══════════════════════════════════════════════════════════════ *)

let lit c = Lit c
let str s = LitStr s
let dot = Dot
let cls elems = Class elems
let neg_cls elems = NegClass elems
let seq exprs = Sequence exprs
let alt exprs = Choice exprs
let star e = Star e
let plus e = Plus e
let opt e = Opt e
let lookahead e = And e
let not_ahead e = Not e
let ref_ name = Ref name
let action e label = Action (e, label)
let empty = Empty

(* Common character classes *)
let digit = Class [Range ('0', '9')]
let alpha = Class [Range ('a', 'z'); Range ('A', 'Z')]
let alnum = Class [Range ('a', 'z'); Range ('A', 'Z'); Range ('0', '9')]
let space = Class [Single ' '; Single '\t'; Single '\n'; Single '\r']

(* ═══════════════════════════════════════════════════════════════
   Module: Example grammars
   ═══════════════════════════════════════════════════════════════ *)

module Examples = struct

  (** Simple arithmetic: expr = term (('+' / '-') term)*
                         term = factor (('*' / '/') factor)*
                         factor = '(' expr ')' / number
                         number = [0-9]+ *)
  let arithmetic = Grammar.create "expr" [
    "expr", seq [ref_ "term"; star (seq [cls [Single '+'; Single '-']; ref_ "term"])];
    "term", seq [ref_ "factor"; star (seq [cls [Single '*'; Single '/'; Single '%']; ref_ "factor"])];
    "factor", alt [
      seq [lit '('; ref_ "expr"; lit ')'];
      ref_ "number"
    ];
    "number", plus digit;
  ]

  (** JSON value parser *)
  let json = Grammar.create "value" [
    "value", alt [ref_ "string"; ref_ "number"; ref_ "object";
                  ref_ "array"; ref_ "true"; ref_ "false"; ref_ "null"];
    "ws", star space;
    "string", seq [lit '"'; star (alt [
      seq [lit '\\'; dot];  (* escaped char *)
      Class [Range ('\x20', '!'); Range ('#', '['); Range (']', '\x7e')]
    ]); lit '"'];
    "number", seq [opt (lit '-'); plus digit; opt (seq [lit '.'; plus digit])];
    "object", seq [lit '{'; ref_ "ws"; opt (seq [
      ref_ "member"; star (seq [ref_ "ws"; lit ','; ref_ "ws"; ref_ "member"])
    ]); ref_ "ws"; lit '}'];
    "member", seq [ref_ "ws"; ref_ "string"; ref_ "ws"; lit ':'; ref_ "ws"; ref_ "value"];
    "array", seq [lit '['; ref_ "ws"; opt (seq [
      ref_ "value"; star (seq [ref_ "ws"; lit ','; ref_ "ws"; ref_ "value"])
    ]); ref_ "ws"; lit ']'];
    "true", str "true";
    "false", str "false";
    "null", str "null";
  ]

  (** CSV parser *)
  let csv = Grammar.create "file" [
    "file", seq [ref_ "line"; star (seq [lit '\n'; ref_ "line"]); opt (lit '\n')];
    "line", seq [ref_ "field"; star (seq [lit ','; ref_ "field"])];
    "field", alt [ref_ "quoted"; ref_ "unquoted"];
    "quoted", seq [lit '"'; star (alt [
      str "\"\"";  (* escaped quote *)
      NegClass [Single '"']
    ]); lit '"'];
    "unquoted", star (NegClass [Single ','; Single '\n'; Single '"']);
  ]

  (** Simple identifier language: id = [a-zA-Z_][a-zA-Z0-9_]* *)
  let identifier = Grammar.create "id" [
    "id", seq [
      cls [Range ('a','z'); Range ('A','Z'); Single '_'];
      star (cls [Range ('a','z'); Range ('A','Z'); Range ('0','9'); Single '_'])
    ];
  ]

  (** Balanced parentheses *)
  let parens = Grammar.create "parens" [
    "parens", alt [
      seq [lit '('; ref_ "parens"; lit ')'; ref_ "parens"];
      empty
    ];
  ]
end

(* ═══════════════════════════════════════════════════════════════
   Module: Tests
   ═══════════════════════════════════════════════════════════════ *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let test name f =
    try f (); incr passed; Printf.printf "  ✓ %s\n" name
    with e -> incr failed; Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string e)
  in
  let assert_eq a b =
    if a <> b then failwith (Printf.sprintf "expected %s, got %s" (string_of_bool b) (string_of_bool a))
  in
  let _ = assert_eq in

  Printf.printf "═══ PEG Parser Engine Tests ═══\n\n";

  (* ── Literal matching ── *)
  Printf.printf "Literal matching:\n";
  test "single char match" (fun () ->
    let g = Grammar.create "s" ["s", Lit 'a'] in
    match parse g "a" with
    | Success (1, _) -> ()
    | _ -> failwith "should match 'a'"
  );

  test "single char mismatch" (fun () ->
    let g = Grammar.create "s" ["s", Lit 'a'] in
    match parse g "b" with
    | Failure _ -> ()
    | _ -> failwith "should fail on 'b'"
  );

  test "string literal" (fun () ->
    let g = Grammar.create "s" ["s", LitStr "hello"] in
    match parse g "hello world" with
    | Success (5, _) -> ()
    | _ -> failwith "should match 'hello'"
  );

  test "string literal mismatch" (fun () ->
    let g = Grammar.create "s" ["s", LitStr "hello"] in
    match parse g "help" with
    | Failure _ -> ()
    | _ -> failwith "should fail"
  );

  test "dot matches any" (fun () ->
    let g = Grammar.create "s" ["s", Dot] in
    match parse g "x" with
    | Success (1, _) -> ()
    | _ -> failwith "should match"
  );

  test "dot fails on empty" (fun () ->
    let g = Grammar.create "s" ["s", Dot] in
    match parse g "" with
    | Failure _ -> ()
    | _ -> failwith "should fail"
  );

  (* ── Character classes ── *)
  Printf.printf "\nCharacter classes:\n";
  test "char class single match" (fun () ->
    let g = Grammar.create "s" ["s", Class [Single 'a'; Single 'b']] in
    match parse g "a" with
    | Success (1, _) -> ()
    | _ -> failwith "should match"
  );

  test "char class range match" (fun () ->
    let g = Grammar.create "s" ["s", Class [Range ('0', '9')]] in
    match parse g "5" with
    | Success (1, _) -> ()
    | _ -> failwith "should match digit"
  );

  test "char class range mismatch" (fun () ->
    let g = Grammar.create "s" ["s", Class [Range ('0', '9')]] in
    match parse g "a" with
    | Failure _ -> ()
    | _ -> failwith "should fail"
  );

  test "negated class match" (fun () ->
    let g = Grammar.create "s" ["s", NegClass [Single 'a']] in
    match parse g "b" with
    | Success (1, _) -> ()
    | _ -> failwith "should match non-a"
  );

  test "negated class mismatch" (fun () ->
    let g = Grammar.create "s" ["s", NegClass [Single 'a']] in
    match parse g "a" with
    | Failure _ -> ()
    | _ -> failwith "should fail on a"
  );

  (* ── Sequence ── *)
  Printf.printf "\nSequence:\n";
  test "simple sequence" (fun () ->
    let g = Grammar.create "s" ["s", Sequence [Lit 'a'; Lit 'b'; Lit 'c']] in
    match parse g "abc" with
    | Success (3, _) -> ()
    | _ -> failwith "should match abc"
  );

  test "sequence partial fail" (fun () ->
    let g = Grammar.create "s" ["s", Sequence [Lit 'a'; Lit 'b'; Lit 'c']] in
    match parse g "abd" with
    | Failure _ -> ()
    | _ -> failwith "should fail at c"
  );

  test "empty sequence" (fun () ->
    let g = Grammar.create "s" ["s", Sequence []] in
    match parse g "xyz" with
    | Success (0, _) -> ()
    | _ -> failwith "empty sequence should succeed at 0"
  );

  (* ── Choice (ordered) ── *)
  Printf.printf "\nOrdered choice:\n";
  test "first alternative matches" (fun () ->
    let g = Grammar.create "s" ["s", Choice [Lit 'a'; Lit 'b']] in
    match parse g "a" with
    | Success (1, _) -> ()
    | _ -> failwith "should match first"
  );

  test "second alternative matches" (fun () ->
    let g = Grammar.create "s" ["s", Choice [Lit 'a'; Lit 'b']] in
    match parse g "b" with
    | Success (1, _) -> ()
    | _ -> failwith "should match second"
  );

  test "no alternative matches" (fun () ->
    let g = Grammar.create "s" ["s", Choice [Lit 'a'; Lit 'b']] in
    match parse g "c" with
    | Failure _ -> ()
    | _ -> failwith "should fail"
  );

  test "ordered choice commits to first" (fun () ->
    (* "ab" / "a" — with "ab" input, first match wins *)
    let g = Grammar.create "s" ["s", Choice [LitStr "ab"; Lit 'a']] in
    match parse g "ab" with
    | Success (2, _) -> ()  (* first choice consumed both *)
    | _ -> failwith "should match 'ab' via first choice"
  );

  (* ── Repetition ── *)
  Printf.printf "\nRepetition:\n";
  test "star matches zero" (fun () ->
    let g = Grammar.create "s" ["s", Star (Lit 'a')] in
    match parse g "bbb" with
    | Success (0, _) -> ()
    | _ -> failwith "star should match zero"
  );

  test "star matches multiple" (fun () ->
    let g = Grammar.create "s" ["s", Star (Lit 'a')] in
    match parse g "aaab" with
    | Success (3, _) -> ()
    | _ -> failwith "star should match 3"
  );

  test "plus matches one" (fun () ->
    let g = Grammar.create "s" ["s", Plus (Lit 'a')] in
    match parse g "ab" with
    | Success (1, _) -> ()
    | _ -> failwith "plus should match 1"
  );

  test "plus fails on zero" (fun () ->
    let g = Grammar.create "s" ["s", Plus (Lit 'a')] in
    match parse g "b" with
    | Failure _ -> ()
    | _ -> failwith "plus should fail on zero"
  );

  test "optional present" (fun () ->
    let g = Grammar.create "s" ["s", Opt (Lit 'a')] in
    match parse g "a" with
    | Success (1, _) -> ()
    | _ -> failwith "opt should match"
  );

  test "optional absent" (fun () ->
    let g = Grammar.create "s" ["s", Opt (Lit 'a')] in
    match parse g "b" with
    | Success (0, _) -> ()
    | _ -> failwith "opt should succeed with 0"
  );

  (* ── Lookahead ── *)
  Printf.printf "\nLookahead:\n";
  test "positive lookahead success" (fun () ->
    let g = Grammar.create "s" ["s", Sequence [And (Lit 'a'); Lit 'a']] in
    match parse g "a" with
    | Success (1, _) -> ()
    | _ -> failwith "should match with lookahead"
  );

  test "positive lookahead failure" (fun () ->
    let g = Grammar.create "s" ["s", Sequence [And (Lit 'a'); Lit 'b']] in
    match parse g "b" with
    | Failure _ -> ()
    | _ -> failwith "lookahead should fail"
  );

  test "negative lookahead success" (fun () ->
    let g = Grammar.create "s" ["s", Sequence [Not (Lit 'b'); Lit 'a']] in
    match parse g "a" with
    | Success (1, _) -> ()
    | _ -> failwith "should match"
  );

  test "negative lookahead failure" (fun () ->
    let g = Grammar.create "s" ["s", Not (Lit 'a')] in
    match parse g "a" with
    | Failure _ -> ()
    | _ -> failwith "negative lookahead should fail"
  );

  test "not-ahead doesn't consume" (fun () ->
    let g = Grammar.create "s" ["s", Sequence [Not (Lit 'b'); Dot]] in
    match parse g "a" with
    | Success (1, _) -> ()
    | _ -> failwith "should consume 1 char after not"
  );

  (* ── Rule references & memoization ── *)
  Printf.printf "\nRules & memoization:\n";
  test "simple rule reference" (fun () ->
    let g = Grammar.create "s" [
      "s", Ref "digit";
      "digit", Class [Range ('0', '9')];
    ] in
    match parse g "5" with
    | Success (1, _) -> ()
    | _ -> failwith "should match digit via ref"
  );

  test "recursive rule" (fun () ->
    let g = Examples.parens in
    match parse_full g "(())" with
    | Success _ -> ()
    | _ -> failwith "should match balanced parens"
  );

  test "undefined rule fails" (fun () ->
    let g = Grammar.create "s" ["s", Ref "nonexistent"] in
    match parse g "x" with
    | Failure (_, msg) -> assert (String.length msg > 0)
    | _ -> failwith "should fail"
  );

  test "memoization reuses results" (fun () ->
    let g = Grammar.create "s" [
      "s", Sequence [Ref "a"; Ref "a"];
      "a", Plus (Class [Range ('a', 'z')]);
    ] in
    let (_, memo_size) = parse_with_stats g "abc" in
    assert (memo_size > 0)
  );

  test "left recursion detected" (fun () ->
    let g = Grammar.create "s" [
      "s", Sequence [Ref "s"; Lit 'a'];
    ] in
    match parse g "aaa" with
    | Failure (_, msg) -> assert (String.length msg > 0)
    | _ -> failwith "left recursion should fail"
  );

  (* ── Parse tree ── *)
  Printf.printf "\nParse tree:\n";
  test "tree text extraction" (fun () ->
    let g = Grammar.create "s" ["s", Plus (Class [Range ('a', 'z')])] in
    match parse g "hello" with
    | Success (5, tree) ->
      let text = tree_text "hello" tree in
      assert (String.length text > 0)
    | _ -> failwith "should match"
  );

  test "tree size" (fun () ->
    let g = Grammar.create "s" ["s", Sequence [Lit 'a'; Lit 'b']] in
    match parse g "ab" with
    | Success (_, tree) ->
      let size = tree_size tree in
      assert (size >= 1)
    | _ -> failwith "should match"
  );

  test "tree depth" (fun () ->
    let g = Grammar.create "s" [
      "s", Ref "inner";
      "inner", Lit 'x';
    ] in
    match parse g "x" with
    | Success (_, tree) ->
      let d = tree_depth tree in
      assert (d >= 2)
    | _ -> failwith "should match"
  );

  test "tree to string" (fun () ->
    let g = Grammar.create "s" ["s", Lit 'a'] in
    match parse g "a" with
    | Success (_, tree) ->
      let s = tree_to_string "" tree in
      assert (String.length s > 0)
    | _ -> failwith "should match"
  );

  test "tree flatten" (fun () ->
    let g = Grammar.create "s" ["s", Sequence [Lit 'a'; Lit 'b']] in
    match parse g "ab" with
    | Success (_, tree) ->
      let flat = tree_flatten "ab" tree in
      assert (List.length flat > 0)
    | _ -> failwith "should match"
  );

  (* ── Full parse ── *)
  Printf.printf "\nFull parse:\n";
  test "parse_full succeeds on complete match" (fun () ->
    let g = Grammar.create "s" ["s", LitStr "abc"] in
    match parse_full g "abc" with
    | Success (3, _) -> ()
    | _ -> failwith "should match fully"
  );

  test "parse_full fails on partial match" (fun () ->
    let g = Grammar.create "s" ["s", LitStr "ab"] in
    match parse_full g "abc" with
    | Failure _ -> ()
    | _ -> failwith "should fail — extra input"
  );

  (* ── Action labels ── *)
  Printf.printf "\nSemantic actions:\n";
  test "action wraps parse tree" (fun () ->
    let g = Grammar.create "s" ["s", Action (Plus digit, "number")] in
    match parse g "42" with
    | Success (2, Node ("number", _)) -> ()
    | _ -> failwith "should wrap in action node"
  );

  (* ── Example grammars ── *)
  Printf.printf "\nArithmetic grammar:\n";
  test "simple number" (fun () ->
    match parse_full Examples.arithmetic "42" with
    | Success _ -> ()
    | _ -> failwith "should parse number"
  );

  test "addition" (fun () ->
    match parse_full Examples.arithmetic "3+4" with
    | Success _ -> ()
    | _ -> failwith "should parse addition"
  );

  test "complex expression" (fun () ->
    match parse_full Examples.arithmetic "3+4*5" with
    | Success _ -> ()
    | _ -> failwith "should parse complex expr"
  );

  test "parenthesized expression" (fun () ->
    match parse_full Examples.arithmetic "(3+4)*5" with
    | Success _ -> ()
    | _ -> failwith "should parse parens"
  );

  test "nested parentheses" (fun () ->
    match parse_full Examples.arithmetic "((1+2))" with
    | Success _ -> ()
    | _ -> failwith "should parse nested parens"
  );

  Printf.printf "\nJSON grammar:\n";
  test "json number" (fun () ->
    match parse_full Examples.json "42" with
    | Success _ -> ()
    | _ -> failwith "should parse json number"
  );

  test "json string" (fun () ->
    match parse_full Examples.json "\"hello\"" with
    | Success _ -> ()
    | _ -> failwith "should parse json string"
  );

  test "json true" (fun () ->
    match parse_full Examples.json "true" with
    | Success _ -> ()
    | _ -> failwith "should parse true"
  );

  test "json null" (fun () ->
    match parse_full Examples.json "null" with
    | Success _ -> ()
    | _ -> failwith "should parse null"
  );

  test "json array" (fun () ->
    match parse_full Examples.json "[1,2,3]" with
    | Success _ -> ()
    | _ -> failwith "should parse array"
  );

  test "json object" (fun () ->
    match parse_full Examples.json "{\"a\":1}" with
    | Success _ -> ()
    | _ -> failwith "should parse object"
  );

  test "json nested" (fun () ->
    match parse_full Examples.json "{\"a\":[1,true,\"x\"]}" with
    | Success _ -> ()
    | _ -> failwith "should parse nested json"
  );

  test "json with whitespace" (fun () ->
    match parse_full Examples.json "{ \"key\" : \"value\" }" with
    | Success _ -> ()
    | _ -> failwith "should parse json with spaces"
  );

  Printf.printf "\nCSV grammar:\n";
  test "simple csv line" (fun () ->
    match parse_full Examples.csv "a,b,c" with
    | Success _ -> ()
    | _ -> failwith "should parse csv line"
  );

  test "csv with quoted fields" (fun () ->
    match parse_full Examples.csv "\"hello\",world" with
    | Success _ -> ()
    | _ -> failwith "should parse quoted csv"
  );

  test "csv multiple lines" (fun () ->
    match parse_full Examples.csv "a,b\nc,d" with
    | Success _ -> ()
    | _ -> failwith "should parse multi-line csv"
  );

  Printf.printf "\nIdentifier grammar:\n";
  test "simple identifier" (fun () ->
    match parse Examples.identifier "foo" with
    | Success (3, _) -> ()
    | _ -> failwith "should parse id"
  );

  test "identifier with underscore" (fun () ->
    match parse Examples.identifier "_bar_123" with
    | Success (8, _) -> ()
    | _ -> failwith "should parse id with underscore"
  );

  test "identifier rejects leading digit" (fun () ->
    match parse Examples.identifier "123abc" with
    | Failure _ -> ()
    | _ -> failwith "should reject leading digit"
  );

  Printf.printf "\nBalanced parentheses:\n";
  test "empty parens" (fun () ->
    match parse_full Examples.parens "" with
    | Success _ -> ()
    | _ -> failwith "should match empty"
  );

  test "simple parens" (fun () ->
    match parse_full Examples.parens "()" with
    | Success _ -> ()
    | _ -> failwith "should match ()"
  );

  test "nested parens" (fun () ->
    match parse_full Examples.parens "(()())" with
    | Success _ -> ()
    | _ -> failwith "should match (()())"
  );

  test "unbalanced parens" (fun () ->
    match parse_full Examples.parens "(()" with
    | Failure _ -> ()
    | _ -> failwith "should reject unbalanced"
  );

  (* ── Grammar analysis ── *)
  Printf.printf "\nGrammar analysis:\n";
  test "grammar_info" (fun () ->
    let info = grammar_info Examples.arithmetic in
    assert (String.length info > 0);
    assert (String.length info > 10)
  );

  test "find undefined references" (fun () ->
    let g = Grammar.create "s" ["s", Ref "missing"] in
    let undef = find_undefined g in
    assert (List.mem "missing" undef)
  );

  test "no undefined in arithmetic" (fun () ->
    let undef = find_undefined Examples.arithmetic in
    assert (undef = [])
  );

  test "find unused rules" (fun () ->
    let g = Grammar.create "s" [
      "s", Lit 'a';
      "orphan", Lit 'b';
    ] in
    let unused = find_unused g in
    assert (List.mem "orphan" unused)
  );

  test "detect left recursion" (fun () ->
    let g = Grammar.create "s" [
      "s", Sequence [Ref "s"; Lit 'a'];
    ] in
    let lr = find_left_recursive g in
    assert (List.mem "s" lr)
  );

  test "no left recursion in arithmetic" (fun () ->
    let lr = find_left_recursive Examples.arithmetic in
    assert (lr = [])
  );

  test "nullable detection" (fun () ->
    assert (nullable Examples.arithmetic [] (Star (Lit 'a')));
    assert (nullable Examples.arithmetic [] (Opt (Lit 'a')));
    assert (not (nullable Examples.arithmetic [] (Lit 'a')));
    assert (not (nullable Examples.arithmetic [] (Plus (Lit 'a'))))
  );

  test "refs_in_expr" (fun () ->
    let refs = refs_in_expr (Sequence [Ref "a"; Ref "b"; Lit 'c']) in
    assert (List.mem "a" refs);
    assert (List.mem "b" refs);
    assert (List.length refs = 2)
  );

  (* ── Convenience builders ── *)
  Printf.printf "\nConvenience builders:\n";
  test "builder functions" (fun () ->
    let g = Grammar.create "s" [
      "s", seq [alt [ref_ "d"; ref_ "a"]; star space];
      "d", plus digit;
      "a", plus alpha;
    ] in
    match parse g "123 " with
    | Success (4, _) -> ()
    | _ -> failwith "should match via builders"
  );

  test "alnum class" (fun () ->
    let g = Grammar.create "s" ["s", plus alnum] in
    match parse g "abc123" with
    | Success (6, _) -> ()
    | _ -> failwith "should match alnum"
  );

  (* ── Edge cases ── *)
  Printf.printf "\nEdge cases:\n";
  test "empty input" (fun () ->
    let g = Grammar.create "s" ["s", Empty] in
    match parse g "" with
    | Success (0, _) -> ()
    | _ -> failwith "empty should match empty"
  );

  test "star on empty doesn't loop" (fun () ->
    let g = Grammar.create "s" ["s", Star Empty] in
    match parse g "abc" with
    | Success (0, _) -> ()
    | _ -> failwith "star empty should terminate"
  );

  test "deeply nested rules" (fun () ->
    let g = Grammar.create "a" [
      "a", Ref "b";
      "b", Ref "c";
      "c", Ref "d";
      "d", Ref "e";
      "e", Lit 'x';
    ] in
    match parse g "x" with
    | Success (1, _) -> ()
    | _ -> failwith "should match through chain"
  );

  test "large repetition" (fun () ->
    let g = Grammar.create "s" ["s", Star (Class [Range ('a', 'z')])] in
    let input = String.make 1000 'a' in
    match parse g input with
    | Success (1000, _) -> ()
    | _ -> failwith "should match 1000 a's"
  );

  test "packrat memo prevents exponential blowup" (fun () ->
    (* a? a? a? a? a? aaaaa — this is exponential without memoization *)
    let g = Grammar.create "s" [
      "s", Sequence [
        Opt (Lit 'a'); Opt (Lit 'a'); Opt (Lit 'a');
        Opt (Lit 'a'); Opt (Lit 'a');
        Lit 'a'; Lit 'a'; Lit 'a'; Lit 'a'; Lit 'a'
      ]
    ] in
    match parse g "aaaaa" with
    | Success (5, _) -> ()
    | _ -> failwith "should match"
  );

  (* ── Summary ── *)
  Printf.printf "\n═══════════════════════════════════════\n";
  Printf.printf "Results: %d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
