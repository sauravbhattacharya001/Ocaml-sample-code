(* regex.ml — Regular Expression Engine
 *
 * A complete regex engine built from scratch in OCaml.
 * Uses Thompson's NFA construction for guaranteed linear-time matching
 * (no pathological backtracking).
 *
 * Concepts demonstrated:
 * - Algebraic data types (regex AST, NFA states)
 * - Recursive descent parsing (regex syntax → AST)
 * - Thompson's NFA construction (AST → NFA)
 * - NFA simulation via epsilon-closure (set-based, no backtracking)
 * - Functional state management with imperative optimizations
 * - Module design, API surface
 *
 * Supported syntax:
 *   .         any character
 *   \d \w \s  digit, word char, whitespace (and \D \W \S negated)
 *   [abc]     character class
 *   [a-z]     character range
 *   [^abc]    negated character class
 *   *         zero or more (greedy)
 *   +         one or more (greedy)
 *   ?         zero or one
 *   |         alternation
 *   (...)     grouping
 *   ^         start of string
 *   $         end of string
 *   \         escape special characters
 *
 * Usage:
 *   let r = compile "ab+c" in
 *   matches r "abbc"         → true
 *   matches r "ac"           → false
 *   find r "xxxabbcyyy"      → Some (3, "abbc")
 *   find_all r "abc abbc"    → ["abc"; "abbc"]
 *   replace r "abc" "X"      → "X"
 *   split r "xabcyabbcz"     → ["x"; "y"; "z"]
 *)

(* ============================================================ *)
(*                         REGEX AST                            *)
(* ============================================================ *)

(** Character matcher — what a single position can match *)
type char_matcher =
  | Lit of char          (** literal character *)
  | Dot                  (** any character (except newline) *)
  | Class of (char * char) list * bool
    (** character class: list of (lo, hi) ranges, negated flag *)

(** Regex AST *)
type regex =
  | Empty                (** empty string ε *)
  | Char of char_matcher (** single character match *)
  | Seq of regex * regex (** concatenation: r1 r2 *)
  | Alt of regex * regex (** alternation: r1 | r2 *)
  | Star of regex        (** Kleene star: r* *)
  | Plus of regex        (** one or more: r+ *)
  | Opt of regex         (** optional: r? *)
  | Anchor_start         (** ^ — matches start of string *)
  | Anchor_end           (** $ — matches end of string *)

(* ============================================================ *)
(*                        REGEX PARSER                          *)
(* ============================================================ *)

(** Parse a regex pattern string into an AST.
    Grammar (precedence low→high):
      expr   = seq ('|' seq)*
      seq    = quant+
      quant  = atom ('*' | '+' | '?')?
      atom   = char | '.' | class | '(' expr ')' | '^' | '$'
      class  = '[' '^'? (range | char)+ ']'
      range  = char '-' char
*)

exception Parse_error of string

let parse (pattern : string) : regex =
  let len = String.length pattern in
  let pos = ref 0 in

  let peek () = if !pos < len then Some pattern.[!pos] else None in
  let advance () = incr pos in
  let expect c =
    match peek () with
    | Some c' when c' = c -> advance ()
    | Some c' -> raise (Parse_error (Printf.sprintf "expected '%c', got '%c' at position %d" c c' !pos))
    | None -> raise (Parse_error (Printf.sprintf "expected '%c', got end of pattern" c))
  in

  (* Parse an escape sequence *)
  let parse_escape () =
    advance (); (* skip '\' *)
    match peek () with
    | None -> raise (Parse_error "unexpected end of pattern after '\\'")
    | Some c ->
      advance ();
      match c with
      | 'd' -> Char (Class ([('0', '9')], false))
      | 'D' -> Char (Class ([('0', '9')], true))
      | 'w' -> Char (Class ([('a', 'z'); ('A', 'Z'); ('0', '9'); ('_', '_')], false))
      | 'W' -> Char (Class ([('a', 'z'); ('A', 'Z'); ('0', '9'); ('_', '_')], true))
      | 's' -> Char (Class ([(' ', ' '); ('\t', '\t'); ('\n', '\n'); ('\r', '\r')], false))
      | 'S' -> Char (Class ([(' ', ' '); ('\t', '\t'); ('\n', '\n'); ('\r', '\r')], true))
      | 'n' -> Char (Lit '\n')
      | 't' -> Char (Lit '\t')
      | 'r' -> Char (Lit '\r')
      | _ -> Char (Lit c)
  in

  (* Parse a character class [...] *)
  let parse_class () =
    advance (); (* skip '[' *)
    let negated = match peek () with
      | Some '^' -> advance (); true
      | _ -> false
    in
    let ranges = ref [] in
    let first = ref true in
    while (match peek () with Some ']' when not !first -> false | Some _ -> true | None -> false) do
      first := false;
      match peek () with
      | None -> raise (Parse_error "unterminated character class")
      | Some '\\' ->
        advance ();
        (match peek () with
         | None -> raise (Parse_error "unexpected end in character class escape")
         | Some c -> advance (); ranges := (c, c) :: !ranges)
      | Some c ->
        advance ();
        (match peek () with
         | Some '-' ->
           let saved = !pos in
           advance ();
           (match peek () with
            | Some ']' ->
              pos := saved;
              ranges := (c, c) :: !ranges
            | Some c2 ->
              advance ();
              ranges := (c, c2) :: !ranges
            | None ->
              pos := saved;
              ranges := (c, c) :: !ranges)
         | _ -> ranges := (c, c) :: !ranges)
    done;
    expect ']';
    Char (Class (List.rev !ranges, negated))
  in

  let rec parse_expr () =
    let left = parse_seq () in
    match peek () with
    | Some '|' ->
      advance ();
      let right = parse_expr () in
      Alt (left, right)
    | _ -> left

  and parse_seq () =
    let terms = ref [] in
    let continues () =
      match peek () with
      | None | Some ')' | Some '|' -> false
      | _ -> true
    in
    while continues () do
      terms := parse_quant () :: !terms
    done;
    match List.rev !terms with
    | [] -> Empty
    | [t] -> t
    | first :: rest -> List.fold_left (fun acc t -> Seq (acc, t)) first rest

  and parse_quant () =
    let atom = parse_atom () in
    match peek () with
    | Some '*' -> advance (); Star atom
    | Some '+' -> advance (); Plus atom
    | Some '?' -> advance (); Opt atom
    | _ -> atom

  and parse_atom () =
    match peek () with
    | None -> raise (Parse_error "unexpected end of pattern")
    | Some '(' ->
      advance ();
      let inner = parse_expr () in
      expect ')';
      inner
    | Some '[' -> parse_class ()
    | Some '\\' -> parse_escape ()
    | Some '.' -> advance (); Char Dot
    | Some '^' -> advance (); Anchor_start
    | Some '$' -> advance (); Anchor_end
    | Some c when c <> ')' && c <> '|' && c <> '*' && c <> '+' && c <> '?' ->
      advance (); Char (Lit c)
    | Some c -> raise (Parse_error (Printf.sprintf "unexpected '%c' at position %d" c !pos))
  in

  let result = parse_expr () in
  if !pos <> len then
    raise (Parse_error (Printf.sprintf "unexpected character '%c' at position %d"
      pattern.[!pos] !pos));
  result

(* ============================================================ *)
(*                   THOMPSON'S NFA CONSTRUCTION                *)
(* ============================================================ *)

(** NFA transition *)
type nfa_transition =
  | Epsilon of int                   (** ε-transition to state *)
  | On_char of char_matcher * int    (** consume char, go to state *)
  | On_anchor_start of int           (** ^ check, go to state *)
  | On_anchor_end of int             (** $ check, go to state *)

(** NFA: states are identified by int ids.
    Each state has a list of transitions.
    There is one accepting state. *)
type nfa = {
  start: int;
  accept: int;
  transitions: nfa_transition list array;
  num_states: int;
}

(** NFA fragment: a piece of NFA with dangling accept state *)
type fragment = {
  frag_start: int;
  frag_accept: int;
}

(** Build an NFA from a regex AST using Thompson's construction *)
let build_nfa (r : regex) : nfa =
  let next_id = ref 0 in
  let new_state () =
    let id = !next_id in
    incr next_id;
    id
  in
  (* We'll collect transitions and build the array at the end *)
  let trans_table : (int * nfa_transition) list ref = ref [] in
  let add_trans src t =
    trans_table := (src, t) :: !trans_table
  in

  let rec build r =
    match r with
    | Empty ->
      let s = new_state () in
      let a = new_state () in
      add_trans s (Epsilon a);
      { frag_start = s; frag_accept = a }

    | Char matcher ->
      let s = new_state () in
      let a = new_state () in
      add_trans s (On_char (matcher, a));
      { frag_start = s; frag_accept = a }

    | Seq (r1, r2) ->
      let f1 = build r1 in
      let f2 = build r2 in
      add_trans f1.frag_accept (Epsilon f2.frag_start);
      { frag_start = f1.frag_start; frag_accept = f2.frag_accept }

    | Alt (r1, r2) ->
      let f1 = build r1 in
      let f2 = build r2 in
      let s = new_state () in
      let a = new_state () in
      add_trans s (Epsilon f1.frag_start);
      add_trans s (Epsilon f2.frag_start);
      add_trans f1.frag_accept (Epsilon a);
      add_trans f2.frag_accept (Epsilon a);
      { frag_start = s; frag_accept = a }

    | Star r1 ->
      let f = build r1 in
      let s = new_state () in
      let a = new_state () in
      add_trans s (Epsilon f.frag_start);
      add_trans s (Epsilon a);
      add_trans f.frag_accept (Epsilon f.frag_start);
      add_trans f.frag_accept (Epsilon a);
      { frag_start = s; frag_accept = a }

    | Plus r1 ->
      let f = build r1 in
      let s = new_state () in
      let a = new_state () in
      add_trans s (Epsilon f.frag_start);
      add_trans f.frag_accept (Epsilon f.frag_start);
      add_trans f.frag_accept (Epsilon a);
      { frag_start = s; frag_accept = a }

    | Opt r1 ->
      let f = build r1 in
      let s = new_state () in
      let a = new_state () in
      add_trans s (Epsilon f.frag_start);
      add_trans s (Epsilon a);
      add_trans f.frag_accept (Epsilon a);
      { frag_start = s; frag_accept = a }

    | Anchor_start ->
      let s = new_state () in
      let a = new_state () in
      add_trans s (On_anchor_start a);
      { frag_start = s; frag_accept = a }

    | Anchor_end ->
      let s = new_state () in
      let a = new_state () in
      add_trans s (On_anchor_end a);
      { frag_start = s; frag_accept = a }
  in

  let frag = build r in
  let n = !next_id in
  let arr = Array.make n [] in
  List.iter (fun (src, t) ->
    arr.(src) <- t :: arr.(src)
  ) !trans_table;
  { start = frag.frag_start; accept = frag.frag_accept;
    transitions = arr; num_states = n }


(* ============================================================ *)
(*                       NFA SIMULATION                         *)
(* ============================================================ *)

(** Does a character match a char_matcher? *)
let char_matches (m : char_matcher) (c : char) : bool =
  match m with
  | Lit expected -> c = expected
  | Dot -> c <> '\n'
  | Class (ranges, negated) ->
    let in_range = List.exists (fun (lo, hi) -> c >= lo && c <= hi) ranges in
    if negated then not in_range else in_range

(** Compute epsilon closure from a set of state ids.
    Follows all epsilon and anchor transitions. *)
let epsilon_closure (nfa : nfa) (state_ids : int list) (input : string) (str_pos : int) : int list =
  let visited = Hashtbl.create 16 in
  let result = ref [] in
  let rec explore id =
    if Hashtbl.mem visited id then ()
    else begin
      Hashtbl.replace visited id true;
      result := id :: !result;
      List.iter (fun t ->
        match t with
        | Epsilon target -> explore target
        | On_anchor_start target ->
          if str_pos = 0 then explore target
        | On_anchor_end target ->
          if str_pos = String.length input then explore target
        | On_char _ -> () (* handled during step *)
      ) nfa.transitions.(id)
    end
  in
  List.iter explore state_ids;
  !result

(** Simulate the NFA on input starting at str_pos.
    Returns the length of the longest match, or None. *)
let simulate_at (nfa : nfa) (input : string) (start_pos : int) : int option =
  let len = String.length input in
  let current = ref (epsilon_closure nfa [nfa.start] input start_pos) in
  let last_match = ref (if List.mem nfa.accept !current then Some 0 else None) in
  let i = ref start_pos in
  while !i < len && !current <> [] do
    let c = input.[!i] in
    let next = List.fold_left (fun acc state_id ->
      List.fold_left (fun acc2 t ->
        match t with
        | On_char (matcher, target) ->
          if char_matches matcher c then target :: acc2 else acc2
        | _ -> acc2
      ) acc nfa.transitions.(state_id)
    ) [] !current in
    incr i;
    current := epsilon_closure nfa next input !i;
    if List.mem nfa.accept !current then
      last_match := Some (!i - start_pos)
  done;
  !last_match


(* ============================================================ *)
(*                         PUBLIC API                           *)
(* ============================================================ *)

(** Compiled regex *)
type compiled = {
  pattern: string;
  ast: regex;
  nfa: nfa;
  anchored_start: bool;
}

(** Compile a regex pattern string *)
let compile (pattern : string) : compiled =
  let ast = parse pattern in
  let nfa = build_nfa ast in
  let anchored_start = match ast with
    | Anchor_start -> true
    | Seq (Anchor_start, _) -> true
    | _ -> false
  in
  { pattern; ast; nfa; anchored_start }

(** Test if the entire string matches the pattern *)
let matches (re : compiled) (input : string) : bool =
  match simulate_at re.nfa input 0 with
  | Some n -> n = String.length input
  | None -> false

(** Find the first match anywhere in the string.
    Returns Some (start_pos, matched_string) or None. *)
let find (re : compiled) (input : string) : (int * string) option =
  let len = String.length input in
  let i = ref 0 in
  let result = ref None in
  while !i <= len && !result = None do
    (match simulate_at re.nfa input !i with
     | Some match_len ->
       result := Some (!i, String.sub input !i match_len)
     | None -> ());
    if !result = None then (
      if re.anchored_start then i := len + 1  (* only try position 0 *)
      else incr i
    )
  done;
  !result

(** Find all non-overlapping matches in the string *)
let find_all (re : compiled) (input : string) : string list =
  let len = String.length input in
  let results = ref [] in
  let i = ref 0 in
  while !i <= len do
    match simulate_at re.nfa input !i with
    | Some match_len when match_len > 0 ->
      results := String.sub input !i match_len :: !results;
      i := !i + match_len
    | Some _ ->
      (* Zero-length match — skip to avoid infinite loop *)
      results := "" :: !results;
      incr i
    | None -> incr i
  done;
  List.rev !results

(** Replace all matches with the replacement string *)
let replace (re : compiled) (input : string) (replacement : string) : string =
  let len = String.length input in
  let buf = Buffer.create (String.length input) in
  let i = ref 0 in
  while !i <= len do
    match simulate_at re.nfa input !i with
    | Some match_len when match_len > 0 ->
      Buffer.add_string buf replacement;
      i := !i + match_len
    | Some _ ->
      Buffer.add_string buf replacement;
      if !i < len then Buffer.add_char buf input.[!i];
      incr i
    | None ->
      if !i < len then Buffer.add_char buf input.[!i];
      incr i
  done;
  Buffer.contents buf

(** Split string by regex matches *)
let split (re : compiled) (input : string) : string list =
  let len = String.length input in
  let parts = ref [] in
  let seg_start = ref 0 in
  let i = ref 0 in
  while !i <= len do
    match simulate_at re.nfa input !i with
    | Some match_len when match_len > 0 ->
      parts := String.sub input !seg_start (!i - !seg_start) :: !parts;
      i := !i + match_len;
      seg_start := !i
    | _ ->
      incr i
  done;
  parts := String.sub input !seg_start (len - !seg_start) :: !parts;
  List.rev !parts

(** Pretty-print the regex AST *)
let rec ast_to_string = function
  | Empty -> "ε"
  | Char (Lit c) -> String.make 1 c
  | Char Dot -> "."
  | Char (Class (ranges, negated)) ->
    let range_str = String.concat ""
      (List.map (fun (lo, hi) ->
        if lo = hi then String.make 1 lo
        else Printf.sprintf "%c-%c" lo hi
      ) ranges)
    in
    Printf.sprintf "[%s%s]" (if negated then "^" else "") range_str
  | Seq (r1, r2) -> ast_to_string r1 ^ ast_to_string r2
  | Alt (r1, r2) -> Printf.sprintf "(%s|%s)" (ast_to_string r1) (ast_to_string r2)
  | Star r -> Printf.sprintf "(%s)*" (ast_to_string r)
  | Plus r -> Printf.sprintf "(%s)+" (ast_to_string r)
  | Opt r -> Printf.sprintf "(%s)?" (ast_to_string r)
  | Anchor_start -> "^"
  | Anchor_end -> "$"


(* ============================================================ *)
(*                           DEMO                               *)
(* ============================================================ *)

let () =
  Printf.printf "=== Regular Expression Engine ===\n\n";

  (* Basic matching *)
  Printf.printf "--- Basic Matching ---\n";
  let r = compile "hello" in
  Printf.printf "matches \"hello\" \"hello\"   = %b\n" (matches r "hello");
  Printf.printf "matches \"hello\" \"world\"   = %b\n" (matches r "world");
  Printf.printf "matches \"hello\" \"hello!!\" = %b\n" (matches r "hello!!");

  (* Quantifiers *)
  Printf.printf "\n--- Quantifiers ---\n";
  let r2 = compile "ab+c" in
  Printf.printf "matches \"ab+c\" \"abc\"     = %b\n" (matches r2 "abc");
  Printf.printf "matches \"ab+c\" \"abbc\"    = %b\n" (matches r2 "abbc");
  Printf.printf "matches \"ab+c\" \"ac\"      = %b\n" (matches r2 "ac");
  Printf.printf "matches \"ab+c\" \"abbbbbc\" = %b\n" (matches r2 "abbbbbc");

  let r3 = compile "colou?r" in
  Printf.printf "matches \"colou?r\" \"color\"  = %b\n" (matches r3 "color");
  Printf.printf "matches \"colou?r\" \"colour\" = %b\n" (matches r3 "colour");

  let r4 = compile "ab*c" in
  Printf.printf "matches \"ab*c\" \"ac\"       = %b\n" (matches r4 "ac");
  Printf.printf "matches \"ab*c\" \"abbc\"     = %b\n" (matches r4 "abbc");

  (* Alternation *)
  Printf.printf "\n--- Alternation ---\n";
  let r5 = compile "cat|dog" in
  Printf.printf "matches \"cat|dog\" \"cat\" = %b\n" (matches r5 "cat");
  Printf.printf "matches \"cat|dog\" \"dog\" = %b\n" (matches r5 "dog");
  Printf.printf "matches \"cat|dog\" \"cow\" = %b\n" (matches r5 "cow");

  (* Dot and classes *)
  Printf.printf "\n--- Dot & Character Classes ---\n";
  let r6 = compile "h.t" in
  Printf.printf "matches \"h.t\" \"hat\"   = %b\n" (matches r6 "hat");
  Printf.printf "matches \"h.t\" \"hot\"   = %b\n" (matches r6 "hot");
  Printf.printf "matches \"h.t\" \"heart\" = %b\n" (matches r6 "heart");

  let r7 = compile "[aeiou]+" in
  Printf.printf "matches \"[aeiou]+\" \"aei\" = %b\n" (matches r7 "aei");
  Printf.printf "matches \"[aeiou]+\" \"xyz\" = %b\n" (matches r7 "xyz");

  let r8 = compile "[a-z]+" in
  Printf.printf "matches \"[a-z]+\" \"hello\" = %b\n" (matches r8 "hello");
  Printf.printf "matches \"[a-z]+\" \"HELLO\" = %b\n" (matches r8 "HELLO");

  (* Shorthand classes *)
  Printf.printf "\n--- Shorthand Classes ---\n";
  let r9 = compile "\\d+" in
  Printf.printf "matches \"\\\\d+\" \"123\"   = %b\n" (matches r9 "123");
  Printf.printf "matches \"\\\\d+\" \"abc\"   = %b\n" (matches r9 "abc");

  let r10 = compile "\\w+" in
  Printf.printf "matches \"\\\\w+\" \"hello\" = %b\n" (matches r10 "hello");
  Printf.printf "matches \"\\\\w+\" \"hi_42\" = %b\n" (matches r10 "hi_42");

  (* Find *)
  Printf.printf "\n--- Find ---\n";
  let r11 = compile "[0-9]+" in
  (match find r11 "abc 123 def 456" with
   | Some (pos, s) -> Printf.printf "find \"[0-9]+\" in \"abc 123 def 456\" = \"%s\" at %d\n" s pos
   | None -> Printf.printf "find: no match\n");

  (* Find all *)
  Printf.printf "\n--- Find All ---\n";
  let found = find_all r11 "abc 123 def 456 ghi" in
  Printf.printf "find_all \"[0-9]+\" in \"abc 123 def 456 ghi\" = [%s]\n"
    (String.concat "; " (List.map (fun s -> "\"" ^ s ^ "\"") found));

  let r12 = compile "[a-z]+" in
  let words = find_all r12 "hello world foo" in
  Printf.printf "find_all \"[a-z]+\" in \"hello world foo\" = [%s]\n"
    (String.concat "; " (List.map (fun s -> "\"" ^ s ^ "\"") words));

  (* Replace *)
  Printf.printf "\n--- Replace ---\n";
  let r13 = compile "[0-9]+" in
  Printf.printf "replace \"[0-9]+\" in \"abc 123 def 456\" with \"#\" = \"%s\"\n"
    (replace r13 "abc 123 def 456" "#");

  let r14 = compile "\\s+" in
  Printf.printf "replace \"\\\\s+\" in \"hello   world\" with \" \" = \"%s\"\n"
    (replace r14 "hello   world" " ");

  (* Split *)
  Printf.printf "\n--- Split ---\n";
  let r15 = compile "[,;]\\s*" in
  let parts = split r15 "apple, banana; cherry,date" in
  Printf.printf "split \"[,;]\\\\s*\" \"apple, banana; cherry,date\" = [%s]\n"
    (String.concat "; " (List.map (fun s -> "\"" ^ s ^ "\"") parts));

  (* Anchors *)
  Printf.printf "\n--- Anchors ---\n";
  let r16 = compile "^hello" in
  (match find r16 "hello world" with
   | Some (_, s) -> Printf.printf "find \"^hello\" in \"hello world\" = \"%s\"\n" s
   | None -> Printf.printf "find \"^hello\" = no match\n");
  (match find r16 "say hello" with
   | Some (_, s) -> Printf.printf "find \"^hello\" in \"say hello\"   = \"%s\"\n" s
   | None -> Printf.printf "find \"^hello\" in \"say hello\"   = no match\n");

  let r17 = compile "world$" in
  Printf.printf "matches \"world$\" \"hello world\" = %b\n"
    (match find r17 "hello world" with Some _ -> true | None -> false);

  (* Negated class *)
  Printf.printf "\n--- Negated Classes ---\n";
  let r18 = compile "[^0-9]+" in
  Printf.printf "matches \"[^0-9]+\" \"hello\" = %b\n" (matches r18 "hello");
  Printf.printf "matches \"[^0-9]+\" \"123\"   = %b\n" (matches r18 "123");

  (* AST display *)
  Printf.printf "\n--- AST Display ---\n";
  Printf.printf "AST of \"ab+c\"     = %s\n" (ast_to_string (parse "ab+c"));
  Printf.printf "AST of \"cat|dog\"  = %s\n" (ast_to_string (parse "cat|dog"));
  Printf.printf "AST of \"[a-z]+\"   = %s\n" (ast_to_string (parse "[a-z]+"));
  Printf.printf "AST of \"colou?r\"  = %s\n" (ast_to_string (parse "colou?r"));

  Printf.printf "\nDone.\n"
