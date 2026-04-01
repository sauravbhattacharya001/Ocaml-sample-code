(* forth.ml - A Forth interpreter in OCaml
 *
 * Implements a stack-based Forth-like language with:
 * - Arithmetic: + - * / mod
 * - Stack manipulation: dup drop swap over rot nip tuck
 * - Comparison: = < > <> <= >=
 * - Logic: and or not (invert)
 * - Control flow: if...else...then, begin...until, begin...while...repeat
 * - Definitions: : name ... ;
 * - Variables & constants: variable, constant, ! @ +!
 * - String output: ." ... "  .( ... )
 * - I/O: . cr emit space spaces
 * - Stack display: .s
 * - Loops: do...loop, do...+loop, with i j access
 * - Comments: ( ... ) and \ to end of line
 * - See (decompile): see word
 *)

(* ===== Core Types ===== *)

type value =
  | VInt of int
  | VBool of bool
  | VString of string
  | VAddr of int  (* memory address *)

type word_def =
  | Primitive of (state -> state)
  | Compiled of token list
  | Variable of int   (* address in memory *)
  | Constant of int

and token =
  | TLit of value
  | TWord of string
  | TIf
  | TElse
  | TThen
  | TBegin
  | TUntil
  | TWhile
  | TRepeat
  | TDo
  | TLoop
  | TPlusLoop
  | TI
  | TJ
  | TStringLit of string
  | TDotParen of string

and state = {
  stack : value list;
  rstack : int list;       (* return/loop stack *)
  dict : (string * word_def) list;
  memory : (int, int) Hashtbl.t;
  next_addr : int;
  output : string list;    (* reversed output buffer *)
  compiling : bool;
  current_def : string;
  compile_buf : token list;
  loop_stack : (int * int) list;  (* do..loop: index, limit *)
}

(* ===== Helpers ===== *)

let empty_state () = {
  stack = [];
  rstack = [];
  dict = [];
  memory = Hashtbl.create 64;
  next_addr = 100;
  output = [];
  compiling = false;
  current_def = "";
  compile_buf = [];
  loop_stack = [];
}

let push v st = { st with stack = v :: st.stack }
let push_int n st = push (VInt n) st
let push_bool b st = push (VBool b) st

let pop st =
  match st.stack with
  | [] -> failwith "Stack underflow"
  | x :: rest -> (x, { st with stack = rest })

let pop_int st =
  let (v, st') = pop st in
  match v with
  | VInt n -> (n, st')
  | VBool b -> (if b then -1 else 0), st'
  | _ -> failwith "Expected integer on stack"

let pop2_int st =
  let (b, st1) = pop_int st in
  let (a, st2) = pop_int st1 in
  (a, b, st2)

let emit_str s st = { st with output = s :: st.output }
let emit_int n st = emit_str (string_of_int n) st

let value_to_string = function
  | VInt n -> string_of_int n
  | VBool b -> if b then "-1" else "0"
  | VString s -> s
  | VAddr a -> Printf.sprintf "<addr:%d>" a

let value_to_int = function
  | VInt n -> n
  | VBool b -> if b then -1 else 0
  | _ -> failwith "Expected integer"

let is_truthy = function
  | VInt 0 -> false
  | VBool false -> false
  | _ -> true

(* ===== Primitives ===== *)

let prim_add st = let (a, b, st') = pop2_int st in push_int (a + b) st'
let prim_sub st = let (a, b, st') = pop2_int st in push_int (a - b) st'
let prim_mul st = let (a, b, st') = pop2_int st in push_int (a * b) st'
let prim_div st = let (a, b, st') = pop2_int st in
  if b = 0 then failwith "Division by zero" else push_int (a / b) st'
let prim_mod st = let (a, b, st') = pop2_int st in
  if b = 0 then failwith "Division by zero" else push_int (a mod b) st'

let prim_dot st =
  let (v, st') = pop st in
  emit_str (value_to_string v ^ " ") st'

let prim_cr st = emit_str "\n" st
let prim_space st = emit_str " " st
let prim_spaces st =
  let (n, st') = pop_int st in
  emit_str (String.make (max 0 n) ' ') st'

let prim_emit st =
  let (n, st') = pop_int st in
  emit_str (String.make 1 (Char.chr (n land 255))) st'

let prim_dup st =
  match st.stack with
  | [] -> failwith "Stack underflow"
  | x :: _ -> push x st

let prim_drop st = let (_, st') = pop st in st'

let prim_swap st =
  match st.stack with
  | a :: b :: rest -> { st with stack = b :: a :: rest }
  | _ -> failwith "Stack underflow"

let prim_over st =
  match st.stack with
  | _ :: b :: _ -> push b st
  | _ -> failwith "Stack underflow"

let prim_rot st =
  match st.stack with
  | c :: b :: a :: rest -> { st with stack = a :: c :: b :: rest }
  | _ -> failwith "Stack underflow"

let prim_nip st =
  match st.stack with
  | a :: _ :: rest -> { st with stack = a :: rest }
  | _ -> failwith "Stack underflow"

let prim_tuck st =
  match st.stack with
  | a :: b :: rest -> { st with stack = a :: b :: a :: rest }
  | _ -> failwith "Stack underflow"

let prim_eq st = let (a, b, st') = pop2_int st in push_bool (a = b) st'
let prim_lt st = let (a, b, st') = pop2_int st in push_bool (a < b) st'
let prim_gt st = let (a, b, st') = pop2_int st in push_bool (a > b) st'
let prim_ne st = let (a, b, st') = pop2_int st in push_bool (a <> b) st'
let prim_le st = let (a, b, st') = pop2_int st in push_bool (a <= b) st'
let prim_ge st = let (a, b, st') = pop2_int st in push_bool (a >= b) st'

let prim_and st =
  let (a, b, st') = pop2_int st in push_int (a land b) st'
let prim_or st =
  let (a, b, st') = pop2_int st in push_int (a lor b) st'
let prim_invert st =
  let (n, st') = pop_int st in push_int (lnot n) st'
let prim_negate st =
  let (n, st') = pop_int st in push_int (-n) st'
let prim_abs st =
  let (n, st') = pop_int st in push_int (abs n) st'
let prim_max st =
  let (a, b, st') = pop2_int st in push_int (max a b) st'
let prim_min st =
  let (a, b, st') = pop2_int st in push_int (min a b) st'

let prim_store st =
  let (addr, st1) = pop_int st in
  let (val_, st2) = pop_int st1 in
  Hashtbl.replace st2.memory addr val_;
  st2

let prim_fetch st =
  let (addr, st') = pop_int st in
  let v = try Hashtbl.find st'.memory addr with Not_found -> 0 in
  push_int v st'

let prim_plus_store st =
  let (addr, st1) = pop_int st in
  let (delta, st2) = pop_int st1 in
  let cur = try Hashtbl.find st2.memory addr with Not_found -> 0 in
  Hashtbl.replace st2.memory addr (cur + delta);
  st2

let prim_dot_s st =
  let items = List.rev st.stack in
  let s = Printf.sprintf "<%d> %s"
    (List.length st.stack)
    (String.concat " " (List.map value_to_string items))
  in
  emit_str s st

let prim_depth st =
  push_int (List.length st.stack) st

let prim_2dup st =
  match st.stack with
  | a :: b :: _ -> { st with stack = a :: b :: a :: b :: (List.tl (List.tl st.stack)) }
  | _ -> failwith "Stack underflow"

let prim_2drop st =
  match st.stack with
  | _ :: _ :: rest -> { st with stack = rest }
  | _ -> failwith "Stack underflow"

let prim_2swap st =
  match st.stack with
  | a :: b :: c :: d :: rest -> { st with stack = c :: d :: a :: b :: rest }
  | _ -> failwith "Stack underflow"

let prim_qdup st =
  match st.stack with
  | (VInt 0) :: _ | (VBool false) :: _ -> st
  | x :: _ -> push x st
  | [] -> failwith "Stack underflow"

(* ===== Dictionary ===== *)

let base_dict = [
  "+", Primitive prim_add;
  "-", Primitive prim_sub;
  "*", Primitive prim_mul;
  "/", Primitive prim_div;
  "mod", Primitive prim_mod;
  ".", Primitive prim_dot;
  "cr", Primitive prim_cr;
  "space", Primitive prim_space;
  "spaces", Primitive prim_spaces;
  "emit", Primitive prim_emit;
  "dup", Primitive prim_dup;
  "drop", Primitive prim_drop;
  "swap", Primitive prim_swap;
  "over", Primitive prim_over;
  "rot", Primitive prim_rot;
  "nip", Primitive prim_nip;
  "tuck", Primitive prim_tuck;
  "=", Primitive prim_eq;
  "<", Primitive prim_lt;
  ">", Primitive prim_gt;
  "<>", Primitive prim_ne;
  "<=", Primitive prim_le;
  ">=", Primitive prim_ge;
  "and", Primitive prim_and;
  "or", Primitive prim_or;
  "invert", Primitive prim_invert;
  "negate", Primitive prim_negate;
  "abs", Primitive prim_abs;
  "max", Primitive prim_max;
  "min", Primitive prim_min;
  "!", Primitive prim_store;
  "@", Primitive prim_fetch;
  "+!", Primitive prim_plus_store;
  ".s", Primitive prim_dot_s;
  "depth", Primitive prim_depth;
  "2dup", Primitive prim_2dup;
  "2drop", Primitive prim_2drop;
  "2swap", Primitive prim_2swap;
  "?dup", Primitive prim_qdup;
  "true", Constant (-1);
  "false", Constant 0;
]

let find_word name dict =
  let lname = String.lowercase_ascii name in
  try Some (List.assoc lname dict)
  with Not_found -> None

(* ===== Tokenizer ===== *)

type scan_result =
  | SToken of token * string  (* token, remaining input *)
  | SDefStart of string       (* signal to start compiling *)
  | SDefEnd                   (* signal to end compiling *)
  | SVarDecl of string        (* variable name *)
  | SConstDecl of string      (* constant name *)
  | SSeeWord of string        (* see target *)
  | SSkip of string           (* skip, remaining *)
  | SDone

let skip_ws s =
  let len = String.length s in
  let i = ref 0 in
  while !i < len && (s.[!i] = ' ' || s.[!i] = '\t' || s.[!i] = '\n' || s.[!i] = '\r') do
    incr i
  done;
  if !i >= len then "" else String.sub s !i (len - !i)

let next_word s =
  let s = skip_ws s in
  if String.length s = 0 then None
  else
    let len = String.length s in
    let i = ref 0 in
    while !i < len && s.[!i] <> ' ' && s.[!i] <> '\t' && s.[!i] <> '\n' && s.[!i] <> '\r' do
      incr i
    done;
    let w = String.sub s 0 !i in
    let rest = if !i >= len then "" else String.sub s !i (len - !i) in
    Some (w, rest)

let extract_string_until delim s =
  (* Find delim in s, return (content, rest_after_delim) *)
  try
    let pos = ref 0 in
    let dlen = String.length delim in
    let slen = String.length s in
    let found = ref false in
    while !pos <= slen - dlen && not !found do
      if String.sub s !pos dlen = delim then found := true
      else incr pos
    done;
    if !found then
      let content = String.sub s 0 !pos in
      let rest = if !pos + dlen >= slen then "" else String.sub s (!pos + dlen) (slen - !pos - dlen) in
      Some (content, rest)
    else None
  with _ -> None

let scan_token s =
  let s = skip_ws s in
  if String.length s = 0 then SDone
  else
    match next_word s with
    | None -> SDone
    | Some (w, rest) ->
      let lw = String.lowercase_ascii w in
      match lw with
      | ":" ->
        (* Next word is the name *)
        (match next_word rest with
         | None -> failwith "Expected word name after :"
         | Some (name, rest2) -> SDefStart (String.lowercase_ascii name))
      | ";" -> SDefEnd
      | "if" -> SToken (TIf, rest)
      | "else" -> SToken (TElse, rest)
      | "then" -> SToken (TThen, rest)
      | "begin" -> SToken (TBegin, rest)
      | "until" -> SToken (TUntil, rest)
      | "while" -> SToken (TWhile, rest)
      | "repeat" -> SToken (TRepeat, rest)
      | "do" -> SToken (TDo, rest)
      | "loop" -> SToken (TLoop, rest)
      | "+loop" -> SToken (TPlusLoop, rest)
      | "i" -> SToken (TI, rest)
      | "j" -> SToken (TJ, rest)
      | "variable" ->
        (match next_word rest with
         | None -> failwith "Expected variable name"
         | Some (name, rest2) -> SVarDecl (String.lowercase_ascii name))
      | "constant" ->
        (match next_word rest with
         | None -> failwith "Expected constant name"
         | Some (name, rest2) -> SConstDecl (String.lowercase_ascii name))
      | "see" ->
        (match next_word rest with
         | None -> failwith "Expected word name after see"
         | Some (name, rest2) -> SSeeWord (String.lowercase_ascii name))
      | "\\" ->
        (* Line comment - skip to end of line *)
        let len = String.length rest in
        let i = ref 0 in
        while !i < len && rest.[!i] <> '\n' do incr i done;
        let r = if !i >= len then "" else String.sub rest (!i+1) (len - !i - 1) in
        SSkip r
      | "(" ->
        (* Block comment *)
        (match extract_string_until ")" rest with
         | Some (_, rest2) -> SSkip rest2
         | None -> failwith "Unterminated comment")
      | ".\"" ->
        (* String literal: ." text" *)
        (match extract_string_until "\"" rest with
         | Some (content, rest2) ->
           let content = if String.length content > 0 && content.[0] = ' ' then String.sub content 1 (String.length content - 1) else content in
           SToken (TStringLit content, rest2)
         | None -> failwith "Unterminated string literal")
      | ".(" ->
        (match extract_string_until ")" rest with
         | Some (content, rest2) ->
           let content = if String.length content > 0 && content.[0] = ' ' then String.sub content 1 (String.length content - 1) else content in
           SToken (TDotParen content, rest2)
         | None -> failwith "Unterminated .( string")
      | _ ->
        (* Try parsing as number *)
        (try
           let n = int_of_string w in
           SToken (TLit (VInt n), rest)
         with Failure _ ->
           SToken (TWord lw, rest))

(* Tokenize entire input for compilation *)
let rec tokenize_rest s acc =
  match scan_token s with
  | SDone -> List.rev acc
  | SDefEnd -> List.rev acc  (* ; encountered *)
  | SToken (tok, rest) -> tokenize_rest rest (tok :: acc)
  | SSkip rest -> tokenize_rest rest acc
  | _ -> failwith "Unexpected directive inside definition"

(* ===== Interpreter ===== *)

(* Execute a compiled token list *)
let rec exec_tokens tokens st =
  match tokens with
  | [] -> st
  | tok :: rest ->
    match tok with
    | TLit v -> exec_tokens rest (push v st)
    | TStringLit s -> exec_tokens rest (emit_str s st)
    | TDotParen s -> exec_tokens rest (emit_str s st)
    | TWord name ->
      let st' = exec_word name st in
      exec_tokens rest st'
    | TIf ->
      let (v, st') = pop st in
      if is_truthy v then
        (* Execute true branch, skip to else or then *)
        let (true_branch, after) = split_if_else rest 0 in
        let st'' = exec_tokens true_branch st' in
        exec_tokens after st''
      else
        (* Skip to else or then *)
        let (_, after) = split_if_else rest 0 in
        (* Check if we hit else or then *)
        let (false_branch, after2) = find_else_branch rest 0 in
        let st'' = exec_tokens false_branch st' in
        exec_tokens after2 st''
    | TBegin ->
      exec_begin rest st
    | TDo ->
      let (limit, st1) = pop_int st in
      let (index, st2) = pop_int st1 in
      let st3 = { st2 with loop_stack = (index, limit) :: st2.loop_stack } in
      exec_do rest st3
    | TI ->
      (match st.loop_stack with
       | (i, _) :: _ -> exec_tokens rest (push_int i st)
       | [] -> failwith "I outside do..loop")
    | TJ ->
      (match st.loop_stack with
       | _ :: (j, _) :: _ -> exec_tokens rest (push_int j st)
       | _ -> failwith "J needs nested do..loop")
    | _ -> failwith (Printf.sprintf "Unexpected control token")

and exec_word name st =
  match find_word name st.dict with
  | Some (Primitive f) -> f st
  | Some (Compiled body) -> exec_tokens body st
  | Some (Variable addr) -> push_int addr st
  | Some (Constant v) -> push_int v st
  | None -> failwith (Printf.sprintf "Unknown word: %s" name)

and split_if_else tokens depth =
  (* Returns (true_branch, after_then). Stops at ELSE or THEN at depth 0 *)
  match tokens with
  | [] -> ([], [])
  | TIf :: rest ->
    let (branch, after) = split_if_else rest (depth + 1) in
    (TIf :: branch, after)
  | TThen :: rest when depth = 0 -> ([], rest)
  | TElse :: rest when depth = 0 -> ([], rest)
  | TThen :: rest ->
    let (branch, after) = split_if_else rest (depth - 1) in
    (TThen :: branch, after)
  | tok :: rest ->
    let (branch, after) = split_if_else rest depth in
    (tok :: branch, after)

and find_else_branch tokens depth =
  (* If we're in the false branch (after skipping true), find content between else..then *)
  match tokens with
  | [] -> ([], [])
  | TIf :: rest ->
    (* Skip nested if *)
    let (inner, after_inner) = skip_to_then rest 0 in
    find_else_branch after_inner depth
  | TElse :: rest when depth = 0 ->
    (* Found else at our level - collect until then *)
    collect_until_then rest 0
  | TThen :: rest when depth = 0 -> ([], rest)
  | _ :: rest -> find_else_branch rest depth

and skip_to_then tokens depth =
  match tokens with
  | [] -> ([], [])
  | TIf :: rest -> skip_to_then rest (depth + 1)
  | TThen :: rest when depth = 0 -> ([], rest)
  | TThen :: rest -> skip_to_then rest (depth - 1)
  | _ :: rest -> skip_to_then rest depth

and collect_until_then tokens depth =
  match tokens with
  | [] -> ([], [])
  | TIf :: rest ->
    let (inner, after) = collect_until_then rest (depth + 1) in
    (TIf :: inner, after)
  | TThen :: rest when depth = 0 -> ([], rest)
  | TThen :: rest ->
    let (inner, after) = collect_until_then rest (depth - 1) in
    (TThen :: inner, after)
  | tok :: rest ->
    let (inner, after) = collect_until_then rest depth in
    (tok :: inner, after)

and exec_begin tokens st =
  (* Find the loop body and type *)
  let (body, loop_type, after) = find_begin_end tokens in
  match loop_type with
  | `Until ->
    let rec go st' =
      let st'' = exec_tokens body st' in
      let (v, st3) = pop st'' in
      if is_truthy v then exec_tokens after st3
      else go st3
    in go st
  | `WhileRepeat (while_body, repeat_body) ->
    let rec go st' =
      let st'' = exec_tokens while_body st' in
      let (v, st3) = pop st'' in
      if is_truthy v then
        let st4 = exec_tokens repeat_body st3 in
        go st4
      else exec_tokens after st3
    in go st

and find_begin_end tokens =
  (* Collect tokens until UNTIL or WHILE...REPEAT *)
  let rec collect acc = function
    | [] -> failwith "Unterminated begin"
    | TUntil :: rest -> (List.rev acc, `Until, rest)
    | TWhile :: rest ->
      let pre_while = List.rev acc in
      let (post_while, rest2) = collect_repeat rest [] in
      (pre_while, `WhileRepeat (pre_while, post_while), rest2)
    | tok :: rest -> collect (tok :: acc) rest
  and collect_repeat tokens acc =
    match tokens with
    | [] -> failwith "Unterminated while..repeat"
    | TRepeat :: rest -> (List.rev acc, rest)
    | tok :: rest -> collect_repeat rest (tok :: acc)
  in
  collect [] tokens

and exec_do body_and_rest st =
  (* Find do body (until LOOP or +LOOP) *)
  let rec find_loop acc = function
    | [] -> failwith "Unterminated do..loop"
    | TLoop :: rest -> (List.rev acc, false, rest)
    | TPlusLoop :: rest -> (List.rev acc, true, rest)
    | tok :: rest -> find_loop (tok :: acc) rest
  in
  let (body, is_plus, after) = find_loop [] body_and_rest in
  let rec go st' =
    match st'.loop_stack with
    | (i, limit) :: outer ->
      if i >= limit then
        exec_tokens after { st' with loop_stack = outer }
      else
        let st'' = exec_tokens body st' in
        let step =
          if is_plus then
            let (s, st3) = pop_int st'' in
            (s, st3)
          else (1, st'')
        in
        let (step_val, st3) = step in
        let new_i = (match st3.loop_stack with (ci, _) :: _ -> ci | _ -> i) + step_val in
        go { st3 with loop_stack = (new_i, limit) :: (List.tl st3.loop_stack) }
    | [] -> failwith "Loop stack underflow"
  in go st

(* ===== See (decompile) ===== *)

let token_to_string = function
  | TLit v -> value_to_string v
  | TWord w -> w
  | TIf -> "if"
  | TElse -> "else"
  | TThen -> "then"
  | TBegin -> "begin"
  | TUntil -> "until"
  | TWhile -> "while"
  | TRepeat -> "repeat"
  | TDo -> "do"
  | TLoop -> "loop"
  | TPlusLoop -> "+loop"
  | TI -> "i"
  | TJ -> "j"
  | TStringLit s -> Printf.sprintf ".\" %s\"" s
  | TDotParen s -> Printf.sprintf ".( %s)" s

let see_word name st =
  match find_word name st.dict with
  | Some (Primitive _) -> emit_str (Printf.sprintf "%s is a primitive\n" name) st
  | Some (Compiled body) ->
    let s = Printf.sprintf ": %s %s ;\n" name
      (String.concat " " (List.map token_to_string body))
    in emit_str s st
  | Some (Variable addr) ->
    emit_str (Printf.sprintf "%s is a variable at address %d\n" name addr) st
  | Some (Constant v) ->
    emit_str (Printf.sprintf "%s is a constant = %d\n" name v) st
  | None -> emit_str (Printf.sprintf "%s is undefined\n" name) st

(* ===== Main Interpreter Loop ===== *)

let rec interpret input st =
  match scan_token input with
  | SDone -> st
  | SSkip rest -> interpret rest st
  | SDefStart name ->
    (* Compile mode *)
    let tokens = tokenize_rest (skip_ws (snd (Option.get (next_word input)))) [] in
    (* We need the rest after ; *)
    let rest = skip_past_semicolon input in
    let st' = { st with dict = (name, Compiled tokens) :: st.dict } in
    interpret rest st'
  | SDefEnd ->
    failwith "; without matching :"
  | SVarDecl name ->
    let addr = st.next_addr in
    let rest = skip_past_word_arg input in
    let st' = { st with
      dict = (name, Variable addr) :: st.dict;
      next_addr = addr + 1;
    } in
    Hashtbl.replace st'.memory addr 0;
    interpret rest st'
  | SConstDecl name ->
    let (v, st1) = pop_int st in
    let rest = skip_past_word_arg input in
    let st' = { st1 with dict = (name, Constant v) :: st1.dict } in
    interpret rest st'
  | SSeeWord name ->
    let rest = skip_past_word_arg input in
    interpret rest (see_word name st)
  | SToken (tok, rest) ->
    let st' = exec_tokens [tok] st in
    interpret rest st'

and skip_past_semicolon input =
  (* Skip input until we find ; then return rest *)
  let rec go s =
    match next_word s with
    | None -> ""
    | Some (w, rest) ->
      if w = ";" then rest
      else go rest
  in
  (* Skip past : and name first *)
  match next_word input with
  | None -> ""
  | Some (_, rest) ->  (* skip : *)
    match next_word rest with
    | None -> ""
    | Some (_, rest2) -> go rest2  (* skip name, then find ; *)

and skip_past_word_arg input =
  (* Skip the keyword and its argument *)
  match next_word input with
  | None -> ""
  | Some (_, rest) ->
    match next_word rest with
    | None -> ""
    | Some (_, rest2) -> rest2

(* ===== Public API ===== *)

let create () =
  let st = empty_state () in
  { st with dict = List.map (fun (k, v) -> (String.lowercase_ascii k, v)) base_dict }

let eval input st =
  let st' = interpret input st in
  let output = String.concat "" (List.rev st'.output) in
  (output, { st' with output = [] })

let eval_print input st =
  let (output, st') = eval input st in
  if String.length output > 0 then print_string output;
  st'

(* ===== Demo & Tests ===== *)

let () =
  print_endline "=== OCaml Forth Interpreter ===\n";

  let st = create () in

  (* Basic arithmetic *)
  print_string "Basic arithmetic: ";
  let st = eval_print "3 4 + ." st in
  let st = eval_print "10 3 - ." st in
  let st = eval_print "6 7 * ." st in
  let _ = eval_print "cr" st in

  (* Stack operations *)
  let st = create () in
  print_string "Stack ops: ";
  let st = eval_print "1 2 3 .s" st in
  let st = eval_print "cr swap .s cr" st in

  (* Word definitions *)
  let st = create () in
  print_string "Definitions:\n";
  let st = eval_print ": square dup * ;" st in
  let st = eval_print "5 square . cr" st in
  let st = eval_print ": cube dup dup * * ;" st in
  let st = eval_print "3 cube . cr" st in

  (* Factorial *)
  let st = create () in
  print_string "Factorial:\n";
  let st = eval_print ": factorial dup 1 > if dup 1 - factorial * then ;" st in
  let st = eval_print "5 factorial . cr" st in
  let st = eval_print "10 factorial . cr" st in

  (* Fibonacci using variables *)
  let st = create () in
  print_string "Variables:\n";
  let st = eval_print "variable counter" st in
  let st = eval_print "42 counter !" st in
  let st = eval_print "counter @ . cr" st in
  let st = eval_print "10 counter +!" st in
  let st = eval_print "counter @ . cr" st in

  (* Constants *)
  let st = create () in
  print_string "Constants:\n";
  let st = eval_print "100 constant max-val" st in
  let st = eval_print "max-val . cr" st in

  (* If/else *)
  let st = create () in
  print_string "Conditionals:\n";
  let st = eval_print ": check dup 0 > if .\" positive\" else .\" non-positive\" then cr ;" st in
  let st = eval_print "5 check" st in
  let st = eval_print "-3 check" st in

  (* Do loop *)
  let st = create () in
  print_string "Do loop: ";
  let st = eval_print ": stars 0 do 42 emit loop ;" st in
  let st = eval_print "10 stars cr" st in

  (* Begin..until loop *)
  let st = create () in
  print_string "Begin..until: ";
  let st = eval_print ": countdown begin dup . 1 - dup 0 = until drop cr ;" st in
  let st = eval_print "5 countdown" st in

  (* FizzBuzz *)
  let st = create () in
  print_string "FizzBuzz (1-20):\n";
  let st = eval_print ": fizzbuzz 1 + 1 do i 15 mod 0 = if .\" FizzBuzz\" else i 3 mod 0 = if .\" Fizz\" else i 5 mod 0 = if .\" Buzz\" else i . then then then .\"  \" loop cr ;" st in
  let st = eval_print "20 fizzbuzz" st in

  (* String output *)
  let st = create () in
  print_string "Strings: ";
  let st = eval_print ".\" Hello, Forth world!\" cr" st in

  (* See / decompile *)
  let st = create () in
  print_string "See:\n";
  let st = eval_print ": triple 3 * ;" st in
  let st = eval_print "see triple" st in
  let st = eval_print "see +" st in

  (* Nested definitions *)
  let st = create () in
  print_string "Composition:\n";
  let st = eval_print ": double 2 * ;" st in
  let st = eval_print ": quadruple double double ;" st in
  let st = eval_print "7 quadruple . cr" st in

  (* Power *)
  let st = create () in
  let st = eval_print ": pow 1 swap 0 do over * loop swap drop ;" st in
  print_string "2^10 = ";
  let _ = eval_print "2 10 pow . cr" st in

  print_endline "\n=== All demos complete ==="
