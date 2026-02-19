(* Parser Combinators — Building Parsers from Small Pieces *)
(* Demonstrates: higher-order functions, closures, algebraic data types,
   monadic composition (bind/map/return), recursive descent, operator precedence,
   polymorphism, partial application, function composition *)

(* A parser combinator library lets you build complex parsers by snapping
   together small, reusable parser functions. Each parser is a function
   that takes an input string and position, and returns either a parsed
   value + new position, or a failure message.

   This is a quintessential functional programming pattern — parsers are
   first-class values that can be passed around, combined, and composed
   just like any other function. *)

(* --- Core types --- *)

(* A parse result is either success (value + remaining position)
   or failure (error message + position where it failed) *)
type 'a result =
  | Ok of 'a * int      (* parsed value, new position *)
  | Error of string * int  (* error message, error position *)

(* A parser is a function: string -> position -> result *)
type 'a parser = string -> int -> 'a result

(* --- Primitive parsers --- *)

(* Parse a single character satisfying a predicate *)
let satisfy (pred : char -> bool) (desc : string) : char parser =
  fun input pos ->
    if pos >= String.length input then
      Error (Printf.sprintf "unexpected end of input, expected %s" desc, pos)
    else
      let c = input.[pos] in
      if pred c then Ok (c, pos + 1)
      else Error (Printf.sprintf "expected %s, got '%c'" desc c, pos)

(* Parse a specific character *)
let char_ (expected : char) : char parser =
  satisfy (fun c -> c = expected) (Printf.sprintf "'%c'" expected)

(* Parse a specific string *)
let string_ (expected : string) : string parser =
  fun input pos ->
    let len = String.length expected in
    if pos + len > String.length input then
      Error (Printf.sprintf "expected \"%s\", unexpected end of input" expected, pos)
    else
      let sub = String.sub input pos len in
      if sub = expected then Ok (expected, pos + len)
      else Error (Printf.sprintf "expected \"%s\", got \"%s\"" expected sub, pos)

(* Parse any single character *)
let any_char : char parser =
  satisfy (fun _ -> true) "any character"

(* Parse a digit character *)
let digit : char parser =
  satisfy (fun c -> c >= '0' && c <= '9') "digit"

(* Parse a letter (a-z, A-Z) *)
let letter : char parser =
  satisfy (fun c -> (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) "letter"

(* Parse a whitespace character *)
let whitespace : char parser =
  satisfy (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r') "whitespace"

(* Always succeed with a value (monadic return) *)
let return_ (x : 'a) : 'a parser =
  fun _input pos -> Ok (x, pos)

(* Always fail with a message *)
let fail (msg : string) : 'a parser =
  fun _input pos -> Error (msg, pos)

(* --- Combinators (the heart of the library) --- *)

(* Sequencing: run parser A, then feed its result to a function
   that produces parser B (monadic bind).
   This is the >>= operator in Haskell. *)
let bind (p : 'a parser) (f : 'a -> 'b parser) : 'b parser =
  fun input pos ->
    match p input pos with
    | Error (msg, epos) -> Error (msg, epos)
    | Ok (a, pos') -> (f a) input pos'

(* Operator for bind: p >>= f *)
let ( >>= ) = bind

(* Sequence two parsers, keep the result of the second *)
let ( *> ) (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  p1 >>= fun _ -> p2

(* Sequence two parsers, keep the result of the first *)
let ( <* ) (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  p1 >>= fun a -> p2 >>= fun _ -> return_ a

(* Transform the result of a parser (functor map) *)
let map (f : 'a -> 'b) (p : 'a parser) : 'b parser =
  p >>= fun a -> return_ (f a)

(* Operator for map: f <$> p *)
let ( <$> ) = map

(* Apply: run a parser that produces a function, then a parser
   that produces an argument, apply the function *)
let ( <*> ) (pf : ('a -> 'b) parser) (pa : 'a parser) : 'b parser =
  pf >>= fun f -> pa >>= fun a -> return_ (f a)

(* Choice: try parser A, if it fails (at same position), try parser B *)
let ( <|> ) (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun input pos ->
    match p1 input pos with
    | Ok _ as result -> result
    | Error (_, epos1) ->
      if epos1 = pos then
        (* Only backtrack if p1 failed without consuming input *)
        p2 input pos
      else
        (* p1 consumed input before failing — don't backtrack *)
        p1 input pos

(* Try a parser: if it fails, always backtrack (reset position) *)
let try_ (p : 'a parser) : 'a parser =
  fun input pos ->
    match p input pos with
    | Ok _ as result -> result
    | Error (msg, _) -> Error (msg, pos)

(* Label a parser with a custom error message *)
let label (msg : string) (p : 'a parser) : 'a parser =
  fun input pos ->
    match p input pos with
    | Ok _ as result -> result
    | Error (_, epos) -> Error (msg, epos)

(* --- Repetition combinators --- *)

(* Parse zero or more occurrences *)
let many (p : 'a parser) : 'a list parser =
  fun input pos ->
    let rec aux acc pos =
      match p input pos with
      | Error _ -> Ok (List.rev acc, pos)
      | Ok (x, pos') ->
        if pos' = pos then Ok (List.rev acc, pos)  (* prevent infinite loop *)
        else aux (x :: acc) pos'
    in
    aux [] pos

(* Parse one or more occurrences *)
let many1 (p : 'a parser) : 'a list parser =
  p >>= fun first ->
  many p >>= fun rest ->
  return_ (first :: rest)

(* Parse zero or more, separated by a delimiter parser *)
let sep_by (p : 'a parser) (sep : 'b parser) : 'a list parser =
  (p >>= fun first ->
   many (sep *> p) >>= fun rest ->
   return_ (first :: rest))
  <|> return_ []

(* Parse one or more, separated by a delimiter parser *)
let sep_by1 (p : 'a parser) (sep : 'b parser) : 'a list parser =
  p >>= fun first ->
  many (sep *> p) >>= fun rest ->
  return_ (first :: rest)

(* Parse something between opening and closing delimiters *)
let between (open_ : 'a parser) (close_ : 'b parser) (p : 'c parser) : 'c parser =
  open_ *> p <* close_

(* Optional parser: returns Some on success, None on failure *)
let optional (p : 'a parser) : 'a option parser =
  (map (fun x -> Some x) p) <|> return_ None

(* Skip zero or more whitespace characters *)
let spaces : unit parser =
  map (fun _ -> ()) (many whitespace)

(* Parse p, surrounded by optional whitespace *)
let lexeme (p : 'a parser) : 'a parser =
  p <* spaces

(* --- Useful derived parsers --- *)

(* Parse a natural number (one or more digits) *)
let natural : int parser =
  many1 digit >>= fun chars ->
  let s = String.init (List.length chars) (List.nth chars) in
  return_ (int_of_string s)

(* Parse an integer (optional sign + digits) *)
let integer : int parser =
  optional (char_ '-') >>= fun sign ->
  natural >>= fun n ->
  return_ (match sign with Some _ -> -n | None -> n)

(* Parse a quoted string (double quotes, no escapes for simplicity) *)
let quoted_string : string parser =
  char_ '"' *>
  many (satisfy (fun c -> c <> '"') "non-quote character") >>= fun chars ->
  char_ '"' *>
  return_ (String.init (List.length chars) (List.nth chars))

(* Parse an identifier (letter followed by letters/digits/underscores) *)
let identifier : string parser =
  letter >>= fun first ->
  many (satisfy (fun c ->
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
    (c >= '0' && c <= '9') || c = '_') "alphanumeric or underscore") >>= fun rest ->
  return_ (String.init (1 + List.length rest) (fun i ->
    if i = 0 then first else List.nth rest (i - 1)))

(* --- Chainl: left-associative operator parsing --- *)
(* This is essential for parsing arithmetic with correct precedence.
   chainl1 p op  parses:  p (op p)*
   and folds left:  ((a op b) op c) op d *)

let chainl1 (p : 'a parser) (op : ('a -> 'a -> 'a) parser) : 'a parser =
  p >>= fun first ->
  let rec aux acc =
    (op >>= fun f ->
     p >>= fun b ->
     aux (f acc b))
    <|> return_ acc
  in
  aux first

(* chainr1: right-associative operator parsing.
   chainr1 p op  parses:  p (op p)*
   and folds right:  a op (b op (c op d)) *)

let chainr1 (p : 'a parser) (op : ('a -> 'a -> 'a) parser) : 'a parser =
  let rec aux () =
    p >>= fun a ->
    (op >>= fun f ->
     aux () >>= fun b ->
     return_ (f a b))
    <|> return_ a
  in
  aux ()

(* --- Running parsers --- *)

(* Run a parser on a string, return a clean result *)
let run (p : 'a parser) (input : string) : ('a, string) Stdlib.result =
  match (p <* spaces) input 0 with
  | Ok (value, pos) ->
    if pos = String.length input then Stdlib.Ok value
    else Stdlib.Error (Printf.sprintf "unexpected character '%c' at position %d"
      input.[pos] pos)
  | Error (msg, pos) ->
    Stdlib.Error (Printf.sprintf "%s at position %d" msg pos)

(* Run a parser, returning a descriptive string *)
let run_show (to_string : 'a -> string) (p : 'a parser) (input : string) : string =
  match run p input with
  | Stdlib.Ok value -> Printf.sprintf "OK: %s" (to_string value)
  | Stdlib.Error msg -> Printf.sprintf "Error: %s" msg

(* =========================================================== *)
(*   Example: Arithmetic Expression Parser with Evaluation     *)
(* =========================================================== *)

(* This parser handles:
   - Integer literals (including negative)
   - Addition (+), subtraction (-)
   - Multiplication (*), division (/)
   - Exponentiation (^) — right-associative
   - Parenthesized sub-expressions
   - Correct operator precedence: ^ > * / > + -
   - Whitespace between tokens *)

(* AST for arithmetic expressions *)
type expr =
  | Num of int
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Pow of expr * expr

(* Evaluate an expression *)
let rec eval = function
  | Num n -> n
  | Add (a, b) -> eval a + eval b
  | Sub (a, b) -> eval a - eval b
  | Mul (a, b) -> eval a * eval b
  | Div (a, b) ->
    let denom = eval b in
    if denom = 0 then failwith "division by zero"
    else eval a / denom
  | Pow (a, b) ->
    let base = eval a and exp = eval b in
    let rec power b e =
      if e = 0 then 1
      else if e = 1 then b
      else b * power b (e - 1)
    in
    if exp < 0 then failwith "negative exponent"
    else power base exp

(* Pretty-print an expression (with minimal parentheses) *)
let rec string_of_expr = function
  | Num n -> string_of_int n
  | Add (a, b) -> Printf.sprintf "(%s + %s)" (string_of_expr a) (string_of_expr b)
  | Sub (a, b) -> Printf.sprintf "(%s - %s)" (string_of_expr a) (string_of_expr b)
  | Mul (a, b) -> Printf.sprintf "(%s * %s)" (string_of_expr a) (string_of_expr b)
  | Div (a, b) -> Printf.sprintf "(%s / %s)" (string_of_expr a) (string_of_expr b)
  | Pow (a, b) -> Printf.sprintf "(%s ^ %s)" (string_of_expr a) (string_of_expr b)

(* The expression parser — built from combinators!
   Grammar (in precedence order, lowest to highest):
     expr   = term (('+' | '-') term)*
     term   = power (('*' | '/') power)*
     power  = atom ('^' power)?          (right-associative)
     atom   = number | '(' expr ')'
*)

(* Forward declaration for recursive grammar *)
let expr_parser_ref : expr parser ref = ref (fail "not initialized")

(* Atom: number or parenthesized expression *)
let atom : expr parser =
  lexeme (
    (map (fun n -> Num n) integer)
    <|>
    (char_ '(' *> spaces *>
     (fun input pos -> !expr_parser_ref input pos) <*
     spaces <* char_ ')')
  )

(* Power: atom ^ power (right-associative) *)
let power : expr parser =
  let pow_op = lexeme (char_ '^') *> return_ (fun a b -> Pow (a, b)) in
  chainr1 atom pow_op

(* Term: power * power | power / power (left-associative) *)
let term : expr parser =
  let mul_op =
    (lexeme (char_ '*') *> return_ (fun a b -> Mul (a, b)))
    <|>
    (lexeme (char_ '/') *> return_ (fun a b -> Div (a, b)))
  in
  chainl1 power mul_op

(* Expression: term + term | term - term (left-associative) *)
let expr_parser : expr parser =
  let add_op =
    (lexeme (char_ '+') *> return_ (fun a b -> Add (a, b)))
    <|>
    (lexeme (char_ '-') *> return_ (fun a b -> Sub (a, b)))
  in
  chainl1 term add_op

(* Wire up the forward reference *)
let () = expr_parser_ref := expr_parser

(* Parse and evaluate an arithmetic expression *)
let calc (input : string) : (int, string) Stdlib.result =
  match run (spaces *> expr_parser) input with
  | Stdlib.Ok expr ->
    (try Stdlib.Ok (eval expr)
     with Failure msg -> Stdlib.Error msg)
  | Stdlib.Error msg -> Stdlib.Error msg

(* =========================================================== *)
(*   Example: Simple List Parser  [1, 2, 3]                   *)
(* =========================================================== *)

let int_list_parser : int list parser =
  between
    (lexeme (char_ '['))
    (lexeme (char_ ']'))
    (sep_by (lexeme integer) (lexeme (char_ ',')))

(* =========================================================== *)
(*   Example: Key-Value Parser  key = "value"                  *)
(* =========================================================== *)

let kv_parser : (string * string) parser =
  lexeme identifier >>= fun key ->
  lexeme (char_ '=') *>
  lexeme quoted_string >>= fun value ->
  return_ (key, value)

let kv_list_parser : (string * string) list parser =
  sep_by kv_parser (lexeme (char_ ','))

(* --- Helpers for display --- *)

let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

let string_of_kv (k, v) = Printf.sprintf "%s = \"%s\"" k v

let string_of_kv_list lst =
  "{" ^ String.concat ", " (List.map string_of_kv lst) ^ "}"

let string_of_calc_result = function
  | Stdlib.Ok n -> string_of_int n
  | Stdlib.Error msg -> "Error: " ^ msg

(* ===== Example usage ===== *)

let () =
  print_endline "=== Parser Combinators ===";
  print_endline "Building parsers from small, composable pieces\n";

  (* --- Primitive parsers --- *)
  print_endline "--- Primitive parsers ---";
  Printf.printf "digit on \"42\":    %s\n"
    (run_show (String.make 1) digit "42");
  Printf.printf "letter on \"abc\":  %s\n"
    (run_show (String.make 1) letter "abc");
  Printf.printf "char 'x' on \"xyz\": %s\n"
    (run_show (String.make 1) (char_ 'x') "xyz");
  Printf.printf "string \"hi\" on \"hi there\": %s\n"
    (run_show (fun s -> "\"" ^ s ^ "\"") (string_ "hi") "hi there");
  print_newline ();

  (* --- Number parsing --- *)
  print_endline "--- Number parsing ---";
  List.iter (fun s ->
    Printf.printf "integer \"%s\": %s\n" s
      (run_show string_of_int integer s)
  ) ["42"; "-7"; "0"; "12345"; "abc"];
  print_newline ();

  (* --- Combinators in action --- *)
  print_endline "--- Combinators: many, sep_by, between ---";
  Printf.printf "many digit \"12345abc\": %s\n"
    (run_show (fun cs -> String.init (List.length cs) (List.nth cs))
      (many digit) "12345");
  Printf.printf "int list \"[1, 2, 3]\": %s\n"
    (run_show string_of_int_list int_list_parser "[1, 2, 3]");
  Printf.printf "int list \"[]\": %s\n"
    (run_show string_of_int_list int_list_parser "[]");
  Printf.printf "int list \"[42]\": %s\n"
    (run_show string_of_int_list int_list_parser "[42]");
  Printf.printf "int list \"[10, 20, 30, 40, 50]\": %s\n"
    (run_show string_of_int_list int_list_parser "[10, 20, 30, 40, 50]");
  print_newline ();

  (* --- Key-value parsing --- *)
  print_endline "--- Key-value parser ---";
  Printf.printf "kv: %s\n"
    (run_show string_of_kv kv_parser "name = \"Alice\"");
  Printf.printf "kv list: %s\n"
    (run_show string_of_kv_list kv_list_parser
      "name = \"Alice\", age = \"30\", city = \"NYC\"");
  print_newline ();

  (* --- Identifier parsing --- *)
  print_endline "--- Identifiers ---";
  List.iter (fun s ->
    Printf.printf "identifier \"%s\": %s\n" s
      (run_show (fun x -> x) identifier s)
  ) ["hello"; "x42"; "my_var"; "camelCase"; "123bad"];
  print_newline ();

  (* --- Arithmetic expression parser --- *)
  print_endline "--- Arithmetic expression parser ---";
  print_endline "Supports: + - * / ^ () with correct precedence\n";

  let test_exprs = [
    "42";
    "2 + 3";
    "2 + 3 * 4";      (* precedence: 2 + (3*4) = 14 *)
    "(2 + 3) * 4";    (* parentheses override: 5*4 = 20 *)
    "2 ^ 3 ^ 2";      (* right-assoc: 2^(3^2) = 2^9 = 512 *)
    "10 - 3 - 2";     (* left-assoc: (10-3)-2 = 5 *)
    "100 / 5 / 4";    (* left-assoc: (100/5)/4 = 5 *)
    "(1 + 2) * (3 + 4)";  (* = 21 *)
    "2 ^ 10";         (* = 1024 *)
    "((3 + 5) * 2) - (10 / 2)";  (* = 11 *)
  ] in

  List.iter (fun input ->
    match run (spaces *> expr_parser) input with
    | Stdlib.Ok expr ->
      Printf.printf "  %-30s  AST: %-35s  = %d\n"
        input (string_of_expr expr) (eval expr)
    | Stdlib.Error msg ->
      Printf.printf "  %-30s  Error: %s\n" input msg
  ) test_exprs;
  print_newline ();

  (* --- calc helper --- *)
  print_endline "--- Quick calculator ---";
  List.iter (fun s ->
    Printf.printf "  calc \"%s\" = %s\n" s (string_of_calc_result (calc s))
  ) ["1+2+3"; "2*3+4"; "2*(3+4)"; "10/0"; "2^8"; "-5 + 10"];
  print_newline ();

  (* --- Error messages --- *)
  print_endline "--- Error handling ---";
  List.iter (fun s ->
    Printf.printf "  \"%s\": %s\n" s
      (match run (spaces *> expr_parser) s with
       | Stdlib.Ok _ -> "OK"
       | Stdlib.Error msg -> msg)
  ) [""; "2 +"; "* 3"; "2 + + 3"];
  print_newline ();

  (* --- Choice combinator --- *)
  print_endline "--- Choice combinator (<|>) ---";
  let bool_parser =
    (string_ "true" *> return_ true)
    <|> (string_ "false" *> return_ false)
  in
  Printf.printf "bool \"true\":  %s\n"
    (run_show string_of_bool bool_parser "true");
  Printf.printf "bool \"false\": %s\n"
    (run_show string_of_bool bool_parser "false");
  Printf.printf "bool \"maybe\": %s\n"
    (run_show string_of_bool bool_parser "maybe");
  print_newline ();

  (* --- Optional parser --- *)
  print_endline "--- Optional parser ---";
  let signed_nat =
    optional (char_ '+' <|> char_ '-') >>= fun sign ->
    natural >>= fun n ->
    return_ (match sign with Some '-' -> -n | _ -> n)
  in
  List.iter (fun s ->
    Printf.printf "signed \"%s\": %s\n" s
      (run_show string_of_int signed_nat s)
  ) ["+42"; "-7"; "99"];
  print_newline ();

  (* --- Summary --- *)
  print_endline "--- Combinator summary ---";
  print_endline "  satisfy  — match a character by predicate";
  print_endline "  char_    — match a specific character";
  print_endline "  string_  — match a specific string";
  print_endline "  >>=      — sequencing (monadic bind)";
  print_endline "  <$>      — transform result (map/fmap)";
  print_endline "  <*>      — applicative apply";
  print_endline "  <|>      — choice (try alternatives)";
  print_endline "  *>       — sequence, keep right";
  print_endline "  <*       — sequence, keep left";
  print_endline "  many     — zero or more repetitions";
  print_endline "  many1    — one or more repetitions";
  print_endline "  sep_by   — delimited lists";
  print_endline "  between  — parse between delimiters";
  print_endline "  chainl1  — left-associative operators";
  print_endline "  chainr1  — right-associative operators";
  print_endline "  optional — maybe parse";
  print_endline "  try_     — backtracking";
  print_endline "  label    — custom error messages"
