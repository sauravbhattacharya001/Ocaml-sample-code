(* mini_sql.ml — Mini SQL Query Engine

   A minimal SQL query engine in OCaml that parses and executes SQL queries
   on in-memory tables. Supports CREATE TABLE, INSERT, SELECT (with WHERE,
   ORDER BY, LIMIT, JOIN, GROUP BY, HAVING), UPDATE, DELETE, and aggregates.

   Usage: ocaml mini_sql.ml

   Provides an interactive REPL and built-in demo tables.
*)

(* ============================================================ *)
(* Types                                                         *)
(* ============================================================ *)

type value =
  | VNull
  | VInt of int
  | VFloat of float
  | VString of string
  | VBool of bool

type column_def = {
  col_name: string;
  col_type: string;
}

type table = {
  name: string;
  columns: column_def list;
  mutable rows: value array list;
}

type expr =
  | Literal of value
  | Column of string
  | QualColumn of string * string
  | BinOp of string * expr * expr
  | UnaryOp of string * expr
  | FuncCall of string * expr list
  | Star

type select_item =
  | SelectExpr of expr * string option
  | SelectAll

type join_clause = {
  join_table: string;
  join_alias: string option;
  join_on: expr;
}

type order_item = expr * bool

type statement =
  | CreateTable of string * column_def list
  | Insert of string * string list option * value list list
  | Select of {
      items: select_item list;
      from: (string * string option) list;
      joins: join_clause list;
      where: expr option;
      group_by: expr list;
      having: expr option;
      order_by: order_item list;
      limit: int option;
      distinct: bool;
    }
  | Update of string * (string * expr) list * expr option
  | Delete of string * expr option
  | DropTable of string
  | ShowTables
  | Describe of string

type database = { mutable tables: table list }
let create_db () = { tables = [] }
let find_table db name =
  List.find_opt (fun t -> String.lowercase_ascii t.name = String.lowercase_ascii name) db.tables

(* ============================================================ *)
(* Lexer                                                         *)
(* ============================================================ *)

type token =
  | TkWord of string | TkInt of int | TkFloat of float | TkString of string
  | TkStar | TkComma | TkDot | TkLParen | TkRParen | TkSemicolon
  | TkOp of string | TkEOF

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_digit c = c >= '0' && c <= '9'
let is_alnum c = is_alpha c || is_digit c

let tokenize input =
  let n = String.length input in
  let pos = ref 0 in
  let tokens = ref [] in
  let peek () = if !pos < n then input.[!pos] else '\000' in
  let advance () = incr pos in
  let rec skip_ws () =
    if !pos < n && (input.[!pos] = ' ' || input.[!pos] = '\t' || input.[!pos] = '\n' || input.[!pos] = '\r') then
      (advance (); skip_ws ()) in
  let read_while pred =
    let buf = Buffer.create 16 in
    while !pos < n && pred input.[!pos] do Buffer.add_char buf input.[!pos]; advance () done;
    Buffer.contents buf in
  let rec go () =
    skip_ws ();
    if !pos >= n then tokens := TkEOF :: !tokens
    else let c = peek () in
      if is_alpha c then (let w = read_while is_alnum in tokens := TkWord w :: !tokens; go ())
      else if is_digit c then begin
        let num = read_while (fun c -> is_digit c || c = '.') in
        (if String.contains num '.' then tokens := TkFloat (float_of_string num) :: !tokens
         else tokens := TkInt (int_of_string num) :: !tokens); go ()
      end else if c = '\'' then begin
        advance ();
        let buf = Buffer.create 32 in
        while !pos < n && peek () <> '\'' do
          if peek () = '\\' then (advance (); if !pos < n then (Buffer.add_char buf (peek ()); advance ()))
          else (Buffer.add_char buf (peek ()); advance ()) done;
        if !pos < n then advance ();
        tokens := TkString (Buffer.contents buf) :: !tokens; go ()
      end else begin
        (match c with
         | '*' -> advance (); tokens := TkStar :: !tokens
         | ',' -> advance (); tokens := TkComma :: !tokens
         | '.' -> advance (); tokens := TkDot :: !tokens
         | '(' -> advance (); tokens := TkLParen :: !tokens
         | ')' -> advance (); tokens := TkRParen :: !tokens
         | ';' -> advance (); tokens := TkSemicolon :: !tokens
         | '=' -> advance (); tokens := TkOp "=" :: !tokens
         | '<' -> advance (); if peek () = '=' then (advance (); tokens := TkOp "<=" :: !tokens)
                  else if peek () = '>' then (advance (); tokens := TkOp "<>" :: !tokens)
                  else tokens := TkOp "<" :: !tokens
         | '>' -> advance (); if peek () = '=' then (advance (); tokens := TkOp ">=" :: !tokens)
                  else tokens := TkOp ">" :: !tokens
         | '!' -> advance (); if peek () = '=' then (advance (); tokens := TkOp "!=" :: !tokens)
                  else tokens := TkOp "!" :: !tokens
         | '+' -> advance (); tokens := TkOp "+" :: !tokens
         | '-' -> advance (); tokens := TkOp "-" :: !tokens
         | '/' -> advance (); tokens := TkOp "/" :: !tokens
         | '%' -> advance (); tokens := TkOp "%" :: !tokens
         | _ -> advance (); go ()); go () end in
  go (); List.rev !tokens

(* ============================================================ *)
(* Parser                                                        *)
(* ============================================================ *)

exception ParseError of string
type parser_state = { mutable toks: token list }
let make_parser tokens = { toks = tokens }
let peek p = match p.toks with t :: _ -> t | [] -> TkEOF
let advance p = match p.toks with _ :: rest -> p.toks <- rest | [] -> ()
let consume p = let t = peek p in advance p; t
let expect_word p = match consume p with TkWord w -> w | _ -> raise (ParseError "Expected identifier")
let expect_word_ci p expected =
  match consume p with
  | TkWord w when String.lowercase_ascii w = String.lowercase_ascii expected -> ()
  | _ -> raise (ParseError (Printf.sprintf "Expected '%s'" expected))
let is_word p w = match peek p with TkWord x when String.lowercase_ascii x = String.lowercase_ascii w -> true | _ -> false
let try_word p w = if is_word p w then (advance p; true) else false
let expect_token p tk = let t = consume p in if t <> tk then raise (ParseError "Unexpected token")

let rec parse_expr p = parse_or p
and parse_or p = let left = parse_and p in
  if is_word p "OR" then (advance p; BinOp ("OR", left, parse_or p)) else left
and parse_and p = let left = parse_comparison p in
  if is_word p "AND" then (advance p; BinOp ("AND", left, parse_and p)) else left
and parse_comparison p =
  let left = parse_add p in
  match peek p with
  | TkOp op when List.mem op ["=";"<>";"!=";"<";">";"<=";">="] -> advance p; BinOp (op, left, parse_add p)
  | _ ->
    if is_word p "IS" then begin advance p;
      let not_ = try_word p "NOT" in expect_word_ci p "NULL";
      if not_ then UnaryOp ("IS NOT NULL", left) else UnaryOp ("IS NULL", left)
    end else if is_word p "LIKE" then (advance p; BinOp ("LIKE", left, parse_add p))
    else if is_word p "IN" then begin
      advance p; expect_token p TkLParen; let vals = parse_expr_list p in expect_token p TkRParen;
      match vals with [] -> Literal (VBool false) | [v] -> BinOp ("=", left, v)
      | v :: rest -> List.fold_left (fun acc x -> BinOp ("OR", acc, BinOp ("=", left, x))) (BinOp ("=", left, v)) rest
    end else if is_word p "BETWEEN" then begin
      advance p; let lo = parse_add p in expect_word_ci p "AND"; let hi = parse_add p in
      BinOp ("AND", BinOp (">=", left, lo), BinOp ("<=", left, hi))
    end else if is_word p "NOT" then begin advance p;
      if is_word p "IN" then begin
        advance p; expect_token p TkLParen; let vals = parse_expr_list p in expect_token p TkRParen;
        UnaryOp ("NOT", List.fold_left (fun acc x -> BinOp ("OR", acc, BinOp ("=", left, x)))
          (BinOp ("=", left, List.hd vals)) (List.tl vals))
      end else if is_word p "LIKE" then (advance p; UnaryOp ("NOT", BinOp ("LIKE", left, parse_add p)))
      else raise (ParseError "Expected IN or LIKE after NOT")
    end else left
and parse_add p = let left = parse_mul p in
  match peek p with
  | TkOp "+" -> advance p; BinOp ("+", left, parse_add p)
  | TkOp "-" -> advance p; BinOp ("-", left, parse_add p) | _ -> left
and parse_mul p = let left = parse_unary p in
  match peek p with
  | TkOp "*" -> advance p; BinOp ("*", left, parse_mul p)
  | TkOp "/" -> advance p; BinOp ("/", left, parse_mul p)
  | TkOp "%" -> advance p; BinOp ("%", left, parse_mul p) | _ -> left
and parse_unary p =
  if is_word p "NOT" then (advance p; UnaryOp ("NOT", parse_unary p))
  else if (match peek p with TkOp "-" -> true | _ -> false) then (advance p; UnaryOp ("-", parse_primary p))
  else parse_primary p
and parse_primary p =
  match peek p with
  | TkInt n -> advance p; Literal (VInt n) | TkFloat f -> advance p; Literal (VFloat f)
  | TkString s -> advance p; Literal (VString s) | TkStar -> advance p; Star
  | TkLParen -> advance p; let e = parse_expr p in expect_token p TkRParen; e
  | TkWord w -> advance p;
    let wl = String.lowercase_ascii w in
    if wl = "null" then Literal VNull else if wl = "true" then Literal (VBool true)
    else if wl = "false" then Literal (VBool false)
    else if (match peek p with TkLParen -> true | _ -> false) then begin
      advance p;
      let args = if (match peek p with TkRParen -> true | _ -> false) then []
                 else if (match peek p with TkStar -> true | _ -> false) then (advance p; [Star])
                 else parse_expr_list p in
      expect_token p TkRParen; FuncCall (String.uppercase_ascii w, args)
    end else if (match peek p with TkDot -> true | _ -> false) then
      (advance p; let col = expect_word p in QualColumn (w, col))
    else Column w
  | _ -> raise (ParseError "Expected expression")
and parse_expr_list p =
  let first = parse_expr p in let rest = ref [] in
  while (match peek p with TkComma -> true | _ -> false) do advance p; rest := parse_expr p :: !rest done;
  first :: List.rev !rest

let reserved_kws = ["from";"where";"order";"group";"having";"limit";"join";"left";"right";"inner";"on";"cross"]

let parse_select_item p = match peek p with
  | TkStar -> advance p; SelectAll
  | _ -> let e = parse_expr p in
    let alias = if is_word p "AS" then (advance p; Some (expect_word p))
      else match peek p with TkWord w when not (List.mem (String.lowercase_ascii w) reserved_kws) -> advance p; Some w | _ -> None in
    SelectExpr (e, alias)

let parse_select_items p =
  let first = parse_select_item p in let rest = ref [] in
  while (match peek p with TkComma -> true | _ -> false) do advance p; rest := parse_select_item p :: !rest done;
  first :: List.rev !rest

let parse_statement p =
  let w = String.uppercase_ascii (expect_word p) in
  match w with
  | "CREATE" ->
    expect_word_ci p "TABLE"; let name = expect_word p in expect_token p TkLParen;
    let cols = ref [] in
    let cn = expect_word p in let ct = String.uppercase_ascii (expect_word p) in
    cols := { col_name = cn; col_type = ct } :: !cols;
    while (match peek p with TkComma -> true | _ -> false) do advance p;
      let cn = expect_word p in let ct = String.uppercase_ascii (expect_word p) in
      cols := { col_name = cn; col_type = ct } :: !cols done;
    expect_token p TkRParen; CreateTable (name, List.rev !cols)
  | "INSERT" ->
    expect_word_ci p "INTO"; let tname = expect_word p in
    let cols = if (match peek p with TkLParen -> true | _ -> false) then begin
      advance p; let names = ref [expect_word p] in
      while (match peek p with TkComma -> true | _ -> false) do advance p; names := expect_word p :: !names done;
      expect_token p TkRParen; Some (List.rev !names) end else None in
    expect_word_ci p "VALUES";
    let parse_row () = expect_token p TkLParen;
      let parse_val () = match peek p with
        | TkInt n -> advance p; VInt n | TkFloat f -> advance p; VFloat f
        | TkString s -> advance p; VString s
        | TkWord w -> advance p; let wl = String.lowercase_ascii w in
          if wl = "null" then VNull else if wl = "true" then VBool true
          else if wl = "false" then VBool false else VString w
        | _ -> raise (ParseError "Expected value") in
      let vals = ref [parse_val ()] in
      while (match peek p with TkComma -> true | _ -> false) do advance p; vals := parse_val () :: !vals done;
      expect_token p TkRParen; List.rev !vals in
    let rows = ref [parse_row ()] in
    while (match peek p with TkComma -> true | _ -> false) do advance p; rows := parse_row () :: !rows done;
    Insert (tname, cols, List.rev !rows)
  | "SELECT" ->
    let distinct = try_word p "DISTINCT" in let items = parse_select_items p in
    let from = if is_word p "FROM" then begin advance p;
      let tname = expect_word p in
      let alias = if is_word p "AS" then (advance p; Some (expect_word p))
        else match peek p with TkWord w when not (List.mem (String.lowercase_ascii w) reserved_kws) -> advance p; Some w | _ -> None in
      let rest = ref [] in
      while (match peek p with TkComma -> true | _ -> false) do advance p;
        let tn = expect_word p in
        let al = if is_word p "AS" then (advance p; Some (expect_word p))
          else match peek p with TkWord w when not (List.mem (String.lowercase_ascii w) reserved_kws) -> advance p; Some w | _ -> None in
        rest := (tn, al) :: !rest done;
      (tname, alias) :: List.rev !rest end else [] in
    let joins = ref [] in
    while is_word p "JOIN" || is_word p "INNER" || is_word p "LEFT" || is_word p "CROSS" do
      let jt_kw = expect_word p in
      if String.lowercase_ascii jt_kw <> "join" then ignore (try_word p "JOIN");
      let jt = expect_word p in
      let ja = if is_word p "AS" then (advance p; Some (expect_word p))
        else match peek p with TkWord w when String.lowercase_ascii w <> "on" && String.lowercase_ascii w <> "where" -> advance p; Some w | _ -> None in
      let jon = if is_word p "ON" then (advance p; parse_expr p) else Literal (VBool true) in
      joins := { join_table = jt; join_alias = ja; join_on = jon } :: !joins done;
    let where = if try_word p "WHERE" then Some (parse_expr p) else None in
    let group_by = if is_word p "GROUP" then (advance p; expect_word_ci p "BY"; parse_expr_list p) else [] in
    let having = if try_word p "HAVING" then Some (parse_expr p) else None in
    let order_by = if is_word p "ORDER" then begin advance p; expect_word_ci p "BY";
      let poi () = let e = parse_expr p in let asc = if try_word p "DESC" then false else (ignore (try_word p "ASC"); true) in (e, asc) in
      let first = poi () in let rest = ref [] in
      while (match peek p with TkComma -> true | _ -> false) do advance p; rest := poi () :: !rest done;
      first :: List.rev !rest end else [] in
    let limit = if try_word p "LIMIT" then (match consume p with TkInt n -> Some n | _ -> raise (ParseError "Expected integer after LIMIT")) else None in
    Select { items; from; joins = List.rev !joins; where; group_by; having; order_by; limit; distinct }
  | "UPDATE" ->
    let tname = expect_word p in expect_word_ci p "SET";
    let pa () = let col = expect_word p in expect_token p (TkOp "="); let e = parse_expr p in (col, e) in
    let first = pa () in let rest = ref [] in
    while (match peek p with TkComma -> true | _ -> false) do advance p; rest := pa () :: !rest done;
    let where = if try_word p "WHERE" then Some (parse_expr p) else None in
    Update (tname, first :: List.rev !rest, where)
  | "DELETE" -> expect_word_ci p "FROM"; let tname = expect_word p in
    let where = if try_word p "WHERE" then Some (parse_expr p) else None in Delete (tname, where)
  | "DROP" -> expect_word_ci p "TABLE"; DropTable (expect_word p)
  | "SHOW" -> expect_word_ci p "TABLES"; ShowTables
  | "DESCRIBE" | "DESC" -> Describe (expect_word p)
  | _ -> raise (ParseError (Printf.sprintf "Unknown statement: %s" w))

let parse input = let p = make_parser (tokenize input) in parse_statement p

(* ============================================================ *)
(* Evaluator                                                     *)
(* ============================================================ *)

exception EvalError of string

let value_to_string = function
  | VNull -> "NULL" | VInt n -> string_of_int n
  | VFloat f -> let s = Printf.sprintf "%.6g" f in
    if String.contains s '.' || String.contains s 'e' then s else s ^ ".0"
  | VString s -> s | VBool b -> if b then "TRUE" else "FALSE"

let value_to_float = function VInt n -> float_of_int n | VFloat f -> f
  | VString s -> (try float_of_string s with _ -> 0.0) | _ -> 0.0
let value_to_int = function VInt n -> n | VFloat f -> int_of_float f
  | VString s -> (try int_of_string s with _ -> 0) | _ -> 0

let compare_values a b = match a, b with
  | VNull, VNull -> 0 | VNull, _ -> -1 | _, VNull -> 1
  | VInt a, VInt b -> compare a b | VFloat a, VFloat b -> compare a b
  | VInt a, VFloat b -> compare (float_of_int a) b | VFloat a, VInt b -> compare a (float_of_int b)
  | VString a, VString b -> String.compare a b | VBool a, VBool b -> compare a b
  | a, b -> String.compare (value_to_string a) (value_to_string b)

let like_match pattern str =
  let pn = String.length pattern and sn = String.length str in
  let rec go pi si =
    if pi = pn && si = sn then true else if pi = pn then false
    else match pattern.[pi] with
    | '%' -> let rec try_skip si = if go (pi+1) si then true else if si < sn then try_skip (si+1) else false in try_skip si
    | '_' -> if si < sn then go (pi+1) (si+1) else false
    | c -> if si < sn && Char.lowercase_ascii c = Char.lowercase_ascii str.[si] then go (pi+1) (si+1) else false
  in go 0 0

let env_lookup env name =
  let nl = String.lowercase_ascii name in
  match List.find_opt (fun (k,_) -> String.lowercase_ascii k = nl) env with
  | Some (_,v) -> v | None -> raise (EvalError (Printf.sprintf "Column '%s' not found" name))

let env_lookup_qual env tbl col =
  let key = String.lowercase_ascii tbl ^ "." ^ String.lowercase_ascii col in
  match List.find_opt (fun (k,_) -> String.lowercase_ascii k = key) env with
  | Some (_,v) -> v | None -> raise (EvalError (Printf.sprintf "Column '%s.%s' not found" tbl col))

let rec eval_expr env = function
  | Literal v -> v | Column name -> env_lookup env name
  | QualColumn (tbl, col) -> env_lookup_qual env tbl col | Star -> VString "*"
  | UnaryOp ("-", e) -> (match eval_expr env e with VInt n -> VInt (-n) | VFloat f -> VFloat (-.f) | _ -> VNull)
  | UnaryOp ("NOT", e) -> (match eval_expr env e with VBool b -> VBool (not b) | VNull -> VNull | _ -> VBool false)
  | UnaryOp ("IS NULL", e) -> VBool (eval_expr env e = VNull)
  | UnaryOp ("IS NOT NULL", e) -> VBool (eval_expr env e <> VNull)
  | UnaryOp _ -> VNull
  | BinOp ("AND", a, b) -> (match eval_expr env a with VBool false -> VBool false | VBool true -> eval_expr env b | _ -> VNull)
  | BinOp ("OR", a, b) -> (match eval_expr env a with VBool true -> VBool true | VBool false -> eval_expr env b | _ -> eval_expr env b)
  | BinOp ("LIKE", a, b) -> VBool (like_match (value_to_string (eval_expr env b)) (value_to_string (eval_expr env a)))
  | BinOp (op, a, b) ->
    let va = eval_expr env a and vb = eval_expr env b in
    if va = VNull || vb = VNull then VNull
    else (match op with
     | "=" -> VBool (compare_values va vb = 0) | "<>" | "!=" -> VBool (compare_values va vb <> 0)
     | "<" -> VBool (compare_values va vb < 0) | ">" -> VBool (compare_values va vb > 0)
     | "<=" -> VBool (compare_values va vb <= 0) | ">=" -> VBool (compare_values va vb >= 0)
     | "+" -> (match va, vb with VInt a, VInt b -> VInt (a+b) | VString a, VString b -> VString (a^b) | _ -> VFloat (value_to_float va +. value_to_float vb))
     | "-" -> (match va, vb with VInt a, VInt b -> VInt (a-b) | _ -> VFloat (value_to_float va -. value_to_float vb))
     | "*" -> (match va, vb with VInt a, VInt b -> VInt (a*b) | _ -> VFloat (value_to_float va *. value_to_float vb))
     | "/" -> (match va, vb with VInt a, VInt b -> if b=0 then VNull else VInt (a/b) | _ -> let fb = value_to_float vb in if fb=0.0 then VNull else VFloat (value_to_float va /. fb))
     | "%" -> (match va, vb with VInt a, VInt b -> if b=0 then VNull else VInt (a mod b) | _ -> VNull)
     | _ -> VNull)
  | FuncCall (name, args) -> eval_func env name args
and eval_func env name args = match name with
  | "UPPER" -> VString (String.uppercase_ascii (value_to_string (eval_expr env (List.hd args))))
  | "LOWER" -> VString (String.lowercase_ascii (value_to_string (eval_expr env (List.hd args))))
  | "LENGTH"|"LEN" -> VInt (String.length (value_to_string (eval_expr env (List.hd args))))
  | "ABS" -> (match eval_expr env (List.hd args) with VInt n -> VInt (abs n) | VFloat f -> VFloat (abs_float f) | v -> v)
  | "COALESCE" -> let rec find = function [] -> VNull | e::rest -> let v = eval_expr env e in if v <> VNull then v else find rest in find args
  | "CONCAT" -> VString (String.concat "" (List.map (fun e -> value_to_string (eval_expr env e)) args))
  | "SUBSTR"|"SUBSTRING" ->
    let s = value_to_string (eval_expr env (List.nth args 0)) in
    let start = max 0 (value_to_int (eval_expr env (List.nth args 1)) - 1) in
    let len = if List.length args > 2 then value_to_int (eval_expr env (List.nth args 2)) else String.length s - start in
    if start >= String.length s then VString "" else VString (String.sub s start (min (max 0 len) (String.length s - start)))
  | "TRIM" -> VString (String.trim (value_to_string (eval_expr env (List.hd args))))
  | "REPLACE" ->
    let s = value_to_string (eval_expr env (List.nth args 0)) in
    let from_s = value_to_string (eval_expr env (List.nth args 1)) in
    let to_s = value_to_string (eval_expr env (List.nth args 2)) in
    let buf = Buffer.create (String.length s) in let fl = String.length from_s in let sl = String.length s in let i = ref 0 in
    while !i < sl do
      if !i + fl <= sl && String.sub s !i fl = from_s then (Buffer.add_string buf to_s; i := !i + fl)
      else (Buffer.add_char buf s.[!i]; incr i) done;
    VString (Buffer.contents buf)
  | "TYPEOF" -> (match eval_expr env (List.hd args) with VNull -> VString "NULL" | VInt _ -> VString "INT" | VFloat _ -> VString "FLOAT" | VString _ -> VString "TEXT" | VBool _ -> VString "BOOL")
  | "COUNT"|"SUM"|"AVG"|"MIN"|"MAX" -> eval_expr env (List.hd args)
  | _ -> raise (EvalError (Printf.sprintf "Unknown function: %s" name))

let is_truthy = function VBool true -> true | VInt n -> n<>0 | VFloat f -> f<>0.0 | VString s -> s<>"" | _ -> false

let build_env parts =
  let env = ref [] in
  List.iter (fun (tname, alias, cols, vals) ->
    List.iteri (fun i col ->
      let v = if i < Array.length vals then vals.(i) else VNull in
      env := (col.col_name, v) :: !env;
      env := (tname ^ "." ^ col.col_name, v) :: !env;
      (match alias with Some a -> env := (a ^ "." ^ col.col_name, v) :: !env | None -> ())
    ) cols) parts; !env

type agg_acc = { mutable count: int; mutable sum: float; mutable min_v: value; mutable max_v: value }
let new_agg () = { count = 0; sum = 0.0; min_v = VNull; max_v = VNull }
let agg_add acc v = if v <> VNull then begin
  acc.count <- acc.count + 1; acc.sum <- acc.sum +. value_to_float v;
  (match acc.min_v with VNull -> acc.min_v <- v | m -> if compare_values v m < 0 then acc.min_v <- v);
  (match acc.max_v with VNull -> acc.max_v <- v | m -> if compare_values v m > 0 then acc.max_v <- v) end

let has_aggregate expr =
  let found = ref false in
  let rec check = function
    | FuncCall (n,_) when List.mem n ["COUNT";"SUM";"AVG";"MIN";"MAX"] -> found := true
    | FuncCall (_,args) -> List.iter check args | BinOp (_,a,b) -> check a; check b
    | UnaryOp (_,e) -> check e | _ -> () in check expr; !found

let has_aggregate_items items =
  List.exists (fun si -> match si with SelectExpr (e,_) -> has_aggregate e | SelectAll -> false) items

let exec_select db sel =
  let resolve (name, alias) = match find_table db name with
    | Some t -> (t, alias) | None -> raise (EvalError (Printf.sprintf "Table '%s' not found" name)) in
  let tables = List.map resolve sel.from in
  let join_tables = List.map (fun j -> match find_table db j.join_table with
    | Some t -> (t, j) | None -> raise (EvalError (Printf.sprintf "Table '%s' not found" j.join_table))) sel.joins in

  let base_rows = match tables with
    | [] -> [[]]
    | (t, a) :: rest ->
      let init = List.map (fun row -> [(t.name, a, t.columns, row)]) t.rows in
      List.fold_left (fun acc (t2, a2) ->
        List.concat_map (fun existing -> List.map (fun row -> existing @ [(t2.name, a2, t2.columns, row)]) t2.rows) acc
      ) init rest in

  let joined_rows = List.fold_left (fun rows (jt, jc) ->
    List.concat_map (fun existing ->
      let matching = List.filter_map (fun jrow ->
        let combined = existing @ [(jt.name, jc.join_alias, jt.columns, jrow)] in
        if is_truthy (eval_expr (build_env combined) jc.join_on) then Some combined else None) jt.rows in
      if matching = [] then [] else matching) rows) base_rows join_tables in

  let filtered = match sel.where with None -> joined_rows
    | Some cond -> List.filter (fun rp -> is_truthy (eval_expr (build_env rp) cond)) joined_rows in

  let all_columns rp = List.concat_map (fun (_tn, _al, cols, _) -> List.map (fun c -> c.col_name) cols) rp in

  let resolve_items rp = List.concat_map (fun item -> match item with
    | SelectAll -> List.map (fun cn -> (cn, Column cn)) (all_columns rp)
    | SelectExpr (e, alias) ->
      let name = match alias with Some a -> a | None -> match e with Column c -> c | QualColumn (_,c) -> c | FuncCall (f,_) -> f | _ -> "?" in
      [(name, e)]) sel.items in

  let needs_group = sel.group_by <> [] || has_aggregate_items sel.items in

  if needs_group then begin
    let groups = Hashtbl.create 16 in
    List.iter (fun rp -> let env = build_env rp in
      let key = List.map (fun ge -> eval_expr env ge) sel.group_by in
      Hashtbl.replace groups key (rp :: (try Hashtbl.find groups key with Not_found -> []))) filtered;
    if sel.group_by = [] && Hashtbl.length groups = 0 then Hashtbl.add groups [] filtered;

    let result_rows = Hashtbl.fold (fun _ group_rows acc ->
      let sample = match group_rows with r::_ -> r | [] -> [] in
      let items = resolve_items sample in
      let row_vals = List.map (fun (_, expr) ->
        let rec eval_agg = function
          | FuncCall ("COUNT", [Star]) -> VInt (List.length group_rows)
          | FuncCall ("COUNT", [arg]) ->
            VInt (List.fold_left (fun n rp -> if eval_expr (build_env rp) arg <> VNull then n+1 else n) 0 group_rows)
          | FuncCall (("SUM"|"AVG"|"MIN"|"MAX" as fn), [arg]) ->
            let a = new_agg () in List.iter (fun rp -> agg_add a (eval_expr (build_env rp) arg)) group_rows;
            (match fn with "SUM" -> if a.count=0 then VNull else VFloat a.sum
             | "AVG" -> if a.count=0 then VNull else VFloat (a.sum /. float_of_int a.count)
             | "MIN" -> a.min_v | "MAX" -> a.max_v | _ -> VNull)
          | BinOp (op, a, b) -> eval_expr [("__a", eval_agg a); ("__b", eval_agg b)] (BinOp (op, Column "__a", Column "__b"))
          | e -> eval_expr (build_env sample) e
        in eval_agg expr) items in
      let cn = List.map fst items in
      let pass = match sel.having with None -> true
        | Some cond -> is_truthy (eval_expr (List.combine cn row_vals) cond) in
      if pass then (cn, Array.of_list row_vals) :: acc else acc) groups [] in

    let col_names = match result_rows with (cn,_)::_ -> cn | [] -> List.map fst (resolve_items []) in
    let rows = List.map snd result_rows in
    let col_idx name = let nl = String.lowercase_ascii name in
      let rec find i = function [] -> -1 | cn::rest -> if String.lowercase_ascii cn = nl then i else find (i+1) rest in find 0 col_names in
    let ordered = if sel.order_by = [] then rows else
      List.sort (fun a b -> List.fold_left (fun acc (oe,asc) ->
        if acc<>0 then acc else
        let va = match oe with Column c -> let i = col_idx c in if i>=0 && i < Array.length a then a.(i) else VNull | _ -> VNull in
        let vb = match oe with Column c -> let i = col_idx c in if i>=0 && i < Array.length b then b.(i) else VNull | _ -> VNull in
        let c = compare_values va vb in if asc then c else -c) 0 sel.order_by) rows in
    let limited = match sel.limit with None -> ordered | Some n -> List.filteri (fun i _ -> i < n) ordered in
    let final = if sel.distinct then let seen = Hashtbl.create 16 in
      List.filter (fun row -> let key = Array.to_list row |> List.map value_to_string |> String.concat "|" in
        if Hashtbl.mem seen key then false else (Hashtbl.add seen key (); true)) limited else limited in
    (col_names, final)
  end else begin
    let col_names = ref [] in
    let result_rows = List.map (fun rp ->
      let items = resolve_items rp in
      if !col_names = [] then col_names := List.map fst items;
      Array.of_list (List.map (fun (_,e) -> eval_expr (build_env rp) e) items)) filtered in
    if !col_names = [] then col_names := List.map (fun item -> match item with
      | SelectAll -> "*" | SelectExpr (_, Some a) -> a | SelectExpr (Column c, _) -> c
      | SelectExpr (FuncCall (f,_), _) -> f | _ -> "?") sel.items;
    let col_idx name = let nl = String.lowercase_ascii name in
      let rec find i = function [] -> -1 | cn::rest -> if String.lowercase_ascii cn = nl then i else find (i+1) rest in find 0 !col_names in
    let ordered = if sel.order_by = [] then result_rows else
      List.sort (fun a b -> List.fold_left (fun acc (oe,asc) ->
        if acc<>0 then acc else
        let get arr = match oe with Column c -> let i = col_idx c in if i>=0 && i < Array.length arr then arr.(i) else VNull | _ -> VNull in
        let c = compare_values (get a) (get b) in if asc then c else -c) 0 sel.order_by) result_rows in
    let limited = match sel.limit with None -> ordered | Some n -> List.filteri (fun i _ -> i < n) ordered in
    let final = if sel.distinct then let seen = Hashtbl.create 16 in
      List.filter (fun row -> let key = Array.to_list row |> List.map value_to_string |> String.concat "|" in
        if Hashtbl.mem seen key then false else (Hashtbl.add seen key (); true)) limited else limited in
    (!col_names, final)
  end

let execute db stmt = match stmt with
  | CreateTable (name, cols) ->
    if find_table db name <> None then Printf.printf "Error: Table '%s' already exists.\n" name
    else (db.tables <- { name; columns = cols; rows = [] } :: db.tables;
      Printf.printf "Table '%s' created (%d columns).\n" name (List.length cols))
  | Insert (tname, col_names, value_rows) ->
    (match find_table db tname with None -> Printf.printf "Error: Table '%s' not found.\n" tname
     | Some tbl ->
       let col_order = match col_names with None -> List.mapi (fun i _ -> i) tbl.columns
         | Some names -> List.map (fun n -> let nl = String.lowercase_ascii n in
           match List.find_index (fun c -> String.lowercase_ascii c.col_name = nl) tbl.columns with
           | Some i -> i | None -> raise (EvalError (Printf.sprintf "Column '%s' not found" n))) names in
       let ncols = List.length tbl.columns in
       List.iter (fun vals -> let row = Array.make ncols VNull in
         List.iteri (fun i v -> if i < List.length col_order then row.(List.nth col_order i) <- v) vals;
         tbl.rows <- tbl.rows @ [row]) value_rows;
       Printf.printf "%d row(s) inserted into '%s'.\n" (List.length value_rows) tname)
  | Select sel ->
    let (col_names, rows) = exec_select db sel in
    let ncols = List.length col_names in
    if ncols = 0 then Printf.printf "(empty result)\n"
    else begin
      let widths = Array.make ncols 0 in
      List.iteri (fun i name -> widths.(i) <- String.length name) col_names;
      List.iter (fun row -> for i = 0 to min ncols (Array.length row) - 1 do
        widths.(i) <- max widths.(i) (String.length (value_to_string row.(i))) done) rows;
      let sep = String.concat "-+-" (List.init ncols (fun i -> String.make (widths.(i)+2) '-')) in
      Printf.printf " %s \n" sep;
      List.iteri (fun i name -> Printf.printf " %-*s " widths.(i) name; if i < ncols-1 then Printf.printf "| ") col_names;
      Printf.printf "\n %s \n" sep;
      List.iter (fun row -> for i = 0 to ncols-1 do
        let v = if i < Array.length row then value_to_string row.(i) else "NULL" in
        Printf.printf " %-*s " widths.(i) v; if i < ncols-1 then Printf.printf "| " done;
        Printf.printf "\n") rows;
      Printf.printf " %s \n" sep;
      Printf.printf "(%d row%s)\n" (List.length rows) (if List.length rows = 1 then "" else "s") end
  | Update (tname, sets, where) ->
    (match find_table db tname with None -> Printf.printf "Error: Table '%s' not found.\n" tname
     | Some tbl -> let count = ref 0 in
       tbl.rows <- List.map (fun row ->
         let env = List.concat_map (fun (i,col) -> [(col.col_name, if i < Array.length row then row.(i) else VNull)])
           (List.mapi (fun i c -> (i,c)) tbl.columns) in
         if (match where with None -> true | Some cond -> is_truthy (eval_expr env cond)) then begin
           incr count; let nr = Array.copy row in
           List.iter (fun (cn, expr) -> match List.find_index (fun c -> String.lowercase_ascii c.col_name = String.lowercase_ascii cn) tbl.columns with
             | Some i -> nr.(i) <- eval_expr env expr | None -> raise (EvalError (Printf.sprintf "Column '%s' not found" cn))) sets; nr
         end else row) tbl.rows;
       Printf.printf "%d row(s) updated.\n" !count)
  | Delete (tname, where) ->
    (match find_table db tname with None -> Printf.printf "Error: Table '%s' not found.\n" tname
     | Some tbl -> let before = List.length tbl.rows in
       tbl.rows <- List.filter (fun row ->
         let env = List.concat_map (fun (i,col) -> [(col.col_name, if i < Array.length row then row.(i) else VNull)])
           (List.mapi (fun i c -> (i,c)) tbl.columns) in
         match where with None -> false | Some cond -> not (is_truthy (eval_expr env cond))) tbl.rows;
       Printf.printf "%d row(s) deleted.\n" (before - List.length tbl.rows))
  | DropTable name ->
    if find_table db name = None then Printf.printf "Error: Table '%s' not found.\n" name
    else (db.tables <- List.filter (fun t -> String.lowercase_ascii t.name <> String.lowercase_ascii name) db.tables;
      Printf.printf "Table '%s' dropped.\n" name)
  | ShowTables ->
    Printf.printf "Tables:\n";
    List.iter (fun t -> Printf.printf "  %s (%d cols, %d rows)\n" t.name (List.length t.columns) (List.length t.rows)) db.tables;
    Printf.printf "(%d table%s)\n" (List.length db.tables) (if List.length db.tables = 1 then "" else "s")
  | Describe tname ->
    (match find_table db tname with None -> Printf.printf "Error: Table '%s' not found.\n" tname
     | Some tbl ->
       Printf.printf "Table: %s (%d rows)\n" tbl.name (List.length tbl.rows);
       Printf.printf "  %-20s %s\n" "Column" "Type"; Printf.printf "  %-20s %s\n" "--------------------" "------";
       List.iter (fun c -> Printf.printf "  %-20s %s\n" c.col_name c.col_type) tbl.columns)

let load_demo db =
  let run sql = execute db (parse sql) in
  run "CREATE TABLE employees (id INT, name TEXT, department TEXT, salary INT, age INT)";
  run "INSERT INTO employees VALUES (1, 'Alice', 'Engineering', 95000, 30), (2, 'Bob', 'Engineering', 88000, 28), (3, 'Carol', 'Marketing', 72000, 35), (4, 'Dave', 'Marketing', 68000, 42), (5, 'Eve', 'Engineering', 105000, 33), (6, 'Frank', 'Sales', 62000, 25), (7, 'Grace', 'Sales', 71000, 29), (8, 'Hank', 'Engineering', 92000, 31)";
  run "CREATE TABLE departments (name TEXT, floor INT, budget INT)";
  run "INSERT INTO departments VALUES ('Engineering', 3, 500000), ('Marketing', 2, 200000), ('Sales', 1, 150000)";
  run "CREATE TABLE products (id INT, name TEXT, price FLOAT, category TEXT, stock INT)";
  run "INSERT INTO products VALUES (1, 'Laptop', 999.99, 'Electronics', 50), (2, 'Mouse', 29.99, 'Electronics', 200), (3, 'Desk', 349.50, 'Furniture', 30), (4, 'Chair', 249.00, 'Furniture', 45), (5, 'Monitor', 449.99, 'Electronics', 75), (6, 'Keyboard', 79.99, 'Electronics', 150), (7, 'Bookshelf', 189.00, 'Furniture', 20)"

let () =
  let db = create_db () in
  Printf.printf "╔══════════════════════════════════════════════╗\n";
  Printf.printf "║       Mini SQL Query Engine v1.0             ║\n";
  Printf.printf "║  An in-memory SQL engine written in OCaml    ║\n";
  Printf.printf "╠══════════════════════════════════════════════╣\n";
  Printf.printf "║  Commands:                                   ║\n";
  Printf.printf "║    CREATE TABLE, INSERT, SELECT, UPDATE,     ║\n";
  Printf.printf "║    DELETE, DROP TABLE, SHOW TABLES, DESCRIBE ║\n";
  Printf.printf "║  Features:                                   ║\n";
  Printf.printf "║    WHERE, ORDER BY, LIMIT, JOIN, GROUP BY,   ║\n";
  Printf.printf "║    HAVING, DISTINCT, BETWEEN, LIKE, IN,      ║\n";
  Printf.printf "║    COUNT/SUM/AVG/MIN/MAX, UPPER/LOWER/...    ║\n";
  Printf.printf "║  Type 'demo' to load sample data             ║\n";
  Printf.printf "║  Type 'help' for example queries             ║\n";
  Printf.printf "║  Type 'quit' or 'exit' to leave              ║\n";
  Printf.printf "╚══════════════════════════════════════════════╝\n\n";
  let print_help () =
    Printf.printf "\n=== Example Queries ===\n\n";
    Printf.printf "  demo                                    -- Load sample tables\n";
    Printf.printf "  SHOW TABLES                             -- List all tables\n";
    Printf.printf "  DESCRIBE employees                      -- Show table schema\n";
    Printf.printf "  SELECT * FROM employees                 -- All rows\n";
    Printf.printf "  SELECT name, salary FROM employees\n";
    Printf.printf "    WHERE salary > 80000 ORDER BY salary DESC\n";
    Printf.printf "  SELECT department, COUNT(*), AVG(salary)\n";
    Printf.printf "    FROM employees GROUP BY department\n";
    Printf.printf "  SELECT e.name, d.floor FROM employees e\n";
    Printf.printf "    JOIN departments d ON e.department = d.name\n";
    Printf.printf "  SELECT DISTINCT category FROM products\n";
    Printf.printf "  SELECT * FROM products WHERE price BETWEEN 100 AND 500\n";
    Printf.printf "  UPDATE products SET stock = stock + 10 WHERE category = 'Furniture'\n";
    Printf.printf "  DELETE FROM products WHERE stock < 25\n\n" in
  let running = ref true in
  while !running do
    Printf.printf "sql> %!";
    match (try Some (input_line stdin) with End_of_file -> None) with
    | None -> running := false
    | Some l ->
      let trimmed = String.trim l in
      let trimmed = if String.length trimmed > 0 && trimmed.[String.length trimmed - 1] = ';'
        then String.sub trimmed 0 (String.length trimmed - 1) |> String.trim else trimmed in
      if trimmed = "" then ()
      else if String.lowercase_ascii trimmed = "quit" || String.lowercase_ascii trimmed = "exit" then
        (Printf.printf "Goodbye!\n"; running := false)
      else if String.lowercase_ascii trimmed = "demo" then
        (Printf.printf "Loading demo data...\n"; load_demo db; Printf.printf "Demo tables loaded: employees, departments, products\n")
      else if String.lowercase_ascii trimmed = "help" then print_help ()
      else (try execute db (parse trimmed) with
        | ParseError msg -> Printf.printf "Parse error: %s\n" msg
        | EvalError msg -> Printf.printf "Error: %s\n" msg
        | e -> Printf.printf "Error: %s\n" (Printexc.to_string e))
  done
