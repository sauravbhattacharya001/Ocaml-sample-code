(* JSON Parser — A Complete JSON Parser Built with Parser Combinators *)
(* Demonstrates: recursive descent, mutual recursion, string escaping,
   floating-point parsing, unicode escapes, pretty printing, JSON queries *)

(* =========================================================== *)
(*   Parser Combinator Core (self-contained)                    *)
(* =========================================================== *)

type 'a result =
  | Ok of 'a * int
  | Error of string * int

type 'a parser = string -> int -> 'a result

let satisfy (pred : char -> bool) (desc : string) : char parser =
  fun input pos ->
    if pos >= String.length input then
      Error (Printf.sprintf "unexpected end of input, expected %s" desc, pos)
    else
      let c = input.[pos] in
      if pred c then Ok (c, pos + 1)
      else Error (Printf.sprintf "expected %s, got '%c'" desc c, pos)

let char_ (expected : char) : char parser =
  satisfy (fun c -> c = expected) (Printf.sprintf "'%c'" expected)

let string_ (expected : string) : string parser =
  fun input pos ->
    let len = String.length expected in
    if pos + len > String.length input then
      Error (Printf.sprintf "expected \"%s\"" expected, pos)
    else
      let sub = String.sub input pos len in
      if sub = expected then Ok (expected, pos + len)
      else Error (Printf.sprintf "expected \"%s\", got \"%s\"" expected sub, pos)

let return_ (x : 'a) : 'a parser =
  fun _input pos -> Ok (x, pos)

let fail (msg : string) : 'a parser =
  fun _input pos -> Error (msg, pos)

let bind (p : 'a parser) (f : 'a -> 'b parser) : 'b parser =
  fun input pos ->
    match p input pos with
    | Error (msg, epos) -> Error (msg, epos)
    | Ok (a, pos') -> (f a) input pos'

let ( >>= ) = bind
let ( *> ) p1 p2 = p1 >>= fun _ -> p2
let ( <* ) p1 p2 = p1 >>= fun a -> p2 >>= fun _ -> return_ a

let map (f : 'a -> 'b) (p : 'a parser) : 'b parser =
  p >>= fun a -> return_ (f a)

let ( <|> ) (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun input pos ->
    match p1 input pos with
    | Ok _ as result -> result
    | Error (_, epos1) as err ->
      if epos1 = pos then p2 input pos
      else err

let try_ (p : 'a parser) : 'a parser =
  fun input pos ->
    match p input pos with
    | Ok _ as result -> result
    | Error (msg, _) -> Error (msg, pos)

let many (p : 'a parser) : 'a list parser =
  fun input pos ->
    let rec aux acc pos =
      match p input pos with
      | Error _ -> Ok (List.rev acc, pos)
      | Ok (x, pos') ->
        if pos' = pos then Ok (List.rev acc, pos)
        else aux (x :: acc) pos'
    in
    aux [] pos

let many1 (p : 'a parser) : 'a list parser =
  p >>= fun first ->
  many p >>= fun rest ->
  return_ (first :: rest)

let sep_by (p : 'a parser) (sep : 'b parser) : 'a list parser =
  (p >>= fun first ->
   many (sep *> p) >>= fun rest ->
   return_ (first :: rest))
  <|> return_ []

let between (open_ : 'a parser) (close_ : 'b parser) (p : 'c parser) : 'c parser =
  open_ *> p <* close_

let optional (p : 'a parser) : 'a option parser =
  (map (fun x -> Some x) p) <|> return_ None

let whitespace : char parser =
  satisfy (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r') "whitespace"

let spaces : unit parser =
  map (fun _ -> ()) (many whitespace)

let lexeme (p : 'a parser) : 'a parser =
  spaces *> p <* spaces

let run (p : 'a parser) (input : string) : ('a, string) Stdlib.result =
  match (spaces *> p <* spaces) input 0 with
  | Ok (value, pos) ->
    if pos = String.length input then Stdlib.Ok value
    else Stdlib.Error (Printf.sprintf "unexpected character '%c' at position %d"
      input.[pos] pos)
  | Error (msg, pos) ->
    Stdlib.Error (Printf.sprintf "%s at position %d" msg pos)

(* =========================================================== *)
(*   JSON Data Type                                             *)
(* =========================================================== *)

(* JSON values as an algebraic data type — the natural OCaml way *)
type json =
  | Null
  | Bool of bool
  | Number of float
  | String of string
  | Array of json list
  | Object of (string * json) list

(* =========================================================== *)
(*   JSON Parser                                                *)
(* =========================================================== *)

(* ── Depth-limited parsing ──────────────────────────────────── *)
(* Protects against stack overflow from deeply nested JSON.     *)
(* A mutable counter is incremented on '[' / '{' and decremented*)
(* on return; parsing fails when the depth exceeds the limit.   *)

(** Maximum nesting depth allowed during parsing (arrays + objects).
    Default 512 — generous for real-world JSON, but prevents
    pathological inputs like 100 000 nested brackets from
    blowing the OCaml call stack. *)
let max_parse_depth = ref 512

let current_depth = ref 0

let with_depth_check (p : json parser) : json parser =
  fun input pos ->
    if !current_depth >= !max_parse_depth then
      Error (Printf.sprintf "maximum nesting depth (%d) exceeded" !max_parse_depth, pos)
    else begin
      incr current_depth;
      Fun.protect
        ~finally:(fun () -> decr current_depth)
        (fun () -> p input pos)
    end

(* Forward reference for recursive grammar *)
let json_parser_ref : json parser ref = ref (fail "not initialized")

let json_null : json parser =
  string_ "null" *> return_ Null

let json_bool : json parser =
  (string_ "true" *> return_ (Bool true))
  <|> (string_ "false" *> return_ (Bool false))

(* JSON numbers: -? (0 | [1-9][0-9]*) (.[0-9]+)? ([eE][+-]?[0-9]+)? *)
let json_number : json parser =
  fun input pos ->
    let start = pos in
    let pos = if pos < String.length input && input.[pos] = '-' then pos + 1 else pos in
    if pos >= String.length input || not (input.[pos] >= '0' && input.[pos] <= '9') then
      Error ("expected number", start)
    else
      let pos =
        if input.[pos] = '0' then pos + 1
        else
          let p = ref pos in
          while !p < String.length input && input.[!p] >= '0' && input.[!p] <= '9' do incr p done;
          !p
      in
      let pos =
        if pos < String.length input && input.[pos] = '.' then
          let p = ref (pos + 1) in
          if !p >= String.length input || not (input.[!p] >= '0' && input.[!p] <= '9') then pos
          else begin
            while !p < String.length input && input.[!p] >= '0' && input.[!p] <= '9' do incr p done;
            !p
          end
        else pos
      in
      let pos =
        if pos < String.length input && (input.[pos] = 'e' || input.[pos] = 'E') then
          let p = ref (pos + 1) in
          if !p < String.length input && (input.[!p] = '+' || input.[!p] = '-') then incr p;
          if !p >= String.length input || not (input.[!p] >= '0' && input.[!p] <= '9') then pos
          else begin
            while !p < String.length input && input.[!p] >= '0' && input.[!p] <= '9' do incr p done;
            !p
          end
        else pos
      in
      let s = String.sub input start (pos - start) in
      (try Ok (Number (float_of_string s), pos)
       with Failure _ -> Error ("invalid number", start))

(* String parsing with escape sequences: \" \\ \/ \b \f \n \r \t \uXXXX *)
let hex_digit : char parser =
  satisfy (fun c ->
    (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'))
    "hex digit"

let hex_value (c : char) : int =
  if c >= '0' && c <= '9' then Char.code c - Char.code '0'
  else if c >= 'a' && c <= 'f' then 10 + Char.code c - Char.code 'a'
  else 10 + Char.code c - Char.code 'A'

(* Convert a Unicode code point to UTF-8 bytes *)
let utf8_of_codepoint (cp : int) : string =
  if cp >= 0xD800 && cp <= 0xDFFF then
    invalid_arg (Printf.sprintf "utf8_of_codepoint: surrogate U+%04X is not a valid Unicode scalar value" cp)
  else if cp < 0 || cp > 0x10FFFF then
    invalid_arg (Printf.sprintf "utf8_of_codepoint: U+%X out of range (0..10FFFF)" cp)
  else if cp < 0x80 then
    String.make 1 (Char.chr cp)
  else if cp < 0x800 then
    Printf.sprintf "%c%c"
      (Char.chr (0xC0 lor (cp lsr 6)))
      (Char.chr (0x80 lor (cp land 0x3F)))
  else if cp < 0x10000 then
    Printf.sprintf "%c%c%c"
      (Char.chr (0xE0 lor (cp lsr 12)))
      (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)))
      (Char.chr (0x80 lor (cp land 0x3F)))
  else
    Printf.sprintf "%c%c%c%c"
      (Char.chr (0xF0 lor (cp lsr 18)))
      (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)))
      (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)))
      (Char.chr (0x80 lor (cp land 0x3F)))

let escape_sequence : string parser =
  char_ '\\' *> (
    (char_ '"' *> return_ "\"")
    <|> (char_ '\\' *> return_ "\\")
    <|> (char_ '/' *> return_ "/")
    <|> (char_ 'b' *> return_ "\b")
    <|> (char_ 'f' *> return_ (String.make 1 (Char.chr 12)))
    <|> (char_ 'n' *> return_ "\n")
    <|> (char_ 'r' *> return_ "\r")
    <|> (char_ 't' *> return_ "\t")
    <|> (char_ 'u' *>
         hex_digit >>= fun h1 ->
         hex_digit >>= fun h2 ->
         hex_digit >>= fun h3 ->
         hex_digit >>= fun h4 ->
         let cp = (hex_value h1 lsl 12) lor (hex_value h2 lsl 8)
                  lor (hex_value h3 lsl 4) lor (hex_value h4) in
         if cp >= 0xD800 && cp <= 0xDBFF then
           char_ '\\' *> char_ 'u' *>
           hex_digit >>= fun l1 ->
           hex_digit >>= fun l2 ->
           hex_digit >>= fun l3 ->
           hex_digit >>= fun l4 ->
           let low = (hex_value l1 lsl 12) lor (hex_value l2 lsl 8)
                     lor (hex_value l3 lsl 4) lor (hex_value l4) in
           if low >= 0xDC00 && low <= 0xDFFF then
             let full = 0x10000 + ((cp - 0xD800) lsl 10) + (low - 0xDC00) in
             return_ (utf8_of_codepoint full)
           else
             fail "invalid low surrogate"
         else if cp >= 0xDC00 && cp <= 0xDFFF then
           fail "lone low surrogate (U+DC00..U+DFFF) is not valid JSON"
         else
           return_ (utf8_of_codepoint cp))
  )

let string_char : string parser =
  escape_sequence
  <|> (satisfy (fun c -> c <> '"' && c <> '\\' && Char.code c >= 0x20)
         "string character"
       |> map (String.make 1))

let json_string_raw : string parser =
  char_ '"' *>
  many string_char >>= fun parts ->
  char_ '"' *>
  return_ (String.concat "" parts)

let json_string : json parser =
  map (fun s -> String s) json_string_raw

let json_array : json parser =
  with_depth_check (
    between
      (lexeme (char_ '['))
      (char_ ']')
      (sep_by (lexeme (fun input pos -> !json_parser_ref input pos))
              (lexeme (char_ ',')))
    |> map (fun items -> Array items)
  )

let json_pair : (string * json) parser =
  lexeme json_string_raw >>= fun key ->
  lexeme (char_ ':') *>
  lexeme (fun input pos -> !json_parser_ref input pos) >>= fun value ->
  return_ (key, value)

let json_object : json parser =
  with_depth_check (
    between
      (lexeme (char_ '{'))
      (char_ '}')
      (sep_by json_pair (lexeme (char_ ',')))
    |> map (fun pairs -> Object pairs)
  )

let json_value : json parser =
  lexeme (
    try_ json_null
    <|> try_ json_bool
    <|> try_ json_number
    <|> try_ json_string
    <|> try_ json_array
    <|> json_object
  )

let () = json_parser_ref := json_value

let parse ?(max_depth = 512) (input : string) : (json, string) Stdlib.result =
  max_parse_depth := max_depth;
  current_depth := 0;
  run json_value input

(* =========================================================== *)
(*   Pretty Printer                                             *)
(* =========================================================== *)

let rec to_string_compact (j : json) : string =
  match j with
  | Null -> "null"
  | Bool b -> if b then "true" else "false"
  | Number n ->
    if Float.is_integer n && Float.is_finite n then
      string_of_int (int_of_float n)
    else Printf.sprintf "%.17g" n
  | String s -> "\"" ^ escape_json_string s ^ "\""
  | Array items ->
    "[" ^ String.concat "," (List.map to_string_compact items) ^ "]"
  | Object pairs ->
    "{" ^ String.concat ","
      (List.map (fun (k, v) ->
        "\"" ^ escape_json_string k ^ "\":" ^ to_string_compact v) pairs)
    ^ "}"

and escape_json_string (s : string) : string =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c ->
    match c with
    | '"' -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '/' -> Buffer.add_string buf "\\/"  (* prevent </script> XSS in HTML contexts *)
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
      Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let to_string_pretty ?(indent=2) (j : json) : string =
  let buf = Buffer.create 256 in
  let rec pp depth j =
    let pad = String.make (depth * indent) ' ' in
    let pad_inner = String.make ((depth + 1) * indent) ' ' in
    match j with
    | Null -> Buffer.add_string buf "null"
    | Bool b -> Buffer.add_string buf (if b then "true" else "false")
    | Number n ->
      if Float.is_integer n && Float.is_finite n then
        Buffer.add_string buf (string_of_int (int_of_float n))
      else Buffer.add_string buf (Printf.sprintf "%.17g" n)
    | String s ->
      Buffer.add_char buf '"';
      Buffer.add_string buf (escape_json_string s);
      Buffer.add_char buf '"'
    | Array [] -> Buffer.add_string buf "[]"
    | Array items ->
      Buffer.add_string buf "[\n";
      List.iteri (fun i item ->
        Buffer.add_string buf pad_inner;
        pp (depth + 1) item;
        if i < List.length items - 1 then Buffer.add_char buf ',';
        Buffer.add_char buf '\n'
      ) items;
      Buffer.add_string buf pad;
      Buffer.add_char buf ']'
    | Object [] -> Buffer.add_string buf "{}"
    | Object pairs ->
      Buffer.add_string buf "{\n";
      List.iteri (fun i (k, v) ->
        Buffer.add_string buf pad_inner;
        Buffer.add_char buf '"';
        Buffer.add_string buf (escape_json_string k);
        Buffer.add_string buf "\": ";
        pp (depth + 1) v;
        if i < List.length pairs - 1 then Buffer.add_char buf ',';
        Buffer.add_char buf '\n'
      ) pairs;
      Buffer.add_string buf pad;
      Buffer.add_char buf '}'
  in
  pp 0 j;
  Buffer.contents buf

(* =========================================================== *)
(*   JSON Query — dot-notation path access                     *)
(* =========================================================== *)

let query (path : string) (j : json) : json option =
  let segments =
    let parts = ref [] in
    let buf = Buffer.create 16 in
    String.iter (fun c ->
      if c = '.' then begin
        parts := Buffer.contents buf :: !parts;
        Buffer.clear buf
      end else
        Buffer.add_char buf c
    ) path;
    parts := Buffer.contents buf :: !parts;
    List.rev !parts
  in
  let rec follow segments j =
    match segments with
    | [] -> Some j
    | seg :: rest ->
      match j with
      | Object pairs ->
        (match List.assoc_opt seg pairs with
         | Some child -> follow rest child
         | None -> None)
      | Array items ->
        (try
           let idx = int_of_string seg in
           let idx = if idx < 0 then List.length items + idx else idx in
           if idx >= 0 && idx < List.length items then
             follow rest (List.nth items idx)
           else None
         with Failure _ -> None)
      | _ -> None
  in
  if path = "" then Some j
  else follow segments j

(* =========================================================== *)
(*   JSON Utilities                                             *)
(* =========================================================== *)

let rec equal (a : json) (b : json) : bool =
  match a, b with
  | Null, Null -> true
  | Bool a, Bool b -> a = b
  | Number a, Number b -> a = b
  | String a, String b -> a = b
  | Array a, Array b ->
    List.length a = List.length b && List.for_all2 equal a b
  | Object a, Object b ->
    List.length a = List.length b &&
    List.for_all (fun (k, v) ->
      match List.assoc_opt k b with Some v' -> equal v v' | None -> false) a
  | _ -> false

let type_name = function
  | Null -> "null" | Bool _ -> "boolean" | Number _ -> "number"
  | String _ -> "string" | Array _ -> "array" | Object _ -> "object"

let is_null = function Null -> true | _ -> false
let is_bool = function Bool _ -> true | _ -> false
let is_number = function Number _ -> true | _ -> false
let is_string = function String _ -> true | _ -> false
let is_array = function Array _ -> true | _ -> false
let is_object = function Object _ -> true | _ -> false

let keys = function Object pairs -> Some (List.map fst pairs) | _ -> None
let values = function Object pairs -> Some (List.map snd pairs) | _ -> None
let length = function
  | Array items -> Some (List.length items)
  | Object pairs -> Some (List.length pairs)
  | String s -> Some (String.length s)
  | _ -> None

(* =========================================================== *)
(*   JSON Transform — map/filter/fold/merge                    *)
(* =========================================================== *)

let map_array (f : json -> json) = function
  | Array items -> Array (List.map f items) | other -> other

let filter_array (f : json -> bool) = function
  | Array items -> Array (List.filter f items) | other -> other

let fold_array (f : 'a -> json -> 'a) (init : 'a) = function
  | Array items -> List.fold_left f init items | _ -> init

let map_object (f : string -> json -> json) = function
  | Object pairs -> Object (List.map (fun (k, v) -> (k, f k v)) pairs) | other -> other

let filter_object (f : string -> json -> bool) = function
  | Object pairs -> Object (List.filter (fun (k, v) -> f k v) pairs) | other -> other

let merge (a : json) (b : json) : json =
  match a, b with
  | Object pa, Object pb ->
    let merged = List.fold_left (fun acc (k, v) ->
      if List.mem_assoc k acc then
        List.map (fun (k', v') -> if k' = k then (k, v) else (k', v')) acc
      else acc @ [(k, v)]
    ) pa pb in
    Object merged
  | _, b -> b

(* Construction helpers *)
let null = Null
let bool_ b = Bool b
let number n = Number n
let int_ n = Number (float_of_int n)

(* =========================================================== *)
(*   Example Usage & Demo                                       *)
(* =========================================================== *)

let () =
  print_endline "=== JSON Parser ===";
  print_endline "A complete JSON parser built with parser combinators\n";

  print_endline "--- Basic values ---";
  List.iter (fun input ->
    match parse input with
    | Stdlib.Ok json ->
      Printf.printf "  %-25s => %s (%s)\n" input (to_string_compact json) (type_name json)
    | Stdlib.Error msg ->
      Printf.printf "  %-25s => Error: %s\n" input msg
  ) [ "null"; "true"; "false"; "42"; "-7"; "3.14"; "1.5e10"; "2.998e8";
      "\"hello\""; "\"hello\\nworld\""; "\"\\u0041\\u0042\"" ];
  print_newline ();

  print_endline "--- Arrays ---";
  List.iter (fun input ->
    match parse input with
    | Stdlib.Ok json -> Printf.printf "  %s\n    => %s\n" input (to_string_compact json)
    | Stdlib.Error msg -> Printf.printf "  %s\n    => Error: %s\n" input msg
  ) [ "[]"; "[1, 2, 3]"; "[\"a\", true, null]"; "[[1, 2], [3, 4]]" ];
  print_newline ();

  print_endline "--- Objects ---";
  List.iter (fun input ->
    match parse input with
    | Stdlib.Ok json -> Printf.printf "  %s\n    => %s\n" input (to_string_compact json)
    | Stdlib.Error msg -> Printf.printf "  %s\n    => Error: %s\n" input msg
  ) [ "{}"; "{\"name\": \"Alice\", \"age\": 30}"; "{\"nested\": {\"a\": 1, \"b\": [2, 3]}}" ];
  print_newline ();

  print_endline "--- Pretty printing ---";
  let complex_json = "{\"users\": [{\"name\": \"Alice\", \"age\": 30, \"tags\": [\"admin\", \"user\"]}, {\"name\": \"Bob\", \"age\": 25, \"tags\": [\"user\"]}], \"total\": 2}" in
  (match parse complex_json with
   | Stdlib.Ok json ->
     Printf.printf "Compact: %s\n\n" (to_string_compact json);
     Printf.printf "Pretty:\n%s\n" (to_string_pretty json)
   | Stdlib.Error msg -> Printf.printf "Error: %s\n" msg);
  print_newline ();

  print_endline "--- Dot-notation queries ---";
  let sample = "{\"user\": {\"name\": \"Alice\", \"scores\": [95, 87, 92]}, \"active\": true}" in
  (match parse sample with
   | Stdlib.Ok json ->
     List.iter (fun path ->
       let result = match query path json with
         | Some v -> to_string_compact v | None -> "<not found>"
       in Printf.printf "  $.%-20s => %s\n" path result
     ) ["user.name"; "user.scores"; "user.scores.0"; "user.scores.2";
        "user.scores.-1"; "active"; "missing"; "user.missing.deep"]
   | Stdlib.Error msg -> Printf.printf "Error: %s\n" msg);
  print_newline ();

  print_endline "--- Transform ---";
  (match parse "[1, 2, 3, 4, 5]" with
   | Stdlib.Ok json ->
     let doubled = map_array (function Number n -> Number (n *. 2.0) | x -> x) json in
     let evens = filter_array (function Number n -> mod_float n 2.0 = 0.0 | _ -> false) json in
     let sum = fold_array (fun acc -> function Number n -> acc +. n | _ -> acc) 0.0 json in
     Printf.printf "  original: %s\n" (to_string_compact json);
     Printf.printf "  doubled:  %s\n" (to_string_compact doubled);
     Printf.printf "  evens:    %s\n" (to_string_compact evens);
     Printf.printf "  sum:      %.0f\n" sum
   | Stdlib.Error msg -> Printf.printf "Error: %s\n" msg);
  print_newline ();

  print_endline "--- Round-trip ---";
  List.iter (fun input ->
    match parse input with
    | Stdlib.Ok j1 ->
      let s = to_string_compact j1 in
      (match parse s with
       | Stdlib.Ok j2 ->
         Printf.printf "  %-30s roundtrip: %s\n" input
           (if equal j1 j2 then "OK" else "MISMATCH!")
       | Stdlib.Error _ -> Printf.printf "  %-30s roundtrip: REPARSE FAILED\n" input)
    | Stdlib.Error msg -> Printf.printf "  %-30s parse error: %s\n" input msg
  ) [ "null"; "true"; "42"; "\"hello\""; "[1,[2,[3]]]"; "{\"a\":{\"b\":{\"c\":true}}}" ];

  print_endline "\n=== JSON Parser complete ==="
