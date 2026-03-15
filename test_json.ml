(* test_json.ml — Comprehensive test suite for the JSON parser *)
(* 170+ assertions covering parsing, serialization, queries, equality,
#use "test_framework.ml";;

   transforms, edge cases, and error handling *)

let current_suite = ref ""

let suite name f = current_suite := name; Printf.printf "Running: %s\n" name; f ()

(* ===== Inline JSON parser (self-contained for single-file compilation) ===== *)

type 'a presult = Ok of 'a * int | Error of string * int
type 'a parser = string -> int -> 'a presult

let satisfy pred desc : char parser = fun input pos ->
  if pos >= String.length input then Error ("unexpected end of input, expected " ^ desc, pos)
  else let c = input.[pos] in if pred c then Ok (c, pos + 1) else Error (Printf.sprintf "expected %s, got '%c'" desc c, pos)

let char_ expected = satisfy (fun c -> c = expected) (Printf.sprintf "'%c'" expected)
let string_ expected : string parser = fun input pos ->
  let len = String.length expected in
  if pos + len > String.length input then Error (Printf.sprintf "expected \"%s\"" expected, pos)
  else let sub = String.sub input pos len in
    if sub = expected then Ok (expected, pos + len) else Error (Printf.sprintf "expected \"%s\", got \"%s\"" expected sub, pos)
let return_ x : 'a parser = fun _input pos -> Ok (x, pos)
let fail msg : 'a parser = fun _input pos -> Error (msg, pos)
let bind (p : 'a parser) (f : 'a -> 'b parser) : 'b parser = fun input pos ->
  match p input pos with Error (msg, epos) -> Error (msg, epos) | Ok (a, pos') -> (f a) input pos'
let ( >>= ) = bind
let ( *> ) p1 p2 = p1 >>= fun _ -> p2
let ( <* ) p1 p2 = p1 >>= fun a -> p2 >>= fun _ -> return_ a
let map f p = p >>= fun a -> return_ (f a)
let ( <|> ) p1 p2 : 'a parser = fun input pos ->
  match p1 input pos with Ok _ as r -> r | Error (_, epos) as err -> if epos = pos then p2 input pos else err
let try_ (p : 'a parser) : 'a parser = fun input pos ->
  match p input pos with Ok _ as r -> r | Error (msg, _) -> Error (msg, pos)
let many (p : 'a parser) : 'a list parser = fun input pos ->
  let rec aux acc pos = match p input pos with
    | Error _ -> Ok (List.rev acc, pos) | Ok (x, pos') -> if pos' = pos then Ok (List.rev acc, pos) else aux (x :: acc) pos'
  in aux [] pos
let many1 p = p >>= fun first -> many p >>= fun rest -> return_ (first :: rest)
let sep_by p sep = (p >>= fun first -> many (sep *> p) >>= fun rest -> return_ (first :: rest)) <|> return_ []
let between open_ close_ p = open_ *> p <* close_
let optional p = (map (fun x -> Some x) p) <|> return_ None
let whitespace = satisfy (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r') "whitespace"
let spaces = map (fun _ -> ()) (many whitespace)
let lexeme p = spaces *> p <* spaces
let run_parser p input = match (spaces *> p <* spaces) input 0 with
  | Ok (value, pos) -> if pos = String.length input then Stdlib.Ok value
    else Stdlib.Error (Printf.sprintf "unexpected character '%c' at position %d" input.[pos] pos)
  | Error (msg, pos) -> Stdlib.Error (Printf.sprintf "%s at position %d" msg pos)

type json = Null | Bool of bool | Number of float | String of string | Array of json list | Object of (string * json) list

let json_parser_ref : json parser ref = ref (fail "not initialized")

(* Depth-limited parsing — prevents stack overflow from deeply nested input *)
let max_parse_depth = ref 512
let current_depth = ref 0
let with_depth_check (p : json parser) : json parser = fun input pos ->
  if !current_depth >= !max_parse_depth then
    Error (Printf.sprintf "maximum nesting depth (%d) exceeded" !max_parse_depth, pos)
  else begin incr current_depth; let result = p input pos in decr current_depth; result end

let json_null = string_ "null" *> return_ Null
let json_bool = (string_ "true" *> return_ (Bool true)) <|> (string_ "false" *> return_ (Bool false))
let json_number : json parser = fun input pos ->
  let start = pos in
  let pos = if pos < String.length input && input.[pos] = '-' then pos + 1 else pos in
  if pos >= String.length input || not (input.[pos] >= '0' && input.[pos] <= '9') then Error ("expected number", start)
  else let pos = if input.[pos] = '0' then pos + 1 else let p = ref pos in
    while !p < String.length input && input.[!p] >= '0' && input.[!p] <= '9' do incr p done; !p in
  let pos = if pos < String.length input && input.[pos] = '.' then
    let p = ref (pos + 1) in
    if !p >= String.length input || not (input.[!p] >= '0' && input.[!p] <= '9') then pos
    else begin while !p < String.length input && input.[!p] >= '0' && input.[!p] <= '9' do incr p done; !p end
  else pos in
  let pos = if pos < String.length input && (input.[pos] = 'e' || input.[pos] = 'E') then
    let p = ref (pos + 1) in
    if !p < String.length input && (input.[!p] = '+' || input.[!p] = '-') then incr p;
    if !p >= String.length input || not (input.[!p] >= '0' && input.[!p] <= '9') then pos
    else begin while !p < String.length input && input.[!p] >= '0' && input.[!p] <= '9' do incr p done; !p end
  else pos in
  let s = String.sub input start (pos - start) in
  (try Ok (Number (float_of_string s), pos) with Failure _ -> Error ("invalid number", start))

let hex_digit = satisfy (fun c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) "hex digit"
let hex_value c =
  if c >= '0' && c <= '9' then Char.code c - Char.code '0'
  else if c >= 'a' && c <= 'f' then 10 + Char.code c - Char.code 'a'
  else 10 + Char.code c - Char.code 'A'
let utf8_of_codepoint cp =
  if cp >= 0xD800 && cp <= 0xDFFF then invalid_arg (Printf.sprintf "utf8_of_codepoint: surrogate U+%04X" cp)
  else if cp < 0 || cp > 0x10FFFF then invalid_arg (Printf.sprintf "utf8_of_codepoint: U+%X out of range" cp)
  else if cp < 0x80 then String.make 1 (Char.chr cp)
  else if cp < 0x800 then Printf.sprintf "%c%c" (Char.chr (0xC0 lor (cp lsr 6))) (Char.chr (0x80 lor (cp land 0x3F)))
  else if cp < 0x10000 then Printf.sprintf "%c%c%c" (Char.chr (0xE0 lor (cp lsr 12))) (Char.chr (0x80 lor ((cp lsr 6) land 0x3F))) (Char.chr (0x80 lor (cp land 0x3F)))
  else Printf.sprintf "%c%c%c%c" (Char.chr (0xF0 lor (cp lsr 18))) (Char.chr (0x80 lor ((cp lsr 12) land 0x3F))) (Char.chr (0x80 lor ((cp lsr 6) land 0x3F))) (Char.chr (0x80 lor (cp land 0x3F)))
let escape_sequence =
  char_ '\\' *> (
    (char_ '"' *> return_ "\"") <|> (char_ '\\' *> return_ "\\") <|> (char_ '/' *> return_ "/")
    <|> (char_ 'b' *> return_ "\b") <|> (char_ 'f' *> return_ (String.make 1 (Char.chr 12)))
    <|> (char_ 'n' *> return_ "\n") <|> (char_ 'r' *> return_ "\r") <|> (char_ 't' *> return_ "\t")
    <|> (char_ 'u' *> hex_digit >>= fun h1 -> hex_digit >>= fun h2 -> hex_digit >>= fun h3 -> hex_digit >>= fun h4 ->
         let cp = (hex_value h1 lsl 12) lor (hex_value h2 lsl 8) lor (hex_value h3 lsl 4) lor (hex_value h4) in
         if cp >= 0xD800 && cp <= 0xDBFF then
           char_ '\\' *> char_ 'u' *> hex_digit >>= fun l1 -> hex_digit >>= fun l2 -> hex_digit >>= fun l3 -> hex_digit >>= fun l4 ->
           let low = (hex_value l1 lsl 12) lor (hex_value l2 lsl 8) lor (hex_value l3 lsl 4) lor (hex_value l4) in
           if low >= 0xDC00 && low <= 0xDFFF then return_ (utf8_of_codepoint (0x10000 + ((cp - 0xD800) lsl 10) + (low - 0xDC00)))
           else fail "invalid low surrogate"
         else if cp >= 0xDC00 && cp <= 0xDFFF then fail "lone low surrogate"
         else return_ (utf8_of_codepoint cp)))
let string_char = escape_sequence <|> (satisfy (fun c -> c <> '"' && c <> '\\' && Char.code c >= 0x20) "string character" |> map (String.make 1))
let json_string_raw = char_ '"' *> many string_char >>= fun parts -> char_ '"' *> return_ (String.concat "" parts)
let json_string = map (fun s -> String s) json_string_raw
let json_array = with_depth_check (between (lexeme (char_ '[')) (char_ ']') (sep_by (lexeme (fun i p -> !json_parser_ref i p)) (lexeme (char_ ','))) |> map (fun items -> Array items))
let json_pair = lexeme json_string_raw >>= fun key -> lexeme (char_ ':') *> lexeme (fun i p -> !json_parser_ref i p) >>= fun value -> return_ (key, value)
let json_object = with_depth_check (between (lexeme (char_ '{')) (char_ '}') (sep_by json_pair (lexeme (char_ ','))) |> map (fun pairs -> Object pairs))
let json_value = lexeme (try_ json_null <|> try_ json_bool <|> try_ json_number <|> try_ json_string <|> try_ json_array <|> json_object)
let () = json_parser_ref := json_value
let parse ?(max_depth=512) input =
  max_parse_depth := max_depth;
  current_depth := 0;
  run_parser json_value input

let rec to_string_compact = function
  | Null -> "null" | Bool b -> if b then "true" else "false"
  | Number n -> if Float.is_integer n && Float.is_finite n then string_of_int (int_of_float n) else Printf.sprintf "%.17g" n
  | String s -> "\"" ^ escape_json_string s ^ "\""
  | Array items -> "[" ^ String.concat "," (List.map to_string_compact items) ^ "]"
  | Object pairs -> "{" ^ String.concat "," (List.map (fun (k, v) -> "\"" ^ escape_json_string k ^ "\":" ^ to_string_compact v) pairs) ^ "}"
and escape_json_string s =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c -> match c with
    | '"' -> Buffer.add_string buf "\\\"" | '\\' -> Buffer.add_string buf "\\\\"
    | '/' -> Buffer.add_string buf "\\/"
    | '\n' -> Buffer.add_string buf "\\n" | '\r' -> Buffer.add_string buf "\\r" | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 -> Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c) s;
  Buffer.contents buf

let to_string_pretty ?(indent=2) j =
  let buf = Buffer.create 256 in
  let rec pp depth j =
    let pad = String.make (depth * indent) ' ' in
    let pad_inner = String.make ((depth + 1) * indent) ' ' in
    match j with
    | Null -> Buffer.add_string buf "null" | Bool b -> Buffer.add_string buf (if b then "true" else "false")
    | Number n -> if Float.is_integer n && Float.is_finite n then Buffer.add_string buf (string_of_int (int_of_float n))
      else Buffer.add_string buf (Printf.sprintf "%.17g" n)
    | String s -> Buffer.add_char buf '"'; Buffer.add_string buf (escape_json_string s); Buffer.add_char buf '"'
    | Array [] -> Buffer.add_string buf "[]"
    | Array items -> Buffer.add_string buf "[\n";
      List.iteri (fun i item -> Buffer.add_string buf pad_inner; pp (depth+1) item;
        if i < List.length items - 1 then Buffer.add_char buf ','; Buffer.add_char buf '\n') items;
      Buffer.add_string buf pad; Buffer.add_char buf ']'
    | Object [] -> Buffer.add_string buf "{}"
    | Object pairs -> Buffer.add_string buf "{\n";
      List.iteri (fun i (k, v) -> Buffer.add_string buf pad_inner; Buffer.add_char buf '"';
        Buffer.add_string buf (escape_json_string k); Buffer.add_string buf "\": "; pp (depth+1) v;
        if i < List.length pairs - 1 then Buffer.add_char buf ','; Buffer.add_char buf '\n') pairs;
      Buffer.add_string buf pad; Buffer.add_char buf '}'
  in pp 0 j; Buffer.contents buf

let query path j =
  let segments = let parts = ref [] in let buf = Buffer.create 16 in
    String.iter (fun c -> if c = '.' then begin parts := Buffer.contents buf :: !parts; Buffer.clear buf end
      else Buffer.add_char buf c) path;
    parts := Buffer.contents buf :: !parts; List.rev !parts in
  let rec follow segments j = match segments with
    | [] -> Some j
    | seg :: rest -> match j with
      | Object pairs -> (match List.assoc_opt seg pairs with Some child -> follow rest child | None -> None)
      | Array items -> (try let idx = int_of_string seg in
          let idx = if idx < 0 then List.length items + idx else idx in
          if idx >= 0 && idx < List.length items then follow rest (List.nth items idx) else None
        with Failure _ -> None)
      | _ -> None
  in if path = "" then Some j else follow segments j

let rec equal a b = match a, b with
  | Null, Null -> true | Bool a, Bool b -> a = b | Number a, Number b -> a = b | String a, String b -> a = b
  | Array a, Array b -> List.length a = List.length b && List.for_all2 equal a b
  | Object a, Object b -> List.length a = List.length b &&
    List.for_all (fun (k, v) -> match List.assoc_opt k b with Some v' -> equal v v' | None -> false) a
  | _ -> false

let type_name = function Null -> "null" | Bool _ -> "boolean" | Number _ -> "number" | String _ -> "string" | Array _ -> "array" | Object _ -> "object"
let is_null = function Null -> true | _ -> false
let is_bool = function Bool _ -> true | _ -> false
let is_number = function Number _ -> true | _ -> false
let is_string = function String _ -> true | _ -> false
let is_array = function Array _ -> true | _ -> false
let is_object = function Object _ -> true | _ -> false
let keys = function Object pairs -> Some (List.map fst pairs) | _ -> None
let values = function Object pairs -> Some (List.map snd pairs) | _ -> None
let length = function Array items -> Some (List.length items) | Object pairs -> Some (List.length pairs) | String s -> Some (String.length s) | _ -> None
let map_array f = function Array items -> Array (List.map f items) | other -> other
let filter_array f = function Array items -> Array (List.filter f items) | other -> other
let fold_array f init = function Array items -> List.fold_left f init items | _ -> init
let map_object f = function Object pairs -> Object (List.map (fun (k, v) -> (k, f k v)) pairs) | other -> other
let filter_object f = function Object pairs -> Object (List.filter (fun (k, v) -> f k v) pairs) | other -> other
let merge a b = match a, b with
  | Object pa, Object pb -> let merged = List.fold_left (fun acc (k, v) ->
      if List.mem_assoc k acc then List.map (fun (k', v') -> if k' = k then (k, v) else (k', v')) acc
      else acc @ [(k, v)]) pa pb in Object merged
  | _, b -> b

let parse_ok input = match parse input with Stdlib.Ok j -> j | Stdlib.Error msg -> failwith ("parse failed: " ^ msg)
let parse_fails input = match parse input with Stdlib.Ok _ -> false | Stdlib.Error _ -> true

(* =========================================================== *)
(*   Test Suites                                                *)
(* =========================================================== *)

let () =
  suite "JSON null" (fun () ->
    assert_true ~msg:"parse null" (parse_ok "null" = Null);
    assert_true ~msg:"parse null with spaces" (parse_ok "  null  " = Null);
    assert_true ~msg:"type_name null" (type_name Null = "null");
    assert_true ~msg:"is_null true" (is_null Null);
    assert_true ~msg:"is_null false for bool" (not (is_null (Bool true)));
  );

  suite "JSON booleans" (fun () ->
    assert_true ~msg:"parse true" (parse_ok "true" = Bool true);
    assert_true ~msg:"parse false" (parse_ok "false" = Bool false);
    assert_true ~msg:"parse true with spaces" (parse_ok " true " = Bool true);
    assert_true ~msg:"type_name boolean" (type_name (Bool true) = "boolean");
    assert_true ~msg:"is_bool true" (is_bool (Bool false));
    assert_true ~msg:"is_bool false for null" (not (is_bool Null));
  );

  suite "JSON numbers" (fun () ->
    assert_true ~msg:"parse 0" (parse_ok "0" = Number 0.0);
    assert_true ~msg:"parse 42" (parse_ok "42" = Number 42.0);
    assert_true ~msg:"parse -7" (parse_ok "-7" = Number (-7.0));
    assert_true ~msg:"parse 3.14" (parse_ok "3.14" = Number 3.14);
    assert_true ~msg:"parse 1e10" (parse_ok "1e10" = Number 1e10);
    assert_true ~msg:"parse 1E10" (parse_ok "1E10" = Number 1e10);
    assert_true ~msg:"parse 2.5e3" (parse_ok "2.5e3" = Number 2500.0);
    assert_true ~msg:"parse 1e-3" (parse_ok "1e-3" = Number 0.001);
    assert_true ~msg:"parse 1e+5" (parse_ok "1e+5" = Number 100000.0);
    assert_true ~msg:"parse -0" (parse_ok "-0" = Number (-0.0));
    assert_true ~msg:"parse 123456789" (parse_ok "123456789" = Number 123456789.0);
    assert_true ~msg:"type_name number" (type_name (Number 1.0) = "number");
    assert_true ~msg:"is_number true" (is_number (Number 0.0));
    assert_true ~msg:"is_number false" (not (is_number (String "1")));
  );

  suite "JSON strings" (fun () ->
    assert_true ~msg:"empty string" (parse_ok "\"\"" = String "");
    assert_true ~msg:"simple string" (parse_ok "\"hello\"" = String "hello");
    assert_true ~msg:"string with spaces" (parse_ok "\"hello world\"" = String "hello world");
    assert_true ~msg:"escaped quote" (parse_ok "\"he said \\\"hi\\\"\"" = String "he said \"hi\"");
    assert_true ~msg:"escaped backslash" (parse_ok "\"a\\\\b\"" = String "a\\b");
    assert_true ~msg:"escaped slash" (parse_ok "\"a\\/b\"" = String "a/b");
    assert_true ~msg:"escaped newline" (parse_ok "\"a\\nb\"" = String "a\nb");
    assert_true ~msg:"escaped tab" (parse_ok "\"a\\tb\"" = String "a\tb");
    assert_true ~msg:"escaped carriage return" (parse_ok "\"a\\rb\"" = String "a\rb");
    assert_true ~msg:"unicode escape A" (parse_ok "\"\\u0041\"" = String "A");
    assert_true ~msg:"unicode escape AB" (parse_ok "\"\\u0041\\u0042\"" = String "AB");
    assert_true ~msg:"type_name string" (type_name (String "") = "string");
    assert_true ~msg:"is_string true" (is_string (String "x"));
    assert_true ~msg:"is_string false" (not (is_string (Number 0.0)));
    assert_true ~msg:"length of string" (length (String "hello") = Some 5);
    assert_true ~msg:"length of empty string" (length (String "") = Some 0);
  );

  suite "JSON arrays" (fun () ->
    assert_true ~msg:"empty array" (parse_ok "[]" = Array []);
    assert_true ~msg:"single element" (parse_ok "[1]" = Array [Number 1.0]);
    assert_true ~msg:"multiple elements" (parse_ok "[1, 2, 3]" = Array [Number 1.0; Number 2.0; Number 3.0]);
    assert_true ~msg:"mixed types" (parse_ok "[1, \"a\", true, null]" = Array [Number 1.0; String "a"; Bool true; Null]);
    assert_true ~msg:"nested arrays" (parse_ok "[[1, 2], [3]]" = Array [Array [Number 1.0; Number 2.0]; Array [Number 3.0]]);
    assert_true ~msg:"array with spaces" (parse_ok "[ 1 , 2 , 3 ]" = Array [Number 1.0; Number 2.0; Number 3.0]);
    assert_true ~msg:"type_name array" (type_name (Array []) = "array");
    assert_true ~msg:"is_array true" (is_array (Array []));
    assert_true ~msg:"is_array false" (not (is_array (Object [])));
    assert_true ~msg:"length of array" (length (Array [Null; Null; Null]) = Some 3);
    assert_true ~msg:"length of empty array" (length (Array []) = Some 0);
  );

  suite "JSON objects" (fun () ->
    assert_true ~msg:"empty object" (parse_ok "{}" = Object []);
    assert_true ~msg:"single pair" (parse_ok "{\"a\": 1}" = Object [("a", Number 1.0)]);
    assert_true ~msg:"multiple pairs" (parse_ok "{\"a\": 1, \"b\": 2}" = Object [("a", Number 1.0); ("b", Number 2.0)]);
    assert_true ~msg:"nested object" (parse_ok "{\"x\": {\"y\": 1}}" = Object [("x", Object [("y", Number 1.0)])]);
    assert_true ~msg:"object with array" (parse_ok "{\"items\": [1, 2]}" = Object [("items", Array [Number 1.0; Number 2.0])]);
    assert_true ~msg:"type_name object" (type_name (Object []) = "object");
    assert_true ~msg:"is_object true" (is_object (Object []));
    assert_true ~msg:"is_object false" (not (is_object (Array [])));
    assert_true ~msg:"length of object" (length (Object [("a", Null); ("b", Null)]) = Some 2);
    assert_true ~msg:"keys" (keys (Object [("a", Null); ("b", Null)]) = Some ["a"; "b"]);
    assert_true ~msg:"values" (values (Object [("a", Number 1.0)]) = Some [Number 1.0]);
    assert_true ~msg:"keys of non-object" (keys (Array []) = None);
  );

  suite "JSON whitespace" (fun () ->
    assert_true ~msg:"leading spaces" (parse_ok "   42" = Number 42.0);
    assert_true ~msg:"trailing spaces" (parse_ok "42   " = Number 42.0);
    assert_true ~msg:"newlines" (parse_ok "{\n\"a\"\n:\n1\n}" = Object [("a", Number 1.0)]);
    assert_true ~msg:"tabs" (parse_ok "{\t\"a\":\t1}" = Object [("a", Number 1.0)]);
    assert_true ~msg:"mixed whitespace" (parse_ok " \t\n\r null \t\n\r " = Null);
  );

  suite "JSON errors" (fun () ->
    assert_true ~msg:"empty input" (parse_fails "");
    assert_true ~msg:"unclosed array" (parse_fails "[1, 2");
    assert_true ~msg:"unclosed object" (parse_fails "{\"a\": 1");
    assert_true ~msg:"unclosed string" (parse_fails "\"hello");
    assert_true ~msg:"undefined keyword" (parse_fails "undefined");
    assert_true ~msg:"single comma" (parse_fails ",");
    assert_true ~msg:"colon alone" (parse_fails ":");
    assert_true ~msg:"trailing garbage" (parse_fails "null foo");
  );

  suite "JSON compact serialization" (fun () ->
    assert_equal ~msg:"null" "null" (to_string_compact Null);
    assert_equal ~msg:"true" "true" (to_string_compact (Bool true));
    assert_equal ~msg:"false" "false" (to_string_compact (Bool false));
    assert_equal ~msg:"integer" "42" (to_string_compact (Number 42.0));
    assert_equal ~msg:"string" "\"hello\"" (to_string_compact (String "hello"));
    assert_equal ~msg:"empty array" "[]" (to_string_compact (Array []));
    assert_equal ~msg:"array" "[1,2,3]" (to_string_compact (Array [Number 1.0; Number 2.0; Number 3.0]));
    assert_equal ~msg:"empty object" "{}" (to_string_compact (Object []));
    assert_equal ~msg:"object" "{\"a\":1}" (to_string_compact (Object [("a", Number 1.0)]));
    assert_equal ~msg:"escaped newline" "\"a\\nb\"" (to_string_compact (String "a\nb"));
    assert_equal ~msg:"escaped quote" "\"a\\\"b\"" (to_string_compact (String "a\"b"));
  );

  suite "JSON pretty printing" (fun () ->
    assert_equal ~msg:"null pretty" "null" (to_string_pretty Null);
    assert_equal ~msg:"empty array" "[]" (to_string_pretty (Array []));
    assert_equal ~msg:"empty object" "{}" (to_string_pretty (Object []));
    assert_true ~msg:"has newlines" (String.contains (to_string_pretty (Array [Number 1.0])) '\n');
    assert_true ~msg:"has indentation" (
      let s = to_string_pretty ~indent:4 (Object [("a", Number 1.0)]) in
      let found = ref false in
      for i = 0 to String.length s - 4 do if String.sub s i 4 = "    " then found := true done;
      !found);
  );

  suite "JSON queries" (fun () ->
    let j = parse_ok "{\"user\": {\"name\": \"Alice\", \"scores\": [95, 87, 92]}, \"active\": true}" in
    assert_true ~msg:"query root" (query "" j = Some j);
    assert_true ~msg:"query top-level" (query "active" j = Some (Bool true));
    assert_true ~msg:"query nested" (query "user.name" j = Some (String "Alice"));
    assert_true ~msg:"query array 0" (query "user.scores.0" j = Some (Number 95.0));
    assert_true ~msg:"query array 2" (query "user.scores.2" j = Some (Number 92.0));
    assert_true ~msg:"query negative index" (query "user.scores.-1" j = Some (Number 92.0));
    assert_true ~msg:"query missing" (query "missing" j = None);
    assert_true ~msg:"query deep missing" (query "user.missing.deep" j = None);
    assert_true ~msg:"query out of bounds" (query "user.scores.5" j = None);
    assert_true ~msg:"query on primitive" (query "x" (Number 1.0) = None);
  );

  suite "JSON equality" (fun () ->
    assert_true ~msg:"null = null" (equal Null Null);
    assert_true ~msg:"true = true" (equal (Bool true) (Bool true));
    assert_true ~msg:"true != false" (not (equal (Bool true) (Bool false)));
    assert_true ~msg:"1 = 1" (equal (Number 1.0) (Number 1.0));
    assert_true ~msg:"1 != 2" (not (equal (Number 1.0) (Number 2.0)));
    assert_true ~msg:"str = str" (equal (String "a") (String "a"));
    assert_true ~msg:"str != str" (not (equal (String "a") (String "b")));
    assert_true ~msg:"[] = []" (equal (Array []) (Array []));
    assert_true ~msg:"[1] != [2]" (not (equal (Array [Number 1.0]) (Array [Number 2.0])));
    assert_true ~msg:"{} = {}" (equal (Object []) (Object []));
    assert_true ~msg:"order independent" (equal (Object [("a", Number 1.0); ("b", Number 2.0)]) (Object [("b", Number 2.0); ("a", Number 1.0)]));
    assert_true ~msg:"null != 0" (not (equal Null (Number 0.0)));
    assert_true ~msg:"different types" (not (equal (String "1") (Number 1.0)));
  );

  suite "JSON round-trip" (fun () ->
    let test_rt input = let j1 = parse_ok input in let s = to_string_compact j1 in let j2 = parse_ok s in equal j1 j2 in
    assert_true ~msg:"null" (test_rt "null");
    assert_true ~msg:"true" (test_rt "true");
    assert_true ~msg:"number" (test_rt "42");
    assert_true ~msg:"string" (test_rt "\"hello\"");
    assert_true ~msg:"nested array" (test_rt "[1, [2, [3]]]");
    assert_true ~msg:"nested object" (test_rt "{\"a\": {\"b\": true}}");
    assert_true ~msg:"complex" (test_rt "{\"users\": [{\"name\": \"Alice\", \"age\": 30}], \"count\": 1}");
  );

  suite "JSON map_array" (fun () ->
    let arr = Array [Number 1.0; Number 2.0; Number 3.0] in
    assert_true ~msg:"doubles" (map_array (function Number n -> Number (n *. 2.0) | x -> x) arr = Array [Number 2.0; Number 4.0; Number 6.0]);
    assert_true ~msg:"on non-array" (map_array (fun x -> x) Null = Null);
  );

  suite "JSON filter_array" (fun () ->
    let arr = Array [Number 1.0; Number 2.0; Number 3.0; Number 4.0] in
    assert_true ~msg:"evens" (filter_array (function Number n -> mod_float n 2.0 = 0.0 | _ -> false) arr = Array [Number 2.0; Number 4.0]);
    assert_true ~msg:"on non-array" (filter_array (fun _ -> true) (String "x") = String "x");
  );

  suite "JSON fold_array" (fun () ->
    let arr = Array [Number 1.0; Number 2.0; Number 3.0] in
    assert_true ~msg:"sum" (fold_array (fun acc -> function Number n -> acc +. n | _ -> acc) 0.0 arr = 6.0);
    assert_true ~msg:"on non-array" (fold_array (fun a _ -> a + 1) 0 Null = 0);
  );

  suite "JSON map_object" (fun () ->
    let obj = Object [("a", Number 1.0); ("b", Number 2.0)] in
    assert_true ~msg:"transform" (map_object (fun k v -> if k = "a" then String "one" else v) obj = Object [("a", String "one"); ("b", Number 2.0)]);
    assert_true ~msg:"on non-object" (map_object (fun _ v -> v) (Array []) = Array []);
  );

  suite "JSON filter_object" (fun () ->
    let obj = Object [("a", Number 1.0); ("b", Number 2.0); ("c", Number 3.0)] in
    assert_true ~msg:"filter" (filter_object (fun k _ -> k <> "b") obj = Object [("a", Number 1.0); ("c", Number 3.0)]);
  );

  suite "JSON merge" (fun () ->
    let a = Object [("a", Number 1.0); ("b", Number 2.0)] in
    let b = Object [("b", Number 99.0); ("c", Number 3.0)] in
    let m = merge a b in
    assert_true ~msg:"overrides" (query "b" m = Some (Number 99.0));
    assert_true ~msg:"keeps left" (query "a" m = Some (Number 1.0));
    assert_true ~msg:"adds right" (query "c" m = Some (Number 3.0));
    assert_true ~msg:"non-objects" (merge (Number 1.0) (Number 2.0) = Number 2.0);
  );

  suite "JSON complex documents" (fun () ->
    let complex = "{\"name\": \"test\", \"version\": 1, \"debug\": false, \"config\": null, \"tags\": [\"a\", \"b\"], \"nested\": {\"deep\": {\"value\": 42}}}" in
    let j = parse_ok complex in
    assert_true ~msg:"is object" (is_object j);
    assert_true ~msg:"deep query" (query "nested.deep.value" j = Some (Number 42.0));
    assert_true ~msg:"array query" (query "tags.1" j = Some (String "b"));
    assert_true ~msg:"null value" (query "config" j = Some Null);
    assert_true ~msg:"round-trip" (equal j (parse_ok (to_string_compact j)));
  );

  suite "JSON edge cases" (fun () ->
    assert_true ~msg:"deeply nested" (query "0.0.0.0" (parse_ok "[[[[1]]]]") = Some (Number 1.0));
    assert_true ~msg:"empty string value" (parse_ok "\"\"" = String "");
    assert_true ~msg:"string with only spaces" (parse_ok "\"   \"" = String "   ");
    assert_true ~msg:"number zero" (parse_ok "0" = Number 0.0);
    assert_true ~msg:"large number" (parse_ok "999999999999" = Number 999999999999.0);
    assert_true ~msg:"scientific notation" (parse_ok "6.022e23" = Number 6.022e23);
    assert_true ~msg:"object in array" (query "1.b" (parse_ok "[{\"a\":1},{\"b\":2}]") = Some (Number 2.0));
    assert_true ~msg:"length returns None for number" (length (Number 1.0) = None);
    assert_true ~msg:"length returns None for null" (length Null = None);
    assert_true ~msg:"values of non-object" (values (Array []) = None);
  );

  suite "JSON pretty-print round-trip" (fun () ->
    let input = "{\"a\": [1, 2, {\"b\": true}], \"c\": null}" in
    let j = parse_ok input in
    let pretty = to_string_pretty j in
    let j2 = parse_ok pretty in
    assert_true ~msg:"pretty round-trip" (equal j j2);
  );

  suite "JSON construction and serialize" (fun () ->
    let j = Object [("x", Number 1.0); ("y", Array [Bool true; Null; String "hi"])] in
    let s = to_string_compact j in
    let j2 = parse_ok s in
    assert_true ~msg:"construct and parse back" (equal j j2);
  );

  suite "JSON depth limit (security)" (fun () ->
    (* Normal nesting should work fine *)
    assert_true ~msg:"depth 5 ok" (
      match parse "[[[[[ 1 ]]]]]" with Stdlib.Ok _ -> true | _ -> false);
    assert_true ~msg:"depth 10 ok" (
      match parse "[[[[[[[[[[1]]]]]]]]]]" with Stdlib.Ok _ -> true | _ -> false);
    (* Custom low depth limit should reject deep nesting *)
    assert_true ~msg:"depth 3 rejects depth 5" (
      match parse ~max_depth:3 "[[[[[1]]]]]" with
      | Stdlib.Error msg -> String.length msg > 0
      | _ -> false);
    assert_true ~msg:"depth 2 rejects depth 3" (
      match parse ~max_depth:2 "[[[1]]]" with
      | Stdlib.Error msg -> String.length msg > 0
      | _ -> false);
    assert_true ~msg:"depth 1 allows single array" (
      match parse ~max_depth:1 "[1, 2, 3]" with Stdlib.Ok _ -> true | _ -> false);
    assert_true ~msg:"depth 1 rejects nested array" (
      match parse ~max_depth:1 "[[1]]" with
      | Stdlib.Error _ -> true | _ -> false);
    (* Object nesting counted too *)
    assert_true ~msg:"depth 2 allows single object" (
      match parse ~max_depth:2 "{\"a\": {\"b\": 1}}" with Stdlib.Ok _ -> true | _ -> false);
    assert_true ~msg:"depth 1 rejects nested object" (
      match parse ~max_depth:1 "{\"a\": {\"b\": 1}}" with
      | Stdlib.Error _ -> true | _ -> false);
    (* Mixed array + object nesting *)
    assert_true ~msg:"depth 3 allows mixed nesting" (
      match parse ~max_depth:3 "[{\"a\": [1]}]" with Stdlib.Ok _ -> true | _ -> false);
    assert_true ~msg:"depth 2 rejects deep mixed" (
      match parse ~max_depth:2 "[{\"a\": [1]}]" with
      | Stdlib.Error _ -> true | _ -> false);
    (* Error message mentions depth limit *)
    assert_true ~msg:"error message mentions depth" (
      match parse ~max_depth:2 "[[[1]]]" with
      | Stdlib.Error msg ->
        let has_depth = ref false in
        (try
          let _ = Scanf.sscanf msg "%_s@depth%_s" () in
          has_depth := true
        with _ -> ());
        (* Simple check: message contains "depth" *)
        let rec check i =
          if i + 5 > String.length msg then false
          else if String.sub msg i 5 = "depth" then true
          else check (i + 1)
        in check 0
      | _ -> false);
    (* Depth resets between parse calls *)
    assert_true ~msg:"depth resets between calls" (
      let _ = parse ~max_depth:2 "[[[1]]]" in (* fails *)
      match parse ~max_depth:100 "[[[1]]]" with Stdlib.Ok _ -> true | _ -> false);
    (* Large depth works with high limit *)
    assert_true ~msg:"depth 50 with high limit" (
      let buf = Buffer.create 200 in
      for _ = 1 to 50 do Buffer.add_char buf '[' done;
      Buffer.add_char buf '1';
      for _ = 1 to 50 do Buffer.add_char buf ']' done;
      match parse ~max_depth:512 (Buffer.contents buf) with Stdlib.Ok _ -> true | _ -> false);
    (* Non-nested structures unaffected by depth limit *)
    assert_true ~msg:"flat array ok with depth 1" (
      match parse ~max_depth:1 "[1, 2, 3, 4, 5]" with Stdlib.Ok _ -> true | _ -> false);
    assert_true ~msg:"flat object ok with depth 1" (
      match parse ~max_depth:1 "{\"a\": 1, \"b\": 2}" with Stdlib.Ok _ -> true | _ -> false);
    assert_true ~msg:"scalar ok with depth 0" (
      match parse ~max_depth:0 "42" with Stdlib.Ok _ -> true | _ -> false);
    assert_true ~msg:"array rejected with depth 0" (
      match parse ~max_depth:0 "[1]" with Stdlib.Error _ -> true | _ -> false);
  );

  suite "JSON forward-slash escaping (XSS prevention)" (fun () ->
    (* Forward slash should be escaped in output *)
    assert_equal ~msg:"slash escaped in compact" "\"a\\/b\"" (to_string_compact (String "a/b"));
    assert_equal ~msg:"script tag escaped" "\"<\\/script>\"" (to_string_compact (String "</script>"));
    assert_equal ~msg:"url escaped" "\"https:\\/\\/example.com\\/path\"" (to_string_compact (String "https://example.com/path"));
    (* Parser still accepts both escaped and unescaped slashes *)
    assert_true ~msg:"parse escaped slash" (parse_ok "\"a\\/b\"" = String "a/b");
    assert_true ~msg:"parse unescaped slash" (parse_ok "\"a/b\"" = String "a/b");
    (* Round-trip with slashes *)
    assert_true ~msg:"slash round-trip" (
      let j = String "path/to/file" in
      let s = to_string_compact j in
      equal j (parse_ok s));
    (* HTML context safety *)
    assert_true ~msg:"no raw </script> in output" (
      let s = to_string_compact (String "</script><script>alert(1)</script>") in
      let rec has_raw_close i =
        if i + 9 > String.length s then false
        else if String.sub s i 9 = "</script>" then true
        else has_raw_close (i + 1)
      in not (has_raw_close 0));
  );


  suite "Surrogate Security" (fun () ->
    (* Lone low surrogates (U+DC00..U+DFFF) must be rejected per RFC 8259 *)
    assert_true ~msg:"lone low surrogate \\uDC00 rejected"
      (match parse "\"\\uDC00\"" with Error _ -> true | Ok _ -> false);
    assert_true ~msg:"lone low surrogate \\uDFFF rejected"
      (match parse "\"\\uDFFF\"" with Error _ -> true | Ok _ -> false);
    assert_true ~msg:"lone low surrogate \\uDD00 rejected"
      (match parse "\"\\uDD00\"" with Error _ -> true | Ok _ -> false);

    (* High surrogate without matching low surrogate *)
    assert_true ~msg:"high surrogate without pair rejected"
      (match parse "\"\\uD800\"" with Error _ -> true | Ok _ -> false);
    assert_true ~msg:"high surrogate with non-surrogate rejected"
      (match parse "\"\\uD800\\u0041\"" with Error _ -> true | Ok _ -> false);

    (* Valid surrogate pair should still work *)
    assert_true ~msg:"valid surrogate pair U+1F600 (grinning face)"
      (match parse "\"\\uD83D\\uDE00\"" with
       | Ok (String s) -> String.length s > 0  (* emoji bytes *)
       | _ -> false);

    (* Normal BMP codepoints still work *)
    assert_true ~msg:"BMP codepoint U+0041 (A)"
      (parse_ok "\"\\u0041\"" = String "A");
    assert_true ~msg:"BMP codepoint U+00E9 (e-acute)"
      (match parse "\"\\u00E9\"" with Ok (String _) -> true | _ -> false);
    assert_true ~msg:"BMP codepoint U+4E16 (CJK)"
      (match parse "\"\\u4E16\"" with Ok (String _) -> true | _ -> false);

    (* utf8_of_codepoint rejects surrogates directly *)
    assert_true ~msg:"utf8_of_codepoint rejects U+D800"
      (try ignore (utf8_of_codepoint 0xD800); false with Invalid_argument _ -> true);
    assert_true ~msg:"utf8_of_codepoint rejects U+DFFF"
      (try ignore (utf8_of_codepoint 0xDFFF); false with Invalid_argument _ -> true);
    assert_true ~msg:"utf8_of_codepoint rejects negative"
      (try ignore (utf8_of_codepoint (-1)); false with Invalid_argument _ -> true);
    assert_true ~msg:"utf8_of_codepoint rejects U+110000"
      (try ignore (utf8_of_codepoint 0x110000); false with Invalid_argument _ -> true);
    assert_true ~msg:"utf8_of_codepoint accepts U+0000"
      (utf8_of_codepoint 0 = String.make 1 (Char.chr 0));
    assert_true ~msg:"utf8_of_codepoint accepts U+10FFFF"
      (String.length (utf8_of_codepoint 0x10FFFF) = 4);
  );

  Printf.printf "\n=== JSON Parser Test Results ===\n";
  Printf.printf "Tests run: %d\n" !tests_run;
  Printf.printf "Passed:    %d\n" !tests_passed;
  Printf.printf "Failed:    %d\n" !tests_failed;
  if !tests_failed = 0 then print_endline "All tests passed!"
  test_summary ()
