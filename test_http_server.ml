(* test_http_server.ml — Tests for http_server.ml helpers.

   Following the repo convention (see test_crypto.ml), the pure helper
   functions under test are inlined here so the test binary does not need
   to link against the Unix library or bind a socket. This keeps the test
   suite portable and fast.

   Compile:
     ocamlopt -o test_http_server test_http_server.ml
   Run:
     ./test_http_server

   Covered:
     - url_decode (percent + plus decoding, malformed input)
     - parse_query_string (multi-=, empty value, empty key, empty input)
     - file_extension / content_type_of
     - json_escape, json_str, json_int, json_arr, json_obj
     - sanitize_header_value, sanitize_header_name (CRLF injection — CWE-113)
     - prefix_matches (path-boundary auth-bypass regression test)
     - serve_static_file traversal rejection (path-only validation)
*)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_eq name expected actual =
  if expected = actual then begin
    incr tests_passed;
    Printf.printf "  + %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  - %s: expected %S, got %S\n" name expected actual
  end

let assert_eq_int name expected actual =
  if expected = actual then begin
    incr tests_passed;
    Printf.printf "  + %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  - %s: expected %d, got %d\n" name expected actual
  end

let assert_true name cond =
  if cond then begin
    incr tests_passed;
    Printf.printf "  + %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  - %s: expected true\n" name
  end

let assert_false name cond = assert_true name (not cond)

(* ================================================================== *)
(*   Inlined helpers (verbatim copies from http_server.ml)             *)
(* ================================================================== *)

let url_decode s =
  let buf = Buffer.create (String.length s) in
  let len = String.length s in
  let i = ref 0 in
  while !i < len do
    if s.[!i] = '%' && !i + 2 < len then begin
      let hex = String.sub s (!i + 1) 2 in
      (try Buffer.add_char buf (Char.chr (int_of_string ("0x" ^ hex)))
       with _ -> Buffer.add_char buf s.[!i]);
      i := !i + 3
    end else if s.[!i] = '+' then begin
      Buffer.add_char buf ' '; incr i
    end else begin
      Buffer.add_char buf s.[!i]; incr i
    end
  done;
  Buffer.contents buf

let parse_query_string qs =
  if qs = "" then []
  else
    let pairs = String.split_on_char '&' qs in
    List.filter_map (fun pair ->
      if pair = "" then None
      else match String.index_opt pair '=' with
      | Some i ->
        let k = String.sub pair 0 i in
        let v = String.sub pair (i + 1) (String.length pair - i - 1) in
        Some (url_decode k, url_decode v)
      | None -> Some (url_decode pair, "")
    ) pairs

let file_extension path =
  match String.rindex_opt path '.' with
  | Some i -> String.sub path i (String.length path - i)
  | None -> ""

let content_type_of ext =
  match String.lowercase_ascii ext with
  | ".html" | ".htm" -> "text/html; charset=utf-8"
  | ".css" -> "text/css; charset=utf-8"
  | ".js" -> "application/javascript; charset=utf-8"
  | ".json" -> "application/json; charset=utf-8"
  | ".xml" -> "application/xml; charset=utf-8"
  | ".txt" | ".md" -> "text/plain; charset=utf-8"
  | ".png" -> "image/png"
  | ".jpg" | ".jpeg" -> "image/jpeg"
  | ".gif" -> "image/gif"
  | ".svg" -> "image/svg+xml"
  | ".ico" -> "image/x-icon"
  | ".pdf" -> "application/pdf"
  | ".wasm" -> "application/wasm"
  | _ -> "application/octet-stream"

let json_escape s =
  let buf = Buffer.create (String.length s + 8) in
  String.iter (fun c -> match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
      Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let json_str s = Printf.sprintf {|"%s"|} (json_escape s)
let json_int n = string_of_int n
let json_arr items = "[" ^ String.concat "," items ^ "]"
let json_obj pairs =
  let entries = List.map (fun (k, v) ->
    Printf.sprintf {|"%s":%s|} (json_escape k) v
  ) pairs in
  "{" ^ String.concat "," entries ^ "}"

let sanitize_header_value v =
  let len = String.length v in
  let buf = Buffer.create len in
  for i = 0 to len - 1 do
    match v.[i] with
    | '\r' | '\n' | '\000' -> ()
    | c -> Buffer.add_char buf c
  done;
  Buffer.contents buf

let sanitize_header_name k =
  let len = String.length k in
  let buf = Buffer.create len in
  for i = 0 to len - 1 do
    let c = k.[i] in
    match c with
    | '\r' | '\n' | '\000' | ':' -> ()
    | _ -> Buffer.add_char buf c
  done;
  Buffer.contents buf

let prefix_matches pattern req_path =
  if pattern = "" then false
  else if pattern = "/" then true
  else if pattern = req_path then true
  else
    let plen = String.length pattern in
    let rlen = String.length req_path in
    if rlen <= plen then false
    else if String.sub req_path 0 plen <> pattern then false
    else
      pattern.[plen - 1] = '/' || req_path.[plen] = '/'

(* Path-validation portion of serve_static_file (no filesystem access). *)
let path_is_safe path =
  let normalized = if path = "/" then "/index.html" else path in
  let segments = String.split_on_char '/' normalized in
  let has_traversal = List.exists (fun s -> s = ".." || s = ".") segments in
  let has_null = String.contains normalized '\000' in
  let has_backslash = String.contains normalized '\\' in
  not has_traversal && not has_null && not has_backslash

(* ================================================================== *)
(*   Tests                                                              *)
(* ================================================================== *)

let test_url_decode () =
  Printf.printf "\n== url_decode ==\n";
  assert_eq "passthrough"        "hello"           (url_decode "hello");
  assert_eq "plus to space"      "a b c"           (url_decode "a+b+c");
  assert_eq "percent-encoded"    "hello world"     (url_decode "hello%20world");
  assert_eq "lowercase hex"      "hi!"             (url_decode "hi%21");
  assert_eq "mixed-case hex"     "@"               (url_decode "%40");
  assert_eq "encoded slash"      "a/b"             (url_decode "a%2Fb");
  assert_eq "empty"              ""                (url_decode "");
  (* Malformed: trailing '%' must not raise, must round-trip the byte. *)
  assert_eq "trailing percent"   "abc%"            (url_decode "abc%");
  assert_eq "percent at end-1"   "abc%a"           (url_decode "abc%a");
  (* Invalid hex pair: previous code falls through with the literal '%' byte. *)
  assert_eq "invalid hex"        "%zzrest"         (url_decode "%zzrest")

let test_parse_query_string () =
  Printf.printf "\n== parse_query_string ==\n";
  assert_eq_int "empty -> []"          0 (List.length (parse_query_string ""));
  assert_eq_int "single pair"          1 (List.length (parse_query_string "a=1"));
  assert_eq_int "two pairs"            2 (List.length (parse_query_string "a=1&b=2"));
  (* Regression: values containing '=' (e.g. base64 padding) must NOT be dropped. *)
  let pairs = parse_query_string "tok=Zm9vYmFy==&u=alice" in
  assert_eq_int "preserves '=' values count" 2 (List.length pairs);
  assert_eq "base64-like value preserved" "Zm9vYmFy==" (List.assoc "tok" pairs);
  assert_eq "second pair after =="        "alice"     (List.assoc "u" pairs);
  (* Empty value ("k=") -> ("k", ""). *)
  let p2 = parse_query_string "k=" in
  assert_eq_int "k= -> 1 pair"    1   (List.length p2);
  assert_eq     "k= -> empty val" ""  (List.assoc "k" p2);
  (* Bare key (no '=') -> ("k", ""). *)
  let p3 = parse_query_string "flag&x=1" in
  assert_eq     "bare key value is empty" "" (List.assoc "flag" p3);
  assert_eq     "x in p3"                 "1" (List.assoc "x" p3);
  (* Adjacent ampersands produce no spurious empty entry. *)
  let p4 = parse_query_string "a=1&&b=2" in
  assert_eq_int "&& collapsed" 2 (List.length p4);
  (* URL-decoding applies to both keys and values. *)
  let p5 = parse_query_string "q=hello%20world&name=al%2Bice" in
  assert_eq "decoded value"  "hello world" (List.assoc "q"    p5);
  assert_eq "decoded value2" "al+ice"      (List.assoc "name" p5)

let test_extensions_and_content_types () =
  Printf.printf "\n== file_extension / content_type_of ==\n";
  assert_eq "ext html"   ".html" (file_extension "index.html");
  assert_eq "ext nested" ".css"  (file_extension "/static/a/b.css");
  assert_eq "no ext"     ""      (file_extension "README");
  assert_eq "trailing ." "."     (file_extension "weird.");
  assert_eq "html ct"    "text/html; charset=utf-8"    (content_type_of ".html");
  assert_eq "HTML ct (case-insensitive)" "text/html; charset=utf-8" (content_type_of ".HTML");
  assert_eq "json ct"    "application/json; charset=utf-8" (content_type_of ".json");
  assert_eq "png ct"     "image/png"                  (content_type_of ".png");
  assert_eq "unknown ct" "application/octet-stream"   (content_type_of ".xyz");
  assert_eq "empty ct"   "application/octet-stream"   (content_type_of "")

let test_json_builders () =
  Printf.printf "\n== json builders ==\n";
  assert_eq "escape quote"        "say \\\"hi\\\""  (json_escape "say \"hi\"");
  assert_eq "escape backslash"    "a\\\\b"           (json_escape "a\\b");
  assert_eq "escape newline"      "a\\nb"            (json_escape "a\nb");
  assert_eq "escape tab"          "a\\tb"            (json_escape "a\tb");
  assert_eq "escape control 0x01" "\\u0001"          (json_escape "\x01");
  assert_eq "ascii passthrough"   "abc"              (json_escape "abc");
  assert_eq "json_str wraps"      "\"hi\""           (json_str "hi");
  assert_eq "json_int 42"         "42"               (json_int 42);
  assert_eq "json_int -7"         "-7"               (json_int (-7));
  assert_eq "json_arr empty"      "[]"               (json_arr []);
  assert_eq "json_arr two"        "[1,2]"            (json_arr ["1"; "2"]);
  assert_eq "json_obj empty"      "{}"               (json_obj []);
  assert_eq "json_obj simple"     "{\"a\":1,\"b\":\"x\"}"
            (json_obj [("a", json_int 1); ("b", json_str "x")]);
  (* Object keys must also be escaped. *)
  assert_eq "json_obj key escape" "{\"a\\\"b\":1}"
            (json_obj [("a\"b", json_int 1)])

let test_header_sanitization () =
  Printf.printf "\n== header sanitization (CWE-113) ==\n";
  assert_eq "value passthrough" "text/html"          (sanitize_header_value "text/html");
  assert_eq "strip CR"          "ab"                  (sanitize_header_value "a\rb");
  assert_eq "strip LF"          "ab"                  (sanitize_header_value "a\nb");
  assert_eq "strip CRLF"        "evil"                (sanitize_header_value "evil\r\n");
  assert_eq "strip injected hdr" "okSet-Cookie: bad=1"
            (sanitize_header_value "ok\r\nSet-Cookie: bad=1");
  assert_eq "strip null"        "ab"                  (sanitize_header_value "a\000b");
  assert_eq "empty"             ""                    (sanitize_header_value "");
  (* Header names: also strip colon (so a malicious key cannot inject a second header). *)
  assert_eq "name strip colon"  "XEvil"               (sanitize_header_name "X:Evil");
  assert_eq "name strip CRLF"   "XGood"               (sanitize_header_name "X\r\nGood");
  assert_eq "name plain ok"     "Content-Type"        (sanitize_header_name "Content-Type")

let test_prefix_matches () =
  Printf.printf "\n== prefix_matches (path-boundary) ==\n";
  (* Exact matches always work. *)
  assert_true  "exact equal"               (prefix_matches "/admin" "/admin");
  (* The classic auth-bypass regression: "/admin" must NOT match "/administrator". *)
  assert_false "admin vs administrator"    (prefix_matches "/admin" "/administrator");
  assert_false "admin vs admin-panel"      (prefix_matches "/admin" "/admin-panel");
  assert_false "admin vs adminx"           (prefix_matches "/admin" "/adminx");
  (* Sub-paths under the prefix ARE allowed. *)
  assert_true  "admin sub-path"            (prefix_matches "/admin" "/admin/users");
  assert_true  "admin trailing-slash sub"  (prefix_matches "/admin/" "/admin/users");
  (* Root pattern matches everything (legacy fallback). *)
  assert_true  "root matches anything"     (prefix_matches "/" "/anything/at/all");
  assert_true  "root matches root"         (prefix_matches "/" "/");
  (* Pattern longer than path -> no match. *)
  assert_false "pattern longer than path"  (prefix_matches "/admin/users" "/admin");
  (* Empty pattern is rejected (defensive). *)
  assert_false "empty pattern"             (prefix_matches "" "/anything");
  (* API namespacing must respect boundaries. *)
  assert_true  "/api/echo == /api/echo"    (prefix_matches "/api/echo" "/api/echo");
  assert_false "/api/echo vs /api/echoes"  (prefix_matches "/api/echo" "/api/echoes");
  assert_true  "/api/echo vs /api/echo/x"  (prefix_matches "/api/echo" "/api/echo/x")

let test_path_safety () =
  Printf.printf "\n== static-file path safety ==\n";
  assert_true  "plain ok"                 (path_is_safe "/index.html");
  assert_true  "nested ok"                (path_is_safe "/css/site.css");
  assert_false "double-dot traversal"     (path_is_safe "/../etc/passwd");
  assert_false "embedded ..  segment"     (path_is_safe "/static/../secret.txt");
  assert_false "single-dot segment"       (path_is_safe "/./secret.txt");
  assert_false "null byte"                (path_is_safe "/index.html\000.png");
  assert_false "backslash"                (path_is_safe "/a\\b.txt");
  (* A filename that *contains* ".." but is not a path segment is safe. *)
  assert_true  "dots in filename"         (path_is_safe "/my..notes.txt");
  assert_true  "trailing dot in name"     (path_is_safe "/file.tar.gz")

(* ================================================================== *)
let () =
  Printf.printf "=== test_http_server ===\n";
  test_url_decode ();
  test_parse_query_string ();
  test_extensions_and_content_types ();
  test_json_builders ();
  test_header_sanitization ();
  test_prefix_matches ();
  test_path_safety ();
  Printf.printf "\n----------------------------------------\n";
  Printf.printf "Passed: %d\n" !tests_passed;
  Printf.printf "Failed: %d\n" !tests_failed;
  if !tests_failed > 0 then exit 1
