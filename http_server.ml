(* http_server.ml — Minimal HTTP/1.1 Server in OCaml
 *
 * A single-file, dependency-free HTTP server using Unix sockets.
 * Supports GET/POST/PUT/DELETE, static file serving, route handlers,
 * query string parsing, and a built-in JSON response helper.
 *
 * Usage:
 *   ocamlfind ocamlopt -package unix -linkpkg http_server.ml -o http_server
 *   ./http_server                    # starts on port 8080
 *   ./http_server 3000               # starts on port 3000
 *
 * Or interpreted:
 *   ocamlfind ocamlopt -package unix -linkpkg http_server.ml -o http_server && ./http_server
 *
 * Features:
 *   - Route registration with pattern matching (exact + prefix)
 *   - Query string parsing (?key=value&...)
 *   - Static file serving from ./public directory
 *   - Content-Type detection for common file types
 *   - Request body reading for POST/PUT
 *   - JSON response helper
 *   - Graceful error handling (404, 405, 500)
 *   - Concurrent request handling via fork()
 *   - Access logging to stdout
 *)

(* ── Types ───────────────────────────────────────────────────────── *)

type http_method = GET | POST | PUT | DELETE | HEAD | OPTIONS | OTHER of string

type request = {
  meth: http_method;
  path: string;
  query: (string * string) list;
  headers: (string * string) list;
  body: string;
  raw_path: string;  (* path + query string *)
}

type response = {
  status: int;
  status_text: string;
  resp_headers: (string * string) list;
  resp_body: string;
}

type route = {
  route_method: http_method;
  route_pattern: string;
  handler: request -> response;
}

(* ── Utility ─────────────────────────────────────────────────────── *)

let method_of_string = function
  | "GET" -> GET | "POST" -> POST | "PUT" -> PUT | "DELETE" -> DELETE
  | "HEAD" -> HEAD | "OPTIONS" -> OPTIONS | s -> OTHER s

let string_of_method = function
  | GET -> "GET" | POST -> "POST" | PUT -> "PUT" | DELETE -> "DELETE"
  | HEAD -> "HEAD" | OPTIONS -> "OPTIONS" | OTHER s -> s

let method_equal a b = match a, b with
  | OTHER x, OTHER y -> x = y
  | _ -> a = b

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
      match String.split_on_char '=' pair with
      | [k; v] -> Some (url_decode k, url_decode v)
      | [k] -> Some (url_decode k, "")
      | _ -> None
    ) pairs

let split_path_query raw =
  match String.index_opt raw '?' with
  | Some i -> (String.sub raw 0 i, String.sub raw (i + 1) (String.length raw - i - 1))
  | None -> (raw, "")

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

let file_extension path =
  match String.rindex_opt path '.' with
  | Some i -> String.sub path i (String.length path - i)
  | None -> ""

let timestamp () =
  let t = Unix.localtime (Unix.gettimeofday ()) in
  Printf.sprintf "%04d-%02d-%02d %02d:%02d:%02d"
    (t.tm_year + 1900) (t.tm_mon + 1) t.tm_mday
    t.tm_hour t.tm_min t.tm_sec

(* ── JSON builder helpers ────────────────────────────────────────── *)

(** Escape a string for safe JSON embedding.
    Handles all control characters, backslashes, and double quotes. *)
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

(** Build a JSON string value (with proper escaping). *)
let json_str s = Printf.sprintf {|"%s"|} (json_escape s)

(** Build a JSON integer value. *)
let json_int n = string_of_int n

(** Build a JSON float value. *)
let json_float f =
  if Float.is_integer f && Float.is_finite f then
    Printf.sprintf "%.0f" f
  else Printf.sprintf "%.17g" f

(** Build a JSON array from a list of pre-serialized JSON strings. *)
let json_arr items = "[" ^ String.concat "," items ^ "]"

(** Build a JSON object from (key, value) pairs of pre-serialized JSON. *)
let json_obj pairs =
  let entries = List.map (fun (k, v) ->
    Printf.sprintf {|"%s":%s|} (json_escape k) v
  ) pairs in
  "{" ^ String.concat "," entries ^ "}"

(* ── Response builders ───────────────────────────────────────────── *)

let make_response ?(status=200) ?(headers=[]) ?(content_type="text/plain; charset=utf-8") body =
  let status_text = match status with
    | 200 -> "OK" | 201 -> "Created" | 204 -> "No Content"
    | 301 -> "Moved Permanently" | 302 -> "Found" | 304 -> "Not Modified"
    | 400 -> "Bad Request" | 401 -> "Unauthorized" | 403 -> "Forbidden"
    | 404 -> "Not Found" | 405 -> "Method Not Allowed"
    | 500 -> "Internal Server Error" | _ -> "Unknown"
  in
  { status; status_text;
    resp_headers = ("Content-Type", content_type) ::
                   ("Content-Length", string_of_int (String.length body)) ::
                   ("Connection", "close") ::
                   headers;
    resp_body = body }

let html_response ?(status=200) body =
  make_response ~status ~content_type:"text/html; charset=utf-8" body

let json_response ?(status=200) body =
  make_response ~status ~content_type:"application/json; charset=utf-8" body

let redirect url =
  make_response ~status:302 ~headers:[("Location", url)] ""

let not_found_response () =
  html_response ~status:404
    "<!DOCTYPE html><html><head><title>404</title>\
     <style>body{font-family:sans-serif;text-align:center;padding:50px}\
     h1{font-size:72px;margin:0;color:#e74c3c}p{color:#666}</style></head>\
     <body><h1>404</h1><p>Not Found</p></body></html>"

let error_response status msg =
  html_response ~status
    (Printf.sprintf "<!DOCTYPE html><html><body><h1>%d</h1><p>%s</p></body></html>" status msg)

(* ── Request parsing ─────────────────────────────────────────────── *)

let read_all ic max_len =
  let buf = Buffer.create 4096 in
  let chunk = Bytes.create 4096 in
  let total = ref 0 in
  (try
    while !total < max_len do
      let n = input ic chunk 0 (min 4096 (max_len - !total)) in
      if n = 0 then raise Exit;
      Buffer.add_subbytes buf chunk 0 n;
      total := !total + n
    done
  with _ -> ());
  Buffer.contents buf

let parse_request ic =
  let request_line = input_line ic in
  let request_line = String.trim request_line in
  let parts = String.split_on_char ' ' request_line in
  match parts with
  | meth_s :: raw_path :: _ ->
    (* Parse headers *)
    let headers = ref [] in
    (try while true do
      let line = String.trim (input_line ic) in
      if line = "" then raise Exit;
      match String.index_opt line ':' with
      | Some i ->
        let key = String.lowercase_ascii (String.trim (String.sub line 0 i)) in
        let value = String.trim (String.sub line (i+1) (String.length line - i - 1)) in
        headers := (key, value) :: !headers
      | None -> ()
    done with _ -> ());
    let headers = List.rev !headers in
    (* Read body if Content-Length present *)
    let body =
      match List.assoc_opt "content-length" headers with
      | Some len_s ->
        let len = try int_of_string len_s with _ -> 0 in
        if len > 0 then read_all ic len else ""
      | None -> ""
    in
    let (path, qs) = split_path_query raw_path in
    let query = parse_query_string qs in
    Some { meth = method_of_string meth_s; path; query; headers; body; raw_path }
  | _ -> None

(* ── Response serialization ──────────────────────────────────────── *)

let send_response oc resp =
  let buf = Buffer.create 1024 in
  Buffer.add_string buf (Printf.sprintf "HTTP/1.1 %d %s\r\n" resp.status resp.status_text);
  List.iter (fun (k, v) ->
    Buffer.add_string buf (Printf.sprintf "%s: %s\r\n" k v)
  ) resp.resp_headers;
  Buffer.add_string buf "\r\n";
  Buffer.add_string buf resp.resp_body;
  output_string oc (Buffer.contents buf);
  flush oc

(* ── Static file serving ─────────────────────────────────────────── *)

let serve_static_file basedir path =
  (* Prevent directory traversal attacks.
     We reject any path containing ".." segments, null bytes, or backslashes,
     then verify the resolved filepath is still under the basedir. *)
  let normalized = if path = "/" then "/index.html" else path in
  (* Split path into segments and reject any ".." component *)
  let segments = String.split_on_char '/' normalized in
  let has_traversal = List.exists (fun s -> s = ".." || s = "." && s <> "") segments in
  let has_null = String.contains normalized '\000' in
  let has_backslash = String.contains normalized '\\' in
  if has_traversal || has_null || has_backslash then None
  else if String.contains normalized '.' then
    let filepath = basedir ^ normalized in
    (* Resolve symlinks and verify the real path is under basedir *)
    let real_base = try Unix.realpath basedir with _ -> basedir in
    let real_file = try Unix.realpath filepath with _ -> "" in
    let base_prefix = real_base ^ "/" in
    if real_file = "" ||
       not (String.length real_file >= String.length base_prefix &&
            String.sub real_file 0 (String.length base_prefix) = base_prefix) then
      None
    else if Sys.file_exists filepath && not (Sys.is_directory filepath) then
      let ic = open_in_bin filepath in
      let len = in_channel_length ic in
      let content = really_input_string ic len in
      close_in ic;
      let ext = file_extension filepath in
      Some (make_response ~content_type:(content_type_of ext) content)
    else None
  else None

(* ── Router ──────────────────────────────────────────────────────── *)

let routes : route list ref = ref []

let register meth pattern handler =
  routes := { route_method = meth; route_pattern = pattern; handler } :: !routes

let find_route req =
  (* Exact match first, then prefix *)
  match List.find_opt (fun r ->
    method_equal r.route_method req.meth && r.route_pattern = req.path
  ) !routes with
  | Some r -> Some r
  | None ->
    List.find_opt (fun r ->
      method_equal r.route_method req.meth &&
      String.length req.path >= String.length r.route_pattern &&
      String.sub req.path 0 (String.length r.route_pattern) = r.route_pattern
    ) !routes

(* ── Built-in demo routes ────────────────────────────────────────── *)

let register_demo_routes () =
  (* Home page *)
  register GET "/" (fun _req ->
    html_response
      "<!DOCTYPE html><html><head><title>OCaml HTTP Server</title>\
       <style>\
       *{margin:0;padding:0;box-sizing:border-box}\
       body{font-family:'Segoe UI',system-ui,sans-serif;background:#0f1117;color:#c9d1d9;\
       min-height:100vh;display:flex;justify-content:center;padding:40px}\
       .container{max-width:700px;width:100%}\
       h1{font-size:2.5em;margin-bottom:8px;color:#58a6ff}\
       .sub{color:#8b949e;margin-bottom:32px;font-size:1.1em}\
       .card{background:#161b22;border:1px solid #30363d;border-radius:8px;\
       padding:20px;margin-bottom:16px}\
       .card h2{color:#58a6ff;font-size:1.1em;margin-bottom:12px}\
       code{background:#1f2937;padding:2px 6px;border-radius:4px;font-size:0.9em;color:#f0883e}\
       a{color:#58a6ff;text-decoration:none}\
       a:hover{text-decoration:underline}\
       ul{list-style:none;padding:0}\
       li{padding:6px 0;border-bottom:1px solid #21262d}\
       li:last-child{border:none}\
       .method{display:inline-block;width:60px;font-weight:bold;font-size:0.85em}\
       .get{color:#3fb950}.post{color:#d29922}.del{color:#f85149}\
       .footer{text-align:center;color:#484f58;margin-top:32px;font-size:0.85em}\
       </style></head><body>\
       <div class='container'>\
       <h1>\xF0\x9F\x90\xAB OCaml HTTP Server</h1>\
       <p class='sub'>A minimal, zero-dependency HTTP/1.1 server written in OCaml</p>\
       <div class='card'><h2>Available Routes</h2><ul>\
       <li><span class='method get'>GET</span> <a href='/'>/</a> — This page</li>\
       <li><span class='method get'>GET</span> <a href='/api/hello'>/api/hello</a> — JSON greeting</li>\
       <li><span class='method get'>GET</span> <a href='/api/echo?msg=hello'>/api/echo?msg=...</a> — Echo query params</li>\
       <li><span class='method get'>GET</span> <a href='/api/time'>/api/time</a> — Current server time</li>\
       <li><span class='method get'>GET</span> <a href='/api/headers'>/api/headers</a> — Request headers</li>\
       <li><span class='method post'>POST</span> <code>/api/echo</code> — Echo request body</li>\
       <li><span class='method get'>GET</span> <a href='/api/fib?n=10'>/api/fib?n=...</a> — Fibonacci numbers</li>\
       <li><span class='method get'>GET</span> <a href='/api/stats'>/api/stats</a> — Server stats</li>\
       </ul></div>\
       <div class='card'><h2>Features</h2><ul>\
       <li>\xE2\x9C\x93 GET / POST / PUT / DELETE support</li>\
       <li>\xE2\x9C\x93 Query string parsing</li>\
       <li>\xE2\x9C\x93 Static file serving (<code>./public</code>)</li>\
       <li>\xE2\x9C\x93 Content-Type detection</li>\
       <li>\xE2\x9C\x93 JSON response helpers</li>\
       <li>\xE2\x9C\x93 Concurrent via <code>fork()</code></li>\
       <li>\xE2\x9C\x93 Access logging</li>\
       </ul></div>\
       <p class='footer'>Built with pure OCaml \xC2\xB7 No dependencies beyond Unix</p>\
       </div></body></html>"
  );

  (* JSON hello *)
  register GET "/api/hello" (fun req ->
    let name = match List.assoc_opt "name" req.query with
      | Some n -> n | None -> "World"
    in
    json_response (json_obj [
      ("greeting", json_str ("Hello, " ^ name ^ "!"));
      ("server", json_str "ocaml-http");
    ])
  );

  (* Echo — GET echoes query params, POST echoes body *)
  register GET "/api/echo" (fun req ->
    json_response (json_obj [
      ("query", json_obj (List.map (fun (k,v) -> (k, json_str v)) req.query));
    ])
  );

  register POST "/api/echo" (fun req ->
    json_response (json_obj [
      ("body", json_str req.body);
      ("length", json_int (String.length req.body));
    ])
  );

  (* Server time *)
  register GET "/api/time" (fun _req ->
    let t = Unix.gettimeofday () in
    let lt = Unix.localtime t in
    let iso = Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02d"
      (lt.tm_year+1900) (lt.tm_mon+1) lt.tm_mday lt.tm_hour lt.tm_min lt.tm_sec in
    let day = [|"Sun";"Mon";"Tue";"Wed";"Thu";"Fri";"Sat"|].(lt.tm_wday) in
    json_response (json_obj [
      ("timestamp", json_float t);
      ("iso", json_str iso);
      ("day", json_str day);
    ])
  );

  (* Request headers *)
  register GET "/api/headers" (fun req ->
    json_response (json_obj [
      ("headers", json_obj (List.map (fun (k,v) -> (k, json_str v)) req.headers));
    ])
  );

  (* Fibonacci *)
  register GET "/api/fib" (fun req ->
    let n = match List.assoc_opt "n" req.query with
      | Some s -> (try min 50 (max 0 (int_of_string s)) with _ -> 10)
      | None -> 10
    in
    let fibs = Array.make (n + 1) 0 in
    if n >= 1 then fibs.(1) <- 1;
    for i = 2 to n do fibs.(i) <- fibs.(i-1) + fibs.(i-2) done;
    let nums = Array.to_list (Array.sub fibs 0 (n + 1)) in
    json_response (json_obj [
      ("n", json_int n);
      ("fibonacci", json_arr (List.map json_int nums));
    ])
  );

  (* Server stats *)
  let request_count = ref 0 in
  let start_time = Unix.gettimeofday () in
  register GET "/api/stats" (fun _req ->
    incr request_count;
    let uptime = Unix.gettimeofday () -. start_time in
    let hours = int_of_float (uptime /. 3600.0) in
    let mins = int_of_float (mod_float (uptime /. 60.0) 60.0) in
    let secs = int_of_float (mod_float uptime 60.0) in
    json_response (json_obj [
      ("uptime_seconds", json_float uptime);
      ("uptime_human", json_str (Printf.sprintf "%dh %dm %ds" hours mins secs));
      ("requests_to_stats", json_int !request_count);
      ("pid", json_int (Unix.getpid ()));
    ])
  )

(* ── Server core ─────────────────────────────────────────────────── *)

let handle_request req =
  match find_route req with
  | Some route ->
    (try route.handler req
     with e -> error_response 500 (Printexc.to_string e))
  | None ->
    (* Try static files from ./public *)
    (match serve_static_file "public" req.path with
     | Some resp -> resp
     | None -> not_found_response ())

let handle_client (client_sock : Unix.file_descr) addr =
  let ic = Unix.in_channel_of_descr client_sock in
  let oc = Unix.out_channel_of_descr client_sock in
  let addr_str = match addr with
    | Unix.ADDR_INET (a, p) -> Printf.sprintf "%s:%d" (Unix.string_of_inet_addr a) p
    | Unix.ADDR_UNIX s -> s
  in
  (try
    match parse_request ic with
    | Some req ->
      let resp = handle_request req in
      send_response oc resp;
      Printf.printf "[%s] %s %s %s → %d\n%!"
        (timestamp ()) addr_str (string_of_method req.meth) req.raw_path resp.status
    | None ->
      let resp = error_response 400 "Bad Request" in
      send_response oc resp
  with e ->
    Printf.printf "[%s] %s Error: %s\n%!" (timestamp ()) addr_str (Printexc.to_string e));
  (try close_in ic with _ -> ());
  (try Unix.close client_sock with _ -> ())

let start_server port =
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt sock Unix.SO_REUSEADDR true;
  Unix.bind sock (Unix.ADDR_INET (Unix.inet_addr_any, port));
  Unix.listen sock 128;
  Printf.printf "\n\xF0\x9F\x90\xAB OCaml HTTP Server running on http://localhost:%d\n" port;
  Printf.printf "   Press Ctrl+C to stop\n\n%!";
  (* Clean up zombie processes *)
  Sys.set_signal Sys.sigchld Sys.Signal_ignore;
  while true do
    let (client_sock, addr) = Unix.accept sock in
    match Unix.fork () with
    | 0 ->
      (* Child process *)
      Unix.close sock;
      handle_client client_sock addr;
      exit 0
    | _pid ->
      (* Parent *)
      Unix.close client_sock
  done

(* ── Main ────────────────────────────────────────────────────────── *)

let () =
  let port = if Array.length Sys.argv > 1
    then (try int_of_string Sys.argv.(1) with _ -> 8080)
    else 8080 in
  register_demo_routes ();
  start_server port
