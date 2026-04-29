(* dependency_auditor.ml — Autonomous Module Dependency Auditor
   Discovers, analyzes, and diagnoses module-level dependencies across
   all OCaml source files in the repository.

   Features:
   - Scans all .ml files (excludes test_ prefixed files)
   - Discovers dependencies via: open Module, Module.x references, include Module
   - Builds a directed dependency graph between files
   - Detects circular dependencies using Tarjan's SCC algorithm
   - Computes coupling metrics per file (fan-in, fan-out, coupling score)
   - Identifies bottleneck modules (high coupling)
   - Finds orphan modules (no incoming or outgoing edges)
   - Infers layers (Foundation, Core, Application, Isolated) from depth
   - Detects layering violations (upward dependencies)
   - Finds shortest dependency paths between any two modules
   - Generates prioritized recommendations with severity
   - Computes repository-wide Modularity Score (0-100)
   - Interactive REPL for exploration

   Usage: ocaml dependency_auditor.ml
*)

(* ── Types ──────────────────────────────────────────────────────── *)

type dependency_kind = Open_dep | Module_ref | Include_dep

type dependency = {
  source_file : string;
  target_module : string;
  kind : dependency_kind;
  line_number : int;
}

type layer = Foundation | Core | Application | Isolated

type module_info = {
  filename : string;
  module_name : string;
  fan_in : int;
  fan_out : int;
  dependencies : dependency list;
  dependents : string list;
  coupling_score : float;
  layer : layer;
}

type recommendation = {
  severity : int; (* 1=low, 2=medium, 3=high *)
  category : string;
  target : string;
  message : string;
}

type audit_result = {
  modules : module_info list;
  cycles : string list list;
  bottlenecks : module_info list;
  orphans : module_info list;
  layer_violations : (string * string * layer * layer) list;
  modularity_score : float;
  recommendations : recommendation list;
}

(* ── Utilities ──────────────────────────────────────────────────── *)

let read_file path =
  let ic = open_in path in
  let buf = Buffer.create 4096 in
  (try while true do
     let line = input_line ic in
     Buffer.add_string buf line;
     Buffer.add_char buf '\n'
   done with End_of_file -> ());
  close_in ic;
  Buffer.contents buf

let lines_of_string s =
  let len = String.length s in
  if len = 0 then []
  else begin
    let result = ref [] in
    let start = ref 0 in
    for i = 0 to len - 1 do
      if s.[i] = '\n' then begin
        result := String.sub s !start (i - !start) :: !result;
        start := i + 1
      end
    done;
    if !start < len then
      result := String.sub s !start (len - !start) :: !result;
    List.rev !result
  end

let trim s =
  let len = String.length s in
  let i = ref 0 in
  while !i < len && (s.[!i] = ' ' || s.[!i] = '\t' || s.[!i] = '\r' || s.[!i] = '\n') do
    incr i
  done;
  let j = ref (len - 1) in
  while !j >= !i && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\r' || s.[!j] = '\n') do
    decr j
  done;
  if !i > !j then "" else String.sub s !i (!j - !i + 1)

let starts_with prefix s =
  let lp = String.length prefix in
  let ls = String.length s in
  ls >= lp && String.sub s 0 lp = prefix

let ends_with suffix s =
  let ls = String.length s in
  let lsuf = String.length suffix in
  ls >= lsuf && String.sub s (ls - lsuf) lsuf = suffix

let contains_substring haystack needle =
  let lh = String.length haystack and ln = String.length needle in
  if ln = 0 then true
  else if ln > lh then false
  else begin
    let found = ref false in
    for i = 0 to lh - ln do
      if not !found && String.sub haystack i ln = needle then found := true
    done;
    !found
  end

let module_name_of_file fn =
  (* foo_bar.ml -> Foo_bar *)
  let base =
    if ends_with ".ml" fn then String.sub fn 0 (String.length fn - 3)
    else fn
  in
  if String.length base = 0 then base
  else
    let first = Char.uppercase_ascii base.[0] in
    String.make 1 first ^ (if String.length base > 1 then String.sub base 1 (String.length base - 1) else "")

let is_uppercase c = c >= 'A' && c <= 'Z'

let list_mem x lst = List.exists (fun y -> y = x) lst

let list_unique lst =
  List.fold_left (fun acc x -> if list_mem x acc then acc else x :: acc) [] lst
  |> List.rev

let list_sort_by f lst =
  List.sort (fun a b -> compare (f a) (f b)) lst

let max_float a b : float = if a > b then a else b
let min_float a b : float = if a < b then a else b
let min_int_ a b = if a < b then a else b

let pad_right s n =
  let l = String.length s in
  if l >= n then s else s ^ String.make (n - l) ' '

let layer_to_string = function
  | Foundation -> "Foundation"
  | Core -> "Core"
  | Application -> "Application"
  | Isolated -> "Isolated"

let layer_to_int = function
  | Foundation -> 0 | Core -> 1 | Application -> 2 | Isolated -> -1

let severity_to_string = function
  | 1 -> "LOW" | 2 -> "MEDIUM" | 3 -> "HIGH" | _ -> "?"

let dep_kind_to_string = function
  | Open_dep -> "open"
  | Module_ref -> "ref"
  | Include_dep -> "include"

(* ── File Discovery ─────────────────────────────────────────────── *)

let discover_ml_files () =
  let entries = Sys.readdir "." in
  let files = ref [] in
  Array.iter (fun e ->
    if ends_with ".ml" e
       && not (starts_with "test_" e)
       && e <> "test_all.ml"
       && e <> "test_framework.ml"
    then files := e :: !files
  ) entries;
  List.sort compare !files

(* ── Dependency Extraction ──────────────────────────────────────── *)

(* Known stdlib/built-in modules to exclude *)
let stdlib_modules = [
  "Printf"; "Scanf"; "Sys"; "Unix"; "Array"; "List"; "String";
  "Buffer"; "Hashtbl"; "Map"; "Set"; "Queue"; "Stack"; "Char";
  "Bytes"; "Int"; "Float"; "Bool"; "Option"; "Result"; "Seq";
  "Lazy"; "Random"; "Format"; "Filename"; "Digest"; "Gc";
  "Printexc"; "Arg"; "Lexing"; "Parsing"; "Complex"; "Int32";
  "Int64"; "Nativeint"; "Marshal"; "Obj"; "Callback"; "Weak";
  "Ephemeron"; "Spacetime"; "Bigarray"; "Genlex"; "Stream";
  "Pervasives"; "Stdlib"; "Fun"; "Unit"; "In_channel"; "Out_channel";
  "Mutex"; "Condition"; "Thread"; "Event"; "Domain"; "Atomic";
  "Dynlink"; "Str"
]

let is_stdlib_module m = list_mem m stdlib_modules

(* Extract a word starting at position i (alphanumeric + underscore) *)
let extract_word s i =
  let len = String.length s in
  let j = ref i in
  while !j < len && (let c = s.[!j] in
    (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
    (c >= '0' && c <= '9') || c = '_') do
    incr j
  done;
  if !j > i then Some (String.sub s i (!j - i), !j) else None

let extract_dependencies_from_file filename =
  let content = read_file filename in
  let lines = lines_of_string content in
  let deps = ref [] in
  let line_num = ref 0 in
  List.iter (fun line ->
    incr line_num;
    let ln = !line_num in
    let trimmed = trim line in

    (* Skip comments *)
    if not (starts_with "(*" trimmed) then begin

      (* Detect: open Module *)
      if starts_with "open " trimmed then begin
        let rest = trim (String.sub trimmed 5 (String.length trimmed - 5)) in
        (* Take first word *)
        match extract_word rest 0 with
        | Some (modname, _) when not (is_stdlib_module modname) ->
          deps := { source_file = filename; target_module = modname;
                    kind = Open_dep; line_number = ln } :: !deps
        | _ -> ()
      end;

      (* Detect: include Module *)
      if starts_with "include " trimmed then begin
        let rest = trim (String.sub trimmed 8 (String.length trimmed - 8)) in
        match extract_word rest 0 with
        | Some (modname, _) when not (is_stdlib_module modname) && is_uppercase modname.[0] ->
          deps := { source_file = filename; target_module = modname;
                    kind = Include_dep; line_number = ln } :: !deps
        | _ -> ()
      end;

      (* Detect: Module.something references *)
      let len = String.length trimmed in
      let i = ref 0 in
      while !i < len - 1 do
        let c = trimmed.[!i] in
        if is_uppercase c then begin
          match extract_word trimmed !i with
          | Some (word, j) when j < len && trimmed.[j] = '.' &&
                                 String.length word > 1 &&
                                 not (is_stdlib_module word) ->
            (* Check it's not inside a string or after a dot *)
            let prev_ok = !i = 0 || (let p = trimmed.[!i - 1] in
              p = ' ' || p = '(' || p = '[' || p = '{' || p = ';' ||
              p = '|' || p = ',' || p = '\t' || p = '~' || p = '!') in
            if prev_ok then
              deps := { source_file = filename; target_module = word;
                        kind = Module_ref; line_number = ln } :: !deps;
            i := j + 1
          | Some (_, j) -> i := j
          | None -> incr i
        end
        else incr i
      done
    end
  ) lines;
  List.rev !deps

(* ── Graph Building ─────────────────────────────────────────────── *)

(* Map module names to filenames *)
let build_module_map files =
  List.map (fun f -> (module_name_of_file f, f)) files

let resolve_deps files all_deps =
  let mod_map = build_module_map files in
  (* For each dependency, try to resolve target_module to a file *)
  List.filter_map (fun dep ->
    match List.assoc_opt dep.target_module mod_map with
    | Some target_file when target_file <> dep.source_file ->
      Some (dep.source_file, target_file, dep)
    | _ -> None
  ) all_deps

(* Build adjacency list: file -> list of files it depends on *)
let build_adj_list files resolved =
  let tbl = Hashtbl.create (List.length files) in
  List.iter (fun f -> Hashtbl.replace tbl f []) files;
  List.iter (fun (src, tgt, _dep) ->
    let cur = try Hashtbl.find tbl src with Not_found -> [] in
    if not (list_mem tgt cur) then Hashtbl.replace tbl src (tgt :: cur)
  ) resolved;
  tbl

(* Build reverse adjacency list *)
let build_rev_adj files resolved =
  let tbl = Hashtbl.create (List.length files) in
  List.iter (fun f -> Hashtbl.replace tbl f []) files;
  List.iter (fun (src, tgt, _dep) ->
    let cur = try Hashtbl.find tbl tgt with Not_found -> [] in
    if not (list_mem src cur) then Hashtbl.replace tbl tgt (src :: cur)
  ) resolved;
  tbl

(* ── Tarjan's SCC ───────────────────────────────────────────────── *)

let tarjan_scc files adj =
  let n = List.length files in
  let index_map = Hashtbl.create n in
  let lowlink = Hashtbl.create n in
  let on_stack = Hashtbl.create n in
  let stack = ref [] in
  let idx = ref 0 in
  let sccs = ref [] in

  let rec strongconnect v =
    Hashtbl.replace index_map v !idx;
    Hashtbl.replace lowlink v !idx;
    incr idx;
    stack := v :: !stack;
    Hashtbl.replace on_stack v true;

    let neighbors = try Hashtbl.find adj v with Not_found -> [] in
    List.iter (fun w ->
      if not (Hashtbl.mem index_map w) then begin
        strongconnect w;
        Hashtbl.replace lowlink v
          (min_int_ (Hashtbl.find lowlink v) (Hashtbl.find lowlink w))
      end else if (try Hashtbl.find on_stack w with Not_found -> false) then
        Hashtbl.replace lowlink v
          (min_int_ (Hashtbl.find lowlink v) (Hashtbl.find index_map w))
    ) neighbors;

    if Hashtbl.find lowlink v = Hashtbl.find index_map v then begin
      let scc = ref [] in
      let cont = ref true in
      while !cont do
        match !stack with
        | w :: rest ->
          stack := rest;
          Hashtbl.replace on_stack w false;
          scc := w :: !scc;
          if w = v then cont := false
        | [] -> cont := false
      done;
      if List.length !scc > 1 then
        sccs := !scc :: !sccs
    end
  in

  List.iter (fun v ->
    if not (Hashtbl.mem index_map v) then strongconnect v
  ) files;
  List.rev !sccs

(* ── Layer Inference ────────────────────────────────────────────── *)

(* Compute max depth from "root" nodes (no dependencies) via BFS *)
let infer_layers files adj =
  let depths = Hashtbl.create (List.length files) in
  (* Start: nodes with no outgoing edges are Foundation *)
  let queue = Queue.create () in
  List.iter (fun f ->
    let out = try Hashtbl.find adj f with Not_found -> [] in
    if out = [] then begin
      Hashtbl.replace depths f 0;
      Queue.push f queue
    end
  ) files;

  (* BFS in reverse: if A depends on B, A's depth >= B's depth + 1 *)
  (* Actually we need reverse traversal: who depends on this node *)
  let rev = Hashtbl.create (List.length files) in
  List.iter (fun f ->
    let outs = try Hashtbl.find adj f with Not_found -> [] in
    List.iter (fun t ->
      let cur = try Hashtbl.find rev t with Not_found -> [] in
      if not (list_mem f cur) then Hashtbl.replace rev t (f :: cur)
    ) outs
  ) files;

  (* BFS propagation *)
  while not (Queue.is_empty queue) do
    let v = Queue.pop queue in
    let d = Hashtbl.find depths v in
    let parents = try Hashtbl.find rev v with Not_found -> [] in
    List.iter (fun p ->
      let cur_d = try Hashtbl.find depths p with Not_found -> -1 in
      if d + 1 > cur_d then begin
        Hashtbl.replace depths p (d + 1);
        Queue.push p queue
      end
    ) parents
  done;

  (* Assign layers based on depth *)
  let max_depth = Hashtbl.fold (fun _ d acc -> max d acc) depths 0 in
  let layer_of_depth d =
    if max_depth = 0 then Foundation
    else
      let ratio = float_of_int d /. float_of_int max_depth in
      if ratio <= 0.33 then Foundation
      else if ratio <= 0.66 then Core
      else Application
  in
  List.map (fun f ->
    match Hashtbl.find_opt depths f with
    | Some d -> (f, layer_of_depth d)
    | None ->
      let out = try Hashtbl.find adj f with Not_found -> [] in
      if out = [] then (f, Isolated) else (f, Application)
  ) files

(* ── Layer Violation Detection ──────────────────────────────────── *)

let detect_layer_violations resolved layer_map =
  let get_layer f =
    try List.assoc f layer_map with Not_found -> Isolated
  in
  let violations = ref [] in
  let seen = Hashtbl.create 64 in
  List.iter (fun (src, tgt, _dep) ->
    let sl = get_layer src in
    let tl = get_layer tgt in
    let si = layer_to_int sl in
    let ti = layer_to_int tl in
    (* Violation: lower layer depends on higher layer *)
    if si >= 0 && ti >= 0 && si < ti then begin
      let key = src ^ "->" ^ tgt in
      if not (Hashtbl.mem seen key) then begin
        Hashtbl.replace seen key true;
        violations := (src, tgt, sl, tl) :: !violations
      end
    end
  ) resolved;
  List.rev !violations

(* ── BFS Shortest Path ──────────────────────────────────────────── *)

let bfs_path adj source target =
  if source = target then Some [source]
  else begin
    let visited = Hashtbl.create 64 in
    let parent = Hashtbl.create 64 in
    let queue = Queue.create () in
    Queue.push source queue;
    Hashtbl.replace visited source true;
    let found = ref false in
    while not (Queue.is_empty queue) && not !found do
      let v = Queue.pop queue in
      let neighbors = try Hashtbl.find adj v with Not_found -> [] in
      List.iter (fun w ->
        if not (Hashtbl.mem visited w) then begin
          Hashtbl.replace visited w true;
          Hashtbl.replace parent w v;
          if w = target then found := true
          else Queue.push w queue
        end
      ) neighbors
    done;
    if not !found then None
    else begin
      let path = ref [target] in
      let cur = ref target in
      while !cur <> source do
        cur := Hashtbl.find parent !cur;
        path := !cur :: !path
      done;
      Some !path
    end
  end

(* ── Full Audit ─────────────────────────────────────────────────── *)

let run_audit () =
  let files = discover_ml_files () in
  let n = List.length files in
  Printf.printf "\n  Scanning %d source files...\n\n" n;

  (* Extract all dependencies *)
  let all_deps = List.concat_map extract_dependencies_from_file files in

  (* Resolve to file-to-file edges *)
  let resolved = resolve_deps files all_deps in

  (* Build graphs *)
  let adj = build_adj_list files resolved in
  let rev_adj = build_rev_adj files resolved in

  (* Compute metrics per file *)
  let layer_map = infer_layers files adj in

  let modules = List.map (fun f ->
    let out = try Hashtbl.find adj f with Not_found -> [] in
    let inc = try Hashtbl.find rev_adj f with Not_found -> [] in
    let fo = List.length out in
    let fi = List.length inc in
    let coupling = float_of_int (fi + fo) in
    let file_deps = List.filter (fun d -> d.source_file = f) all_deps in
    let layer = try List.assoc f layer_map with Not_found -> Isolated in
    { filename = f;
      module_name = module_name_of_file f;
      fan_in = fi;
      fan_out = fo;
      dependencies = file_deps;
      dependents = inc;
      coupling_score = coupling;
      layer }
  ) files in

  (* Detect cycles *)
  let cycles = tarjan_scc files adj in

  (* Bottlenecks: top coupling *)
  let sorted_coupling = List.sort (fun a b ->
    compare b.coupling_score a.coupling_score) modules in
  let avg_coupling =
    if n = 0 then 0.0
    else List.fold_left (fun acc m -> acc +. m.coupling_score) 0.0 modules /. float_of_int n
  in
  let threshold = max_float (avg_coupling *. 2.0) 5.0 in
  let bottlenecks = List.filter (fun m -> m.coupling_score >= threshold) sorted_coupling in

  (* Orphans *)
  let orphans = List.filter (fun m -> m.fan_in = 0 && m.fan_out = 0) modules in

  (* Layer violations *)
  let layer_violations = detect_layer_violations resolved layer_map in

  (* Recommendations *)
  let recs = ref [] in

  (* Cycle recommendations *)
  List.iter (fun cycle ->
    let names = String.concat " -> " cycle in
    recs := { severity = 3; category = "Circular Dependency";
              target = List.hd cycle;
              message = Printf.sprintf "Cycle detected: %s. Consider extracting shared interfaces." names
            } :: !recs
  ) cycles;

  (* Bottleneck recommendations *)
  List.iter (fun m ->
    recs := { severity = 2; category = "High Coupling";
              target = m.filename;
              message = Printf.sprintf "%s has coupling score %.0f (fan-in=%d, fan-out=%d). Consider splitting into smaller modules."
                m.filename m.coupling_score m.fan_in m.fan_out
            } :: !recs
  ) bottlenecks;

  (* Orphan recommendations *)
  if List.length orphans > 10 then
    recs := { severity = 1; category = "Orphan Modules";
              target = "(multiple)";
              message = Printf.sprintf "%d modules have zero connections. Some may be self-contained utilities — consider cross-referencing or documenting relationships." (List.length orphans)
            } :: !recs;

  (* Layer violation recommendations *)
  List.iter (fun (src, tgt, sl, tl) ->
    recs := { severity = 2; category = "Layer Violation";
              target = src;
              message = Printf.sprintf "%s (%s) depends on %s (%s) — lower layer depending on higher layer."
                src (layer_to_string sl) tgt (layer_to_string tl)
            } :: !recs
  ) layer_violations;

  (* Sort recommendations by severity descending *)
  let recommendations = List.sort (fun a b -> compare b.severity a.severity) !recs in

  (* Modularity Score *)
  let cycle_penalty = float_of_int (List.length cycles) *. 10.0 in
  let violation_penalty = float_of_int (List.length layer_violations) *. 3.0 in
  let bottleneck_penalty = float_of_int (List.length bottlenecks) *. 5.0 in
  let orphan_ratio = if n = 0 then 0.0 else float_of_int (List.length orphans) /. float_of_int n in
  let orphan_penalty = orphan_ratio *. 20.0 in
  let raw_score = 100.0 -. cycle_penalty -. violation_penalty -. bottleneck_penalty -. orphan_penalty in
  let modularity_score = max_float 0.0 (min_float 100.0 raw_score) in

  { modules; cycles; bottlenecks; orphans; layer_violations;
    modularity_score; recommendations }

(* ── Display ────────────────────────────────────────────────────── *)

let print_bar width value max_val =
  let filled = if max_val = 0.0 then 0
    else int_of_float (float_of_int width *. value /. max_val) in
  let filled = min_int_ filled width in
  String.make filled '#' ^ String.make (width - filled) '-'

let print_separator () =
  Printf.printf "  %s\n" (String.make 70 '-')

let print_header title =
  Printf.printf "\n  === %s ===\n\n" title

let display_summary result =
  let n = List.length result.modules in
  let total_edges = List.fold_left (fun acc m -> acc + m.fan_out) 0 result.modules in
  print_header "DEPENDENCY AUDIT SUMMARY";
  Printf.printf "  %-30s %d\n" "Source files scanned:" n;
  Printf.printf "  %-30s %d\n" "Dependency edges:" total_edges;
  Printf.printf "  %-30s %d\n" "Circular dep cycles:" (List.length result.cycles);
  Printf.printf "  %-30s %d\n" "Bottleneck modules:" (List.length result.bottlenecks);
  Printf.printf "  %-30s %d\n" "Orphan modules:" (List.length result.orphans);
  Printf.printf "  %-30s %d\n" "Layer violations:" (List.length result.layer_violations);
  Printf.printf "\n  Modularity Score: %.1f / 100  [%s]\n"
    result.modularity_score
    (if result.modularity_score >= 80.0 then "EXCELLENT"
     else if result.modularity_score >= 60.0 then "GOOD"
     else if result.modularity_score >= 40.0 then "FAIR"
     else if result.modularity_score >= 20.0 then "POOR"
     else "CRITICAL");
  Printf.printf "  [%s]\n\n"
    (print_bar 40 result.modularity_score 100.0)

let display_top_coupled result =
  print_header "TOP 15 MOST COUPLED MODULES";
  Printf.printf "  %-30s %6s %6s %8s  %s\n" "File" "Fan-in" "Fan-out" "Score" "Bar";
  print_separator ();
  let top = List.sort (fun a b -> compare b.coupling_score a.coupling_score) result.modules in
  let max_c = match top with m :: _ -> m.coupling_score | [] -> 1.0 in
  let shown = ref 0 in
  List.iter (fun m ->
    if !shown < 15 && m.coupling_score > 0.0 then begin
      Printf.printf "  %-30s %6d %6d %8.1f  [%s]\n"
        m.filename m.fan_in m.fan_out m.coupling_score
        (print_bar 20 m.coupling_score max_c);
      incr shown
    end
  ) top

let display_cycles result =
  print_header "CIRCULAR DEPENDENCIES";
  if result.cycles = [] then
    Printf.printf "  No circular dependencies detected.\n"
  else begin
    Printf.printf "  Found %d cycle(s):\n\n" (List.length result.cycles);
    List.iteri (fun i cycle ->
      Printf.printf "  Cycle %d: %s -> (back to %s)\n"
        (i + 1) (String.concat " -> " cycle) (List.hd cycle)
    ) result.cycles
  end

let display_bottlenecks result =
  print_header "BOTTLENECK MODULES";
  if result.bottlenecks = [] then
    Printf.printf "  No bottleneck modules detected.\n"
  else begin
    Printf.printf "  %d module(s) exceed coupling threshold:\n\n" (List.length result.bottlenecks);
    List.iter (fun m ->
      Printf.printf "  * %-28s  coupling=%.0f  (in=%d, out=%d)  layer=%s\n"
        m.filename m.coupling_score m.fan_in m.fan_out (layer_to_string m.layer)
    ) result.bottlenecks
  end

let display_orphans result =
  print_header "ORPHAN MODULES";
  let n = List.length result.orphans in
  if n = 0 then
    Printf.printf "  No orphan modules.\n"
  else begin
    Printf.printf "  %d module(s) with no resolved dependencies in either direction:\n\n" n;
    let per_row = 4 in
    let sorted = list_sort_by (fun m -> m.filename) result.orphans in
    let idx = ref 0 in
    List.iter (fun m ->
      Printf.printf "  %-24s" m.filename;
      incr idx;
      if !idx mod per_row = 0 then Printf.printf "\n"
    ) sorted;
    if !idx mod per_row <> 0 then Printf.printf "\n"
  end

let display_layers result =
  print_header "INFERRED ARCHITECTURE LAYERS";
  let count layer = List.length (List.filter (fun m -> m.layer = layer) result.modules) in
  let layers = [Application; Core; Foundation; Isolated] in
  List.iter (fun l ->
    let c = count l in
    Printf.printf "  %-15s %3d modules  [%s]\n"
      (layer_to_string l) c
      (print_bar 30 (float_of_int c) (float_of_int (List.length result.modules)))
  ) layers;
  Printf.printf "\n  Top Application-layer modules:\n";
  let app_modules = List.filter (fun m -> m.layer = Application) result.modules in
  let sorted = List.sort (fun a b -> compare b.fan_out a.fan_out) app_modules in
  let shown = ref 0 in
  List.iter (fun m ->
    if !shown < 10 then begin
      Printf.printf "    %-30s (fan-out=%d)\n" m.filename m.fan_out;
      incr shown
    end
  ) sorted

let display_violations result =
  print_header "LAYER VIOLATIONS";
  let n = List.length result.layer_violations in
  if n = 0 then
    Printf.printf "  No layer violations detected.\n"
  else begin
    Printf.printf "  %d violation(s) — lower-layer modules depending on higher layers:\n\n" n;
    List.iter (fun (src, tgt, sl, tl) ->
      Printf.printf "  * %s (%s) --> %s (%s)\n"
        src (layer_to_string sl) tgt (layer_to_string tl)
    ) result.layer_violations
  end

let display_recommendations result =
  print_header "RECOMMENDATIONS";
  if result.recommendations = [] then
    Printf.printf "  No issues found — repository is well-structured!\n"
  else begin
    Printf.printf "  %d recommendation(s):\n\n" (List.length result.recommendations);
    List.iteri (fun i r ->
      Printf.printf "  %d. [%s] %s\n     Target: %s\n     %s\n\n"
        (i + 1) (severity_to_string r.severity) r.category r.target r.message
    ) result.recommendations
  end

let display_file_deps result filename =
  match List.find_opt (fun m -> m.filename = filename) result.modules with
  | None -> Printf.printf "  File not found: %s\n" filename
  | Some m ->
    Printf.printf "\n  Dependencies of %s (fan-out=%d):\n" filename m.fan_out;
    let out = list_unique (List.filter_map (fun d ->
      let mod_map = build_module_map (List.map (fun m -> m.filename) result.modules) in
      match List.assoc_opt d.target_module mod_map with
      | Some f when f <> filename -> Some (f, d)
      | _ -> None
    ) m.dependencies) in
    if out = [] then Printf.printf "    (none resolved)\n"
    else List.iter (fun (f, d) ->
      Printf.printf "    -> %-30s  [%s] line %d\n" f (dep_kind_to_string d.kind) d.line_number
    ) out

let display_file_rdeps result filename =
  match List.find_opt (fun m -> m.filename = filename) result.modules with
  | None -> Printf.printf "  File not found: %s\n" filename
  | Some m ->
    Printf.printf "\n  Reverse dependencies of %s (fan-in=%d):\n" filename m.fan_in;
    if m.dependents = [] then Printf.printf "    (none)\n"
    else List.iter (fun d ->
      Printf.printf "    <- %s\n" d
    ) m.dependents

let display_full_report result =
  display_summary result;
  display_top_coupled result;
  display_cycles result;
  display_bottlenecks result;
  display_orphans result;
  display_layers result;
  display_violations result;
  display_recommendations result

(* ── Score Breakdown ────────────────────────────────────────────── *)

let display_score_breakdown result =
  let n = List.length result.modules in
  let cycle_penalty = float_of_int (List.length result.cycles) *. 10.0 in
  let violation_penalty = float_of_int (List.length result.layer_violations) *. 3.0 in
  let bottleneck_penalty = float_of_int (List.length result.bottlenecks) *. 5.0 in
  let orphan_ratio = if n = 0 then 0.0 else float_of_int (List.length result.orphans) /. float_of_int n in
  let orphan_penalty = orphan_ratio *. 20.0 in
  print_header "MODULARITY SCORE BREAKDOWN";
  Printf.printf "  %-35s %8s\n" "Factor" "Penalty";
  print_separator ();
  Printf.printf "  %-35s %8.1f  (%d cycles x 10)\n" "Circular dependencies" cycle_penalty (List.length result.cycles);
  Printf.printf "  %-35s %8.1f  (%d violations x 3)\n" "Layer violations" violation_penalty (List.length result.layer_violations);
  Printf.printf "  %-35s %8.1f  (%d bottlenecks x 5)\n" "Bottleneck modules" bottleneck_penalty (List.length result.bottlenecks);
  Printf.printf "  %-35s %8.1f  (%.0f%% orphans x 20)\n" "Orphan ratio" orphan_penalty (orphan_ratio *. 100.0);
  print_separator ();
  Printf.printf "  %-35s %8.1f\n" "Total penalty" (cycle_penalty +. violation_penalty +. bottleneck_penalty +. orphan_penalty);
  Printf.printf "  %-35s %8.1f / 100\n\n" "Final Modularity Score" result.modularity_score

(* ── Path Finding ───────────────────────────────────────────────── *)

let display_path result src tgt =
  let files = List.map (fun m -> m.filename) result.modules in
  let resolved = resolve_deps files
    (List.concat_map (fun m -> m.dependencies) result.modules) in
  let adj = build_adj_list files resolved in
  match bfs_path adj src tgt with
  | None -> Printf.printf "\n  No dependency path from %s to %s\n" src tgt
  | Some path ->
    Printf.printf "\n  Dependency path (%d hops):\n  " (List.length path - 1);
    Printf.printf "  %s\n" (String.concat " -> " path)

(* ── Interactive REPL ───────────────────────────────────────────── *)

let print_help () =
  Printf.printf "\n  Dependency Auditor Commands:\n";
  Printf.printf "  %-25s %s\n" "scan" "Run full dependency audit";
  Printf.printf "  %-25s %s\n" "deps <file>" "Show dependencies of a file";
  Printf.printf "  %-25s %s\n" "rdeps <file>" "Show who depends on a file";
  Printf.printf "  %-25s %s\n" "cycles" "List circular dependency cycles";
  Printf.printf "  %-25s %s\n" "bottlenecks" "Show highest-coupling modules";
  Printf.printf "  %-25s %s\n" "orphans" "List orphan modules";
  Printf.printf "  %-25s %s\n" "layers" "Show inferred architecture layers";
  Printf.printf "  %-25s %s\n" "violations" "Show layer violations";
  Printf.printf "  %-25s %s\n" "path <from> <to>" "Find dependency path between files";
  Printf.printf "  %-25s %s\n" "score" "Show modularity score breakdown";
  Printf.printf "  %-25s %s\n" "report" "Full text report";
  Printf.printf "  %-25s %s\n" "help" "Show this help";
  Printf.printf "  %-25s %s\n" "quit" "Exit";
  Printf.printf "\n"

let () =
  Printf.printf "\n";
  Printf.printf "  ╔══════════════════════════════════════════════╗\n";
  Printf.printf "  ║     Dependency Auditor — Module Analysis     ║\n";
  Printf.printf "  ║   Autonomous dependency graph diagnostics    ║\n";
  Printf.printf "  ╚══════════════════════════════════════════════╝\n";
  Printf.printf "\n  Type 'help' for commands, 'scan' to begin audit.\n\n";

  let result = ref None in

  let get_result () =
    match !result with
    | Some r -> r
    | None ->
      Printf.printf "  Running initial scan...\n";
      let r = run_audit () in
      result := Some r;
      r
  in

  let running = ref true in
  while !running do
    Printf.printf "  audit> ";
    flush stdout;
    match try Some (input_line stdin) with End_of_file -> None with
    | None -> running := false
    | Some line ->
      let parts = String.split_on_char ' ' (trim line) in
      match parts with
      | ["quit"] | ["exit"] | ["q"] -> running := false
      | ["help"] | ["h"] | ["?"] -> print_help ()
      | ["scan"] ->
        let r = run_audit () in
        result := Some r;
        display_summary r
      | ["report"] ->
        let r = get_result () in
        display_full_report r
      | ["cycles"] ->
        let r = get_result () in
        display_cycles r
      | ["bottlenecks"] ->
        let r = get_result () in
        display_bottlenecks r
      | ["orphans"] ->
        let r = get_result () in
        display_orphans r
      | ["layers"] ->
        let r = get_result () in
        display_layers r
      | ["violations"] ->
        let r = get_result () in
        display_violations r
      | ["score"] ->
        let r = get_result () in
        display_score_breakdown r
      | ["deps"; f] ->
        let r = get_result () in
        display_file_deps r f
      | ["rdeps"; f] ->
        let r = get_result () in
        display_file_rdeps r f
      | ["path"; src; tgt] ->
        let r = get_result () in
        display_path r src tgt
      | [""] -> ()
      | _ -> Printf.printf "  Unknown command. Type 'help' for available commands.\n"
  done;
  Printf.printf "\n  Audit complete. Goodbye!\n\n"
