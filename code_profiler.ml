(* code_profiler.ml — Autonomous Code Complexity Profiler
   Analyzes OCaml source files to assess complexity and suggest improvements.

   Features:
   - Scans all .ml files in the repository (excludes test files)
   - Computes per-file metrics: line counts, function count, nesting depth,
     cyclomatic complexity, pattern match density
   - Composite complexity scoring (0-100)
   - Ranks files by complexity with top-10 display
   - Suggests refactoring actions for complex files
   - Category distribution analysis (Simple/Moderate/Complex/Very Complex)
   - ASCII histogram of complexity distribution
   - Cluster detection for related complex files

   Usage: ocaml code_profiler.ml
*)

(* ── Types ─────────────────────────────────────────────────────── *)

type file_metrics = {
  filename : string;
  total_lines : int;
  code_lines : int;
  comment_lines : int;
  blank_lines : int;
  function_count : int;
  max_nesting : int;
  cyclomatic : int;
  match_expressions : int;
  pattern_density : float;  (* match exprs per 100 lines *)
  complexity_score : float; (* 0-100 *)
}

type complexity_tier =
  | Simple       (* 0-25 *)
  | Moderate     (* 26-50 *)
  | Complex      (* 51-75 *)
  | Very_complex (* 76-100 *)

(* ── Utility ───────────────────────────────────────────────────── *)

let tier_of_score s =
  if s <= 25.0 then Simple
  else if s <= 50.0 then Moderate
  else if s <= 75.0 then Complex
  else Very_complex

let tier_name = function
  | Simple -> "Simple"
  | Moderate -> "Moderate"
  | Complex -> "Complex"
  | Very_complex -> "Very Complex"

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

let string_contains haystack needle =
  let nlen = String.length needle in
  let hlen = String.length haystack in
  if nlen > hlen then false
  else begin
    let found = ref false in
    for i = 0 to hlen - nlen do
      if not !found then begin
        let matches = ref true in
        for j = 0 to nlen - 1 do
          if haystack.[i + j] <> needle.[j] then matches := false
        done;
        if !matches then found := true
      end
    done;
    !found
  end

let starts_with s prefix =
  let plen = String.length prefix in
  String.length s >= plen && String.sub s 0 plen = prefix

let trim s =
  let len = String.length s in
  let i = ref 0 in
  while !i < len && (s.[!i] = ' ' || s.[!i] = '\t' || s.[!i] = '\r') do
    incr i
  done;
  let j = ref (len - 1) in
  while !j >= !i && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\r') do
    decr j
  done;
  if !i > !j then "" else String.sub s !i (!j - !i + 1)

(* ── File discovery ────────────────────────────────────────────── *)

let is_target_file name =
  let len = String.length name in
  len > 3
  && String.sub name (len - 3) 3 = ".ml"
  && not (starts_with name "test_")
  && name <> "code_profiler.ml"

let discover_files () =
  let entries = Sys.readdir "." in
  let result = ref [] in
  Array.iter (fun name ->
    if is_target_file name then
      result := name :: !result
  ) entries;
  List.sort compare !result

(* ── Metrics computation ───────────────────────────────────────── *)

let count_occurrences line pattern =
  let plen = String.length pattern in
  let llen = String.length line in
  if plen > llen then 0
  else begin
    let count = ref 0 in
    for i = 0 to llen - plen do
      let ok = ref true in
      for j = 0 to plen - 1 do
        if line.[i + j] <> pattern.[j] then ok := false
      done;
      if !ok then incr count
    done;
    !count
  end

let analyze_file filename =
  let content = read_file filename in
  let all_lines = lines_of_string content in
  let total_lines = List.length all_lines in

  let blank = ref 0 in
  let comment = ref 0 in
  let code = ref 0 in
  let func_count = ref 0 in
  let match_count = ref 0 in
  let cyclo = ref 1 in (* base complexity *)
  let max_nest = ref 0 in
  let in_comment = ref false in

  (* Simple nesting tracker: indent-based heuristic *)
  let measure_indent line =
    let len = String.length line in
    let i = ref 0 in
    while !i < len && (line.[!i] = ' ' || line.[!i] = '\t') do
      (if line.[!i] = '\t' then i := !i + 2 else incr i)
    done;
    !i / 2  (* approximate nesting level *)
  in

  List.iter (fun line ->
    let trimmed = trim line in
    if String.length trimmed = 0 then
      incr blank
    else if starts_with trimmed "(*" || !in_comment then begin
      incr comment;
      if string_contains trimmed "(*" then in_comment := true;
      if string_contains trimmed "*)" then in_comment := false
    end else begin
      incr code;

      (* Function count *)
      if string_contains trimmed "let " || string_contains trimmed "let rec " then
        incr func_count;

      (* Match expressions *)
      if string_contains trimmed "match " && string_contains trimmed " with" then
        incr match_count;

      (* Cyclomatic complexity contributors *)
      cyclo := !cyclo + count_occurrences trimmed "| ";
      cyclo := !cyclo + count_occurrences trimmed "if ";
      cyclo := !cyclo + count_occurrences trimmed "||";
      cyclo := !cyclo + count_occurrences trimmed "&&";

      (* Nesting depth *)
      let nest = measure_indent line in
      if nest > !max_nest then max_nest := nest
    end
  ) all_lines;

  let pattern_density =
    if total_lines > 0 then
      (float_of_int !match_count) /. (float_of_int total_lines) *. 100.0
    else 0.0
  in

  (* Composite complexity score: weighted combination, capped at 100 *)
  let raw_score =
    (float_of_int total_lines) *. 0.02          (* lines: 500 lines -> 10 pts *)
    +. (float_of_int !func_count) *. 0.8        (* funcs: 25 funcs -> 20 pts *)
    +. (float_of_int !max_nest) *. 2.5           (* nesting: depth 8 -> 20 pts *)
    +. (float_of_int !cyclo) *. 0.15             (* cyclomatic: 100 -> 15 pts *)
    +. pattern_density *. 1.0                     (* pattern density *)
    +. (float_of_int !match_count) *. 0.5        (* match count *)
  in
  let score = min 100.0 (max 0.0 raw_score) in

  { filename;
    total_lines;
    code_lines = !code;
    comment_lines = !comment;
    blank_lines = !blank;
    function_count = !func_count;
    max_nesting = !max_nest;
    cyclomatic = !cyclo;
    match_expressions = !match_count;
    pattern_density;
    complexity_score = score;
  }

(* ── Refactoring suggestions ──────────────────────────────────── *)

let suggest_refactorings m =
  let suggestions = ref [] in
  if m.total_lines > 500 then
    suggestions :=
      (Printf.sprintf "Consider breaking into submodules (%d lines)" m.total_lines)
      :: !suggestions;
  if m.max_nesting > 5 then
    suggestions :=
      (Printf.sprintf "Deeply nested logic (depth %d) — extract helper functions" m.max_nesting)
      :: !suggestions;
  if m.pattern_density > 15.0 then
    suggestions :=
      (Printf.sprintf "High pattern density (%.1f/100 lines) — consider polymorphic variants or GADTs" m.pattern_density)
      :: !suggestions;
  if m.function_count > 20 then
    suggestions :=
      (Printf.sprintf "Many functions (%d) — consider splitting into interface (.mli) + implementation" m.function_count)
      :: !suggestions;
  if m.cyclomatic > 80 then
    suggestions :=
      (Printf.sprintf "High cyclomatic complexity (%d) — simplify branching logic" m.cyclomatic)
      :: !suggestions;
  List.rev !suggestions

(* ── Cluster detection ─────────────────────────────────────────── *)

let extract_prefix name =
  (* Get prefix before first underscore, or first 4 chars *)
  try
    let idx = String.index name '_' in
    if idx > 0 then String.sub name 0 idx else name
  with Not_found ->
    let len = String.length name in
    if len > 4 then String.sub name 0 4 else name

let detect_clusters metrics =
  (* Find prefixes with multiple complex files *)
  let complex_files = List.filter (fun m -> m.complexity_score > 50.0) metrics in
  let prefix_groups = Hashtbl.create 16 in
  List.iter (fun m ->
    let pfx = extract_prefix m.filename in
    let existing = try Hashtbl.find prefix_groups pfx with Not_found -> [] in
    Hashtbl.replace prefix_groups pfx (m :: existing)
  ) complex_files;
  let clusters = ref [] in
  Hashtbl.iter (fun pfx files ->
    if List.length files >= 2 then
      clusters := (pfx, files) :: !clusters
  ) prefix_groups;
  List.sort (fun (_, a) (_, b) -> compare (List.length b) (List.length a)) !clusters

(* ── Reporting ─────────────────────────────────────────────────── *)

let print_separator () =
  Printf.printf "%s\n" (String.make 72 '-')

let print_header () =
  Printf.printf "\n";
  print_separator ();
  Printf.printf "  CODE COMPLEXITY PROFILER — Autonomous Analysis Report\n";
  print_separator ();
  Printf.printf "\n"

let print_top_files metrics n =
  let sorted = List.sort (fun a b ->
    compare b.complexity_score a.complexity_score
  ) metrics in
  let top = ref [] in
  let i = ref 0 in
  List.iter (fun m ->
    if !i < n then begin
      top := m :: !top;
      incr i
    end
  ) sorted;
  let top = List.rev !top in

  Printf.printf "  TOP %d MOST COMPLEX FILES\n" n;
  print_separator ();
  Printf.printf "  %-35s  Score  Lines  Funcs  Nest  Cyclo\n" "File";
  print_separator ();
  List.iter (fun m ->
    Printf.printf "  %-35s  %5.1f  %5d  %5d  %4d  %5d\n"
      m.filename
      m.complexity_score
      m.total_lines
      m.function_count
      m.max_nesting
      m.cyclomatic
  ) top;
  Printf.printf "\n"

let print_distribution metrics =
  let simple = ref 0 in
  let moderate = ref 0 in
  let complex_ = ref 0 in
  let very_complex = ref 0 in
  List.iter (fun m ->
    match tier_of_score m.complexity_score with
    | Simple -> incr simple
    | Moderate -> incr moderate
    | Complex -> incr complex_
    | Very_complex -> incr very_complex
  ) metrics;

  Printf.printf "  COMPLEXITY DISTRIBUTION\n";
  print_separator ();
  Printf.printf "  Simple (0-25):       %3d files\n" !simple;
  Printf.printf "  Moderate (26-50):    %3d files\n" !moderate;
  Printf.printf "  Complex (51-75):     %3d files\n" !complex_;
  Printf.printf "  Very Complex (76+):  %3d files\n" !very_complex;
  Printf.printf "\n"

let print_histogram metrics =
  (* 10-bucket histogram *)
  let buckets = Array.make 10 0 in
  List.iter (fun m ->
    let idx = min 9 (int_of_float (m.complexity_score /. 10.0)) in
    buckets.(idx) <- buckets.(idx) + 1
  ) metrics;
  let max_count = Array.fold_left max 1 buckets in

  Printf.printf "  COMPLEXITY HISTOGRAM\n";
  print_separator ();
  for i = 0 to 9 do
    let lo = i * 10 in
    let hi = lo + 9 in
    let bar_len = buckets.(i) * 40 / max_count in
    let bar = String.make bar_len '#' in
    Printf.printf "  %3d-%3d | %-40s %d\n" lo hi bar buckets.(i)
  done;
  Printf.printf "\n"

let print_suggestions metrics =
  let complex_files = List.filter (fun m -> m.complexity_score > 70.0) metrics in
  let complex_sorted = List.sort (fun a b ->
    compare b.complexity_score a.complexity_score
  ) complex_files in
  if complex_sorted <> [] then begin
    Printf.printf "  REFACTORING SUGGESTIONS\n";
    print_separator ();
    List.iter (fun m ->
      let suggestions = suggest_refactorings m in
      if suggestions <> [] then begin
        Printf.printf "  %s (score: %.1f):\n" m.filename m.complexity_score;
        List.iter (fun s ->
          Printf.printf "    -> %s\n" s
        ) suggestions;
        Printf.printf "\n"
      end
    ) complex_sorted
  end

let print_clusters metrics =
  let clusters = detect_clusters metrics in
  if clusters <> [] then begin
    Printf.printf "  COMPLEXITY CLUSTERS (related complex files)\n";
    print_separator ();
    List.iter (fun (pfx, files) ->
      Printf.printf "  Prefix '%s' (%d complex files):\n" pfx (List.length files);
      List.iter (fun m ->
        Printf.printf "    - %-30s  score: %.1f\n" m.filename m.complexity_score
      ) files;
      Printf.printf "\n"
    ) clusters
  end

let print_summary metrics =
  let n = List.length metrics in
  let total_score = List.fold_left (fun acc m -> acc +. m.complexity_score) 0.0 metrics in
  let avg = if n > 0 then total_score /. float_of_int n else 0.0 in
  let total_lines = List.fold_left (fun acc m -> acc + m.total_lines) 0 metrics in
  let total_funcs = List.fold_left (fun acc m -> acc + m.function_count) 0 metrics in
  let max_file = List.fold_left (fun best m ->
    if m.complexity_score > best.complexity_score then m else best
  ) (List.hd metrics) (List.tl metrics) in
  let min_file = List.fold_left (fun best m ->
    if m.complexity_score < best.complexity_score then m else best
  ) (List.hd metrics) (List.tl metrics) in

  Printf.printf "  SUMMARY\n";
  print_separator ();
  Printf.printf "  Files analyzed:       %d\n" n;
  Printf.printf "  Total lines:          %d\n" total_lines;
  Printf.printf "  Total functions:      %d\n" total_funcs;
  Printf.printf "  Average complexity:   %.1f\n" avg;
  Printf.printf "  Most complex:         %s (%.1f)\n" max_file.filename max_file.complexity_score;
  Printf.printf "  Least complex:        %s (%.1f)\n" min_file.filename min_file.complexity_score;
  Printf.printf "\n"

(* ── Main ──────────────────────────────────────────────────────── *)

let () =
  let files = discover_files () in
  let n = List.length files in
  if n = 0 then begin
    Printf.printf "No .ml files found to analyze.\n";
    exit 0
  end;

  Printf.eprintf "Scanning %d files...\n%!" n;
  let metrics = List.map analyze_file files in

  print_header ();
  print_top_files metrics 10;
  print_distribution metrics;
  print_histogram metrics;
  print_suggestions metrics;
  print_clusters metrics;
  print_summary metrics;
  print_separator ();
  Printf.printf "  Analysis complete. %d files profiled.\n" n;
  print_separator ();
  Printf.printf "\n"
