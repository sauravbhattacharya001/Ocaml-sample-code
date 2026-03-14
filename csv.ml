(* csv.ml — CSV parser with type inference and data analysis
 *
 * A functional CSV processing library demonstrating:
 *   - Character-level parsing with proper quote/escape handling (RFC 4180)
 *   - Automatic type inference (int, float, string) per column
 *   - Fold-based aggregation: sum, avg, min, max, count
 *   - Group-by operations with multi-column support
 *   - Pretty-printed tabular output with alignment
 *   - Pipeline-style data transformations
 *
 * Concepts: string parsing, algebraic data types, higher-order functions,
 * fold/map/filter, pattern matching, records, modules, pretty-printing,
 * option types, polymorphic comparison, tail recursion.
 *
 * Compile & run:
 *   ocamlfind ocamlopt -package str -linkpkg csv.ml -o csv && ./csv
 *)

(* ---------- Cell types and type inference ---------- *)

(** A typed cell value — automatically inferred from CSV text. *)
type cell =
  | Int of int
  | Float of float
  | Str of string
  | Empty

(** Infer the type of a raw string cell. Tries int, then float, then string. *)
let infer_cell (s : string) : cell =
  let trimmed = String.trim s in
  if trimmed = "" then Empty
  else
    match int_of_string_opt trimmed with
    | Some i -> Int i
    | None ->
      match float_of_string_opt trimmed with
      | Some f -> Float f
      | None -> Str trimmed

(** Convert a cell to float, if numeric. *)
let cell_to_float = function
  | Int i -> Some (float_of_int i)
  | Float f -> Some f
  | _ -> None

(** Convert a cell to string for display. *)
let cell_to_string = function
  | Int i -> string_of_int i
  | Float f ->
    (* Clean up trailing zeros: 3.0 instead of 3.000000 *)
    let s = Printf.sprintf "%.6f" f in
    let s = Str.global_replace (Str.regexp "0+$") "" s in
    let s = Str.global_replace (Str.regexp "\\.$") ".0" s in
    s
  | Str s -> s
  | Empty -> ""

(* ---------- RFC 4180 CSV parser ---------- *)

(** Parse a single CSV line, handling quoted fields with escaped quotes.
    Delimiter defaults to comma. Handles: "field", "fie""ld", bare field. *)
let parse_line ?(delim = ',') (line : string) : string list =
  let len = String.length line in
  let buf = Buffer.create 64 in
  let fields = ref [] in
  let i = ref 0 in

  let flush () =
    fields := Buffer.contents buf :: !fields;
    Buffer.clear buf
  in

  while !i < len do
    let c = line.[!i] in
    if c = '"' then begin
      (* Quoted field: read until closing quote *)
      incr i;
      let in_quotes = ref true in
      while !i < len && !in_quotes do
        if line.[!i] = '"' then begin
          if !i + 1 < len && line.[!i + 1] = '"' then begin
            (* Escaped quote "" → literal " *)
            Buffer.add_char buf '"';
            i := !i + 2
          end else begin
            (* End of quoted field *)
            in_quotes := false;
            incr i
          end
        end else begin
          Buffer.add_char buf line.[!i];
          incr i
        end
      done;
      (* Skip to next delimiter or end *)
      while !i < len && line.[!i] <> delim do incr i done;
      flush ();
      if !i < len then incr i (* skip delimiter *)
    end else if c = delim then begin
      flush ();
      incr i
    end else begin
      Buffer.add_char buf c;
      incr i
    end
  done;
  flush ();
  List.rev !fields

(** Parse multi-line CSV text into header + rows of typed cells. *)
let parse ?(delim = ',') ?(has_header = true) (text : string) :
    string list * cell list list =
  let lines =
    String.split_on_char '\n' text
    |> List.map String.trim
    |> List.filter (fun s -> s <> "")
  in
  match lines with
  | [] -> ([], [])
  | first :: rest ->
    if has_header then
      let headers = parse_line ~delim first in
      let rows = List.map (fun l ->
        parse_line ~delim l |> List.map infer_cell
      ) rest in
      (headers, rows)
    else
      let ncols = List.length (parse_line ~delim first) in
      let headers = List.init ncols (fun i -> Printf.sprintf "col%d" (i + 1)) in
      let rows = List.map (fun l ->
        parse_line ~delim l |> List.map infer_cell
      ) lines in
      (headers, rows)

(* ---------- Column access ---------- *)

(** Find column index by name (case-insensitive). *)
let col_index (headers : string list) (name : string) : int option =
  let lname = String.lowercase_ascii name in
  let rec find i = function
    | [] -> None
    | h :: _ when String.lowercase_ascii h = lname -> Some i
    | _ :: rest -> find (i + 1) rest
  in
  find 0 headers

(** Get all values in a column by index.
    Converts each row to an array for O(1) access instead of
    O(col_index) per row via List.nth. *)
let col_values (rows : cell list list) (idx : int) : cell list =
  List.filter_map (fun row ->
    let arr = Array.of_list row in
    if idx < Array.length arr then Some arr.(idx) else None
  ) rows

(* ---------- Aggregation ---------- *)

(** Aggregation functions operating on a column of cells. *)

let agg_count (cells : cell list) : int =
  List.length (List.filter (fun c -> c <> Empty) cells)

let agg_sum (cells : cell list) : float =
  List.fold_left (fun acc c ->
    match cell_to_float c with Some f -> acc +. f | None -> acc
  ) 0.0 cells

let agg_avg (cells : cell list) : float option =
  let nums = List.filter_map cell_to_float cells in
  match nums with
  | [] -> None
  | _ ->
    let total = List.fold_left ( +. ) 0.0 nums in
    Some (total /. float_of_int (List.length nums))

(** Shared helper for agg_min/agg_max — extracts numeric cells and folds
    with the given comparator to find the extreme value. *)
let agg_extreme (cmp : float -> float -> bool) (cells : cell list) : cell option =
  let nums = List.filter_map (fun c ->
    match cell_to_float c with Some f -> Some (f, c) | None -> None
  ) cells in
  match nums with
  | [] -> None
  | _ ->
    let (_, mc) = List.fold_left (fun (mv, mc) (v, c) ->
      if cmp v mv then (v, c) else (mv, mc)
    ) (List.hd nums) (List.tl nums) in
    Some mc

let agg_min (cells : cell list) : cell option = agg_extreme ( < ) cells
let agg_max (cells : cell list) : cell option = agg_extreme ( > ) cells

(* ---------- Group-by ---------- *)

(** Group rows by the value of a specific column.
    Returns (group_key, rows) pairs sorted by key. *)
let group_by (rows : cell list list) (col_idx : int) :
    (string * cell list list) list =
  let tbl = Hashtbl.create 16 in
  List.iter (fun row ->
    let key =
      if col_idx < List.length row then cell_to_string (List.nth row col_idx)
      else "<missing>"
    in
    let existing = try Hashtbl.find tbl key with Not_found -> [] in
    Hashtbl.replace tbl key (row :: existing)
  ) rows;
  Hashtbl.fold (fun k v acc -> (k, List.rev v) :: acc) tbl []
  |> List.sort (fun (a, _) (b, _) -> String.compare a b)

(* ---------- Filtering ---------- *)

(** Filter rows where a column matches a predicate. *)
let filter_rows (rows : cell list list) (col_idx : int)
    (pred : cell -> bool) : cell list list =
  List.filter (fun row ->
    col_idx < List.length row && pred (List.nth row col_idx)
  ) rows

(** Filter: numeric column > threshold. *)
let where_gt (rows : cell list list) (col_idx : int) (threshold : float) =
  filter_rows rows col_idx (fun c ->
    match cell_to_float c with Some v -> v > threshold | None -> false)


(** Filter: string column contains substring (case-insensitive). *)
let where_contains (rows : cell list list) (col_idx : int) (sub : string) =
  let lsub = String.lowercase_ascii sub in
  filter_rows rows col_idx (fun c ->
    let s = String.lowercase_ascii (cell_to_string c) in
    try
      let _ = Str.search_forward (Str.regexp_string lsub) s 0 in true
    with Not_found -> false)

(* ---------- Sorting ---------- *)

(** Sort rows by a column (ascending). Numeric comparison for numbers,
    lexicographic for strings. *)
let sort_by (rows : cell list list) (col_idx : int)
    ?(desc = false) () : cell list list =
  let get_key row =
    if col_idx < List.length row then List.nth row col_idx else Empty
  in
  let cmp a b =
    let ka = get_key a and kb = get_key b in
    let result = match cell_to_float ka, cell_to_float kb with
      | Some fa, Some fb -> compare fa fb
      | _ -> String.compare (cell_to_string ka) (cell_to_string kb)
    in
    if desc then -result else result
  in
  List.sort cmp rows

(* ---------- Pretty-printing ---------- *)

(** Pretty-print a table with aligned columns and borders. *)
let pretty_print (headers : string list) (rows : cell list list) : string =
  let ncols = List.length headers in
  let header_arr = Array.of_list headers in
  (* Convert all cells to string arrays for O(1) column access
     instead of O(col) per List.nth call in the inner loops. *)
  let str_rows = List.map (fun row ->
    let arr = Array.of_list row in
    Array.init ncols (fun i ->
      if i < Array.length arr then cell_to_string arr.(i) else ""
    )
  ) rows in
  (* Calculate column widths *)
  let widths = Array.init ncols (fun i ->
    let header_w = String.length header_arr.(i) in
    let data_w = List.fold_left (fun mx row ->
      max mx (String.length row.(i))
    ) 0 str_rows in
    max header_w data_w
  ) in
  let buf = Buffer.create 512 in
  (* Separator line *)
  let sep () =
    Buffer.add_char buf '+';
    Array.iter (fun w ->
      Buffer.add_string buf (String.make (w + 2) '-');
      Buffer.add_char buf '+'
    ) widths;
    Buffer.add_char buf '\n'
  in
  (* Row — uses array indexing for O(1) width lookup *)
  let print_row (cells : string array) =
    Buffer.add_char buf '|';
    Array.iteri (fun i cell ->
      let w = widths.(i) in
      Buffer.add_char buf ' ';
      (* Right-align numbers, left-align strings *)
      let is_num = match cell_to_float (infer_cell cell) with
        | Some _ -> true | None -> cell = ""
      in
      if is_num then begin
        Buffer.add_string buf (String.make (w - String.length cell) ' ');
        Buffer.add_string buf cell
      end else begin
        Buffer.add_string buf cell;
        Buffer.add_string buf (String.make (w - String.length cell) ' ')
      end;
      Buffer.add_string buf " |"
    ) cells;
    Buffer.add_char buf '\n'
  in
  sep ();
  print_row header_arr;
  sep ();
  List.iter print_row str_rows;
  sep ();
  Buffer.contents buf

(* ---------- Summary statistics ---------- *)

(** Generate a summary report for all numeric columns. *)
let summary (headers : string list) (rows : cell list list) : string =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "=== Data Summary ===\n";
  Buffer.add_string buf (Printf.sprintf "Rows: %d | Columns: %d\n\n"
    (List.length rows) (List.length headers));
  List.iteri (fun i h ->
    let vals = col_values rows i in
    let count = agg_count vals in
    Buffer.add_string buf (Printf.sprintf "Column: %s\n" h);
    Buffer.add_string buf (Printf.sprintf "  Non-empty: %d\n" count);
    (match agg_avg vals with
     | Some avg ->
       Buffer.add_string buf (Printf.sprintf "  Sum: %.2f\n" (agg_sum vals));
       Buffer.add_string buf (Printf.sprintf "  Avg: %.2f\n" avg);
       (match agg_min vals with
        | Some m -> Buffer.add_string buf (Printf.sprintf "  Min: %s\n" (cell_to_string m))
        | None -> ());
       (match agg_max vals with
        | Some m -> Buffer.add_string buf (Printf.sprintf "  Max: %s\n" (cell_to_string m))
        | None -> ())
     | None ->
       Buffer.add_string buf "  (non-numeric)\n");
    Buffer.add_char buf '\n'
  ) headers;
  Buffer.contents buf

(* ========== Demo / Tests ========== *)

let () =
  print_endline "=== OCaml CSV Parser & Data Analyzer ===\n";

  (* --- Test 1: Basic parsing --- *)
  print_endline "--- Test 1: Parse & display ---";
  let csv_data =
    "Name,Department,Salary,Years\n\
     Alice,Engineering,95000,5\n\
     Bob,Marketing,72000,3\n\
     Charlie,Engineering,105000,8\n\
     Diana,Marketing,68000,2\n\
     Eve,Engineering,88000,4\n\
     Frank,Sales,71000,6\n\
     Grace,Sales,79000,7\n\
     Hank,Marketing,82000,5"
  in
  let (headers, rows) = parse csv_data in
  print_string (pretty_print headers rows);
  print_newline ();
  assert (List.length headers = 4);
  assert (List.length rows = 8);

  (* --- Test 2: Type inference --- *)
  print_endline "--- Test 2: Type inference ---";
  assert (infer_cell "42" = Int 42);
  assert (infer_cell "3.14" = Float 3.14);
  assert (infer_cell "hello" = Str "hello");
  assert (infer_cell "" = Empty);
  assert (infer_cell "  99  " = Int 99);
  print_endline "  int/float/string/empty inference: OK";

  (* --- Test 3: Aggregation --- *)
  print_endline "\n--- Test 3: Aggregation on Salary column ---";
  let sal_idx = match col_index headers "Salary" with
    | Some i -> i | None -> failwith "no Salary column" in
  let sal_vals = col_values rows sal_idx in
  Printf.printf "  Count: %d\n" (agg_count sal_vals);
  Printf.printf "  Sum:   %.0f\n" (agg_sum sal_vals);
  (match agg_avg sal_vals with
   | Some a -> Printf.printf "  Avg:   %.2f\n" a | None -> ());
  (match agg_min sal_vals with
   | Some m -> Printf.printf "  Min:   %s\n" (cell_to_string m) | None -> ());
  (match agg_max sal_vals with
   | Some m -> Printf.printf "  Max:   %s\n" (cell_to_string m) | None -> ());
  assert (agg_count sal_vals = 8);
  assert (agg_sum sal_vals = 660000.0);

  (* --- Test 4: Group-by --- *)
  print_endline "\n--- Test 4: Group by Department ---";
  let dept_idx = match col_index headers "Department" with
    | Some i -> i | None -> failwith "no Dept column" in
  let groups = group_by rows dept_idx in
  List.iter (fun (key, group_rows) ->
    let sal_vals = col_values group_rows sal_idx in
    Printf.printf "  %s: %d employees, avg salary %.0f\n"
      key (List.length group_rows)
      (match agg_avg sal_vals with Some a -> a | None -> 0.0)
  ) groups;
  assert (List.length groups = 3);

  (* --- Test 5: Filtering --- *)
  print_endline "\n--- Test 5: Filter salary > 80000 ---";
  let high_earners = where_gt rows sal_idx 80000.0 in
  print_string (pretty_print headers high_earners);
  assert (List.length high_earners = 4);

  print_endline "--- Test 5b: Filter department contains 'eng' ---";
  let eng = where_contains rows dept_idx "eng" in
  print_string (pretty_print headers eng);
  assert (List.length eng = 3);

  (* --- Test 6: Sorting --- *)
  print_endline "--- Test 6: Sort by salary descending ---";
  let sorted = sort_by rows sal_idx ~desc:true () in
  print_string (pretty_print headers sorted);
  (* Charlie should be first (105000) *)
  let first_name = cell_to_string (List.hd (List.hd sorted)) in
  assert (first_name = "Charlie");

  (* --- Test 7: Quoted fields --- *)
  print_endline "--- Test 7: Quoted fields (RFC 4180) ---";
  let quoted_csv =
    "Title,Note\n\
     \"Hello, World\",simple\n\
     normal,\"She said \"\"hi\"\"\"\n\
     \"a\"\"b\",\"c,d\""
  in
  let (qh, qr) = parse quoted_csv in
  print_string (pretty_print qh qr);
  assert (List.length qr = 3);
  (* First row, first column should be "Hello, World" (with comma) *)
  let first_cell = cell_to_string (List.hd (List.hd qr)) in
  assert (first_cell = "Hello, World");
  (* Second row, second column should contain literal quote *)
  let quote_cell = cell_to_string (List.nth (List.nth qr 1) 1) in
  assert (String.contains quote_cell '"');

  (* --- Test 8: Summary --- *)
  print_endline "--- Test 8: Summary statistics ---";
  print_string (summary headers rows);

  (* --- Test 9: No-header mode --- *)
  print_endline "--- Test 9: No-header mode ---";
  let (nh, nr) = parse ~has_header:false "1,2,3\n4,5,6" in
  assert (nh = ["col1"; "col2"; "col3"]);
  assert (List.length nr = 2);
  print_string (pretty_print nh nr);

  (* --- Test 10: Pipeline example --- *)
  print_endline "--- Test 10: Pipeline (filter → sort → display) ---";
  let result =
    rows
    |> fun r -> where_gt r sal_idx 70000.0      (* salary > 70k *)
    |> fun r -> sort_by r sal_idx ~desc:true ()  (* sort desc *)
  in
  print_string (pretty_print headers result);
  assert (List.length result >= 5);

  (* --- Test 11: Custom delimiter --- *)
  print_endline "--- Test 11: Tab-delimited ---";
  let tsv = "A\tB\tC\n1\t2\t3\n4\t5\t6" in
  let (th, tr) = parse ~delim:'\t' tsv in
  print_string (pretty_print th tr);
  assert (List.nth th 1 = "B");

  (* --- Test 12: Edge cases --- *)
  print_endline "--- Test 12: Edge cases ---";
  let (_, empty_rows) = parse "A,B\n" in
  assert (List.length empty_rows = 0);
  let single = parse_line "hello" in
  assert (single = ["hello"]);
  let trailing = parse_line "a,b," in
  assert (List.length trailing = 3);
  print_endline "  Empty input, single field, trailing delimiter: OK";

  print_endline "\n✅ All 12 tests passed!";
  print_endline "CSV parser with type inference, aggregation, group-by, filtering, sorting."
