(* relational.ml — Mini Relational Algebra Engine
   Demonstrates: algebraic data types, pattern matching, higher-order
   functions, modules, immutable data, set operations, and query
   composition.

   Features:
   - Schema-validated tables with typed columns
   - Relational algebra operators: select, project, rename, union,
     intersect, difference, cross product, natural join, theta join
   - Aggregate functions: count, sum, avg, min, max, group-by
   - Query composition via a pipeline DSL
   - Pretty-printed table output
   - Functional indexes for fast lookup

   Compile: ocamlfind ocamlopt relational.ml -o relational
   Run:     ./relational
*)

(* ── Column Types ─────────────────────────────────────────────────── *)

type col_type = TInt | TFloat | TString | TBool

type value =
  | VInt    of int
  | VFloat  of float
  | VString of string
  | VBool   of bool
  | VNull

let type_of_value = function
  | VInt _    -> Some TInt
  | VFloat _  -> Some TFloat
  | VString _ -> Some TString
  | VBool _   -> Some TBool
  | VNull     -> None

let value_to_string = function
  | VInt n    -> string_of_int n
  | VFloat f  -> Printf.sprintf "%.2f" f
  | VString s -> s
  | VBool b   -> if b then "true" else "false"
  | VNull     -> "NULL"

let compare_values a b =
  match a, b with
  | VNull, VNull -> 0
  | VNull, _     -> -1
  | _, VNull     -> 1
  | VInt x,    VInt y    -> compare x y
  | VFloat x,  VFloat y  -> compare x y
  | VString x, VString y -> String.compare x y
  | VBool x,   VBool y   -> compare x y
  | VInt x,    VFloat y  -> compare (float_of_int x) y
  | VFloat x,  VInt y    -> compare x (float_of_int y)
  | _ -> failwith "incompatible types for comparison"

(* ── Schema & Table ───────────────────────────────────────────────── *)

type column_def = {
  col_name : string;
  col_type : col_type;
}

type row = value array

type table = {
  schema  : column_def array;
  rows    : row list;
}

let col_index schema name =
  let rec find i =
    if i >= Array.length schema then
      failwith ("column not found: " ^ name)
    else if schema.(i).col_name = name then i
    else find (i + 1)
  in
  find 0

let col_index_opt schema name =
  let rec find i =
    if i >= Array.length schema then None
    else if schema.(i).col_name = name then Some i
    else find (i + 1)
  in
  find 0

let make_table cols rows =
  let schema = Array.of_list (List.map (fun (n, t) -> { col_name = n; col_type = t }) cols) in
  let n_cols = Array.length schema in
  let validated_rows = List.map (fun vals ->
    let arr = Array.of_list vals in
    if Array.length arr <> n_cols then
      failwith (Printf.sprintf "row has %d values but schema has %d columns"
                  (Array.length arr) n_cols);
    arr
  ) rows in
  { schema; rows = validated_rows }

let empty_table cols =
  make_table cols []

(* ── Pretty Printing ──────────────────────────────────────────────── *)

let to_string_table t =
  let n = Array.length t.schema in
  (* Compute column widths *)
  let widths = Array.init n (fun i ->
    let header_w = String.length t.schema.(i).col_name in
    List.fold_left (fun acc row ->
      max acc (String.length (value_to_string row.(i)))
    ) header_w t.rows
  ) in
  let buf = Buffer.create 256 in
  (* Separator line *)
  let sep () =
    Buffer.add_char buf '+';
    Array.iter (fun w ->
      Buffer.add_string buf (String.make (w + 2) '-');
      Buffer.add_char buf '+'
    ) widths;
    Buffer.add_char buf '\n'
  in
  (* Row *)
  let print_row vals =
    Buffer.add_char buf '|';
    Array.iteri (fun i v ->
      let s = match v with
        | `Header h -> h
        | `Value v  -> value_to_string v
      in
      let pad = widths.(i) - String.length s in
      Buffer.add_char buf ' ';
      Buffer.add_string buf s;
      Buffer.add_string buf (String.make (pad + 1) ' ');
      Buffer.add_char buf '|'
    ) vals;
    Buffer.add_char buf '\n'
  in
  sep ();
  print_row (Array.init n (fun i -> `Header t.schema.(i).col_name));
  sep ();
  List.iter (fun row ->
    print_row (Array.init n (fun i -> `Value row.(i)))
  ) t.rows;
  sep ();
  Buffer.add_string buf (Printf.sprintf "(%d row%s)\n"
    (List.length t.rows) (if List.length t.rows = 1 then "" else "s"));
  Buffer.contents buf

(* ── Relational Algebra Operators ─────────────────────────────────── *)

(** σ (select / where): keep rows matching predicate *)
let select pred t =
  { t with rows = List.filter pred t.rows }

(** π (project): keep only named columns *)
let project col_names t =
  let indices = List.map (col_index t.schema) col_names in
  let schema = Array.of_list (List.map (fun i -> t.schema.(i)) indices) in
  let rows = List.map (fun row ->
    Array.of_list (List.map (fun i -> row.(i)) indices)
  ) t.rows in
  (* Remove duplicate rows *)
  let seen = Hashtbl.create 16 in
  let unique = List.filter (fun row ->
    let key = Array.to_list row |> List.map value_to_string |> String.concat "|" in
    if Hashtbl.mem seen key then false
    else (Hashtbl.add seen key (); true)
  ) rows in
  { schema; rows = unique }

(** ρ (rename): rename a column *)
let rename old_name new_name t =
  let schema = Array.map (fun c ->
    if c.col_name = old_name then { c with col_name = new_name }
    else c
  ) t.schema in
  { t with schema }

(** ∪ (union): combine rows from two union-compatible tables *)
let union t1 t2 =
  if Array.length t1.schema <> Array.length t2.schema then
    failwith "union: schemas must have the same number of columns";
  let seen = Hashtbl.create 32 in
  let add_unique rows =
    List.filter (fun row ->
      let key = Array.to_list row |> List.map value_to_string |> String.concat "|" in
      if Hashtbl.mem seen key then false
      else (Hashtbl.add seen key (); true)
    ) rows
  in
  let rows = add_unique t1.rows @ add_unique t2.rows in
  { schema = t1.schema; rows }

(** ∩ (intersect): rows present in both tables *)
let intersect t1 t2 =
  let keys2 = Hashtbl.create 16 in
  List.iter (fun row ->
    let key = Array.to_list row |> List.map value_to_string |> String.concat "|" in
    Hashtbl.replace keys2 key ()
  ) t2.rows;
  let rows = List.filter (fun row ->
    let key = Array.to_list row |> List.map value_to_string |> String.concat "|" in
    Hashtbl.mem keys2 key
  ) t1.rows in
  { schema = t1.schema; rows }

(** − (difference): rows in t1 but not t2 *)
let difference t1 t2 =
  let keys2 = Hashtbl.create 16 in
  List.iter (fun row ->
    let key = Array.to_list row |> List.map value_to_string |> String.concat "|" in
    Hashtbl.replace keys2 key ()
  ) t2.rows;
  let rows = List.filter (fun row ->
    let key = Array.to_list row |> List.map value_to_string |> String.concat "|" in
    not (Hashtbl.mem keys2 key)
  ) t1.rows in
  { schema = t1.schema; rows }

(** × (cross product / cartesian product) *)
let cross t1 t2 =
  let schema = Array.append t1.schema t2.schema in
  let rows = List.concat_map (fun r1 ->
    List.map (fun r2 -> Array.append r1 r2) t2.rows
  ) t1.rows in
  { schema; rows }

(** ⋈ (natural join): join on all common column names *)
let natural_join t1 t2 =
  (* Find common columns *)
  let common = Array.to_list t1.schema |> List.filter_map (fun c1 ->
    match col_index_opt t2.schema c1.col_name with
    | Some i2 -> Some (col_index t1.schema c1.col_name, i2, c1.col_name)
    | None    -> None
  ) in
  if common = [] then cross t1 t2
  else begin
    (* Schema: all of t1 + non-common columns of t2 *)
    let t2_extra = Array.to_list t2.schema |> List.filter (fun c ->
      not (List.exists (fun (_, _, name) -> name = c.col_name) common)
    ) in
    let t2_extra_indices = List.map (col_index t2.schema) (
      List.map (fun c -> c.col_name) t2_extra
    ) in
    let schema = Array.append t1.schema (Array.of_list t2_extra) in
    (* Build hash index on t2 common columns *)
    let t2_index = Hashtbl.create 32 in
    List.iter (fun r2 ->
      let key = List.map (fun (_, i2, _) -> value_to_string r2.(i2)) common
                |> String.concat "|" in
      let existing = try Hashtbl.find t2_index key with Not_found -> [] in
      Hashtbl.replace t2_index key (r2 :: existing)
    ) t2.rows;
    let rows = List.concat_map (fun r1 ->
      let key = List.map (fun (i1, _, _) -> value_to_string r1.(i1)) common
                |> String.concat "|" in
      let matches = try Hashtbl.find t2_index key with Not_found -> [] in
      List.map (fun r2 ->
        let extra = Array.of_list (List.map (fun i -> r2.(i)) t2_extra_indices) in
        Array.append r1 extra
      ) matches
    ) t1.rows in
    { schema; rows }
  end

(** ⋈_θ (theta join): join on arbitrary predicate *)
let theta_join pred t1 t2 =
  let cp = cross t1 t2 in
  select pred cp

(* ── Sort ─────────────────────────────────────────────────────────── *)

let order_by col_name ?(desc=false) t =
  let i = col_index t.schema col_name in
  let cmp r1 r2 =
    let c = compare_values r1.(i) r2.(i) in
    if desc then -c else c
  in
  { t with rows = List.sort cmp t.rows }

(* ── Aggregate Functions ──────────────────────────────────────────── *)

type aggregate =
  | Count
  | Sum    of string  (* column name *)
  | Avg    of string
  | Min    of string
  | Max    of string
  | CountDistinct of string

let to_float = function
  | VInt n   -> float_of_int n
  | VFloat f -> f
  | _        -> failwith "aggregate: non-numeric value"

let compute_aggregate agg rows schema =
  match agg with
  | Count -> VInt (List.length rows)
  | CountDistinct col ->
    let i = col_index schema col in
    let seen = Hashtbl.create 16 in
    List.iter (fun row ->
      let key = value_to_string row.(i) in
      Hashtbl.replace seen key ()
    ) rows;
    VInt (Hashtbl.length seen)
  | Sum col ->
    let i = col_index schema col in
    let total = List.fold_left (fun acc row ->
      match row.(i) with VNull -> acc | v -> acc +. to_float v
    ) 0.0 rows in
    VFloat total
  | Avg col ->
    let i = col_index schema col in
    let sum, cnt = List.fold_left (fun (s, c) row ->
      match row.(i) with VNull -> (s, c) | v -> (s +. to_float v, c + 1)
    ) (0.0, 0) rows in
    if cnt = 0 then VNull else VFloat (sum /. float_of_int cnt)
  | Min col ->
    let i = col_index schema col in
    let vals = List.filter_map (fun row ->
      match row.(i) with VNull -> None | v -> Some v
    ) rows in
    (match vals with
     | [] -> VNull
     | _  -> List.fold_left (fun acc v ->
               if compare_values v acc < 0 then v else acc) (List.hd vals) vals)
  | Max col ->
    let i = col_index schema col in
    let vals = List.filter_map (fun row ->
      match row.(i) with VNull -> None | v -> Some v
    ) rows in
    (match vals with
     | [] -> VNull
     | _  -> List.fold_left (fun acc v ->
               if compare_values v acc > 0 then v else acc) (List.hd vals) vals)

(** GROUP BY with aggregates *)
let group_by group_cols aggs t =
  let group_indices = List.map (col_index t.schema) group_cols in
  (* Group rows by key *)
  let groups = Hashtbl.create 16 in
  List.iter (fun row ->
    let key = List.map (fun i -> value_to_string row.(i)) group_indices
              |> String.concat "|" in
    let existing = try Hashtbl.find groups key with Not_found -> [] in
    Hashtbl.replace groups key (row :: existing)
  ) t.rows;
  (* Build result schema *)
  let group_schema = List.map (fun i -> t.schema.(i)) group_indices in
  let agg_schema = List.map (fun (agg, alias) ->
    let ct = match agg with
      | Count | CountDistinct _ -> TInt
      | Sum _ | Avg _ -> TFloat
      | Min col | Max col ->
        let i = col_index t.schema col in
        t.schema.(i).col_type
    in
    { col_name = alias; col_type = ct }
  ) aggs in
  let schema = Array.of_list (group_schema @ agg_schema) in
  (* Compute results *)
  let rows = Hashtbl.fold (fun _key group_rows acc ->
    let sample = List.hd group_rows in
    let group_vals = List.map (fun i -> sample.(i)) group_indices in
    let agg_vals = List.map (fun (agg, _) ->
      compute_aggregate agg group_rows t.schema
    ) aggs in
    (Array.of_list (group_vals @ agg_vals)) :: acc
  ) groups [] in
  { schema; rows }

(* ── Functional Index ─────────────────────────────────────────────── *)

type 'a index = {
  idx_col    : string;
  idx_lookup : (string, row list) Hashtbl.t;
}

let create_index col_name t =
  let i = col_index t.schema col_name in
  let tbl = Hashtbl.create (List.length t.rows) in
  List.iter (fun row ->
    let key = value_to_string row.(i) in
    let existing = try Hashtbl.find tbl key with Not_found -> [] in
    Hashtbl.replace tbl key (row :: existing)
  ) t.rows;
  { idx_col = col_name; idx_lookup = tbl }

let index_lookup idx value =
  let key = value_to_string value in
  try Hashtbl.find idx.idx_lookup key with Not_found -> []

(* ── Pipeline DSL ─────────────────────────────────────────────────── *)

(** Query operations for composable pipelines *)
type query_op =
  | Select   of (row -> bool)
  | Project  of string list
  | Rename   of string * string
  | OrderBy  of string * bool  (* col_name, descending *)
  | Limit    of int
  | Distinct

let apply_op t = function
  | Select pred   -> select pred t
  | Project cols  -> project cols t
  | Rename (o, n) -> rename o n t
  | OrderBy (c,d) -> order_by c ~desc:d t
  | Limit n       -> { t with rows = List.filteri (fun i _ -> i < n) t.rows }
  | Distinct      -> project (Array.to_list (Array.map (fun c -> c.col_name) t.schema)) t

let pipeline ops t =
  List.fold_left apply_op t ops

(* ── Helper: where clauses ────────────────────────────────────────── *)

let where_eq col_name value schema row =
  let i = col_index schema col_name in
  compare_values row.(i) value = 0

let where_gt col_name value schema row =
  let i = col_index schema col_name in
  compare_values row.(i) value > 0

let where_lt col_name value schema row =
  let i = col_index schema col_name in
  compare_values row.(i) value < 0

let where_between col_name lo hi schema row =
  let i = col_index schema col_name in
  compare_values row.(i) lo >= 0 && compare_values row.(i) hi <= 0

let where_like col_name pattern schema row =
  let i = col_index schema col_name in
  match row.(i) with
  | VString s ->
    (* Simple LIKE: % at start/end for contains/startswith/endswith *)
    let p = String.lowercase_ascii pattern in
    let s = String.lowercase_ascii s in
    let plen = String.length p in
    if plen >= 2 && p.[0] = '%' && p.[plen-1] = '%' then
      let sub = String.sub p 1 (plen - 2) in
      let rec contains_at i =
        if i + String.length sub > String.length s then false
        else if String.sub s i (String.length sub) = sub then true
        else contains_at (i + 1)
      in
      contains_at 0
    else if plen >= 1 && p.[0] = '%' then
      let sub = String.sub p 1 (plen - 1) in
      let slen = String.length s in
      slen >= String.length sub &&
        String.sub s (slen - String.length sub) (String.length sub) = sub
    else if plen >= 1 && p.[plen-1] = '%' then
      let sub = String.sub p 0 (plen - 1) in
      String.length s >= String.length sub &&
        String.sub s 0 (String.length sub) = sub
    else
      s = p
  | _ -> false

let where_in col_name values schema row =
  let i = col_index schema col_name in
  List.exists (fun v -> compare_values row.(i) v = 0) values

let where_is_null col_name schema row =
  let i = col_index schema col_name in
  row.(i) = VNull

let where_not pred schema row = not (pred schema row)

let where_and p1 p2 schema row = p1 schema row && p2 schema row

let where_or p1 p2 schema row = p1 schema row || p2 schema row

(* ── Tests ────────────────────────────────────────────────────────── *)

let test_count = ref 0
let test_pass = ref 0
let test_fail = ref 0

let assert_eq name expected actual =
  incr test_count;
  if expected = actual then
    incr test_pass
  else begin
    incr test_fail;
    Printf.printf "  FAIL %s: expected %s, got %s\n" name expected actual
  end

let assert_true name cond =
  incr test_count;
  if cond then incr test_pass
  else begin
    incr test_fail;
    Printf.printf "  FAIL %s\n" name
  end

(* ── Demo / Test Suite ────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Mini Relational Algebra Engine ===\n\n";

  (* Create employees table *)
  let employees = make_table
    [("id", TInt); ("name", TString); ("dept", TString);
     ("salary", TFloat); ("active", TBool)]
    [
      [VInt 1; VString "Alice";   VString "Engineering"; VFloat 95000.0;  VBool true];
      [VInt 2; VString "Bob";     VString "Engineering"; VFloat 88000.0;  VBool true];
      [VInt 3; VString "Charlie"; VString "Marketing";   VFloat 72000.0;  VBool true];
      [VInt 4; VString "Diana";   VString "Marketing";   VFloat 78000.0;  VBool false];
      [VInt 5; VString "Eve";     VString "Sales";       VFloat 65000.0;  VBool true];
      [VInt 6; VString "Frank";   VString "Sales";       VFloat 70000.0;  VBool true];
      [VInt 7; VString "Grace";   VString "Engineering"; VFloat 105000.0; VBool true];
    ] in

  (* Create departments table *)
  let departments = make_table
    [("dept", TString); ("floor", TInt); ("budget", TFloat)]
    [
      [VString "Engineering"; VInt 3; VFloat 500000.0];
      [VString "Marketing";   VInt 2; VFloat 200000.0];
      [VString "Sales";       VInt 1; VFloat 150000.0];
      [VString "HR";          VInt 2; VFloat 100000.0];
    ] in

  Printf.printf "── Employees ──\n%s\n" (to_string_table employees);
  Printf.printf "── Departments ──\n%s\n" (to_string_table departments);

  (* Test 1: SELECT — filter active employees *)
  Printf.printf "── Test: σ active = true ──\n";
  let active = select (fun row -> row.(4) = VBool true) employees in
  assert_eq "active count" "6" (string_of_int (List.length active.rows));
  Printf.printf "%s\n" (to_string_table active);

  (* Test 2: PROJECT — names and departments *)
  Printf.printf "── Test: π name, dept ──\n";
  let names_depts = project ["name"; "dept"] employees in
  assert_eq "projected cols" "2" (string_of_int (Array.length names_depts.schema));
  assert_eq "projected col1" "name" names_depts.schema.(0).col_name;
  Printf.printf "%s\n" (to_string_table names_depts);

  (* Test 3: RENAME *)
  let renamed = rename "name" "employee_name" employees in
  assert_eq "renamed col" "employee_name" renamed.schema.(1).col_name;

  (* Test 4: NATURAL JOIN *)
  Printf.printf "── Test: Employees ⋈ Departments ──\n";
  let joined = natural_join employees departments in
  assert_eq "joined cols" "7" (string_of_int (Array.length joined.schema));
  assert_eq "joined rows" "7" (string_of_int (List.length joined.rows));
  Printf.printf "%s\n" (to_string_table joined);

  (* Test 5: SELECT with salary > 80000 *)
  Printf.printf "── Test: σ salary > 80000 ──\n";
  let high_earners = select (where_gt "salary" (VFloat 80000.0) employees.schema)
                       employees in
  assert_eq "high earners" "3" (string_of_int (List.length high_earners.rows));
  Printf.printf "%s\n" (to_string_table high_earners);

  (* Test 6: GROUP BY with aggregates *)
  Printf.printf "── Test: GROUP BY dept with AVG(salary), COUNT ──\n";
  let by_dept = group_by ["dept"]
    [(Avg "salary", "avg_salary"); (Count, "count");
     (Max "salary", "max_salary")]
    employees in
  assert_eq "groups" "3" (string_of_int (List.length by_dept.rows));
  Printf.printf "%s\n" (to_string_table by_dept);

  (* Test 7: ORDER BY *)
  Printf.printf "── Test: ORDER BY salary DESC ──\n";
  let sorted = order_by "salary" ~desc:true employees in
  let top = List.hd sorted.rows in
  assert_eq "highest salary" "Grace" (value_to_string top.(1));
  Printf.printf "%s\n" (to_string_table sorted);

  (* Test 8: UNION *)
  let eng = select (where_eq "dept" (VString "Engineering") employees.schema) employees in
  let sales = select (where_eq "dept" (VString "Sales") employees.schema) employees in
  let combined = union eng sales in
  assert_eq "union count" "5" (string_of_int (List.length combined.rows));

  (* Test 9: INTERSECT *)
  let high_and_active = intersect
    (select (where_gt "salary" (VFloat 80000.0) employees.schema) employees)
    (select (fun row -> row.(4) = VBool true) employees) in
  assert_eq "intersect count" "3" (string_of_int (List.length high_and_active.rows));

  (* Test 10: DIFFERENCE *)
  let all_minus_sales = difference employees sales in
  assert_eq "difference count" "5" (string_of_int (List.length all_minus_sales.rows));

  (* Test 11: CROSS PRODUCT *)
  let tiny1 = make_table [("a", TInt)] [[VInt 1]; [VInt 2]] in
  let tiny2 = make_table [("b", TString)] [[VString "x"]; [VString "y"]] in
  let cp = cross tiny1 tiny2 in
  assert_eq "cross product rows" "4" (string_of_int (List.length cp.rows));
  assert_eq "cross product cols" "2" (string_of_int (Array.length cp.schema));

  (* Test 12: THETA JOIN *)
  let theta = theta_join (fun row ->
    (* employees.salary > departments.budget * 0.4 *)
    to_float row.(3) > to_float row.(7) *. 0.4
  ) employees departments in
  assert_true "theta join non-empty" (List.length theta.rows > 0);

  (* Test 13: Pipeline DSL *)
  Printf.printf "── Test: Pipeline — active engineers earning > 90k ──\n";
  let result = pipeline [
    Select (where_eq "dept" (VString "Engineering") employees.schema);
    Select (where_gt "salary" (VFloat 90000.0) employees.schema);
    Select (fun row -> row.(4) = VBool true);
    Project ["name"; "salary"];
    OrderBy ("salary", true);
  ] employees in
  assert_eq "pipeline count" "2" (string_of_int (List.length result.rows));
  Printf.printf "%s\n" (to_string_table result);

  (* Test 14: WHERE LIKE *)
  let a_names = select (where_like "name" "a%" employees.schema) employees in
  assert_eq "LIKE a% count" "1" (string_of_int (List.length a_names.rows));

  let contains_a = select (where_like "name" "%a%" employees.schema) employees in
  assert_true "LIKE %a% non-empty" (List.length contains_a.rows >= 3);

  (* Test 15: WHERE IN *)
  let in_eng_sales = select
    (where_in "dept" [VString "Engineering"; VString "Sales"] employees.schema)
    employees in
  assert_eq "IN count" "5" (string_of_int (List.length in_eng_sales.rows));

  (* Test 16: WHERE IS NULL *)
  let with_null = make_table [("x", TInt); ("y", TString)]
    [[VInt 1; VString "a"]; [VInt 2; VNull]; [VNull; VString "c"]] in
  let nulls = select (where_is_null "y" with_null.schema) with_null in
  assert_eq "IS NULL count" "1" (string_of_int (List.length nulls.rows));

  (* Test 17: WHERE NOT *)
  let not_eng = select
    (where_not (where_eq "dept" (VString "Engineering")) employees.schema)
    employees in
  assert_eq "NOT Engineering" "4" (string_of_int (List.length not_eng.rows));

  (* Test 18: WHERE AND / OR *)
  let and_pred = where_and
    (where_gt "salary" (VFloat 70000.0))
    (where_eq "active" (VBool true)) in
  let and_result = select (and_pred employees.schema) employees in
  assert_eq "AND count" "4" (string_of_int (List.length and_result.rows));

  let or_pred = where_or
    (where_eq "dept" (VString "Sales"))
    (where_gt "salary" (VFloat 100000.0)) in
  let or_result = select (or_pred employees.schema) employees in
  assert_eq "OR count" "3" (string_of_int (List.length or_result.rows));

  (* Test 19: WHERE BETWEEN *)
  let between_result = select
    (where_between "salary" (VFloat 70000.0) (VFloat 90000.0) employees.schema)
    employees in
  assert_eq "BETWEEN count" "4" (string_of_int (List.length between_result.rows));

  (* Test 20: Functional index *)
  let name_idx = create_index "name" employees in
  let alice_rows = index_lookup name_idx (VString "Alice") in
  assert_eq "index lookup" "1" (string_of_int (List.length alice_rows));
  let nobody = index_lookup name_idx (VString "Nobody") in
  assert_eq "index miss" "0" (string_of_int (List.length nobody));

  (* Test 21: COUNT DISTINCT *)
  let dept_count = group_by []
    [(CountDistinct "dept", "distinct_depts"); (Count, "total")]
    employees in
  let row0 = List.hd dept_count.rows in
  assert_eq "distinct depts" "3" (value_to_string row0.(0));
  assert_eq "total employees" "7" (value_to_string row0.(1));

  (* Test 22: SUM aggregate *)
  let total_salary = group_by []
    [(Sum "salary", "total_salary")] employees in
  let s = List.hd total_salary.rows in
  assert_eq "total salary" "573000.00" (value_to_string s.(0));

  (* Test 23: MIN aggregate *)
  let min_salary = group_by []
    [(Min "salary", "min_salary")] employees in
  assert_eq "min salary" "65000.00" (value_to_string (List.hd min_salary.rows).(0));

  (* Test 24: Empty table operations *)
  let empty = empty_table [("a", TInt); ("b", TString)] in
  assert_eq "empty rows" "0" (string_of_int (List.length empty.rows));
  let empty_select = select (fun _ -> true) empty in
  assert_eq "empty select" "0" (string_of_int (List.length empty_select.rows));
  let empty_group = group_by [] [(Count, "n")] empty in
  assert_eq "empty group count" "0" (value_to_string (List.hd empty_group.rows).(0));

  (* Test 25: LIMIT *)
  let limited = pipeline [
    OrderBy ("salary", true);
    Limit 3;
  ] employees in
  assert_eq "limit 3" "3" (string_of_int (List.length limited.rows));

  (* Test 26: DISTINCT on full table *)
  let with_dupes = make_table [("x", TInt)]
    [[VInt 1]; [VInt 2]; [VInt 1]; [VInt 3]; [VInt 2]] in
  let deduped = pipeline [Distinct] with_dupes in
  assert_eq "distinct" "3" (string_of_int (List.length deduped.rows));

  (* Test 27: Schema validation *)
  let bad_row = try
    ignore (make_table [("a", TInt)] [[VInt 1; VInt 2]]);
    false
  with Failure _ -> true in
  assert_true "schema validation" bad_row;

  (* Test 28: Column not found *)
  let bad_col = try
    ignore (col_index employees.schema "nonexistent");
    false
  with Failure _ -> true in
  assert_true "column not found" bad_col;

  (* Test 29: Value comparison edge cases *)
  assert_true "null < int" (compare_values VNull (VInt 1) < 0);
  assert_true "int > null" (compare_values (VInt 1) VNull > 0);
  assert_true "null = null" (compare_values VNull VNull = 0);
  assert_true "int-float cross compare" (compare_values (VInt 5) (VFloat 5.0) = 0);

  (* Test 30: type_of_value *)
  assert_true "type int" (type_of_value (VInt 1) = Some TInt);
  assert_true "type null" (type_of_value VNull = None);

  (* Test 31: Complex query — top 2 departments by average salary *)
  Printf.printf "── Test: Top departments by avg salary ──\n";
  let top_depts = employees
    |> group_by ["dept"] [(Avg "salary", "avg_sal"); (Count, "headcount")]
    |> order_by "avg_sal" ~desc:true
    |> pipeline [Limit 2] in
  assert_eq "top 2 depts" "2" (string_of_int (List.length top_depts.rows));
  Printf.printf "%s\n" (to_string_table top_depts);

  (* Test 32: Join then aggregate *)
  Printf.printf "── Test: Join + Aggregate — salary as %% of budget ──\n";
  let dept_analysis = natural_join employees departments
    |> group_by ["dept"]
       [(Sum "salary", "total_salary"); (Max "budget", "budget");
        (Count, "headcount")] in
  assert_eq "dept analysis groups" "3"
    (string_of_int (List.length dept_analysis.rows));
  Printf.printf "%s\n" (to_string_table dept_analysis);

  (* Test 33: Self-join — find employee pairs in same department *)
  let e1 = rename "id" "id1" (rename "name" "name1" (
    project ["id"; "name"; "dept"] employees)) in
  let e2 = rename "id" "id2" (rename "name" "name2" (
    project ["id"; "name"; "dept"] employees)) in
  let pairs = natural_join e1 e2
    |> select (fun row ->
         compare_values row.(0) row.(2) < 0  (* id1 < id2 *)
       ) in
  assert_true "self-join pairs" (List.length pairs.rows > 0);

  (* Test 34: Chained renames *)
  let double_renamed = employees
    |> rename "name" "emp_name"
    |> rename "dept" "department" in
  assert_eq "rename chain" "emp_name" double_renamed.schema.(1).col_name;
  assert_eq "rename chain 2" "department" double_renamed.schema.(2).col_name;

  (* Test 35: Index on non-unique column *)
  let dept_idx = create_index "dept" employees in
  let eng_rows = index_lookup dept_idx (VString "Engineering") in
  assert_eq "dept index" "3" (string_of_int (List.length eng_rows));

  (* Summary *)
  Printf.printf "\n=== Results: %d passed, %d failed out of %d tests ===\n"
    !test_pass !test_fail !test_count
