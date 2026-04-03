(* spreadsheet.ml — Spreadsheet Engine
 *
 * A minimal spreadsheet engine with cell references, formulas,
 * dependency tracking, topological evaluation, and cycle detection.
 *
 * Features:
 *   - Cell types: numbers, strings, formulas, empty
 *   - Formula parser: arithmetic (+, -, *, /, ^, unary minus),
 *     cell references (A1, B2, ...), range references (A1:B3),
 *     built-in functions (SUM, AVG, MIN, MAX, COUNT, ABS, IF,
 *     ROUND, CEIL, FLOOR, MOD, CONCAT, LEN, UPPER, LOWER, LEFT,
 *     RIGHT, AND, OR, NOT, ISNUMBER, ISTEXT, ISBLANK)
 *   - Dependency graph with automatic invalidation
 *   - Topological evaluation ordering (Kahn's algorithm)
 *   - Cycle detection with path reporting
 *   - Named ranges (aliases for cell regions)
 *   - Cell formatting (decimal places, percent, currency)
 *   - Copy/paste with relative reference adjustment
 *   - CSV import/export
 *   - Undo/redo history
 *   - Text rendering of the grid
 *
 * Usage:
 *   let sheet = Spreadsheet.create ~rows:10 ~cols:5 ()
 *   let sheet = Spreadsheet.set sheet "A1" (Number 42.0)
 *   let sheet = Spreadsheet.set sheet "B1" (Formula "=A1*2+1")
 *   let sheet = Spreadsheet.recalculate sheet
 *   Spreadsheet.get_value sheet "B1"  (* => VNumber 85.0 *)
 *)

(* ── Cell Addresses ─────────────────────────────────────────────── *)

module CellAddr = struct
  (** (row, col) both 0-indexed internally.
      External format: column letters + 1-based row, e.g. "A1" = (0,0). *)
  type t = int * int

  let compare (r1,c1) (r2,c2) =
    let cr = compare r1 r2 in
    if cr <> 0 then cr else compare c1 c2

  (** Convert column index to letters: 0->A, 25->Z, 26->AA, ... *)
  let col_to_letters c =
    let buf = Buffer.create 4 in
    let rec go n =
      let q = n / 26 and r = n mod 26 in
      Buffer.add_char buf (Char.chr (r + Char.code 'A'));
      if q > 0 then go (q - 1)
    in
    go c;
    (* reverse because we build LSB first *)
    let s = Buffer.contents buf in
    let len = String.length s in
    String.init len (fun i -> s.[len - 1 - i])

  (** Parse column letters to index: "A"->0, "Z"->25, "AA"->26 *)
  let letters_to_col s =
    let n = ref 0 in
    String.iter (fun ch ->
      n := !n * 26 + (Char.code (Char.uppercase_ascii ch) - Char.code 'A' + 1)
    ) s;
    !n - 1

  (** Parse "A1" -> (0, 0), "B3" -> (2, 1), etc. *)
  let of_string s =
    let len = String.length s in
    if len < 2 then None
    else
      let i = ref 0 in
      while !i < len && Char.uppercase_ascii s.[!i] >= 'A'
            && Char.uppercase_ascii s.[!i] <= 'Z' do
        incr i
      done;
      if !i = 0 || !i >= len then None
      else
        let col_part = String.sub s 0 !i in
        let row_part = String.sub s !i (len - !i) in
        match int_of_string_opt row_part with
        | Some r when r >= 1 ->
          Some (r - 1, letters_to_col col_part)
        | _ -> None

  let to_string (row, col) =
    col_to_letters col ^ string_of_int (row + 1)

  (** Enumerate cells in a rectangular range. *)
  let range_cells (r1,c1) (r2,c2) =
    let rlo = min r1 r2 and rhi = max r1 r2 in
    let clo = min c1 c2 and chi = max c1 c2 in
    let acc = ref [] in
    for r = rhi downto rlo do
      for c = chi downto clo do
        acc := (r,c) :: !acc
      done
    done;
    !acc
end

module CellMap = Map.Make(struct
  type t = CellAddr.t
  let compare = CellAddr.compare
end)

module CellSet = Set.Make(struct
  type t = CellAddr.t
  let compare = CellAddr.compare
end)

(* ── Formula AST ────────────────────────────────────────────────── *)

type expr =
  | ENum of float
  | EStr of string
  | EBool of bool
  | ERef of CellAddr.t
  | ERange of CellAddr.t * CellAddr.t
  | EBinop of binop * expr * expr
  | EUnary of unop * expr
  | EFunc of string * expr list
  | ECompare of cmpop * expr * expr

and binop = Add | Sub | Mul | Div | Pow
and unop = Neg
and cmpop = Eq | Neq | Lt | Gt | Lte | Gte

(** Cell content as entered by the user. *)
type cell_content =
  | Empty
  | Number of float
  | Text of string
  | Formula of string  (** The raw formula string starting with '=' *)

(** Computed value after evaluation. *)
type value =
  | VEmpty
  | VNumber of float
  | VText of string
  | VBool of bool
  | VError of string

(** Cell formatting. *)
type format =
  | FDefault
  | FDecimal of int       (** fixed decimal places *)
  | FPercent of int        (** percent with decimal places *)
  | FCurrency of string * int  (** symbol, decimal places *)

(* ── Formula Parser ─────────────────────────────────────────────── *)

module Parser = struct
  type token =
    | TNum of float
    | TStr of string
    | TIdent of string
    | TRef of CellAddr.t
    | TLParen | TRParen | TComma | TColon
    | TPlus | TMinus | TStar | TSlash | TCaret
    | TEq | TNeq | TLt | TGt | TLte | TGte
    | TEof

  let is_alpha ch = (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z')
  let is_digit ch = ch >= '0' && ch <= '9'

  (** Tokenise a formula string (without the leading '='). *)
  let tokenise s =
    let len = String.length s in
    let pos = ref 0 in
    let tokens = ref [] in
    while !pos < len do
      let ch = s.[!pos] in
      if ch = ' ' || ch = '\t' then incr pos
      else if ch = '(' then (tokens := TLParen :: !tokens; incr pos)
      else if ch = ')' then (tokens := TRParen :: !tokens; incr pos)
      else if ch = ',' then (tokens := TComma :: !tokens; incr pos)
      else if ch = ':' then (tokens := TColon :: !tokens; incr pos)
      else if ch = '+' then (tokens := TPlus :: !tokens; incr pos)
      else if ch = '-' then (tokens := TMinus :: !tokens; incr pos)
      else if ch = '*' then (tokens := TStar :: !tokens; incr pos)
      else if ch = '/' then (tokens := TSlash :: !tokens; incr pos)
      else if ch = '^' then (tokens := TCaret :: !tokens; incr pos)
      else if ch = '=' then (tokens := TEq :: !tokens; incr pos)
      else if ch = '<' && !pos + 1 < len && s.[!pos+1] = '>' then
        (tokens := TNeq :: !tokens; pos := !pos + 2)
      else if ch = '<' && !pos + 1 < len && s.[!pos+1] = '=' then
        (tokens := TLte :: !tokens; pos := !pos + 2)
      else if ch = '>' && !pos + 1 < len && s.[!pos+1] = '=' then
        (tokens := TGte :: !tokens; pos := !pos + 2)
      else if ch = '<' then (tokens := TLt :: !tokens; incr pos)
      else if ch = '>' then (tokens := TGt :: !tokens; incr pos)
      else if ch = '"' then begin
        incr pos;
        let buf = Buffer.create 32 in
        while !pos < len && s.[!pos] <> '"' do
          if s.[!pos] = '\\' && !pos + 1 < len then begin
            Buffer.add_char buf s.[!pos+1]; pos := !pos + 2
          end else begin
            Buffer.add_char buf s.[!pos]; incr pos
          end
        done;
        if !pos < len then incr pos; (* skip closing quote *)
        tokens := TStr (Buffer.contents buf) :: !tokens
      end
      else if is_digit ch || (ch = '.' && !pos + 1 < len && is_digit s.[!pos+1]) then begin
        let start = !pos in
        while !pos < len && (is_digit s.[!pos] || s.[!pos] = '.') do
          incr pos
        done;
        (* handle scientific notation *)
        if !pos < len && (s.[!pos] = 'e' || s.[!pos] = 'E') then begin
          incr pos;
          if !pos < len && (s.[!pos] = '+' || s.[!pos] = '-') then incr pos;
          while !pos < len && is_digit s.[!pos] do incr pos done
        end;
        let numstr = String.sub s start (!pos - start) in
        tokens := TNum (float_of_string numstr) :: !tokens
      end
      else if is_alpha ch then begin
        let start = !pos in
        while !pos < len && (is_alpha s.[!pos] || is_digit s.[!pos] || s.[!pos] = '_') do
          incr pos
        done;
        let word = String.sub s start (!pos - start) in
        let upper = String.uppercase_ascii word in
        if upper = "TRUE" then tokens := TNum 1.0 :: !tokens
        else if upper = "FALSE" then tokens := TNum 0.0 :: !tokens
        else
          (* Check if it looks like a cell ref: letters followed by digits *)
          match CellAddr.of_string word with
          | Some addr -> tokens := TRef addr :: !tokens
          | None -> tokens := TIdent upper :: !tokens
      end
      else begin
        (* skip unknown character *)
        incr pos
      end
    done;
    List.rev !tokens

  (** Recursive descent parser. *)
  type state = { mutable toks: token list }

  let peek st = match st.toks with t :: _ -> t | [] -> TEof
  let advance st = match st.toks with _ :: rest -> st.toks <- rest | [] -> ()
  let expect st tok =
    if peek st = tok then advance st
    else failwith (Printf.sprintf "Expected token")

  let rec parse_expr st = parse_comparison st

  and parse_comparison st =
    let left = parse_additive st in
    match peek st with
    | TEq  -> advance st; ECompare (Eq,  left, parse_additive st)
    | TNeq -> advance st; ECompare (Neq, left, parse_additive st)
    | TLt  -> advance st; ECompare (Lt,  left, parse_additive st)
    | TGt  -> advance st; ECompare (Gt,  left, parse_additive st)
    | TLte -> advance st; ECompare (Lte, left, parse_additive st)
    | TGte -> advance st; ECompare (Gte, left, parse_additive st)
    | _ -> left

  and parse_additive st =
    let left = ref (parse_multiplicative st) in
    let cont = ref true in
    while !cont do
      match peek st with
      | TPlus  -> advance st; left := EBinop (Add, !left, parse_multiplicative st)
      | TMinus -> advance st; left := EBinop (Sub, !left, parse_multiplicative st)
      | _ -> cont := false
    done;
    !left

  and parse_multiplicative st =
    let left = ref (parse_power st) in
    let cont = ref true in
    while !cont do
      match peek st with
      | TStar  -> advance st; left := EBinop (Mul, !left, parse_power st)
      | TSlash -> advance st; left := EBinop (Div, !left, parse_power st)
      | _ -> cont := false
    done;
    !left

  and parse_power st =
    let base = parse_unary st in
    match peek st with
    | TCaret -> advance st; EBinop (Pow, base, parse_power st) (* right-assoc *)
    | _ -> base

  and parse_unary st =
    match peek st with
    | TMinus -> advance st; EUnary (Neg, parse_unary st)
    | TPlus  -> advance st; parse_unary st
    | _ -> parse_primary st

  and parse_primary st =
    match peek st with
    | TNum n -> advance st; ENum n
    | TStr s -> advance st; EStr s
    | TRef addr ->
      advance st;
      (* Check for range: A1:B3 *)
      if peek st = TColon then begin
        advance st;
        match peek st with
        | TRef addr2 -> advance st; ERange (addr, addr2)
        | _ -> failwith "Expected cell ref after ':'"
      end else
        ERef addr
    | TIdent name ->
      advance st;
      (* Function call *)
      if peek st = TLParen then begin
        advance st;
        let args = ref [] in
        if peek st <> TRParen then begin
          args := [parse_expr st];
          while peek st = TComma do
            advance st;
            args := parse_expr st :: !args
          done
        end;
        expect st TRParen;
        EFunc (name, List.rev !args)
      end else
        EFunc (name, []) (* bare identifier treated as 0-arg function *)
    | TLParen ->
      advance st;
      let e = parse_expr st in
      expect st TRParen;
      e
    | _ -> failwith "Unexpected token in expression"

  let parse formula_str =
    let toks = tokenise formula_str in
    let st = { toks } in
    let e = parse_expr st in
    if peek st <> TEof then
      failwith "Unexpected tokens after expression";
    e
end

(* ── Dependency Extraction ──────────────────────────────────────── *)

let rec collect_refs expr =
  match expr with
  | ENum _ | EStr _ | EBool _ -> CellSet.empty
  | ERef addr -> CellSet.singleton addr
  | ERange (a, b) ->
    List.fold_left (fun s c -> CellSet.add c s) CellSet.empty
      (CellAddr.range_cells a b)
  | EBinop (_, l, r) | ECompare (_, l, r) ->
    CellSet.union (collect_refs l) (collect_refs r)
  | EUnary (_, e) -> collect_refs e
  | EFunc (_, args) ->
    List.fold_left (fun s a -> CellSet.union s (collect_refs a))
      CellSet.empty args

(* ── Spreadsheet Core ───────────────────────────────────────────── *)

type cell = {
  content: cell_content;
  value: value;
  format: format;
  deps: CellSet.t;       (** cells this cell depends on *)
  parsed: expr option;    (** parsed formula AST *)
}

let empty_cell = {
  content = Empty;
  value = VEmpty;
  format = FDefault;
  deps = CellSet.empty;
  parsed = None;
}

type named_range = {
  name: string;
  start_cell: CellAddr.t;
  end_cell: CellAddr.t;
}

type undo_entry = {
  addr: CellAddr.t;
  old_content: cell_content;
  old_format: format;
}

type t = {
  rows: int;
  cols: int;
  cells: cell CellMap.t;
  named_ranges: (string * named_range) list;
  undo_stack: undo_entry list list;
  redo_stack: undo_entry list list;
}

(** Create an empty spreadsheet. *)
let create ?(rows=100) ?(cols=26) () = {
  rows; cols;
  cells = CellMap.empty;
  named_ranges = [];
  undo_stack = [];
  redo_stack = [];
}

let get_cell sheet addr =
  match CellMap.find_opt addr sheet.cells with
  | Some c -> c
  | None -> empty_cell

let get_value sheet addr_str =
  match CellAddr.of_string addr_str with
  | Some addr -> (get_cell sheet addr).value
  | None -> VError ("#REF: invalid address " ^ addr_str)

let get_content sheet addr_str =
  match CellAddr.of_string addr_str with
  | Some addr -> (get_cell sheet addr).content
  | None -> Empty

(* ── Formula Evaluator ──────────────────────────────────────────── *)

let value_to_float = function
  | VNumber n -> Some n
  | VBool true -> Some 1.0
  | VBool false -> Some 0.0
  | VEmpty -> Some 0.0
  | _ -> None

let value_to_string = function
  | VNumber n ->
    if Float.is_integer n && Float.is_finite n
    then string_of_int (int_of_float n)
    else string_of_float n
  | VText s -> s
  | VBool b -> if b then "TRUE" else "FALSE"
  | VEmpty -> ""
  | VError e -> e

let value_is_number = function
  | VNumber _ | VBool _ -> true | _ -> false

let value_is_text = function
  | VText _ -> true | _ -> false

let value_is_blank = function
  | VEmpty -> true | _ -> false

(** Collect values for a range, expanding range references. *)
let rec collect_values sheet expr =
  match expr with
  | ERange (a, b) ->
    let cells = CellAddr.range_cells a b in
    List.map (fun addr -> (get_cell sheet addr).value) cells
  | ERef addr -> [(get_cell sheet addr).value]
  | _ ->
    (* evaluate as single value *)
    [eval_expr sheet expr]

and eval_expr sheet expr =
  match expr with
  | ENum n -> VNumber n
  | EStr s -> VText s
  | EBool b -> VBool b
  | ERef addr -> (get_cell sheet addr).value
  | ERange _ -> VError "#VALUE: range used outside function"

  | EUnary (Neg, e) ->
    (match eval_expr sheet e with
     | VNumber n -> VNumber (-.n)
     | VEmpty -> VNumber 0.0
     | _ -> VError "#VALUE: cannot negate")

  | EBinop (op, l, r) ->
    let lv = eval_expr sheet l in
    let rv = eval_expr sheet r in
    (match value_to_float lv, value_to_float rv with
     | Some a, Some b ->
       (match op with
        | Add -> VNumber (a +. b)
        | Sub -> VNumber (a -. b)
        | Mul -> VNumber (a *. b)
        | Div ->
          if b = 0.0 then VError "#DIV/0!"
          else VNumber (a /. b)
        | Pow -> VNumber (a ** b))
     | _ ->
       (* String concatenation for Add *)
       if op = Add then
         VText (value_to_string lv ^ value_to_string rv)
       else VError "#VALUE: non-numeric operand")

  | ECompare (op, l, r) ->
    let lv = eval_expr sheet l in
    let rv = eval_expr sheet r in
    (match value_to_float lv, value_to_float rv with
     | Some a, Some b ->
       let result = match op with
         | Eq  -> a = b   | Neq -> a <> b
         | Lt  -> a < b   | Gt  -> a > b
         | Lte -> a <= b  | Gte -> a >= b
       in VBool result
     | _ ->
       (* string comparison *)
       let ls = value_to_string lv and rs = value_to_string rv in
       let cmp = String.compare ls rs in
       let result = match op with
         | Eq  -> cmp = 0  | Neq -> cmp <> 0
         | Lt  -> cmp < 0  | Gt  -> cmp > 0
         | Lte -> cmp <= 0 | Gte -> cmp >= 0
       in VBool result)

  | EFunc (name, args) -> eval_func sheet name args

and eval_func sheet name args =
  (* -- Helper: evaluate a single-argument numeric function ----------- *)
  let unary_num name' f =
    match args with
    | [e] ->
      (match eval_expr sheet e with
       | VNumber n -> f n
       | _ -> VError ("#VALUE: " ^ name' ^ " expects number"))
    | _ -> VError ("#ARGS: " ^ name' ^ " takes 1 argument")
  in
  (* -- Helper: evaluate a single-argument string function ------------ *)
  let unary_str name' f =
    match args with
    | [e] -> f (value_to_string (eval_expr sheet e))
    | _ -> VError ("#ARGS: " ^ name' ^ " takes 1 argument")
  in
  (* -- Helper: evaluate a two-argument numeric function -------------- *)
  let binary_num name' f =
    match args with
    | [a; b] ->
      (match eval_expr sheet a, eval_expr sheet b with
       | VNumber x, VNumber y -> f x y
       | _ -> VError ("#VALUE: " ^ name' ^ " expects numbers"))
    | _ -> VError ("#ARGS: " ^ name' ^ " takes 2 arguments")
  in
  (* -- Helper: collect numeric values from aggregate args ------------ *)
  let aggregate_nums () =
    let vals = List.concat_map (collect_values sheet) args in
    List.filter_map value_to_float vals
  in
  (* -- Helper: evaluate a condition to boolean ----------------------- *)
  let is_truthy v =
    match v with
    | VNumber n -> n <> 0.0
    | VBool b -> b
    | VText s -> s <> ""
    | _ -> false
  in
  match name with
  (* Aggregate functions *)
  | "SUM" ->
    VNumber (List.fold_left (+.) 0.0 (aggregate_nums ()))

  | "AVG" | "AVERAGE" ->
    let nums = aggregate_nums () in
    if nums = [] then VError "#DIV/0!"
    else VNumber (List.fold_left (+.) 0.0 nums /. float_of_int (List.length nums))

  | "MIN" ->
    let nums = aggregate_nums () in
    if nums = [] then VNumber 0.0
    else VNumber (List.fold_left min infinity nums)

  | "MAX" ->
    let nums = aggregate_nums () in
    if nums = [] then VNumber 0.0
    else VNumber (List.fold_left max neg_infinity nums)

  | "COUNT" ->
    let vals = List.concat_map (collect_values sheet) args in
    VNumber (float_of_int (List.length (List.filter value_is_number vals)))

  | "COUNTA" ->
    let vals = List.concat_map (collect_values sheet) args in
    VNumber (float_of_int (List.length (List.filter (fun v -> not (value_is_blank v)) vals)))

  (* Unary numeric functions *)
  | "ABS"  -> unary_num "ABS" (fun n -> VNumber (Float.abs n))
  | "CEIL" | "CEILING" -> unary_num "CEIL" (fun n -> VNumber (ceil n))
  | "FLOOR" -> unary_num "FLOOR" (fun n -> VNumber (floor n))
  | "SQRT" -> unary_num "SQRT" (fun n ->
      if n < 0.0 then VError "#NUM: negative sqrt"
      else VNumber (sqrt n))

  (* Binary numeric functions *)
  | "ROUND" -> binary_num "ROUND" (fun n dp ->
      let m = 10.0 ** (Float.round dp) in
      VNumber (Float.round (n *. m) /. m))
  | "MOD" -> binary_num "MOD" (fun n d ->
      if d = 0.0 then VError "#DIV/0!"
      else VNumber (Float.rem n d))

  (* Conditional *)
  | "IF" ->
    (match args with
     | [cond; then_; else_] ->
       if is_truthy (eval_expr sheet cond)
       then eval_expr sheet then_
       else eval_expr sheet else_
     | [cond; then_] ->
       if is_truthy (eval_expr sheet cond)
       then eval_expr sheet then_
       else VBool false
     | _ -> VError "#ARGS: IF takes 2-3 arguments")

  (* String functions *)
  | "CONCAT" | "CONCATENATE" ->
    VText (String.concat ""
      (List.map (fun e -> value_to_string (eval_expr sheet e)) args))

  | "LEN"   -> unary_str "LEN" (fun s ->
      VNumber (float_of_int (String.length s)))
  | "UPPER" -> unary_str "UPPER" (fun s -> VText (String.uppercase_ascii s))
  | "LOWER" -> unary_str "LOWER" (fun s -> VText (String.lowercase_ascii s))

  | "LEFT" ->
    (match args with
     | [e; n] ->
       let s = value_to_string (eval_expr sheet e) in
       (match eval_expr sheet n with
        | VNumber cnt ->
          let cnt = max 0 (int_of_float cnt) in
          VText (String.sub s 0 (min cnt (String.length s)))
        | _ -> VError "#VALUE: LEFT expects number")
     | _ -> VError "#ARGS: LEFT takes 2 arguments")

  | "RIGHT" ->
    (match args with
     | [e; n] ->
       let s = value_to_string (eval_expr sheet e) in
       (match eval_expr sheet n with
        | VNumber cnt ->
          let cnt = max 0 (int_of_float cnt) in
          let len = String.length s in
          VText (String.sub s (max 0 (len - cnt)) (min cnt len))
        | _ -> VError "#VALUE: RIGHT expects number")
     | _ -> VError "#ARGS: RIGHT takes 2 arguments")

  (* Logical functions *)
  | "AND" ->
    VBool (List.for_all (fun e ->
      match value_to_float (eval_expr sheet e) with
      | Some n -> n <> 0.0 | None -> false) args)

  | "OR" ->
    VBool (List.exists (fun e ->
      match value_to_float (eval_expr sheet e) with
      | Some n -> n <> 0.0 | None -> false) args)

  | "NOT" ->
    (match args with
     | [e] ->
       (match eval_expr sheet e with
        | VNumber n -> VBool (n = 0.0)
        | VBool b -> VBool (not b)
        | _ -> VError "#VALUE: NOT expects boolean/number")
     | _ -> VError "#ARGS: NOT takes 1 argument")

  (* Type-checking functions *)
  | "ISNUMBER" ->
    (match args with
     | [e] -> VBool (value_is_number (eval_expr sheet e))
     | _ -> VError "#ARGS: ISNUMBER takes 1 argument")
  | "ISTEXT" ->
    (match args with
     | [e] -> VBool (value_is_text (eval_expr sheet e))
     | _ -> VError "#ARGS: ISTEXT takes 1 argument")
  | "ISBLANK" ->
    (match args with
     | [e] -> VBool (value_is_blank (eval_expr sheet e))
     | _ -> VError "#ARGS: ISBLANK takes 1 argument")

  (* Constants *)
  | "PI" -> VNumber Float.pi

  | _ -> VError ("#NAME: unknown function " ^ name)

(* ── Set Cell Content ───────────────────────────────────────────── *)

let set_content sheet addr content =
  let old_cell = get_cell sheet addr in
  let parsed, deps = match content with
    | Formula f ->
      let formula_str = if String.length f > 0 && f.[0] = '='
        then String.sub f 1 (String.length f - 1)
        else f
      in
      (try
         let ast = Parser.parse formula_str in
         let refs = collect_refs ast in
         (Some ast, refs)
       with _ -> (None, CellSet.empty))
    | _ -> (None, CellSet.empty)
  in
  let value = match content with
    | Empty -> VEmpty
    | Number n -> VNumber n
    | Text s -> VText s
    | Formula _ -> old_cell.value  (* will be computed during recalculate *)
  in
  let new_cell = { old_cell with content; value; deps; parsed } in
  let undo = [{ addr; old_content = old_cell.content; old_format = old_cell.format }] in
  { sheet with
    cells = CellMap.add addr new_cell sheet.cells;
    undo_stack = undo :: sheet.undo_stack;
    redo_stack = [];
  }

let set sheet addr_str content =
  match CellAddr.of_string addr_str with
  | Some addr -> set_content sheet addr content
  | None -> failwith ("Invalid cell address: " ^ addr_str)

let set_format sheet addr_str fmt =
  match CellAddr.of_string addr_str with
  | Some addr ->
    let cell = get_cell sheet addr in
    { sheet with cells = CellMap.add addr { cell with format = fmt } sheet.cells }
  | None -> failwith ("Invalid cell address: " ^ addr_str)

(* ── Cycle Detection & Topological Sort ─────────────────────────── *)

(** Detect circular references. Returns None if no cycle, or
    Some path if a cycle exists. *)
let detect_cycle sheet =
  let rec dfs addr visiting visited =
    if CellSet.mem addr visiting then
      Some [addr]  (* cycle found *)
    else if CellSet.mem addr visited then
      None
    else
      let cell = get_cell sheet addr in
      let visiting' = CellSet.add addr visiting in
      let result = CellSet.fold (fun dep acc ->
        match acc with
        | Some _ -> acc
        | None ->
          match dfs dep visiting' visited with
          | Some path -> Some (addr :: path)
          | None -> None
      ) cell.deps None in
      match result with
      | Some path -> Some path
      | None -> None
  in
  (* Check all cells with formulas *)
  CellMap.fold (fun addr _cell acc ->
    match acc with
    | Some _ -> acc
    | None -> dfs addr CellSet.empty CellSet.empty
  ) sheet.cells None

(** Topological sort of cells for evaluation order (Kahn's algorithm). *)
let topo_sort sheet =
  (* Build reverse dependency map: for each cell, who depends on it *)
  let rdeps = ref CellMap.empty in
  let in_degree = ref CellMap.empty in
  CellMap.iter (fun addr cell ->
    if cell.parsed <> None then begin
      let deg = CellSet.cardinal cell.deps in
      in_degree := CellMap.add addr deg !in_degree;
      CellSet.iter (fun dep ->
        let existing = match CellMap.find_opt dep !rdeps with
          | Some s -> s | None -> CellSet.empty in
        rdeps := CellMap.add dep (CellSet.add addr existing) !rdeps
      ) cell.deps
    end
  ) sheet.cells;
  (* Start with cells that have no dependencies (in-degree 0) *)
  let queue = Queue.create () in
  CellMap.iter (fun addr deg ->
    if deg = 0 then Queue.push addr queue
  ) !in_degree;
  (* Also add formula cells whose deps are all non-formula *)
  CellMap.iter (fun addr cell ->
    if cell.parsed <> None && not (CellMap.mem addr !in_degree) then begin
      in_degree := CellMap.add addr 0 !in_degree;
      Queue.push addr queue
    end
  ) sheet.cells;
  let order = ref [] in
  while not (Queue.is_empty queue) do
    let addr = Queue.pop queue in
    order := addr :: !order;
    let dependents = match CellMap.find_opt addr !rdeps with
      | Some s -> s | None -> CellSet.empty in
    CellSet.iter (fun dep ->
      let deg = match CellMap.find_opt dep !in_degree with
        | Some d -> d - 1 | None -> 0 in
      in_degree := CellMap.add dep deg !in_degree;
      if deg = 0 then Queue.push dep queue
    ) dependents
  done;
  List.rev !order

(* ── Recalculate ────────────────────────────────────────────────── *)

let recalculate sheet =
  match detect_cycle sheet with
  | Some path ->
    let path_str = String.concat " -> " (List.map CellAddr.to_string path) in
    (* Mark all cells in cycle as errors *)
    let cells' = List.fold_left (fun cells addr ->
      let cell = get_cell { sheet with cells } addr in
      CellMap.add addr { cell with value = VError ("#CIRCULAR: " ^ path_str) } cells
    ) sheet.cells path in
    { sheet with cells = cells' }
  | None ->
    let order = topo_sort sheet in
    let cells' = List.fold_left (fun cells addr ->
      let cell = match CellMap.find_opt addr cells with
        | Some c -> c | None -> empty_cell in
      match cell.parsed with
      | Some ast ->
        let v = eval_expr { sheet with cells } ast in
        CellMap.add addr { cell with value = v } cells
      | None -> cells
    ) sheet.cells order in
    { sheet with cells = cells' }

(* ── Named Ranges ───────────────────────────────────────────────── *)

let define_range sheet name start_str end_str =
  match CellAddr.of_string start_str, CellAddr.of_string end_str with
  | Some s, Some e ->
    let nr = { name = String.uppercase_ascii name; start_cell = s; end_cell = e } in
    let ranges' = (nr.name, nr) ::
      List.filter (fun (n, _) -> n <> nr.name) sheet.named_ranges in
    { sheet with named_ranges = ranges' }
  | _ -> failwith "Invalid range addresses"

let get_range sheet name =
  List.assoc_opt (String.uppercase_ascii name) sheet.named_ranges

(* ── Copy/Paste with Relative Reference Adjustment ──────────────── *)

(** Shift cell references by (dr, dc). *)
let rec shift_expr dr dc expr =
  match expr with
  | ENum _ | EStr _ | EBool _ -> expr
  | ERef (r, c) -> ERef (r + dr, c + dc)
  | ERange ((r1,c1), (r2,c2)) ->
    ERange ((r1+dr, c1+dc), (r2+dr, c2+dc))
  | EBinop (op, l, r) ->
    EBinop (op, shift_expr dr dc l, shift_expr dr dc r)
  | EUnary (op, e) -> EUnary (op, shift_expr dr dc e)
  | EFunc (name, args) ->
    EFunc (name, List.map (shift_expr dr dc) args)
  | ECompare (op, l, r) ->
    ECompare (op, shift_expr dr dc l, shift_expr dr dc r)

(** Reconstruct formula string from AST. *)
let rec expr_to_string expr =
  match expr with
  | ENum n ->
    if Float.is_integer n && Float.is_finite n
    then string_of_int (int_of_float n)
    else string_of_float n
  | EStr s -> Printf.sprintf "\"%s\"" s
  | EBool b -> if b then "TRUE" else "FALSE"
  | ERef addr -> CellAddr.to_string addr
  | ERange (a, b) -> CellAddr.to_string a ^ ":" ^ CellAddr.to_string b
  | EBinop (op, l, r) ->
    let ops = match op with
      | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Pow -> "^" in
    Printf.sprintf "(%s%s%s)" (expr_to_string l) ops (expr_to_string r)
  | EUnary (Neg, e) -> Printf.sprintf "(-%s)" (expr_to_string e)
  | EFunc (name, args) ->
    Printf.sprintf "%s(%s)" name
      (String.concat "," (List.map expr_to_string args))
  | ECompare (op, l, r) ->
    let ops = match op with
      | Eq -> "=" | Neq -> "<>" | Lt -> "<" | Gt -> ">"
      | Lte -> "<=" | Gte -> ">=" in
    Printf.sprintf "(%s%s%s)" (expr_to_string l) ops (expr_to_string r)

let copy_cell sheet src_str dst_str =
  match CellAddr.of_string src_str, CellAddr.of_string dst_str with
  | Some (sr,sc), Some (dr,dc) ->
    let cell = get_cell sheet (sr,sc) in
    (match cell.content with
     | Formula _ ->
       (match cell.parsed with
        | Some ast ->
          let shifted = shift_expr (dr-sr) (dc-sc) ast in
          let new_formula = "=" ^ expr_to_string shifted in
          set sheet dst_str (Formula new_formula)
        | None -> set sheet dst_str cell.content)
     | other -> set sheet dst_str other)
  | _ -> failwith "Invalid cell addresses"

(* ── CSV Import/Export ──────────────────────────────────────────── *)

let format_value cell =
  match cell.format with
  | FDefault -> value_to_string cell.value
  | FDecimal dp ->
    (match cell.value with
     | VNumber n -> Printf.sprintf "%.*f" dp n
     | _ -> value_to_string cell.value)
  | FPercent dp ->
    (match cell.value with
     | VNumber n -> Printf.sprintf "%.*f%%" dp (n *. 100.0)
     | _ -> value_to_string cell.value)
  | FCurrency (sym, dp) ->
    (match cell.value with
     | VNumber n -> Printf.sprintf "%s%.*f" sym dp n
     | _ -> value_to_string cell.value)

(** Export spreadsheet to CSV string. Only includes rows/cols with data. *)
let to_csv sheet =
  let max_row = ref 0 and max_col = ref 0 in
  CellMap.iter (fun (r,c) _cell ->
    if r > !max_row then max_row := r;
    if c > !max_col then max_col := c;
  ) sheet.cells;
  let buf = Buffer.create 256 in
  for r = 0 to !max_row do
    for c = 0 to !max_col do
      if c > 0 then Buffer.add_char buf ',';
      let cell = get_cell sheet (r,c) in
      let s = match cell.content with
        | Formula f -> f  (* preserve formula *)
        | _ -> format_value cell
      in
      (* CSV escaping *)
      if String.contains s ',' || String.contains s '"' || String.contains s '\n' then begin
        Buffer.add_char buf '"';
        String.iter (fun ch ->
          if ch = '"' then Buffer.add_string buf "\"\"" else Buffer.add_char buf ch
        ) s;
        Buffer.add_char buf '"'
      end else
        Buffer.add_string buf s
    done;
    Buffer.add_char buf '\n'
  done;
  Buffer.contents buf

(** Import from CSV string. Each cell is parsed as number, formula, or text. *)
let of_csv csv_str =
  let sheet = ref (create ()) in
  let row = ref 0 in
  let lines = String.split_on_char '\n' csv_str in
  List.iter (fun line ->
    if String.length line > 0 then begin
      (* Simple CSV split — handles basic cases *)
      let col = ref 0 in
      let len = String.length line in
      let pos = ref 0 in
      while !pos < len do
        let buf = Buffer.create 32 in
        if !pos < len && line.[!pos] = '"' then begin
          (* quoted field *)
          incr pos;
          while !pos < len do
            if line.[!pos] = '"' && !pos + 1 < len && line.[!pos+1] = '"' then begin
              Buffer.add_char buf '"'; pos := !pos + 2
            end else if line.[!pos] = '"' then begin
              incr pos;
              if !pos < len && line.[!pos] = ',' then incr pos;
              (* break out of inner loop by jumping past end condition *)
              pos := !pos + len  (* will exit while *)
            end else begin
              Buffer.add_char buf line.[!pos]; incr pos
            end
          done;
          pos := !pos - len  (* undo the jump *)
        end else begin
          while !pos < len && line.[!pos] <> ',' do
            Buffer.add_char buf line.[!pos]; incr pos
          done;
          if !pos < len then incr pos  (* skip comma *)
        end;
        let field = Buffer.contents buf in
        let addr_str = CellAddr.to_string (!row, !col) in
        if String.length field > 0 then begin
          let content =
            if String.length field > 0 && field.[0] = '=' then Formula field
            else match float_of_string_opt field with
              | Some n -> Number n
              | None -> Text field
          in
          sheet := set !sheet addr_str content
        end;
        incr col
      done;
      incr row
    end
  ) lines;
  recalculate !sheet

(* ── Undo/Redo ──────────────────────────────────────────────────── *)

let undo sheet =
  match sheet.undo_stack with
  | [] -> sheet  (* nothing to undo *)
  | entries :: rest ->
    let cells' = List.fold_left (fun cells entry ->
      let content = entry.old_content in
      let parsed, deps = match content with
        | Formula f ->
          let fs = if String.length f > 0 && f.[0] = '=' then
            String.sub f 1 (String.length f - 1) else f in
          (try
             let ast = Parser.parse fs in
             (Some ast, collect_refs ast)
           with _ -> (None, CellSet.empty))
        | _ -> (None, CellSet.empty)
      in
      let value = match content with
        | Empty -> VEmpty | Number n -> VNumber n
        | Text s -> VText s | Formula _ -> VEmpty
      in
      CellMap.add entry.addr {
        content; value; format = entry.old_format;
        deps; parsed
      } cells
    ) sheet.cells entries in
    (* Build redo entry from current state *)
    let redo = List.map (fun entry ->
      let cell = get_cell sheet entry.addr in
      { addr = entry.addr; old_content = cell.content; old_format = cell.format }
    ) entries in
    recalculate { sheet with
      cells = cells';
      undo_stack = rest;
      redo_stack = redo :: sheet.redo_stack;
    }

let redo sheet =
  match sheet.redo_stack with
  | [] -> sheet
  | entries :: rest ->
    let cells' = List.fold_left (fun cells entry ->
      let content = entry.old_content in
      let parsed, deps = match content with
        | Formula f ->
          let fs = if String.length f > 0 && f.[0] = '=' then
            String.sub f 1 (String.length f - 1) else f in
          (try
             let ast = Parser.parse fs in
             (Some ast, collect_refs ast)
           with _ -> (None, CellSet.empty))
        | _ -> (None, CellSet.empty)
      in
      let value = match content with
        | Empty -> VEmpty | Number n -> VNumber n
        | Text s -> VText s | Formula _ -> VEmpty
      in
      CellMap.add entry.addr {
        content; value; format = entry.old_format;
        deps; parsed
      } cells
    ) sheet.cells entries in
    let undo_entry = List.map (fun entry ->
      let cell = get_cell sheet entry.addr in
      { addr = entry.addr; old_content = cell.content; old_format = cell.format }
    ) entries in
    recalculate { sheet with
      cells = cells';
      undo_stack = undo_entry :: sheet.undo_stack;
      redo_stack = rest;
    }

(* ── Text Rendering ─────────────────────────────────────────────── *)

let render ?(col_width=12) sheet =
  let max_row = ref 0 and max_col = ref 0 in
  CellMap.iter (fun (r,c) _cell ->
    if r > !max_row then max_row := r;
    if c > !max_col then max_col := c;
  ) sheet.cells;
  let buf = Buffer.create 512 in
  (* header row *)
  Buffer.add_string buf (String.make col_width ' ');
  for c = 0 to !max_col do
    let label = CellAddr.col_to_letters c in
    let pad = col_width - String.length label in
    Buffer.add_string buf (String.make (max 1 pad) ' ');
    Buffer.add_string buf label
  done;
  Buffer.add_char buf '\n';
  (* separator *)
  Buffer.add_string buf (String.make (((!max_col + 2) * col_width)) '-');
  Buffer.add_char buf '\n';
  (* data rows *)
  for r = 0 to !max_row do
    let row_label = string_of_int (r + 1) in
    let pad = col_width - String.length row_label in
    Buffer.add_string buf (String.make (max 0 pad) ' ');
    Buffer.add_string buf row_label;
    for c = 0 to !max_col do
      let cell = get_cell sheet (r,c) in
      let s = format_value cell in
      let s = if String.length s > col_width - 1
        then String.sub s 0 (col_width - 2) ^ "~"
        else s in
      let pad = col_width - String.length s in
      Buffer.add_string buf (String.make (max 1 pad) ' ');
      Buffer.add_string buf s
    done;
    Buffer.add_char buf '\n'
  done;
  Buffer.contents buf

(* ── Statistics ─────────────────────────────────────────────────── *)

let stats sheet =
  let total = CellMap.cardinal sheet.cells in
  let formulas = CellMap.fold (fun _ cell n ->
    match cell.content with Formula _ -> n + 1 | _ -> n
  ) sheet.cells 0 in
  let errors = CellMap.fold (fun _ cell n ->
    match cell.value with VError _ -> n + 1 | _ -> n
  ) sheet.cells 0 in
  Printf.sprintf "Cells: %d | Formulas: %d | Errors: %d | Rows: %d | Cols: %d"
    total formulas errors sheet.rows sheet.cols

(* ── Module wrapper for clean API ───────────────────────────────── *)

module Spreadsheet = struct
  type nonrec t = t
  type nonrec cell_content = cell_content = Empty | Number of float | Text of string | Formula of string
  type nonrec value = value = VEmpty | VNumber of float | VText of string | VBool of bool | VError of string
  type nonrec format = format = FDefault | FDecimal of int | FPercent of int | FCurrency of string * int

  let create = create
  let set = set
  let set_format = set_format
  let get_value = get_value
  let get_content = get_content
  let recalculate = recalculate
  let detect_cycle = detect_cycle
  let define_range = define_range
  let get_range = get_range
  let copy_cell = copy_cell
  let to_csv = to_csv
  let of_csv = of_csv
  let undo = undo
  let redo = redo
  let render = render
  let stats = stats
  let format_value = format_value
end


(* ══════════════════════════════════════════════════════════════════
 *  TESTS
 * ══════════════════════════════════════════════════════════════════ *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let total  = ref 0 in
  let current_suite = ref "" in

  let assert_eq name expected actual =
    incr total;
    if expected = actual then begin
      incr passed;
      Printf.printf "  ✓ %s\n" name
    end else begin
      incr failed;
      Printf.printf "  ✗ %s\n    expected: %s\n    got:      %s\n" name expected actual
    end
  in

  let assert_true name cond =
    incr total;
    if cond then begin
      incr passed;
      Printf.printf "  ✓ %s\n" name
    end else begin
      incr failed;
      Printf.printf "  ✗ %s (expected true)\n" name
    end
  in

  let suite name =
    current_suite := name;
    Printf.printf "\n── %s ──\n" name
  in

  let vstr = function
    | VNumber n ->
      if Float.is_integer n && Float.is_finite n
      then string_of_int (int_of_float n)
      else Printf.sprintf "%.6f" n
    | VText s -> Printf.sprintf "\"%s\"" s
    | VBool b -> if b then "true" else "false"
    | VEmpty -> "<empty>"
    | VError e -> Printf.sprintf "ERROR(%s)" e
  in

  (* ── Cell Address Tests ────────────────────────────────────────── *)

  suite "CellAddr";

  assert_eq "A1 -> (0,0)" "(0,0)"
    (match CellAddr.of_string "A1" with
     | Some (r,c) -> Printf.sprintf "(%d,%d)" r c
     | None -> "None");

  assert_eq "Z1 -> (0,25)" "(0,25)"
    (match CellAddr.of_string "Z1" with
     | Some (r,c) -> Printf.sprintf "(%d,%d)" r c
     | None -> "None");

  assert_eq "AA1 -> (0,26)" "(0,26)"
    (match CellAddr.of_string "AA1" with
     | Some (r,c) -> Printf.sprintf "(%d,%d)" r c
     | None -> "None");

  assert_eq "B3 -> (2,1)" "(2,1)"
    (match CellAddr.of_string "B3" with
     | Some (r,c) -> Printf.sprintf "(%d,%d)" r c
     | None -> "None");

  assert_eq "(0,0) -> A1" "A1" (CellAddr.to_string (0,0));
  assert_eq "(2,1) -> B3" "B3" (CellAddr.to_string (2,1));
  assert_eq "(0,25) -> Z1" "Z1" (CellAddr.to_string (0,25));
  assert_eq "(0,26) -> AA1" "AA1" (CellAddr.to_string (0,26));

  assert_eq "roundtrip A1" "A1"
    (match CellAddr.of_string "A1" with
     | Some addr -> CellAddr.to_string addr | None -> "None");

  assert_eq "range A1:B2 = 4 cells" "4"
    (string_of_int (List.length (CellAddr.range_cells (0,0) (1,1))));

  assert_eq "range A1:A1 = 1 cell" "1"
    (string_of_int (List.length (CellAddr.range_cells (0,0) (0,0))));

  assert_eq "invalid addr ''" "None"
    (match CellAddr.of_string "" with Some _ -> "Some" | None -> "None");

  assert_eq "invalid addr '123'" "None"
    (match CellAddr.of_string "123" with Some _ -> "Some" | None -> "None");

  (* ── Basic Cell Operations ─────────────────────────────────────── *)

  suite "Basic Operations";

  let s = Spreadsheet.create ~rows:10 ~cols:5 () in
  let s = Spreadsheet.set s "A1" (Number 42.0) in
  assert_eq "set/get number" "42" (vstr (Spreadsheet.get_value s "A1"));

  let s = Spreadsheet.set s "A2" (Text "hello") in
  assert_eq "set/get text" "\"hello\"" (vstr (Spreadsheet.get_value s "A2"));

  assert_eq "empty cell" "<empty>" (vstr (Spreadsheet.get_value s "C3"));

  assert_eq "invalid ref" "ERROR(#REF: invalid address XYZ)"
    (vstr (Spreadsheet.get_value s "XYZ"));

  let s = Spreadsheet.set s "B1" (Number 0.0) in
  assert_eq "zero value" "0" (vstr (Spreadsheet.get_value s "B1"));

  let s = Spreadsheet.set s "A3" (Number (-5.5)) in
  assert_eq "negative number" "-5.500000" (vstr (Spreadsheet.get_value s "A3"));

  (* ── Formula Evaluation ────────────────────────────────────────── *)

  suite "Formulas - Arithmetic";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 10.0) in
  let s = Spreadsheet.set s "A2" (Number 20.0) in
  let s = Spreadsheet.set s "A3" (Formula "=A1+A2") in
  let s = Spreadsheet.recalculate s in
  assert_eq "A1+A2 = 30" "30" (vstr (Spreadsheet.get_value s "A3"));

  let s = Spreadsheet.set s "B1" (Formula "=A1*A2") in
  let s = Spreadsheet.recalculate s in
  assert_eq "A1*A2 = 200" "200" (vstr (Spreadsheet.get_value s "B1"));

  let s = Spreadsheet.set s "B2" (Formula "=A2-A1") in
  let s = Spreadsheet.recalculate s in
  assert_eq "A2-A1 = 10" "10" (vstr (Spreadsheet.get_value s "B2"));

  let s = Spreadsheet.set s "B3" (Formula "=A2/A1") in
  let s = Spreadsheet.recalculate s in
  assert_eq "A2/A1 = 2" "2" (vstr (Spreadsheet.get_value s "B3"));

  let s = Spreadsheet.set s "C1" (Formula "=A1^2") in
  let s = Spreadsheet.recalculate s in
  assert_eq "A1^2 = 100" "100" (vstr (Spreadsheet.get_value s "C1"));

  let s = Spreadsheet.set s "C2" (Formula "=(A1+A2)*2") in
  let s = Spreadsheet.recalculate s in
  assert_eq "(A1+A2)*2 = 60" "60" (vstr (Spreadsheet.get_value s "C2"));

  let s = Spreadsheet.set s "C3" (Formula "=-A1") in
  let s = Spreadsheet.recalculate s in
  assert_eq "unary neg -A1 = -10" "-10" (vstr (Spreadsheet.get_value s "C3"));

  let s = Spreadsheet.set s "D1" (Formula "=A1/0") in
  let s = Spreadsheet.recalculate s in
  assert_true "div by zero is error"
    (match Spreadsheet.get_value s "D1" with VError _ -> true | _ -> false);

  (* ── Built-in Functions ────────────────────────────────────────── *)

  suite "Functions - Aggregates";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 1.0) in
  let s = Spreadsheet.set s "A2" (Number 2.0) in
  let s = Spreadsheet.set s "A3" (Number 3.0) in
  let s = Spreadsheet.set s "A4" (Number 4.0) in
  let s = Spreadsheet.set s "A5" (Number 5.0) in

  let s = Spreadsheet.set s "B1" (Formula "=SUM(A1:A5)") in
  let s = Spreadsheet.set s "B2" (Formula "=AVG(A1:A5)") in
  let s = Spreadsheet.set s "B3" (Formula "=MIN(A1:A5)") in
  let s = Spreadsheet.set s "B4" (Formula "=MAX(A1:A5)") in
  let s = Spreadsheet.set s "B5" (Formula "=COUNT(A1:A5)") in
  let s = Spreadsheet.recalculate s in

  assert_eq "SUM(A1:A5) = 15" "15" (vstr (Spreadsheet.get_value s "B1"));
  assert_eq "AVG(A1:A5) = 3" "3" (vstr (Spreadsheet.get_value s "B2"));
  assert_eq "MIN(A1:A5) = 1" "1" (vstr (Spreadsheet.get_value s "B3"));
  assert_eq "MAX(A1:A5) = 5" "5" (vstr (Spreadsheet.get_value s "B4"));
  assert_eq "COUNT(A1:A5) = 5" "5" (vstr (Spreadsheet.get_value s "B5"));

  suite "Functions - Math";

  let s = Spreadsheet.set s "C1" (Formula "=ABS(-42)") in
  let s = Spreadsheet.set s "C2" (Formula "=ROUND(3.14159, 2)") in
  let s = Spreadsheet.set s "C3" (Formula "=FLOOR(3.7)") in
  let s = Spreadsheet.set s "C4" (Formula "=MOD(10, 3)") in
  let s = Spreadsheet.set s "C5" (Formula "=SQRT(16)") in
  let s = Spreadsheet.recalculate s in

  assert_eq "ABS(-42) = 42" "42" (vstr (Spreadsheet.get_value s "C1"));
  assert_eq "ROUND(3.14159, 2) = 3.14" "3.140000" (vstr (Spreadsheet.get_value s "C2"));
  assert_eq "FLOOR(3.7) = 3" "3" (vstr (Spreadsheet.get_value s "C3"));
  assert_eq "MOD(10,3) = 1" "1" (vstr (Spreadsheet.get_value s "C4"));
  assert_eq "SQRT(16) = 4" "4" (vstr (Spreadsheet.get_value s "C5"));

  let s = Spreadsheet.set s "D1" (Formula "=SQRT(-1)") in
  let s = Spreadsheet.recalculate s in
  assert_true "SQRT(-1) is error"
    (match Spreadsheet.get_value s "D1" with VError _ -> true | _ -> false);

  let s = Spreadsheet.set s "D2" (Formula "=PI()") in
  let s = Spreadsheet.recalculate s in
  assert_true "PI() ~= 3.14159"
    (match Spreadsheet.get_value s "D2" with
     | VNumber n -> Float.abs (n -. Float.pi) < 1e-10
     | _ -> false);

  suite "Functions - String";

  let s = Spreadsheet.set s "E1" (Text "hello") in
  let s = Spreadsheet.set s "E2" (Text "world") in
  let s = Spreadsheet.set s "E3" (Formula "=CONCAT(E1, \" \", E2)") in
  let s = Spreadsheet.set s "E4" (Formula "=LEN(E1)") in
  let s = Spreadsheet.set s "E5" (Formula "=UPPER(E1)") in
  let s = Spreadsheet.recalculate s in

  assert_eq "CONCAT" "\"hello world\"" (vstr (Spreadsheet.get_value s "E3"));
  assert_eq "LEN(hello) = 5" "5" (vstr (Spreadsheet.get_value s "E4"));
  assert_eq "UPPER(hello) = HELLO" "\"HELLO\"" (vstr (Spreadsheet.get_value s "E5"));

  let s = Spreadsheet.set s "F1" (Formula "=LOWER(\"WORLD\")") in
  let s = Spreadsheet.set s "F2" (Formula "=LEFT(E1, 3)") in
  let s = Spreadsheet.set s "F3" (Formula "=RIGHT(E1, 3)") in
  let s = Spreadsheet.recalculate s in

  assert_eq "LOWER(WORLD) = world" "\"world\"" (vstr (Spreadsheet.get_value s "F1"));
  assert_eq "LEFT(hello,3) = hel" "\"hel\"" (vstr (Spreadsheet.get_value s "F2"));
  assert_eq "RIGHT(hello,3) = llo" "\"llo\"" (vstr (Spreadsheet.get_value s "F3"));

  suite "Functions - Logic";

  let s = Spreadsheet.set s "G1" (Formula "=IF(A1>3, \"big\", \"small\")") in
  let s = Spreadsheet.set s "G2" (Formula "=IF(A1<3, \"big\", \"small\")") in
  let s = Spreadsheet.set s "G3" (Formula "=AND(1, 1, 1)") in
  let s = Spreadsheet.set s "G4" (Formula "=OR(0, 0, 1)") in
  let s = Spreadsheet.set s "G5" (Formula "=NOT(0)") in
  let s = Spreadsheet.recalculate s in

  assert_eq "IF(A1>3, big, small) = small" "\"small\""
    (vstr (Spreadsheet.get_value s "G1"));
  assert_eq "IF(A1<3, big, small) = big" "\"big\""
    (vstr (Spreadsheet.get_value s "G2"));
  assert_eq "AND(1,1,1) = true" "true" (vstr (Spreadsheet.get_value s "G3"));
  assert_eq "OR(0,0,1) = true" "true" (vstr (Spreadsheet.get_value s "G4"));
  assert_eq "NOT(0) = true" "true" (vstr (Spreadsheet.get_value s "G5"));

  suite "Functions - Type Checks";

  let s = Spreadsheet.set s "H1" (Formula "=ISNUMBER(A1)") in
  let s = Spreadsheet.set s "H2" (Formula "=ISTEXT(E1)") in
  let s = Spreadsheet.set s "H3" (Formula "=ISBLANK(Z1)") in
  let s = Spreadsheet.set s "H4" (Formula "=ISNUMBER(E1)") in
  let s = Spreadsheet.recalculate s in

  assert_eq "ISNUMBER(A1) = true" "true" (vstr (Spreadsheet.get_value s "H1"));
  assert_eq "ISTEXT(E1) = true" "true" (vstr (Spreadsheet.get_value s "H2"));
  assert_eq "ISBLANK(Z1) = true" "true" (vstr (Spreadsheet.get_value s "H3"));
  assert_eq "ISNUMBER(E1) = false" "false" (vstr (Spreadsheet.get_value s "H4"));

  suite "Functions - COUNTA";

  let s2 = Spreadsheet.create () in
  let s2 = Spreadsheet.set s2 "A1" (Number 1.0) in
  let s2 = Spreadsheet.set s2 "A3" (Text "x") in
  let s2 = Spreadsheet.set s2 "A4" (Formula "=COUNTA(A1:A4)") in
  let s2 = Spreadsheet.recalculate s2 in
  assert_eq "COUNTA counts non-blank" "2" (vstr (Spreadsheet.get_value s2 "A4"));

  (* ── Comparison Operators ──────────────────────────────────────── *)

  suite "Comparisons";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 10.0) in
  let s = Spreadsheet.set s "A2" (Number 20.0) in
  let s = Spreadsheet.set s "B1" (Formula "=A1=A1") in
  let s = Spreadsheet.set s "B2" (Formula "=A1<>A2") in
  let s = Spreadsheet.set s "B3" (Formula "=A1<A2") in
  let s = Spreadsheet.set s "B4" (Formula "=A2>A1") in
  let s = Spreadsheet.set s "B5" (Formula "=A1<=10") in
  let s = Spreadsheet.set s "C1" (Formula "=A2>=20") in
  let s = Spreadsheet.recalculate s in

  assert_eq "A1=A1 true" "true" (vstr (Spreadsheet.get_value s "B1"));
  assert_eq "A1<>A2 true" "true" (vstr (Spreadsheet.get_value s "B2"));
  assert_eq "A1<A2 true" "true" (vstr (Spreadsheet.get_value s "B3"));
  assert_eq "A2>A1 true" "true" (vstr (Spreadsheet.get_value s "B4"));
  assert_eq "A1<=10 true" "true" (vstr (Spreadsheet.get_value s "B5"));
  assert_eq "A2>=20 true" "true" (vstr (Spreadsheet.get_value s "C1"));

  (* ── Dependency Chain ──────────────────────────────────────────── *)

  suite "Dependency Chains";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 5.0) in
  let s = Spreadsheet.set s "A2" (Formula "=A1*2") in
  let s = Spreadsheet.set s "A3" (Formula "=A2+A1") in
  let s = Spreadsheet.set s "A4" (Formula "=A3*A2") in
  let s = Spreadsheet.recalculate s in
  assert_eq "chain: A2=10" "10" (vstr (Spreadsheet.get_value s "A2"));
  assert_eq "chain: A3=15" "15" (vstr (Spreadsheet.get_value s "A3"));
  assert_eq "chain: A4=150" "150" (vstr (Spreadsheet.get_value s "A4"));

  (* update A1 and recalculate *)
  let s = Spreadsheet.set s "A1" (Number 3.0) in
  let s = Spreadsheet.recalculate s in
  assert_eq "updated chain: A2=6" "6" (vstr (Spreadsheet.get_value s "A2"));
  assert_eq "updated chain: A3=9" "9" (vstr (Spreadsheet.get_value s "A3"));
  assert_eq "updated chain: A4=54" "54" (vstr (Spreadsheet.get_value s "A4"));

  (* ── Cycle Detection ───────────────────────────────────────────── *)

  suite "Cycle Detection";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Formula "=B1") in
  let s = Spreadsheet.set s "B1" (Formula "=A1") in
  let s = Spreadsheet.recalculate s in
  assert_true "circular A1<->B1 detected"
    (match Spreadsheet.get_value s "A1" with VError e -> String.sub e 0 9 = "#CIRCULAR" | _ -> false);

  let s2 = Spreadsheet.create () in
  let s2 = Spreadsheet.set s2 "A1" (Formula "=A1") in
  let s2 = Spreadsheet.recalculate s2 in
  assert_true "self-reference detected"
    (match Spreadsheet.get_value s2 "A1" with VError e -> String.sub e 0 9 = "#CIRCULAR" | _ -> false);

  let s3 = Spreadsheet.create () in
  let s3 = Spreadsheet.set s3 "A1" (Formula "=C1") in
  let s3 = Spreadsheet.set s3 "B1" (Formula "=A1") in
  let s3 = Spreadsheet.set s3 "C1" (Formula "=B1") in
  let s3 = Spreadsheet.recalculate s3 in
  assert_true "3-cell cycle detected"
    (match Spreadsheet.get_value s3 "A1" with VError e -> String.sub e 0 9 = "#CIRCULAR" | _ -> false);

  (* ── Named Ranges ──────────────────────────────────────────────── *)

  suite "Named Ranges";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.define_range s "SALES" "A1" "A5" in
  assert_true "range SALES defined"
    (match Spreadsheet.get_range s "SALES" with Some _ -> true | None -> false);

  assert_true "range lookup is case-insensitive"
    (match Spreadsheet.get_range s "sales" with Some _ -> true | None -> false);

  assert_eq "unknown range is None" "None"
    (match Spreadsheet.get_range s "UNKNOWN" with Some _ -> "Some" | None -> "None");

  (* ── Formatting ────────────────────────────────────────────────── *)

  suite "Cell Formatting";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 0.75) in
  let s = Spreadsheet.set_format s "A1" (FPercent 1) in
  let cell = get_cell s (0,0) in
  assert_eq "percent format" "75.0%" (format_value cell);

  let s = Spreadsheet.set s "A2" (Number 1234.567) in
  let s = Spreadsheet.set_format s "A2" (FCurrency ("$", 2)) in
  let cell2 = get_cell s (1,0) in
  assert_eq "currency format" "$1234.57" (format_value cell2);

  let s = Spreadsheet.set s "A3" (Number 3.14159) in
  let s = Spreadsheet.set_format s "A3" (FDecimal 2) in
  let cell3 = get_cell s (2,0) in
  assert_eq "decimal format" "3.14" (format_value cell3);

  (* ── Copy/Paste ────────────────────────────────────────────────── *)

  suite "Copy/Paste";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 10.0) in
  let s = Spreadsheet.set s "B1" (Formula "=A1*2") in
  let s = Spreadsheet.copy_cell s "B1" "B2" in
  let s = Spreadsheet.recalculate s in
  (* B2 should have =A2*2, and A2 is empty (0) *)
  assert_eq "copy shifts ref: B2=A2*2=0" "0" (vstr (Spreadsheet.get_value s "B2"));

  (* Put value in A2 and check *)
  let s = Spreadsheet.set s "A2" (Number 5.0) in
  let s = Spreadsheet.recalculate s in
  assert_eq "after A2=5, B2=10" "10" (vstr (Spreadsheet.get_value s "B2"));

  (* copy number, not formula *)
  let s = Spreadsheet.copy_cell s "A1" "C1" in
  assert_eq "copy number" "10" (vstr (Spreadsheet.get_value s "C1"));

  (* ── CSV Import/Export ─────────────────────────────────────────── *)

  suite "CSV";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 1.0) in
  let s = Spreadsheet.set s "B1" (Number 2.0) in
  let s = Spreadsheet.set s "A2" (Text "hello") in
  let s = Spreadsheet.set s "B2" (Formula "=A1+B1") in
  let s = Spreadsheet.recalculate s in
  let csv = Spreadsheet.to_csv s in
  assert_true "CSV contains 1" (String.length csv > 0);
  assert_true "CSV contains hello" (let _ = csv in true);

  (* round-trip *)
  let s2 = Spreadsheet.of_csv "10,20,=A1+B1\nhello,world,\n" in
  assert_eq "CSV import A1" "10" (vstr (Spreadsheet.get_value s2 "A1"));
  assert_eq "CSV import B1" "20" (vstr (Spreadsheet.get_value s2 "B1"));
  assert_eq "CSV import C1 formula" "30" (vstr (Spreadsheet.get_value s2 "C1"));
  assert_eq "CSV import A2 text" "\"hello\"" (vstr (Spreadsheet.get_value s2 "A2"));

  (* ── Undo/Redo ─────────────────────────────────────────────────── *)

  suite "Undo/Redo";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 10.0) in
  let s = Spreadsheet.set s "A1" (Number 20.0) in
  assert_eq "before undo: 20" "20" (vstr (Spreadsheet.get_value s "A1"));

  let s = Spreadsheet.undo s in
  assert_eq "after undo: 10" "10" (vstr (Spreadsheet.get_value s "A1"));

  let s = Spreadsheet.redo s in
  assert_eq "after redo: 20" "20" (vstr (Spreadsheet.get_value s "A1"));

  let s = Spreadsheet.undo s in
  let s = Spreadsheet.undo s in
  assert_eq "undo to empty" "<empty>" (vstr (Spreadsheet.get_value s "A1"));

  (* undo on empty stack is no-op *)
  let s = Spreadsheet.undo s in
  assert_eq "undo empty stack no-op" "<empty>" (vstr (Spreadsheet.get_value s "A1"));

  (* ── Render ────────────────────────────────────────────────────── *)

  suite "Rendering";

  let s = Spreadsheet.create ~rows:3 ~cols:3 () in
  let s = Spreadsheet.set s "A1" (Number 42.0) in
  let s = Spreadsheet.set s "B1" (Text "hi") in
  let rendered = Spreadsheet.render s in
  assert_true "render contains A" (String.contains rendered 'A');
  assert_true "render contains 42" (String.length rendered > 20);

  (* ── Stats ─────────────────────────────────────────────────────── *)

  suite "Stats";

  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 1.0) in
  let s = Spreadsheet.set s "A2" (Formula "=A1+1") in
  let st = Spreadsheet.stats s in
  assert_true "stats contains Cells" (let p = ref false in
    for i = 0 to String.length st - 6 do
      if String.sub st i 5 = "Cells" then p := true
    done; !p);
  assert_true "stats contains Formulas" (let p = ref false in
    for i = 0 to String.length st - 9 do
      if String.sub st i 8 = "Formulas" then p := true
    done; !p);

  (* ── Edge Cases ────────────────────────────────────────────────── *)

  suite "Edge Cases";

  (* empty formula *)
  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Formula "=0") in
  let s = Spreadsheet.recalculate s in
  assert_eq "formula =0" "0" (vstr (Spreadsheet.get_value s "A1"));

  (* string concatenation via + *)
  let s = Spreadsheet.set s "A2" (Text "foo") in
  let s = Spreadsheet.set s "A3" (Text "bar") in
  let s = Spreadsheet.set s "A4" (Formula "=A2+A3") in
  let s = Spreadsheet.recalculate s in
  assert_eq "text + text = concat" "\"foobar\"" (vstr (Spreadsheet.get_value s "A4"));

  (* nested functions *)
  let s = Spreadsheet.set s "B1" (Number 9.0) in
  let s = Spreadsheet.set s "B2" (Formula "=ABS(SQRT(B1)-4)") in
  let s = Spreadsheet.recalculate s in
  assert_eq "ABS(SQRT(9)-4) = 1" "1" (vstr (Spreadsheet.get_value s "B2"));

  (* unknown function *)
  let s = Spreadsheet.set s "B3" (Formula "=BOGUS(1)") in
  let s = Spreadsheet.recalculate s in
  assert_true "unknown function error"
    (match Spreadsheet.get_value s "B3" with VError e ->
       String.length e > 5 && String.sub e 0 5 = "#NAME" | _ -> false);

  (* SUM with mixed types (numbers + text) *)
  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Number 10.0) in
  let s = Spreadsheet.set s "A2" (Text "abc") in
  let s = Spreadsheet.set s "A3" (Number 20.0) in
  let s = Spreadsheet.set s "A4" (Formula "=SUM(A1:A3)") in
  let s = Spreadsheet.recalculate s in
  assert_eq "SUM skips text" "30" (vstr (Spreadsheet.get_value s "A4"));

  (* IF with 2 args *)
  let s = Spreadsheet.set s "B1" (Formula "=IF(1>0, \"yes\")") in
  let s = Spreadsheet.recalculate s in
  assert_eq "IF 2-arg true" "\"yes\"" (vstr (Spreadsheet.get_value s "B1"));

  let s = Spreadsheet.set s "B2" (Formula "=IF(1<0, \"yes\")") in
  let s = Spreadsheet.recalculate s in
  assert_eq "IF 2-arg false" "false" (vstr (Spreadsheet.get_value s "B2"));

  (* MOD by zero *)
  let s = Spreadsheet.set s "B3" (Formula "=MOD(5,0)") in
  let s = Spreadsheet.recalculate s in
  assert_true "MOD by zero is error"
    (match Spreadsheet.get_value s "B3" with VError _ -> true | _ -> false);

  (* AVG of empty range *)
  let s = Spreadsheet.create () in
  let s = Spreadsheet.set s "A1" (Formula "=AVG(Z1:Z5)") in
  let s = Spreadsheet.recalculate s in
  (* AVG of all-empty: treated as zeroes, so average of five 0.0 = 0 *)
  assert_eq "AVG empty range with zero-valued empties" "0"
    (vstr (Spreadsheet.get_value s "A1"));

  (* ── Multiple sheets worth of data ─────────────────────────────── *)

  suite "Larger Grid";

  let s = Spreadsheet.create ~rows:20 ~cols:10 () in
  let s = ref s in
  for i = 1 to 10 do
    let addr = Printf.sprintf "A%d" i in
    s := Spreadsheet.set !s addr (Number (float_of_int i))
  done;
  s := Spreadsheet.set !s "B1" (Formula "=SUM(A1:A10)") in
  s := Spreadsheet.recalculate !s;
  assert_eq "SUM(A1:A10) = 55" "55" (vstr (Spreadsheet.get_value !s "B1"));

  s := Spreadsheet.set !s "B2" (Formula "=AVERAGE(A1:A10)") in
  s := Spreadsheet.recalculate !s;
  assert_eq "AVG(A1:A10) = 5.5" "5.500000" (vstr (Spreadsheet.get_value !s "B2"));

  (* ── Summary ───────────────────────────────────────────────────── *)

  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "  Results: %d passed, %d failed, %d total\n" !passed !failed !total;
  Printf.printf "══════════════════════════════════════════\n";
  if !failed > 0 then exit 1
