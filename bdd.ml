(* Binary Decision Diagram (BDD) — Reduced Ordered BDDs with memoized operations
 *
 * BDDs are canonical representations of Boolean functions. This implementation
 * provides:
 * - ROBDD construction with variable ordering
 * - Boolean operations (AND, OR, NOT, XOR, IMPLIES, IFF) via Apply algorithm
 * - Shannon expansion and cofactoring
 * - Satisfiability: SAT, TAUT, counting, all-SAT enumeration
 * - Variable restriction (setting a variable to true/false)
 * - Quantification (existential, universal, unique)
 * - If-Then-Else (ITE) with computed table
 * - DOT graph export for visualization
 * - Interactive REPL for building and querying BDDs
 *
 * Usage: ocaml bdd.ml
 *)

(* ══════════════════════════════════════════════════════════════════════════════
   Core BDD type and unique table
   ══════════════════════════════════════════════════════════════════════════════ *)

type bdd =
  | Zero
  | One
  | Node of int * bdd * bdd  (* variable, low branch, high branch *)

(* Unique table for hash-consing *)
let unique_table : (int * int * int, bdd) Hashtbl.t = Hashtbl.create 1024
let node_id_table : (bdd, int) Hashtbl.t = Hashtbl.create 1024
let next_id = ref 2  (* 0=Zero, 1=One *)

let bdd_id node =
  match node with
  | Zero -> 0
  | One -> 1
  | _ ->
    (try Hashtbl.find node_id_table node
     with Not_found ->
       let id = !next_id in
       incr next_id;
       Hashtbl.add node_id_table node id;
       id)

let mk var low high =
  if low == high then low  (* redundancy elimination *)
  else
    let key = (var, bdd_id low, bdd_id high) in
    try Hashtbl.find unique_table key
    with Not_found ->
      let node = Node (var, low, high) in
      Hashtbl.add unique_table key node;
      ignore (bdd_id node);
      node

(* ══════════════════════════════════════════════════════════════════════════════
   Variable creation
   ══════════════════════════════════════════════════════════════════════════════ *)

let bdd_var v = mk v Zero One
let bdd_nvar v = mk v One Zero
let bdd_true = One
let bdd_false = Zero

(* ══════════════════════════════════════════════════════════════════════════════
   Apply algorithm — generic Boolean operation on two BDDs
   ══════════════════════════════════════════════════════════════════════════════ *)

let apply_cache : ((int * int * string), bdd) Hashtbl.t = Hashtbl.create 4096

let var_of = function
  | Node (v, _, _) -> v
  | _ -> max_int

let low_of = function
  | Node (_, l, _) -> l
  | _ -> failwith "low_of: terminal"

let high_of = function
  | Node (_, _, h) -> h
  | _ -> failwith "high_of: terminal"

let rec apply op f g =
  (* Terminal cases *)
  let result = match op with
    | "and" -> (match f, g with
        | Zero, _ | _, Zero -> Some Zero
        | One, x | x, One -> Some x
        | _ -> None)
    | "or" -> (match f, g with
        | One, _ | _, One -> Some One
        | Zero, x | x, Zero -> Some x
        | _ -> None)
    | "xor" -> (match f, g with
        | Zero, x | x, Zero -> Some x
        | One, One -> Some Zero
        | _ -> None)
    | "nand" -> (match f, g with
        | Zero, _ | _, Zero -> Some One
        | One, One -> Some Zero
        | _ -> None)
    | "nor" -> (match f, g with
        | One, _ | _, One -> Some Zero
        | Zero, Zero -> Some One
        | _ -> None)
    | "implies" -> (match f, g with
        | Zero, _ -> Some One
        | One, x -> Some x
        | _, One -> Some One
        | _ -> None)
    | "iff" -> (match f, g with
        | Zero, Zero | One, One -> Some One
        | Zero, One | One, Zero -> Some Zero
        | _ -> None)
    | _ -> None
  in
  match result with
  | Some r -> r
  | None ->
    let key = (bdd_id f, bdd_id g, op) in
    try Hashtbl.find apply_cache key
    with Not_found ->
      let vf = var_of f and vg = var_of g in
      let v = min vf vg in
      let fl = if vf = v then low_of f else f in
      let fh = if vf = v then high_of f else f in
      let gl = if vg = v then low_of g else g in
      let gh = if vg = v then high_of g else g in
      let low = apply op fl gl in
      let high = apply op fh gh in
      let res = mk v low high in
      Hashtbl.add apply_cache key res;
      res

let bdd_and a b = apply "and" a b
let bdd_or a b = apply "or" a b
let bdd_xor a b = apply "xor" a b
let bdd_nand a b = apply "nand" a b
let bdd_nor a b = apply "nor" a b
let bdd_implies a b = apply "implies" a b
let bdd_iff a b = apply "iff" a b

let rec bdd_not = function
  | Zero -> One
  | One -> Zero
  | Node (v, l, h) -> mk v (bdd_not l) (bdd_not h)

(* ══════════════════════════════════════════════════════════════════════════════
   ITE (If-Then-Else) — the universal BDD operation
   ══════════════════════════════════════════════════════════════════════════════ *)

let ite_cache : ((int * int * int), bdd) Hashtbl.t = Hashtbl.create 4096

let rec ite f g h =
  match f with
  | One -> g
  | Zero -> h
  | _ when g = One && h = Zero -> f
  | _ when g = Zero && h = One -> bdd_not f
  | _ when g == h -> g
  | _ ->
    let key = (bdd_id f, bdd_id g, bdd_id h) in
    try Hashtbl.find ite_cache key
    with Not_found ->
      let vf = var_of f and vg = var_of g and vh = var_of h in
      let v = min vf (min vg vh) in
      let split b = if var_of b = v then (low_of b, high_of b) else (b, b) in
      let (fl, fh) = split f in
      let (gl, gh) = split g in
      let (hl, hh) = split h in
      let low = ite fl gl hl in
      let high = ite fh gh hh in
      let res = mk v low high in
      Hashtbl.add ite_cache key res;
      res

(* ══════════════════════════════════════════════════════════════════════════════
   Restriction — set a variable to a constant
   ══════════════════════════════════════════════════════════════════════════════ *)

let rec restrict bdd var value =
  match bdd with
  | Zero | One -> bdd
  | Node (v, l, h) ->
    if v = var then
      if value then restrict h var value
      else restrict l var value
    else if v > var then bdd
    else mk v (restrict l var value) (restrict h var value)

(* ══════════════════════════════════════════════════════════════════════════════
   Cofactors (Shannon expansion)
   ══════════════════════════════════════════════════════════════════════════════ *)

let positive_cofactor bdd var = restrict bdd var true
let negative_cofactor bdd var = restrict bdd var false

(* ══════════════════════════════════════════════════════════════════════════════
   Quantification
   ══════════════════════════════════════════════════════════════════════════════ *)

let exists var bdd =
  bdd_or (restrict bdd var true) (restrict bdd var false)

let forall var bdd =
  bdd_and (restrict bdd var true) (restrict bdd var false)

let unique var bdd =
  bdd_xor (restrict bdd var true) (restrict bdd var false)

(* ══════════════════════════════════════════════════════════════════════════════
   Satisfiability
   ══════════════════════════════════════════════════════════════════════════════ *)

let is_sat bdd = bdd <> Zero
let is_taut bdd = bdd = One

(* Count satisfying assignments for n variables *)
let rec sat_count n bdd =
  match bdd with
  | Zero -> 0.0
  | One -> 2.0 ** (float_of_int n)
  | Node (v, l, h) ->
    let low_count = sat_count n l in
    let high_count = sat_count n h in
    let low_scale = match l with
      | Node (v', _, _) -> 2.0 ** (float_of_int (v' - v - 1))
      | _ -> 2.0 ** (float_of_int (n - v - 1))
    in
    let high_scale = match h with
      | Node (v', _, _) -> 2.0 ** (float_of_int (v' - v - 1))
      | _ -> 2.0 ** (float_of_int (n - v - 1))
    in
    ignore low_scale; ignore high_scale;
    (* Simple counting: each branch contributes its count *)
    let rec count_paths = function
      | Zero -> 0
      | One -> 1
      | Node (_, l, h) -> count_paths l + count_paths h
    in
    float_of_int (count_paths bdd) *. (2.0 ** float_of_int (n - (num_vars bdd)))

and num_vars bdd =
  let vars = Hashtbl.create 16 in
  let rec collect = function
    | Zero | One -> ()
    | Node (v, l, h) ->
      Hashtbl.replace vars v ();
      collect l; collect h
  in
  collect bdd;
  Hashtbl.length vars

(* Enumerate all satisfying assignments *)
let all_sat bdd =
  let results = ref [] in
  let rec find path = function
    | Zero -> ()
    | One -> results := List.rev path :: !results
    | Node (v, l, h) ->
      find ((v, false) :: path) l;
      find ((v, true) :: path) h
  in
  find [] bdd;
  List.rev !results

(* Find one satisfying assignment *)
let any_sat bdd =
  let rec find path = function
    | Zero -> None
    | One -> Some (List.rev path)
    | Node (v, l, h) ->
      match find ((v, false) :: path) l with
      | Some _ as r -> r
      | None -> find ((v, true) :: path) h
  in
  find [] bdd

(* ══════════════════════════════════════════════════════════════════════════════
   BDD statistics
   ══════════════════════════════════════════════════════════════════════════════ *)

let node_count bdd =
  let seen = Hashtbl.create 64 in
  let rec count node =
    let id = bdd_id node in
    if Hashtbl.mem seen id then 0
    else begin
      Hashtbl.add seen id ();
      match node with
      | Zero | One -> 1
      | Node (_, l, h) -> 1 + count l + count h
    end
  in
  count bdd

let variables bdd =
  let vars = Hashtbl.create 16 in
  let rec collect = function
    | Zero | One -> ()
    | Node (v, l, h) ->
      Hashtbl.replace vars v ();
      collect l; collect h
  in
  collect bdd;
  Hashtbl.fold (fun k () acc -> k :: acc) vars []
  |> List.sort compare

let path_count bdd =
  let rec count = function
    | Zero -> 0
    | One -> 1
    | Node (_, l, h) -> count l + count h
  in
  count bdd

(* ══════════════════════════════════════════════════════════════════════════════
   DOT export for visualization
   ══════════════════════════════════════════════════════════════════════════════ *)

let to_dot ?(name="BDD") bdd =
  let buf = Buffer.create 256 in
  let seen = Hashtbl.create 64 in
  let add s = Buffer.add_string buf s; Buffer.add_char buf '\n' in
  add (Printf.sprintf "digraph %s {" name);
  add "  rankdir=TB;";
  add "  node [shape=circle];";
  add (Printf.sprintf "  0 [label=\"0\" shape=box style=filled fillcolor=\"#ffcccc\"];");
  add (Printf.sprintf "  1 [label=\"1\" shape=box style=filled fillcolor=\"#ccffcc\"];");
  let rec visit node =
    let id = bdd_id node in
    if not (Hashtbl.mem seen id) then begin
      Hashtbl.add seen id ();
      match node with
      | Zero | One -> ()
      | Node (v, l, h) ->
        add (Printf.sprintf "  %d [label=\"x%d\"];" id v);
        add (Printf.sprintf "  %d -> %d [style=dashed label=\"0\"];" id (bdd_id l));
        add (Printf.sprintf "  %d -> %d [label=\"1\"];" id (bdd_id h));
        visit l; visit h
    end
  in
  visit bdd;
  (* Group nodes by variable for rank alignment *)
  let var_nodes = Hashtbl.create 16 in
  let rec collect = function
    | Zero | One -> ()
    | Node (v, l, h) as n ->
      let id = bdd_id n in
      let existing = try Hashtbl.find var_nodes v with Not_found -> [] in
      Hashtbl.replace var_nodes v (id :: existing);
      collect l; collect h
  in
  collect bdd;
  Hashtbl.iter (fun _ ids ->
    let ids_str = List.map string_of_int ids |> String.concat "; " in
    add (Printf.sprintf "  { rank=same; %s }" ids_str)
  ) var_nodes;
  add "}";
  Buffer.contents buf

(* ══════════════════════════════════════════════════════════════════════════════
   Pretty printing
   ══════════════════════════════════════════════════════════════════════════════ *)

let rec to_string = function
  | Zero -> "0"
  | One -> "1"
  | Node (v, l, h) ->
    Printf.sprintf "(x%d ? %s : %s)" v (to_string h) (to_string l)

let to_expr = function
  | Zero -> "FALSE"
  | One -> "TRUE"
  | bdd ->
    let sats = all_sat bdd in
    if sats = [] then "FALSE"
    else
      let term_str assignment =
        let parts = List.map (fun (v, b) ->
          if b then Printf.sprintf "x%d" v
          else Printf.sprintf "¬x%d" v
        ) assignment in
        String.concat " ∧ " parts
      in
      let terms = List.map term_str sats in
      String.concat " ∨ " terms

let print_truth_table bdd =
  let vars = variables bdd in
  let n = List.length vars in
  (* Header *)
  List.iter (fun v -> Printf.printf "x%d  " v) vars;
  Printf.printf "│ f\n";
  List.iter (fun _ -> Printf.printf "────") vars;
  Printf.printf "┼──\n";
  (* Rows *)
  for i = 0 to (1 lsl n) - 1 do
    let assignment = List.mapi (fun j v ->
      let bit = (i lsr (n - 1 - j)) land 1 = 1 in
      (v, bit)
    ) vars in
    List.iter (fun (_, b) ->
      Printf.printf " %d  " (if b then 1 else 0)
    ) assignment;
    let result = List.fold_left (fun b (v, value) ->
      restrict b v value
    ) bdd assignment in
    Printf.printf "│ %d\n" (if result = One then 1 else 0)
  done

(* ══════════════════════════════════════════════════════════════════════════════
   Compose — replace variable with another BDD
   ══════════════════════════════════════════════════════════════════════════════ *)

let rec compose bdd var replacement =
  match bdd with
  | Zero | One -> bdd
  | Node (v, l, h) ->
    if v = var then
      ite replacement (compose h var replacement) (compose l var replacement)
    else if v > var then bdd
    else mk v (compose l var replacement) (compose h var replacement)

(* ══════════════════════════════════════════════════════════════════════════════
   Boolean function builder helpers
   ══════════════════════════════════════════════════════════════════════════════ *)

(* Majority function: at least k of n variables are true *)
let majority vars =
  let n = List.length vars in
  let k = (n + 1) / 2 in
  (* Build BDD for "at least k true" using DP *)
  let var_arr = Array.of_list vars in
  let memo = Hashtbl.create 64 in
  let rec build i need =
    if need = 0 then One
    else if i >= n then Zero
    else if n - i < need then Zero  (* not enough vars left *)
    else
      let key = (i, need) in
      try Hashtbl.find memo key
      with Not_found ->
        let skip = build (i + 1) need in
        let take = build (i + 1) (need - 1) in
        let res = mk var_arr.(i) skip take in
        Hashtbl.add memo key res;
        res
  in
  build 0 k

(* Parity: XOR of all variables *)
let parity vars =
  List.fold_left (fun acc v -> bdd_xor acc (bdd_var v)) Zero vars

(* Exactly-one: exactly one variable is true *)
let exactly_one vars =
  let n = List.length vars in
  let var_arr = Array.of_list vars in
  let memo = Hashtbl.create 64 in
  let rec build i count =
    if count > 1 then Zero
    else if i >= n then (if count = 1 then One else Zero)
    else
      let key = (i, count) in
      try Hashtbl.find memo key
      with Not_found ->
        let skip = build (i + 1) count in
        let take = build (i + 1) (count + 1) in
        let res = mk var_arr.(i) skip take in
        Hashtbl.add memo key res;
        res
  in
  build 0 0

(* ══════════════════════════════════════════════════════════════════════════════
   Expression parser for the REPL
   ══════════════════════════════════════════════════════════════════════════════ *)

type token =
  | TVar of int
  | TTrue | TFalse
  | TAnd | TOr | TXor | TNot | TImplies | TIff
  | TLParen | TRParen
  | TEOF

let tokenize input =
  let tokens = ref [] in
  let i = ref 0 in
  let len = String.length input in
  while !i < len do
    match input.[!i] with
    | ' ' | '\t' -> incr i
    | '(' -> tokens := TLParen :: !tokens; incr i
    | ')' -> tokens := TRParen :: !tokens; incr i
    | '&' | '∧' -> tokens := TAnd :: !tokens; incr i
    | '|' | '∨' -> tokens := TOr :: !tokens; incr i
    | '^' | '⊕' -> tokens := TXor :: !tokens; incr i
    | '!' | '¬' | '~' -> tokens := TNot :: !tokens; incr i
    | '0' -> tokens := TFalse :: !tokens; incr i
    | '1' when !i + 1 >= len || input.[!i + 1] <> 'x' ->
      tokens := TTrue :: !tokens; incr i
    | 'x' | 'X' ->
      incr i;
      let start = !i in
      while !i < len && input.[!i] >= '0' && input.[!i] <= '9' do incr i done;
      if start = !i then failwith "Expected variable number after 'x'"
      else
        let n = int_of_string (String.sub input start (!i - start)) in
        tokens := TVar n :: !tokens
    | '-' when !i + 1 < len && input.[!i + 1] = '>' ->
      tokens := TImplies :: !tokens; i := !i + 2
    | '<' when !i + 2 < len && input.[!i + 1] = '-' && input.[!i + 2] = '>' ->
      tokens := TIff :: !tokens; i := !i + 3
    | '=' when !i + 1 < len && input.[!i + 1] = '>' ->
      tokens := TImplies :: !tokens; i := !i + 2
    | c -> failwith (Printf.sprintf "Unexpected character: '%c'" c)
  done;
  List.rev (TEOF :: !tokens)

(* Recursive descent parser: iff < implies < or < xor < and < not < atom *)
let parse_expr input =
  let tokens = ref (tokenize input) in
  let peek () = match !tokens with t :: _ -> t | [] -> TEOF in
  let advance () = match !tokens with _ :: rest -> tokens := rest | [] -> () in
  let expect t =
    if peek () = t then advance ()
    else failwith "Unexpected token"
  in
  let rec parse_iff () =
    let left = parse_implies () in
    if peek () = TIff then begin
      advance (); let right = parse_iff () in bdd_iff left right
    end else left
  and parse_implies () =
    let left = parse_or () in
    if peek () = TImplies then begin
      advance (); let right = parse_implies () in bdd_implies left right
    end else left
  and parse_or () =
    let left = ref (parse_xor ()) in
    while peek () = TOr do advance (); left := bdd_or !left (parse_xor ()) done;
    !left
  and parse_xor () =
    let left = ref (parse_and ()) in
    while peek () = TXor do advance (); left := bdd_xor !left (parse_and ()) done;
    !left
  and parse_and () =
    let left = ref (parse_not ()) in
    while peek () = TAnd do advance (); left := bdd_and !left (parse_not ()) done;
    !left
  and parse_not () =
    if peek () = TNot then begin advance (); bdd_not (parse_not ()) end
    else parse_atom ()
  and parse_atom () =
    match peek () with
    | TVar n -> advance (); bdd_var n
    | TTrue -> advance (); One
    | TFalse -> advance (); Zero
    | TLParen ->
      advance ();
      let e = parse_iff () in
      expect TRParen; e
    | _ -> failwith "Expected variable, constant, or '('"
  in
  let result = parse_iff () in
  if peek () <> TEOF then failwith "Unexpected tokens after expression";
  result

(* ══════════════════════════════════════════════════════════════════════════════
   Demo: Classic examples
   ══════════════════════════════════════════════════════════════════════════════ *)

let demo () =
  Printf.printf "╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║     Binary Decision Diagrams (BDDs) in OCaml                ║\n";
  Printf.printf "║     Reduced Ordered BDDs with Apply Algorithm               ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n\n";

  (* Example 1: Simple Boolean expression *)
  Printf.printf "━━━ Example 1: f = (x0 ∧ x1) ∨ x2 ━━━\n\n";
  let x0 = bdd_var 0 in
  let x1 = bdd_var 1 in
  let x2 = bdd_var 2 in
  let f = bdd_or (bdd_and x0 x1) x2 in
  Printf.printf "Expression: %s\n" (to_string f);
  Printf.printf "Nodes: %d\n" (node_count f);
  Printf.printf "Variables: [%s]\n" (String.concat ", " (List.map (fun v -> "x" ^ string_of_int v) (variables f)));
  Printf.printf "SAT paths: %d\n" (path_count f);
  Printf.printf "Satisfiable: %b\n" (is_sat f);
  Printf.printf "Tautology: %b\n\n" (is_taut f);

  Printf.printf "Truth table:\n";
  print_truth_table f;
  Printf.printf "\n";

  Printf.printf "DNF: %s\n\n" (to_expr f);

  (* Example 2: Tautology check *)
  Printf.printf "━━━ Example 2: Tautology — x0 ∨ ¬x0 ━━━\n\n";
  let taut = bdd_or x0 (bdd_not x0) in
  Printf.printf "x0 ∨ ¬x0 = %s (tautology: %b)\n\n" (to_string taut) (is_taut taut);

  (* Example 3: Satisfying assignments *)
  Printf.printf "━━━ Example 3: All satisfying assignments of f ━━━\n\n";
  let sats = all_sat f in
  List.iteri (fun i assignment ->
    let s = List.map (fun (v, b) ->
      Printf.sprintf "x%d=%d" v (if b then 1 else 0)
    ) assignment in
    Printf.printf "  #%d: {%s}\n" (i + 1) (String.concat ", " s)
  ) sats;
  Printf.printf "\n";

  (* Example 4: Restriction *)
  Printf.printf "━━━ Example 4: Restriction — f|x2=1 ━━━\n\n";
  let restricted = restrict f 2 true in
  Printf.printf "f|x2=1 = %s\n" (to_string restricted);
  Printf.printf "  (should be TRUE since x2=1 makes f true)\n\n";

  (* Example 5: Quantification *)
  Printf.printf "━━━ Example 5: Existential quantification — ∃x2. f ━━━\n\n";
  let ex = exists 2 f in
  Printf.printf "∃x2. f = %s\n" (to_string ex);
  Printf.printf "  (TRUE, since x2 can always be set to 1)\n\n";

  (* Example 6: Majority function *)
  Printf.printf "━━━ Example 6: Majority of {x0, x1, x2} ━━━\n\n";
  let maj = majority [0; 1; 2] in
  Printf.printf "majority(x0,x1,x2):\n";
  print_truth_table maj;
  Printf.printf "Nodes: %d\n\n" (node_count maj);

  (* Example 7: Parity *)
  Printf.printf "━━━ Example 7: Parity (XOR) of {x0, x1, x2} ━━━\n\n";
  let par = parity [0; 1; 2] in
  Printf.printf "parity(x0,x1,x2):\n";
  print_truth_table par;
  Printf.printf "Nodes: %d\n\n" (node_count par);

  (* Example 8: DOT export *)
  Printf.printf "━━━ Example 8: DOT graph export ━━━\n\n";
  let dot = to_dot ~name:"example" f in
  Printf.printf "%s\n" dot;

  Printf.printf "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"

(* ══════════════════════════════════════════════════════════════════════════════
   Interactive REPL
   ══════════════════════════════════════════════════════════════════════════════ *)

let repl () =
  Printf.printf "\n🔹 BDD Interactive REPL\n";
  Printf.printf "   Enter Boolean expressions using: x0, x1, ... (variables)\n";
  Printf.printf "   Operators: & (AND), | (OR), ^ (XOR), ! (NOT), -> (IMPLIES), <-> (IFF)\n";
  Printf.printf "   Commands: :truth, :sat, :dot, :vars, :nodes, :demo, :quit\n\n";
  let env : (string, bdd) Hashtbl.t = Hashtbl.create 16 in
  let last = ref None in
  try while true do
    Printf.printf "bdd> %!";
    let line = input_line stdin in
    let line = String.trim line in
    if line = "" then ()
    else if line = ":quit" || line = ":q" then raise Exit
    else if line = ":demo" then demo ()
    else if line = ":truth" then
      (match !last with
       | Some b -> print_truth_table b
       | None -> Printf.printf "No expression. Enter one first.\n")
    else if line = ":sat" then
      (match !last with
       | Some b ->
         let sats = all_sat b in
         if sats = [] then Printf.printf "UNSAT\n"
         else List.iteri (fun i a ->
           let s = List.map (fun (v, b) ->
             Printf.sprintf "x%d=%d" v (if b then 1 else 0)
           ) a in
           Printf.printf "  #%d: {%s}\n" (i + 1) (String.concat ", " s)
         ) sats
       | None -> Printf.printf "No expression.\n")
    else if line = ":dot" then
      (match !last with
       | Some b -> Printf.printf "%s\n" (to_dot b)
       | None -> Printf.printf "No expression.\n")
    else if line = ":vars" then
      (match !last with
       | Some b ->
         Printf.printf "Variables: [%s]\n"
           (String.concat ", " (List.map (fun v -> "x" ^ string_of_int v) (variables b)))
       | None -> Printf.printf "No expression.\n")
    else if line = ":nodes" then
      (match !last with
       | Some b -> Printf.printf "Nodes: %d, Paths: %d\n" (node_count b) (path_count b)
       | None -> Printf.printf "No expression.\n")
    else if String.length line > 4 && String.sub line 0 4 = "let " then begin
      (* let name = expr *)
      try
        let eq_pos = String.index line '=' in
        let name = String.trim (String.sub line 4 (eq_pos - 4)) in
        let expr_str = String.trim (String.sub line (eq_pos + 1) (String.length line - eq_pos - 1)) in
        let b = parse_expr expr_str in
        Hashtbl.replace env name b;
        last := Some b;
        Printf.printf "%s = %s  [%d nodes]\n" name (to_string b) (node_count b)
      with _ -> Printf.printf "Syntax: let name = expression\n"
    end
    else begin
      try
        let b = parse_expr line in
        last := Some b;
        Printf.printf "= %s\n" (to_string b);
        Printf.printf "  SAT: %b | TAUT: %b | Nodes: %d | Paths: %d\n"
          (is_sat b) (is_taut b) (node_count b) (path_count b)
      with Failure msg ->
        Printf.printf "Error: %s\n" msg
    end
  done with
  | Exit -> Printf.printf "Bye!\n"
  | End_of_file -> Printf.printf "\nBye!\n"

(* ══════════════════════════════════════════════════════════════════════════════
   Main
   ══════════════════════════════════════════════════════════════════════════════ *)

let () =
  demo ();
  repl ()
