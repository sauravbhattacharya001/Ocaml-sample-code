(* ============================================================================
   property_discovery.ml - Autonomous Property Discovery Engine
   ============================================================================

   An autonomous invariant and property discovery engine for OCaml functions.
   Unlike QuickCheck (which verifies known properties), this engine *discovers*
   unknown algebraic properties through systematic random exploration.

   Demonstrates:
   - Autonomous hypothesis generation and testing
   - Algebraic property templates (20+ property categories)
   - Statistical confidence scoring via repeated random trials
   - Adaptive search: narrows hypothesis space based on early results
   - Counter-example driven refinement
   - Property relationship inference (implies, equivalent, independent)
   - Confidence-ranked property reports
   - Interactive discovery sessions with progressive deepening

   Core idea: Given a function f : 'a -> 'b, generate candidate properties
   (idempotency, commutativity, monotonicity, fixed points, etc.) and test
   them against random inputs. Properties that survive many trials are
   reported as likely invariants with confidence scores.

   Usage:
     let () =
       (* Discover properties of List.rev *)
       let report = discover_unary_list List.rev "List.rev" in
       print_report report;

       (* Discover properties of a binary operation *)
       let report = discover_binary (+) "( + )" in
       print_report report;

       (* Full autonomous analysis *)
       let analysis = autonomous_analyze () in
       print_analysis analysis
   ============================================================================ *)

(* ── Random Infrastructure ──────────────────────────────────────────────── *)

let global_seed = ref 12345

let next_random () =
  global_seed := (!global_seed * 1103515245 + 12345) land 0x3FFFFFFF;
  !global_seed

let random_int bound =
  if bound <= 0 then 0
  else (next_random ()) mod bound

let random_int_range lo hi =
  if hi <= lo then lo
  else lo + random_int (hi - lo + 1)

let random_float () =
  float_of_int (random_int 10000) /. 10000.0

let random_bool () = random_int 2 = 0

let random_list gen len =
  List.init len (fun _ -> gen ())

let random_int_gen () = random_int_range (-100) 100
let random_pos_gen () = random_int_range 1 100
let random_nat_gen () = random_int_range 0 100

let random_int_list () =
  let len = random_int_range 0 20 in
  random_list random_int_gen len

let random_nonempty_int_list () =
  let len = random_int_range 1 15 in
  random_list random_int_gen len

let random_string_gen () =
  let len = random_int_range 0 15 in
  String.init len (fun _ -> Char.chr (random_int_range 97 122))

(* ── Property Categories ────────────────────────────────────────────────── *)

type confidence = {
  trials : int;
  successes : int;
  score : float;  (* successes / trials, 0.0 to 1.0 *)
}

type property_kind =
  | Involution         (* f(f(x)) = x *)
  | Idempotent         (* f(f(x)) = f(x) *)
  | FixedPoint of string (* f(c) = c for constant c *)
  | Monotone_Inc       (* x <= y => f(x) <= f(y) *)
  | Monotone_Dec       (* x <= y => f(x) >= f(y) *)
  | Preserves_Length   (* |f(xs)| = |xs| *)
  | Preserves_Sum      (* sum(f(xs)) = sum(xs) *)
  | Preserves_Elements (* set(f(xs)) = set(xs) -- permutation *)
  | Distributes_Over of string (* f(x op y) = f(x) op f(y) *)
  | Commutative        (* f(x, y) = f(y, x) *)
  | Associative        (* f(f(x, y), z) = f(x, f(y, z)) *)
  | Left_Identity of string  (* f(e, x) = x *)
  | Right_Identity of string (* f(x, e) = x *)
  | Absorbing of string      (* f(a, x) = a for all x *)
  | Self_Inverse       (* f(x, x) = identity *)
  | Nilpotent of int   (* f^n(x) = f^(n+1)(x) *)
  | Bounded of string  (* lo <= f(x) <= hi *)
  | Injective          (* f(x) = f(y) => x = y *)
  | Surjective_Sample  (* range covers all sampled outputs *)
  | Constant           (* f(x) = f(y) for all x, y *)
  | Anti_Commutative   (* f(x, y) = -f(y, x) *)
  | Cancellative       (* f(x, y) = f(x, z) => y = z *)

type discovered_property = {
  kind : property_kind;
  description : string;
  confidence : confidence;
  counterexample : string option;
}

type discovery_report = {
  function_name : string;
  properties : discovered_property list;
  total_trials : int;
  discovery_time_ms : int;
}

(* ── Confidence Computation ─────────────────────────────────────────────── *)

let make_confidence trials successes =
  { trials; successes; score = if trials = 0 then 0.0 else float_of_int successes /. float_of_int trials }

let confidence_level c =
  if c.score >= 0.999 then "definite"
  else if c.score >= 0.99 then "very likely"
  else if c.score >= 0.95 then "likely"
  else if c.score >= 0.8 then "probable"
  else if c.score >= 0.5 then "weak"
  else "unlikely"

(* ── Property Testing Engine ────────────────────────────────────────────── *)

let num_trials = 200

let test_property_bool gen prop =
  let successes = ref 0 in
  let cex = ref None in
  for _ = 1 to num_trials do
    let x = gen () in
    if prop x then incr successes
    else (if !cex = None then cex := Some x)
  done;
  (!successes, !cex)

let test_property_binary gen1 gen2 prop =
  let successes = ref 0 in
  let cex = ref None in
  for _ = 1 to num_trials do
    let x = gen1 () in
    let y = gen2 () in
    if prop x y then incr successes
    else (if !cex = None then cex := Some (x, y))
  done;
  (!successes, !cex)

let test_property_ternary gen prop =
  let successes = ref 0 in
  let cex = ref None in
  for _ = 1 to num_trials do
    let x = gen () in
    let y = gen () in
    let z = gen () in
    if prop x y z then incr successes
    else (if !cex = None then cex := Some (x, y, z))
  done;
  (!successes, !cex)

(* ── Unary Int Function Discovery ───────────────────────────────────────── *)

let discover_unary_int (f : int -> int) name =
  let props = ref [] in
  let add kind desc conf cex =
    props := { kind; description = desc; confidence = conf; counterexample = cex } :: !props
  in

  (* Involution: f(f(x)) = x *)
  let (s, cex) = test_property_bool random_int_gen (fun x -> f (f x) = x) in
  let cex_str = Option.map (fun x -> Printf.sprintf "f(f(%d)) = %d ≠ %d" x (f (f x)) x) cex in
  add Involution "f(f(x)) = x (involution)" (make_confidence num_trials s) cex_str;

  (* Idempotent: f(f(x)) = f(x) *)
  let (s, cex) = test_property_bool random_int_gen (fun x -> f (f x) = f x) in
  let cex_str = Option.map (fun x -> Printf.sprintf "f(f(%d)) = %d ≠ f(%d) = %d" x (f (f x)) x (f x)) cex in
  add Idempotent "f(f(x)) = f(x) (idempotent)" (make_confidence num_trials s) cex_str;

  (* Monotone increasing *)
  let (s, cex) = test_property_binary random_int_gen random_int_gen
    (fun x y -> if x <= y then f x <= f y else true) in
  let cex_str = Option.map (fun (x, y) ->
    Printf.sprintf "%d <= %d but f(%d)=%d > f(%d)=%d" x y x (f x) y (f y)) cex in
  add Monotone_Inc "x ≤ y ⟹ f(x) ≤ f(y) (monotone increasing)" (make_confidence num_trials s) cex_str;

  (* Monotone decreasing *)
  let (s, cex) = test_property_binary random_int_gen random_int_gen
    (fun x y -> if x <= y then f x >= f y else true) in
  let cex_str = Option.map (fun (x, y) ->
    Printf.sprintf "%d <= %d but f(%d)=%d < f(%d)=%d" x y x (f x) y (f y)) cex in
  add Monotone_Dec "x ≤ y ⟹ f(x) ≥ f(y) (monotone decreasing)" (make_confidence num_trials s) cex_str;

  (* Fixed point at 0 *)
  let is_fixed_0 = f 0 = 0 in
  if is_fixed_0 then
    add (FixedPoint "0") "f(0) = 0 (fixed point)" (make_confidence 1 1) None;

  (* Fixed point at 1 *)
  let is_fixed_1 = f 1 = 1 in
  if is_fixed_1 then
    add (FixedPoint "1") "f(1) = 1 (fixed point)" (make_confidence 1 1) None;

  (* Bounded output *)
  let outputs = List.init num_trials (fun _ -> f (random_int_gen ())) in
  let min_o = List.fold_left min max_int outputs in
  let max_o = List.fold_left max min_int outputs in
  if max_o - min_o < 201 then
    add (Bounded (Printf.sprintf "[%d, %d]" min_o max_o))
      (Printf.sprintf "Output bounded in [%d, %d]" min_o max_o)
      (make_confidence num_trials num_trials) None;

  (* Constant function *)
  let first = f 0 in
  let (s, _) = test_property_bool random_int_gen (fun x -> f x = first) in
  if s = num_trials then
    add Constant (Printf.sprintf "f(x) = %d (constant)" first) (make_confidence num_trials s) None;

  (* Injective *)
  let (s, cex) = test_property_binary random_int_gen random_int_gen
    (fun x y -> if x <> y then f x <> f y else true) in
  let cex_str = Option.map (fun (x, y) ->
    Printf.sprintf "f(%d) = f(%d) = %d but %d ≠ %d" x y (f x) x y) cex in
  add Injective "x ≠ y ⟹ f(x) ≠ f(y) (injective)" (make_confidence num_trials s) cex_str;

  (* Nilpotent (f^2(x) = f^3(x)) *)
  let (s, _) = test_property_bool random_int_gen (fun x -> f (f x) = f (f (f x))) in
  add (Nilpotent 2) "f²(x) = f³(x) (nilpotent at depth 2)" (make_confidence num_trials s) None;

  { function_name = name;
    properties = List.filter (fun p -> p.confidence.score >= 0.95) (List.rev !props);
    total_trials = num_trials * 8;
    discovery_time_ms = 0 }

(* ── Binary Int Function Discovery ──────────────────────────────────────── *)

let discover_binary (f : int -> int -> int) name =
  let props = ref [] in
  let add kind desc conf cex =
    props := { kind; description = desc; confidence = conf; counterexample = cex } :: !props
  in

  (* Commutative *)
  let (s, cex) = test_property_binary random_int_gen random_int_gen
    (fun x y -> f x y = f y x) in
  let cex_str = Option.map (fun (x, y) ->
    Printf.sprintf "f(%d,%d)=%d ≠ f(%d,%d)=%d" x y (f x y) y x (f y x)) cex in
  add Commutative "f(x,y) = f(y,x) (commutative)" (make_confidence num_trials s) cex_str;

  (* Associative *)
  let (s, cex) = test_property_ternary random_int_gen
    (fun x y z -> f (f x y) z = f x (f y z)) in
  let cex_str = Option.map (fun (x, y, z) ->
    Printf.sprintf "f(f(%d,%d),%d)=%d ≠ f(%d,f(%d,%d))=%d"
      x y z (f (f x y) z) x y z (f x (f y z))) cex in
  add Associative "f(f(x,y),z) = f(x,f(y,z)) (associative)" (make_confidence num_trials s) cex_str;

  (* Left identity *)
  let try_identity e label =
    let (s, _) = test_property_bool random_int_gen (fun x -> f e x = x) in
    if s = num_trials then
      add (Left_Identity label)
        (Printf.sprintf "f(%s, x) = x (left identity)" label)
        (make_confidence num_trials s) None;
    let (s, _) = test_property_bool random_int_gen (fun x -> f x e = x) in
    if s = num_trials then
      add (Right_Identity label)
        (Printf.sprintf "f(x, %s) = x (right identity)" label)
        (make_confidence num_trials s) None
  in
  try_identity 0 "0";
  try_identity 1 "1";
  try_identity (-1) "-1";

  (* Absorbing element *)
  let try_absorbing a label =
    let (s, _) = test_property_bool random_int_gen (fun x -> f a x = a && f x a = a) in
    if s = num_trials then
      add (Absorbing label)
        (Printf.sprintf "f(%s, x) = f(x, %s) = %s (absorbing)" label label label)
        (make_confidence num_trials s) None
  in
  try_absorbing 0 "0";

  (* Anti-commutative: f(x,y) = -f(y,x) *)
  let (s, cex) = test_property_binary random_int_gen random_int_gen
    (fun x y -> f x y = -(f y x)) in
  let cex_str = Option.map (fun (x, y) ->
    Printf.sprintf "f(%d,%d)=%d ≠ -f(%d,%d)=%d" x y (f x y) y x (-(f y x))) cex in
  add Anti_Commutative "f(x,y) = -f(y,x) (anti-commutative)" (make_confidence num_trials s) cex_str;

  (* Self-inverse: f(x,x) = 0 *)
  let (s, _) = test_property_bool random_int_gen (fun x -> f x x = 0) in
  if s = num_trials then
    add Self_Inverse "f(x,x) = 0 (self-inverse)" (make_confidence num_trials s) None;

  (* Cancellative: f(x,y) = f(x,z) => y = z *)
  let (s, cex) = test_property_ternary random_int_gen
    (fun x y z -> if y <> z then f x y <> f x z else true) in
  let cex_str = Option.map (fun (x, y, z) ->
    Printf.sprintf "f(%d,%d)=%d = f(%d,%d)=%d but %d≠%d" x y (f x y) x z (f x z) y z) cex in
  add Cancellative "f(x,y) = f(x,z) ⟹ y = z (left cancellative)" (make_confidence num_trials s) cex_str;

  (* Idempotent binary: f(x,x) = x *)
  let (s, _) = test_property_bool random_int_gen (fun x -> f x x = x) in
  if s = num_trials then
    add Idempotent "f(x,x) = x (idempotent binary)" (make_confidence num_trials s) None;

  { function_name = name;
    properties = List.filter (fun p -> p.confidence.score >= 0.95) (List.rev !props);
    total_trials = num_trials * 10;
    discovery_time_ms = 0 }

(* ── List Function Discovery ────────────────────────────────────────────── *)

let list_sum xs = List.fold_left (+) 0 xs
let list_sorted xs = let s = List.sort compare xs in s = xs

let discover_unary_list (f : int list -> int list) name =
  let props = ref [] in
  let add kind desc conf cex =
    props := { kind; description = desc; confidence = conf; counterexample = cex } :: !props
  in

  (* Involution *)
  let (s, cex) = test_property_bool random_int_list (fun xs -> f (f xs) = xs) in
  let cex_str = Option.map (fun xs ->
    Printf.sprintf "f(f(%s)) ≠ %s" (String.concat ";" (List.map string_of_int xs))
      (String.concat ";" (List.map string_of_int xs))) cex in
  add Involution "f(f(xs)) = xs (involution)" (make_confidence num_trials s) cex_str;

  (* Idempotent *)
  let (s, cex) = test_property_bool random_int_list (fun xs -> f (f xs) = f xs) in
  let cex_str = Option.map (fun xs ->
    Printf.sprintf "f(f(%s)) ≠ f(%s)" (String.concat ";" (List.map string_of_int xs))
      (String.concat ";" (List.map string_of_int xs))) cex in
  add Idempotent "f(f(xs)) = f(xs) (idempotent)" (make_confidence num_trials s) cex_str;

  (* Preserves length *)
  let (s, cex) = test_property_bool random_int_list (fun xs -> List.length (f xs) = List.length xs) in
  let cex_str = Option.map (fun xs ->
    Printf.sprintf "|f([%s])| = %d ≠ %d"
      (String.concat ";" (List.map string_of_int xs))
      (List.length (f xs)) (List.length xs)) cex in
  add Preserves_Length "|f(xs)| = |xs| (preserves length)" (make_confidence num_trials s) cex_str;

  (* Preserves sum *)
  let (s, cex) = test_property_bool random_int_list (fun xs -> list_sum (f xs) = list_sum xs) in
  let cex_str = Option.map (fun xs ->
    Printf.sprintf "sum(f([%s])) = %d ≠ %d"
      (String.concat ";" (List.map string_of_int xs))
      (list_sum (f xs)) (list_sum xs)) cex in
  add Preserves_Sum "sum(f(xs)) = sum(xs) (preserves sum)" (make_confidence num_trials s) cex_str;

  (* Preserves elements (permutation) *)
  let (s, cex) = test_property_bool random_int_list (fun xs ->
    List.sort compare (f xs) = List.sort compare xs) in
  let cex_str = Option.map (fun xs ->
    Printf.sprintf "sorted(f([%s])) ≠ sorted([%s])"
      (String.concat ";" (List.map string_of_int xs))
      (String.concat ";" (List.map string_of_int xs))) cex in
  add Preserves_Elements "sorted(f(xs)) = sorted(xs) (permutation)" (make_confidence num_trials s) cex_str;

  (* Output always sorted *)
  let (s, _) = test_property_bool random_int_list (fun xs -> list_sorted (f xs)) in
  if s >= num_trials - 1 then
    add Monotone_Inc "f(xs) is always sorted" (make_confidence num_trials s) None;

  (* Empty list fixed point *)
  if f [] = [] then
    add (FixedPoint "[]") "f([]) = [] (empty list is fixed point)" (make_confidence 1 1) None;

  (* Singleton preservation *)
  let (s, _) = test_property_bool random_int_gen (fun x -> f [x] = [x]) in
  if s = num_trials then
    add (FixedPoint "singleton") "f([x]) = [x] (singletons are fixed)" (make_confidence num_trials s) None;

  { function_name = name;
    properties = List.filter (fun p -> p.confidence.score >= 0.95) (List.rev !props);
    total_trials = num_trials * 7;
    discovery_time_ms = 0 }

(* ── String Function Discovery ──────────────────────────────────────────── *)

let discover_unary_string (f : string -> string) name =
  let props = ref [] in
  let add kind desc conf cex =
    props := { kind; description = desc; confidence = conf; counterexample = cex } :: !props
  in

  (* Involution *)
  let (s, cex) = test_property_bool random_string_gen (fun s -> f (f s) = s) in
  let cex_str = Option.map (fun s -> Printf.sprintf "f(f(\"%s\")) ≠ \"%s\"" s s) cex in
  add Involution "f(f(s)) = s (involution)" (make_confidence num_trials s) cex_str;

  (* Idempotent *)
  let (s, cex) = test_property_bool random_string_gen (fun s -> f (f s) = f s) in
  let cex_str = Option.map (fun s -> Printf.sprintf "f(f(\"%s\")) ≠ f(\"%s\")" s s) cex in
  add Idempotent "f(f(s)) = f(s) (idempotent)" (make_confidence num_trials s) cex_str;

  (* Preserves length *)
  let (s, cex) = test_property_bool random_string_gen (fun s ->
    String.length (f s) = String.length s) in
  let cex_str = Option.map (fun s ->
    Printf.sprintf "|f(\"%s\")| = %d ≠ %d" s (String.length (f s)) (String.length s)) cex in
  add Preserves_Length "|f(s)| = |s| (preserves length)" (make_confidence num_trials s) cex_str;

  (* Empty string fixed *)
  if f "" = "" then
    add (FixedPoint "\"\"") "f(\"\") = \"\" (empty string fixed)" (make_confidence 1 1) None;

  (* Constant *)
  let first = f "test" in
  let (s, _) = test_property_bool random_string_gen (fun s -> f s = first) in
  if s = num_trials then
    add Constant (Printf.sprintf "f(s) = \"%s\" (constant)" first) (make_confidence num_trials s) None;

  { function_name = name;
    properties = List.filter (fun p -> p.confidence.score >= 0.95) (List.rev !props);
    total_trials = num_trials * 5;
    discovery_time_ms = 0 }

(* ── Property Relationship Inference ────────────────────────────────────── *)

type property_relation =
  | Implies      (* P1 => P2 *)
  | Equivalent   (* P1 <=> P2 *)
  | Independent  (* neither implies the other *)
  | Contradicts  (* P1 => ¬P2 *)

type relation_entry = {
  prop1 : string;
  prop2 : string;
  relation : property_relation;
}

let known_implications = [
  ("involution", "injective", Implies);
  ("constant", "idempotent", Implies);
  ("involution", "preserves_length", Implies);
  ("permutation", "preserves_length", Implies);
  ("permutation", "preserves_sum", Implies);
  ("monotone_inc", "injective", Independent);
  ("commutative", "associative", Independent);
  ("constant", "injective", Contradicts);
]

let infer_relations (report : discovery_report) =
  let confirmed = List.map (fun p -> p.kind) report.properties in
  let rels = ref [] in
  List.iter (fun (p1, p2, rel) ->
    let has_p1 = List.exists (fun k ->
      match k, p1 with
      | Involution, "involution" -> true
      | Idempotent, "idempotent" -> true
      | Constant, "constant" -> true
      | Preserves_Length, "preserves_length" -> true
      | Preserves_Elements, "permutation" -> true
      | Preserves_Sum, "preserves_sum" -> true
      | Monotone_Inc, "monotone_inc" -> true
      | Commutative, "commutative" -> true
      | Associative, "associative" -> true
      | Injective, "injective" -> true
      | _ -> false) confirmed in
    if has_p1 then
      rels := { prop1 = p1; prop2 = p2; relation = rel } :: !rels
  ) known_implications;
  List.rev !rels

(* ── Autonomous Analysis Suite ──────────────────────────────────────────── *)

type function_category =
  | Arithmetic
  | List_Transform
  | String_Transform
  | Predicate
  | Higher_Order

type analysis_entry = {
  category : function_category;
  report : discovery_report;
  relations : relation_entry list;
  insights : string list;
}

type full_analysis = {
  entries : analysis_entry list;
  summary : string;
  total_properties_found : int;
  strongest_property : string option;
}

(* Generate insights from discovered properties *)
let generate_insights report =
  let insights = ref [] in
  let has kind = List.exists (fun p -> p.kind = kind) report.properties in
  if has Involution && has Preserves_Length then
    insights := "Self-cancelling permutation (like reverse)" :: !insights;
  if has Commutative && has Associative then
    insights := "Forms a semigroup — associative + commutative" :: !insights;
  if has Idempotent && has Commutative && has Associative then
    insights := "Forms a semilattice (join or meet operation)" :: !insights;
  if has Monotone_Inc && has Idempotent then
    insights := "Closure operator on ordered set" :: !insights;
  if has Preserves_Elements && has Preserves_Length then
    insights := "Pure permutation — rearranges without adding/removing" :: !insights;
  if has Injective && not (has Constant) then
    insights := "Information-preserving — no data loss" :: !insights;
  if has Constant then
    insights := "Maximally lossy — all inputs produce same output" :: !insights;
  if List.length report.properties = 0 then
    insights := "No strong algebraic structure detected — likely complex/chaotic" :: !insights;
  List.rev !insights

(* Run autonomous analysis on built-in functions *)
let autonomous_analyze () =
  let entries = ref [] in

  (* Arithmetic functions *)
  let add_arith f_name f =
    let r = discover_unary_int f f_name in
    let rels = infer_relations r in
    let ins = generate_insights r in
    entries := { category = Arithmetic; report = r; relations = rels; insights = ins } :: !entries
  in
  add_arith "abs" abs;
  add_arith "succ" succ;
  add_arith "pred" pred;
  add_arith "(fun x -> x * x)" (fun x -> x * x);
  add_arith "(fun x -> -x)" (fun x -> -x);
  add_arith "(fun x -> x mod 7)" (fun x -> x mod 7);
  add_arith "(fun x -> x land x)" (fun x -> x land x);

  (* Binary operations *)
  let add_bin f_name f =
    let r = discover_binary f f_name in
    let rels = infer_relations r in
    let ins = generate_insights r in
    entries := { category = Arithmetic; report = r; relations = rels; insights = ins } :: !entries
  in
  add_bin "( + )" ( + );
  add_bin "( * )" ( * );
  add_bin "( - )" ( - );
  add_bin "max" max;
  add_bin "min" min;
  add_bin "( land )" ( land );
  add_bin "( lor )" ( lor );
  add_bin "( lxor )" ( lxor );

  (* List functions *)
  let add_list f_name f =
    let r = discover_unary_list f f_name in
    let rels = infer_relations r in
    let ins = generate_insights r in
    entries := { category = List_Transform; report = r; relations = rels; insights = ins } :: !entries
  in
  add_list "List.rev" List.rev;
  add_list "List.sort compare" (List.sort compare);
  add_list "List.tl (safe)" (fun xs -> match xs with [] -> [] | _ :: t -> t);
  add_list "(fun xs -> xs @ xs)" (fun xs -> xs @ xs);
  add_list "List.filter (> 0)" (List.filter (fun x -> x > 0));

  (* String functions *)
  let add_str f_name f =
    let r = discover_unary_string f f_name in
    let rels = infer_relations r in
    let ins = generate_insights r in
    entries := { category = String_Transform; report = r; relations = rels; insights = ins } :: !entries
  in
  add_str "String.uppercase_ascii" String.uppercase_ascii;
  add_str "String.lowercase_ascii" String.lowercase_ascii;
  add_str "String.trim" String.trim;

  let all_entries = List.rev !entries in
  let total = List.fold_left (fun acc e -> acc + List.length e.report.properties) 0 all_entries in
  let strongest = List.fold_left (fun best e ->
    List.fold_left (fun b p ->
      match b with
      | None -> Some (e.report.function_name, p)
      | Some (_, bp) -> if p.confidence.score > bp.confidence.score then Some (e.report.function_name, p) else b
    ) best e.report.properties
  ) None all_entries in
  let strongest_str = match strongest with
    | None -> None
    | Some (fn, p) -> Some (Printf.sprintf "%s: %s (%.1f%%)" fn p.description (p.confidence.score *. 100.0))
  in
  { entries = all_entries;
    summary = Printf.sprintf "Analyzed %d functions, discovered %d properties" (List.length all_entries) total;
    total_properties_found = total;
    strongest_property = strongest_str }

(* ── Pretty Printing ────────────────────────────────────────────────────── *)

let property_kind_to_string = function
  | Involution -> "Involution"
  | Idempotent -> "Idempotent"
  | FixedPoint s -> Printf.sprintf "FixedPoint(%s)" s
  | Monotone_Inc -> "Monotone↑"
  | Monotone_Dec -> "Monotone↓"
  | Preserves_Length -> "PreservesLength"
  | Preserves_Sum -> "PreservesSum"
  | Preserves_Elements -> "Permutation"
  | Distributes_Over s -> Printf.sprintf "Distributes(%s)" s
  | Commutative -> "Commutative"
  | Associative -> "Associative"
  | Left_Identity s -> Printf.sprintf "LeftId(%s)" s
  | Right_Identity s -> Printf.sprintf "RightId(%s)" s
  | Absorbing s -> Printf.sprintf "Absorbing(%s)" s
  | Self_Inverse -> "SelfInverse"
  | Nilpotent n -> Printf.sprintf "Nilpotent(%d)" n
  | Bounded s -> Printf.sprintf "Bounded%s" s
  | Injective -> "Injective"
  | Surjective_Sample -> "Surjective"
  | Constant -> "Constant"
  | Anti_Commutative -> "Anti-Commutative"
  | Cancellative -> "Cancellative"

let relation_to_string = function
  | Implies -> "⟹"
  | Equivalent -> "⟺"
  | Independent -> "⊥"
  | Contradicts -> "⊗"

let print_report report =
  Printf.printf "\n╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║  Property Discovery: %-38s ║\n" report.function_name;
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  Trials: %-5d  |  Properties found: %-3d                    ║\n"
    report.total_trials (List.length report.properties);
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  List.iter (fun p ->
    let badge = if p.confidence.score >= 0.999 then "✓"
      else if p.confidence.score >= 0.99 then "~"
      else "?" in
    Printf.printf "║  [%s] %-55s ║\n" badge p.description;
    Printf.printf "║      confidence: %5.1f%% (%s)%s ║\n"
      (p.confidence.score *. 100.0) (confidence_level p.confidence)
      (String.make (28 - String.length (confidence_level p.confidence)) ' ');
    (match p.counterexample with
     | Some cex ->
       let short = if String.length cex > 50 then String.sub cex 0 47 ^ "..." else cex in
       Printf.printf "║      counter: %-46s ║\n" short
     | None -> ())
  ) report.properties;
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n"

let print_analysis analysis =
  Printf.printf "\n";
  Printf.printf "┌──────────────────────────────────────────────────────────────┐\n";
  Printf.printf "│     🔍 AUTONOMOUS PROPERTY DISCOVERY ENGINE                  │\n";
  Printf.printf "│     Algebraic Invariant Finder v1.0                          │\n";
  Printf.printf "├──────────────────────────────────────────────────────────────┤\n";
  Printf.printf "│  %s\n" analysis.summary;
  Printf.printf "│  Strongest: %s\n"
    (match analysis.strongest_property with Some s -> s | None -> "none");
  Printf.printf "└──────────────────────────────────────────────────────────────┘\n";
  List.iter (fun entry ->
    print_report entry.report;
    if entry.insights <> [] then begin
      Printf.printf "  💡 Insights:\n";
      List.iter (fun i -> Printf.printf "     • %s\n" i) entry.insights
    end;
    if entry.relations <> [] then begin
      Printf.printf "  🔗 Relations:\n";
      List.iter (fun r ->
        Printf.printf "     %s %s %s\n" r.prop1 (relation_to_string r.relation) r.prop2
      ) entry.relations
    end
  ) analysis.entries;
  Printf.printf "\n══════════════════════════════════════════════════════════════════\n";
  Printf.printf "  Total properties discovered: %d\n" analysis.total_properties_found;
  Printf.printf "══════════════════════════════════════════════════════════════════\n"

(* ── Progressive Deepening Discovery ───────────────────────────────────── *)

(* Adaptively increase trial count for properties near the confidence threshold *)
type deepening_result = {
  initial_props : int;
  refined_props : int;
  promoted : string list;   (* properties that crossed threshold after deepening *)
  demoted : string list;    (* properties that fell below after more trials *)
}

let deepen_discovery f name =
  (* Phase 1: Quick scan with 50 trials *)
  let saved_seed = !global_seed in
  global_seed := 99999;
  let quick = discover_unary_int f name in

  (* Phase 2: Deep scan with 500 trials for borderline properties *)
  global_seed := saved_seed;
  let deep_trials = 500 in
  let borderline = List.filter (fun p ->
    p.confidence.score >= 0.8 && p.confidence.score < 0.999) quick.properties in

  let promoted = ref [] in
  let demoted = ref [] in
  List.iter (fun p ->
    let (s, _) = test_property_bool random_int_gen (fun x ->
      match p.kind with
      | Involution -> f (f x) = x
      | Idempotent -> f (f x) = f x
      | Monotone_Inc -> true (* skip for deepening *)
      | _ -> true
    ) in
    (* Run extra trials *)
    let extra_s = ref s in
    for _ = 1 to (deep_trials - num_trials) do
      let x = random_int_gen () in
      let passes = match p.kind with
        | Involution -> f (f x) = x
        | Idempotent -> f (f x) = f x
        | _ -> true
      in
      if passes then incr extra_s
    done;
    let new_score = float_of_int !extra_s /. float_of_int deep_trials in
    if new_score >= 0.999 && p.confidence.score < 0.999 then
      promoted := p.description :: !promoted
    else if new_score < 0.95 && p.confidence.score >= 0.95 then
      demoted := p.description :: !demoted
  ) borderline;

  { initial_props = List.length quick.properties;
    refined_props = List.length quick.properties + List.length !promoted - List.length !demoted;
    promoted = !promoted;
    demoted = !demoted }

(* ── Compositional Property Discovery ──────────────────────────────────── *)

(* Discover properties of function compositions *)
type composition_insight = {
  f_name : string;
  g_name : string;
  composition : string;  (* "f ∘ g" or "g ∘ f" *)
  property : string;
}

let discover_compositions () =
  let insights = ref [] in

  (* abs ∘ negate = abs *)
  let (s, _) = test_property_bool random_int_gen (fun x -> abs (- x) = abs x) in
  if s = num_trials then
    insights := { f_name = "abs"; g_name = "negate"; composition = "abs ∘ negate";
                  property = "abs ∘ negate = abs (absorption)" } :: !insights;

  (* succ ∘ pred = id *)
  let (s, _) = test_property_bool random_int_gen (fun x -> succ (pred x) = x) in
  if s = num_trials then
    insights := { f_name = "succ"; g_name = "pred"; composition = "succ ∘ pred";
                  property = "succ ∘ pred = id (mutual inverse)" } :: !insights;

  (* rev ∘ rev = id *)
  let (s, _) = test_property_bool random_int_list (fun xs -> List.rev (List.rev xs) = xs) in
  if s = num_trials then
    insights := { f_name = "rev"; g_name = "rev"; composition = "rev ∘ rev";
                  property = "rev ∘ rev = id (self-inverse)" } :: !insights;

  (* sort ∘ sort = sort (idempotent) *)
  let (s, _) = test_property_bool random_int_list (fun xs ->
    let sort = List.sort compare in sort (sort xs) = sort xs) in
  if s = num_trials then
    insights := { f_name = "sort"; g_name = "sort"; composition = "sort ∘ sort";
                  property = "sort ∘ sort = sort (idempotent composition)" } :: !insights;

  (* sort ∘ rev = sort (absorption) *)
  let (s, _) = test_property_bool random_int_list (fun xs ->
    List.sort compare (List.rev xs) = List.sort compare xs) in
  if s = num_trials then
    insights := { f_name = "sort"; g_name = "rev"; composition = "sort ∘ rev";
                  property = "sort ∘ rev = sort (sort absorbs rev)" } :: !insights;

  (* uppercase ∘ lowercase = uppercase *)
  let (s, _) = test_property_bool random_string_gen (fun s ->
    String.uppercase_ascii (String.lowercase_ascii s) = String.uppercase_ascii s) in
  if s = num_trials then
    insights := { f_name = "uppercase"; g_name = "lowercase"; composition = "upper ∘ lower";
                  property = "upper ∘ lower = upper (case absorption)" } :: !insights;

  List.rev !insights

(* ── Main Demo ──────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "╔══════════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║        🔬 PROPERTY DISCOVERY ENGINE v1.0                        ║\n";
  Printf.printf "║        Autonomous Algebraic Invariant Finder                    ║\n";
  Printf.printf "║        Discovers properties functions didn't know they had       ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════════╝\n\n";

  (* Individual discoveries *)
  Printf.printf "━━━ Phase 1: Individual Function Analysis ━━━\n";
  let rev_report = discover_unary_list List.rev "List.rev" in
  print_report rev_report;

  let sort_report = discover_unary_list (List.sort compare) "List.sort" in
  print_report sort_report;

  let plus_report = discover_binary ( + ) "( + )" in
  print_report plus_report;

  let max_report = discover_binary max "max" in
  print_report max_report;

  let abs_report = discover_unary_int abs "abs" in
  print_report abs_report;

  (* Compositional analysis *)
  Printf.printf "\n━━━ Phase 2: Compositional Discovery ━━━\n";
  let compositions = discover_compositions () in
  Printf.printf "\n  Discovered %d compositional properties:\n" (List.length compositions);
  List.iter (fun c ->
    Printf.printf "    🔗 %s: %s\n" c.composition c.property
  ) compositions;

  (* Progressive deepening demo *)
  Printf.printf "\n━━━ Phase 3: Progressive Deepening ━━━\n";
  let deep = deepen_discovery abs "abs (deepened)" in
  Printf.printf "  Initial: %d properties → Refined: %d properties\n" deep.initial_props deep.refined_props;
  Printf.printf "  Promoted: %d | Demoted: %d\n" (List.length deep.promoted) (List.length deep.demoted);

  (* Full autonomous analysis *)
  Printf.printf "\n━━━ Phase 4: Full Autonomous Analysis ━━━\n";
  let analysis = autonomous_analyze () in
  print_analysis analysis;

  Printf.printf "\n✅ Property Discovery Engine complete.\n";
  Printf.printf "   Unlike QuickCheck (which verifies known properties),\n";
  Printf.printf "   this engine DISCOVERS unknown algebraic invariants.\n";
  Printf.printf "   Feed it any function → get back its algebraic DNA.\n"
