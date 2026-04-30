(* ============================================================================
   test_property_discovery.ml - Tests for Property Discovery Engine
   ============================================================================
   Self-contained test file that inlines necessary logic from property_discovery.ml
   ============================================================================ *)

(* ── Test Framework ─────────────────────────────────────────────────────── *)

let tests_run = ref 0
let tests_passed = ref 0

let assert_true msg cond =
  incr tests_run;
  if cond then (incr tests_passed; Printf.printf "  ✓ %s\n" msg)
  else Printf.printf "  ✗ FAIL: %s\n" msg

let assert_equal msg expected actual =
  incr tests_run;
  if expected = actual then (incr tests_passed; Printf.printf "  ✓ %s\n" msg)
  else Printf.printf "  ✗ FAIL: %s (expected %s, got %s)\n" msg expected actual

(* ── Inlined Core from property_discovery.ml ────────────────────────────── *)

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

let random_list gen len =
  List.init len (fun _ -> gen ())

let random_int_gen () = random_int_range (-100) 100
let random_int_list () =
  let len = random_int_range 0 20 in
  random_list random_int_gen len

let random_string_gen () =
  let len = random_int_range 0 15 in
  String.init len (fun _ -> Char.chr (random_int_range 97 122))

type confidence = { trials : int; successes : int; score : float }

type property_kind =
  | Involution | Idempotent | FixedPoint of string
  | Monotone_Inc | Monotone_Dec
  | Preserves_Length | Preserves_Sum | Preserves_Elements
  | Distributes_Over of string | Commutative | Associative
  | Left_Identity of string | Right_Identity of string
  | Absorbing of string | Self_Inverse | Nilpotent of int
  | Bounded of string | Injective | Surjective_Sample
  | Constant | Anti_Commutative | Cancellative

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

let make_confidence trials successes =
  { trials; successes; score = if trials = 0 then 0.0 else float_of_int successes /. float_of_int trials }

let confidence_level c =
  if c.score >= 0.999 then "definite"
  else if c.score >= 0.99 then "very likely"
  else if c.score >= 0.95 then "likely"
  else if c.score >= 0.8 then "probable"
  else if c.score >= 0.5 then "weak"
  else "unlikely"

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

(* Discover properties of unary int function *)
let discover_unary_int (f : int -> int) name =
  let props = ref [] in
  let add kind desc conf cex =
    props := { kind; description = desc; confidence = conf; counterexample = cex } :: !props in
  let (s, cex) = test_property_bool random_int_gen (fun x -> f (f x) = x) in
  let cex_str = Option.map (fun x -> Printf.sprintf "f(f(%d))=%d≠%d" x (f (f x)) x) cex in
  add Involution "f(f(x)) = x" (make_confidence num_trials s) cex_str;
  let (s, cex) = test_property_bool random_int_gen (fun x -> f (f x) = f x) in
  let cex_str = Option.map (fun x -> Printf.sprintf "f(f(%d))=%d≠f(%d)=%d" x (f (f x)) x (f x)) cex in
  add Idempotent "f(f(x)) = f(x)" (make_confidence num_trials s) cex_str;
  let (s, _) = test_property_binary random_int_gen random_int_gen
    (fun x y -> if x <= y then f x <= f y else true) in
  add Monotone_Inc "monotone increasing" (make_confidence num_trials s) None;
  let (s, _) = test_property_binary random_int_gen random_int_gen
    (fun x y -> if x <= y then f x >= f y else true) in
  add Monotone_Dec "monotone decreasing" (make_confidence num_trials s) None;
  let first = f 0 in
  let (s, _) = test_property_bool random_int_gen (fun x -> f x = first) in
  if s = num_trials then add Constant (Printf.sprintf "constant=%d" first) (make_confidence num_trials s) None;
  let (s, _) = test_property_binary random_int_gen random_int_gen
    (fun x y -> if x <> y then f x <> f y else true) in
  add Injective "injective" (make_confidence num_trials s) None;
  if f 0 = 0 then add (FixedPoint "0") "f(0)=0" (make_confidence 1 1) None;
  { function_name = name;
    properties = List.filter (fun p -> p.confidence.score >= 0.95) (List.rev !props);
    total_trials = num_trials * 6; discovery_time_ms = 0 }

(* Discover binary *)
let discover_binary (f : int -> int -> int) name =
  let props = ref [] in
  let add kind desc conf cex =
    props := { kind; description = desc; confidence = conf; counterexample = cex } :: !props in
  let (s, _) = test_property_binary random_int_gen random_int_gen (fun x y -> f x y = f y x) in
  add Commutative "commutative" (make_confidence num_trials s) None;
  let (s, _) = test_property_ternary random_int_gen (fun x y z -> f (f x y) z = f x (f y z)) in
  add Associative "associative" (make_confidence num_trials s) None;
  let (s, _) = test_property_bool random_int_gen (fun x -> f 0 x = x) in
  if s = num_trials then add (Left_Identity "0") "left identity 0" (make_confidence num_trials s) None;
  let (s, _) = test_property_bool random_int_gen (fun x -> f x 0 = x) in
  if s = num_trials then add (Right_Identity "0") "right identity 0" (make_confidence num_trials s) None;
  let (s, _) = test_property_bool random_int_gen (fun x -> f 0 x = 0 && f x 0 = 0) in
  if s = num_trials then add (Absorbing "0") "absorbing 0" (make_confidence num_trials s) None;
  let (s, _) = test_property_binary random_int_gen random_int_gen (fun x y -> f x y = -(f y x)) in
  add Anti_Commutative "anti-commutative" (make_confidence num_trials s) None;
  let (s, _) = test_property_bool random_int_gen (fun x -> f x x = x) in
  if s = num_trials then add Idempotent "f(x,x)=x" (make_confidence num_trials s) None;
  { function_name = name;
    properties = List.filter (fun p -> p.confidence.score >= 0.95) (List.rev !props);
    total_trials = num_trials * 7; discovery_time_ms = 0 }

(* Discover list properties *)
let list_sorted xs = (List.sort compare xs) = xs

let discover_unary_list (f : int list -> int list) name =
  let props = ref [] in
  let add kind desc conf cex =
    props := { kind; description = desc; confidence = conf; counterexample = cex } :: !props in
  let (s, _) = test_property_bool random_int_list (fun xs -> f (f xs) = xs) in
  add Involution "f(f(xs))=xs" (make_confidence num_trials s) None;
  let (s, _) = test_property_bool random_int_list (fun xs -> f (f xs) = f xs) in
  add Idempotent "f(f(xs))=f(xs)" (make_confidence num_trials s) None;
  let (s, _) = test_property_bool random_int_list (fun xs -> List.length (f xs) = List.length xs) in
  add Preserves_Length "preserves length" (make_confidence num_trials s) None;
  let (s, _) = test_property_bool random_int_list (fun xs ->
    List.sort compare (f xs) = List.sort compare xs) in
  add Preserves_Elements "permutation" (make_confidence num_trials s) None;
  let (s, _) = test_property_bool random_int_list (fun xs -> list_sorted (f xs)) in
  if s >= num_trials - 1 then add Monotone_Inc "output sorted" (make_confidence num_trials s) None;
  if f [] = [] then add (FixedPoint "[]") "f([])=[]" (make_confidence 1 1) None;
  { function_name = name;
    properties = List.filter (fun p -> p.confidence.score >= 0.95) (List.rev !props);
    total_trials = num_trials * 5; discovery_time_ms = 0 }

(* ══════════════════════════════════════════════════════════════════════════ *)
(* ── TESTS ──────────────────────────────────────────────────────────────── *)
(* ══════════════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n🔬 Property Discovery Engine - Test Suite\n"
let () = Printf.printf "══════════════════════════════════════════\n"

(* ── Random Infrastructure Tests ────────────────────────────────────────── *)
let () = Printf.printf "\n── Random Infrastructure ──\n"

let () =
  global_seed := 42;
  let v1 = next_random () in
  let v2 = next_random () in
  assert_true "next_random produces different values" (v1 <> v2)

let () =
  let r = random_int_range 5 10 in
  assert_true "random_int_range within bounds" (r >= 5 && r <= 10)

let () =
  global_seed := 100;
  let lst = random_int_list () in
  assert_true "random_int_list produces list (len 0-20)" (List.length lst >= 0 && List.length lst <= 20)

let () =
  global_seed := 200;
  let s = random_string_gen () in
  assert_true "random_string_gen produces string (len 0-15)" (String.length s >= 0 && String.length s <= 15)

let () =
  global_seed := 300;
  let values = List.init 50 (fun _ -> random_int_range 0 1) in
  let has_0 = List.mem 0 values and has_1 = List.mem 1 values in
  assert_true "random covers range" (has_0 && has_1)

(* ── Confidence Tests ───────────────────────────────────────────────────── *)
let () = Printf.printf "\n── Confidence Computation ──\n"

let () =
  let c = make_confidence 100 100 in
  assert_true "perfect confidence = 1.0" (c.score = 1.0)

let () =
  let c = make_confidence 100 0 in
  assert_true "zero confidence = 0.0" (c.score = 0.0)

let () =
  let c = make_confidence 200 190 in
  assert_true "95% confidence" (c.score = 0.95)

let () =
  let c = make_confidence 0 0 in
  assert_true "zero trials = 0.0" (c.score = 0.0)

let () =
  assert_equal "definite level" "definite" (confidence_level { trials=100; successes=100; score=1.0 })

let () =
  assert_equal "very likely level" "very likely" (confidence_level { trials=100; successes=99; score=0.99 })

let () =
  assert_equal "likely level" "likely" (confidence_level { trials=100; successes=96; score=0.96 })

let () =
  assert_equal "probable level" "probable" (confidence_level { trials=100; successes=85; score=0.85 })

let () =
  assert_equal "weak level" "weak" (confidence_level { trials=100; successes=60; score=0.60 })

let () =
  assert_equal "unlikely level" "unlikely" (confidence_level { trials=100; successes=30; score=0.30 })

(* ── Unary Int Discovery Tests ──────────────────────────────────────────── *)
let () = Printf.printf "\n── Unary Int Discovery ──\n"

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x) "identity" in
  assert_true "identity name correct" (report.function_name = "identity")

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x) "identity" in
  let has_invol = List.exists (fun p -> p.kind = Involution) report.properties in
  assert_true "identity is involution" has_invol

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x) "identity" in
  let has_idemp = List.exists (fun p -> p.kind = Idempotent) report.properties in
  assert_true "identity is idempotent" has_idemp

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x) "identity" in
  let has_mono = List.exists (fun p -> p.kind = Monotone_Inc) report.properties in
  assert_true "identity is monotone increasing" has_mono

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x) "identity" in
  let has_inj = List.exists (fun p -> p.kind = Injective) report.properties in
  assert_true "identity is injective" has_inj

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> 42) "constant_42" in
  let has_const = List.exists (fun p -> p.kind = Constant) report.properties in
  assert_true "constant function detected" has_const

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> 42) "constant_42" in
  let has_idemp = List.exists (fun p -> p.kind = Idempotent) report.properties in
  assert_true "constant is idempotent" has_idemp

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> -x) "negate" in
  let has_invol = List.exists (fun p -> p.kind = Involution) report.properties in
  assert_true "negate is involution" has_invol

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> -x) "negate" in
  let has_mono = List.exists (fun p -> p.kind = Monotone_Dec) report.properties in
  assert_true "negate is monotone decreasing" has_mono

let () =
  global_seed := 12345;
  let report = discover_unary_int abs "abs" in
  let has_idemp = List.exists (fun p -> p.kind = Idempotent) report.properties in
  assert_true "abs is idempotent" has_idemp

let () =
  global_seed := 12345;
  let report = discover_unary_int abs "abs" in
  let has_fixed = List.exists (fun p -> p.kind = FixedPoint "0") report.properties in
  assert_true "abs has fixed point 0" has_fixed

let () =
  global_seed := 12345;
  let report = discover_unary_int abs "abs" in
  let has_mono = List.exists (fun p -> p.kind = Monotone_Inc) report.properties in
  assert_true "abs is NOT monotone increasing" (not has_mono)

let () =
  global_seed := 12345;
  let report = discover_unary_int succ "succ" in
  let has_mono = List.exists (fun p -> p.kind = Monotone_Inc) report.properties in
  assert_true "succ is monotone increasing" has_mono

let () =
  global_seed := 12345;
  let report = discover_unary_int succ "succ" in
  let has_inj = List.exists (fun p -> p.kind = Injective) report.properties in
  assert_true "succ is injective" has_inj

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x * x) "square" in
  let has_invol = List.exists (fun p -> p.kind = Involution) report.properties in
  assert_true "square is NOT involution" (not has_invol)

(* ── Binary Discovery Tests ─────────────────────────────────────────────── *)
let () = Printf.printf "\n── Binary Discovery ──\n"

let () =
  global_seed := 12345;
  let report = discover_binary ( + ) "plus" in
  let has_comm = List.exists (fun p -> p.kind = Commutative) report.properties in
  assert_true "plus is commutative" has_comm

let () =
  global_seed := 12345;
  let report = discover_binary ( + ) "plus" in
  let has_assoc = List.exists (fun p -> p.kind = Associative) report.properties in
  assert_true "plus is associative" has_assoc

let () =
  global_seed := 12345;
  let report = discover_binary ( + ) "plus" in
  let has_lid = List.exists (fun p -> match p.kind with Left_Identity _ -> true | _ -> false) report.properties in
  assert_true "plus has left identity" has_lid

let () =
  global_seed := 12345;
  let report = discover_binary ( + ) "plus" in
  let has_rid = List.exists (fun p -> match p.kind with Right_Identity _ -> true | _ -> false) report.properties in
  assert_true "plus has right identity" has_rid

let () =
  global_seed := 12345;
  let report = discover_binary ( * ) "times" in
  let has_comm = List.exists (fun p -> p.kind = Commutative) report.properties in
  assert_true "times is commutative" has_comm

let () =
  global_seed := 12345;
  let report = discover_binary ( * ) "times" in
  let has_assoc = List.exists (fun p -> p.kind = Associative) report.properties in
  assert_true "times is associative" has_assoc

let () =
  global_seed := 12345;
  let report = discover_binary ( * ) "times" in
  let has_abs = List.exists (fun p -> match p.kind with Absorbing _ -> true | _ -> false) report.properties in
  assert_true "times has absorbing element 0" has_abs

let () =
  global_seed := 12345;
  let report = discover_binary ( - ) "minus" in
  let has_comm = List.exists (fun p -> p.kind = Commutative) report.properties in
  assert_true "minus is NOT commutative" (not has_comm)

let () =
  global_seed := 12345;
  let report = discover_binary ( - ) "minus" in
  let has_anti = List.exists (fun p -> p.kind = Anti_Commutative) report.properties in
  assert_true "minus is anti-commutative" has_anti

let () =
  global_seed := 12345;
  let report = discover_binary max "max" in
  let has_comm = List.exists (fun p -> p.kind = Commutative) report.properties in
  assert_true "max is commutative" has_comm

let () =
  global_seed := 12345;
  let report = discover_binary max "max" in
  let has_assoc = List.exists (fun p -> p.kind = Associative) report.properties in
  assert_true "max is associative" has_assoc

let () =
  global_seed := 12345;
  let report = discover_binary max "max" in
  let has_idemp = List.exists (fun p -> p.kind = Idempotent) report.properties in
  assert_true "max(x,x) = x (idempotent)" has_idemp

let () =
  global_seed := 12345;
  let report = discover_binary min "min" in
  let has_comm = List.exists (fun p -> p.kind = Commutative) report.properties in
  assert_true "min is commutative" has_comm

let () =
  global_seed := 12345;
  let report = discover_binary min "min" in
  let has_idemp = List.exists (fun p -> p.kind = Idempotent) report.properties in
  assert_true "min(x,x) = x (idempotent)" has_idemp

(* ── List Discovery Tests ───────────────────────────────────────────────── *)
let () = Printf.printf "\n── List Discovery ──\n"

let () =
  global_seed := 12345;
  let report = discover_unary_list List.rev "rev" in
  let has_invol = List.exists (fun p -> p.kind = Involution) report.properties in
  assert_true "List.rev is involution" has_invol

let () =
  global_seed := 12345;
  let report = discover_unary_list List.rev "rev" in
  let has_len = List.exists (fun p -> p.kind = Preserves_Length) report.properties in
  assert_true "List.rev preserves length" has_len

let () =
  global_seed := 12345;
  let report = discover_unary_list List.rev "rev" in
  let has_perm = List.exists (fun p -> p.kind = Preserves_Elements) report.properties in
  assert_true "List.rev is a permutation" has_perm

let () =
  global_seed := 12345;
  let report = discover_unary_list List.rev "rev" in
  let has_fixed = List.exists (fun p -> p.kind = FixedPoint "[]") report.properties in
  assert_true "List.rev fixes empty list" has_fixed

let () =
  global_seed := 12345;
  let report = discover_unary_list (List.sort compare) "sort" in
  let has_idemp = List.exists (fun p -> p.kind = Idempotent) report.properties in
  assert_true "sort is idempotent" has_idemp

let () =
  global_seed := 12345;
  let report = discover_unary_list (List.sort compare) "sort" in
  let has_perm = List.exists (fun p -> p.kind = Preserves_Elements) report.properties in
  assert_true "sort is a permutation" has_perm

let () =
  global_seed := 12345;
  let report = discover_unary_list (List.sort compare) "sort" in
  let has_sorted = List.exists (fun p -> p.kind = Monotone_Inc) report.properties in
  assert_true "sort output is always sorted" has_sorted

let () =
  global_seed := 12345;
  let report = discover_unary_list (List.sort compare) "sort" in
  let has_len = List.exists (fun p -> p.kind = Preserves_Length) report.properties in
  assert_true "sort preserves length" has_len

let () =
  global_seed := 12345;
  let report = discover_unary_list (fun xs -> match xs with [] -> [] | _ :: t -> t) "tail" in
  let has_len = List.exists (fun p -> p.kind = Preserves_Length) report.properties in
  assert_true "tail does NOT preserve length" (not has_len)

(* ── Edge Cases ─────────────────────────────────────────────────────────── *)
let () = Printf.printf "\n── Edge Cases ──\n"

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun _ -> 0) "zero" in
  let has_const = List.exists (fun p -> p.kind = Constant) report.properties in
  assert_true "zero function is constant" has_const

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun _ -> 0) "zero" in
  let has_idemp = List.exists (fun p -> p.kind = Idempotent) report.properties in
  assert_true "zero function is idempotent" has_idemp

let () =
  global_seed := 12345;
  let report = discover_binary (fun x _ -> x) "first" in
  let has_comm = List.exists (fun p -> p.kind = Commutative) report.properties in
  assert_true "projection is NOT commutative" (not has_comm)

let () =
  global_seed := 12345;
  let report = discover_unary_list (fun _ -> []) "empty" in
  let has_idemp = List.exists (fun p -> p.kind = Idempotent) report.properties in
  assert_true "constant-empty is idempotent" has_idemp

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x + 1) "succ" in
  let has_invol = List.exists (fun p -> p.kind = Involution) report.properties in
  assert_true "succ is NOT involution" (not has_invol)

(* ── Property Filtering ─────────────────────────────────────────────────── *)
let () = Printf.printf "\n── Property Filtering ──\n"

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x * x + x + 1) "complex" in
  (* Most properties should NOT hold for a complex function *)
  assert_true "complex function has few strong properties" (List.length report.properties <= 5)

let () =
  global_seed := 12345;
  let report = discover_unary_int (fun x -> x) "id" in
  (* Identity should have many properties *)
  assert_true "identity has many properties" (List.length report.properties >= 3)

(* ── Summary ────────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "  Results: %d/%d tests passed\n" !tests_passed !tests_run;
  Printf.printf "══════════════════════════════════════════\n";
  if !tests_passed = !tests_run then
    Printf.printf "  ✅ All tests passed!\n"
  else
    Printf.printf "  ❌ %d tests failed\n" (!tests_run - !tests_passed)
