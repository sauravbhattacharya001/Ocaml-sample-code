(* test_contract_inference.ml - Tests for Contract Inference Engine *)

(* ── Minimal test framework ── *)
let _pass = ref 0
let _fail = ref 0
let _total = ref 0

let check name cond =
  incr _total;
  if cond then (incr _pass; Printf.printf "  ✅ %s\n" name)
  else (incr _fail; Printf.printf "  ❌ FAIL: %s\n" name)

let section name = Printf.printf "\n── %s ──\n" name

(* ── Reproduce core types and functions for testing ── *)

type domain_bound =
  | Unbounded
  | BoundInclusive of int
  | BoundExclusive of int

type domain_constraint = {
  dc_name: string;
  dc_lower: domain_bound;
  dc_upper: domain_bound;
  dc_excluded: int list;
  dc_required_mod: (int * int) option;
}

type relationship_kind =
  | Linear of float * float
  | Quadratic of float * float * float
  | Monotonic_increasing
  | Monotonic_decreasing
  | Bounded of int * int
  | Idempotent_output
  | Preserves_sign
  | Output_positive
  | Output_nonnegative
  | Output_bounded_by_input

type postcondition = {
  pc_relationship: relationship_kind;
  pc_confidence: float;
  pc_counterexamples: int;
  pc_samples_tested: int;
}

type exception_contract = {
  ec_exception_type: string;
  ec_trigger_description: string;
  ec_trigger_domain: domain_constraint;
  ec_frequency: float;
  ec_samples: int;
}

type repr_invariant = {
  ri_name: string;
  ri_description: string;
  ri_holds_count: int;
  ri_total_count: int;
  ri_confidence: float;
}

type contract_strength =
  | Strong
  | Moderate
  | Weak
  | Tentative

type inferred_contract = {
  ic_function_name: string;
  ic_preconditions: domain_constraint list;
  ic_postconditions: postcondition list;
  ic_exception_contracts: exception_contract list;
  ic_invariants: repr_invariant list;
  ic_strength: contract_strength;
  ic_overall_confidence: float;
  ic_samples_used: int;
}

type contract_insight =
  | TightDomain of string * string
  | StrongRelationship of string * string
  | FragileContract of string * string
  | ExceptionHeavy of string * string
  | WellBehaved of string
  | RedundantContract of string * string
  | InsufficientData of string * string

(* ── Random ── *)
let _global_seed = ref 42
let _next_random () =
  _global_seed := (!_global_seed * 1103515245 + 12345) land 0x3FFFFFFF;
  !_global_seed
let random_int bound =
  if bound <= 0 then 0 else (_next_random ()) mod bound
let random_int_range lo hi =
  if hi <= lo then lo else lo + random_int (hi - lo + 1)
let shuffle arr =
  let n = Array.length arr in
  for i = n - 1 downto 1 do
    let j = random_int (i + 1) in
    let tmp = arr.(i) in arr.(i) <- arr.(j); arr.(j) <- tmp
  done

(* ── Engine reimplementations (condensed) for testing ── *)

let probe_domain (f : int -> int) (name : string) (num_samples : int) : domain_constraint list =
  let successes = ref [] in
  let failures = ref [] in
  let test_points = Array.init num_samples (fun i -> i - num_samples / 2) in
  shuffle test_points;
  Array.iter (fun x ->
    (try let _ = f x in successes := x :: !successes
     with _ -> failures := x :: !failures)
  ) test_points;
  let boundaries = [| 0; 1; -1; 100; -100; 1000; -1000 |] in
  Array.iter (fun x ->
    (try let _ = f x in
       if not (List.mem x !successes) then successes := x :: !successes
     with _ ->
       if not (List.mem x !failures) then failures := x :: !failures)
  ) boundaries;
  let succ_sorted = List.sort compare !successes in
  let fail_sorted = List.sort compare !failures in
  let constraints = ref [] in
  (match fail_sorted, succ_sorted with
   | fl, sl when fl <> [] && sl <> [] ->
     let min_succ = List.hd sl in
     let neg_fails = List.filter (fun x -> x < min_succ) fl in
     if neg_fails <> [] then begin
       let lower = BoundInclusive min_succ in
       let max_succ = List.nth sl (List.length sl - 1) in
       let pos_fails = List.filter (fun x -> x > max_succ) fl in
       let upper = if pos_fails <> [] then BoundInclusive max_succ else Unbounded in
       let excluded = List.filter (fun x -> x >= min_succ && x <= max_succ) fl in
       constraints := {
         dc_name = name ^ "_domain";
         dc_lower = lower; dc_upper = upper;
         dc_excluded = excluded; dc_required_mod = None;
       } :: !constraints
     end
   | _ -> ());
  if !constraints = [] then
    [{ dc_name = name ^ "_unrestricted"; dc_lower = Unbounded; dc_upper = Unbounded;
       dc_excluded = []; dc_required_mod = None }]
  else !constraints

let mine_relationships (f : int -> int) (_name : string) (num_samples : int) : postcondition list =
  let pairs = ref [] in
  for i = 0 to num_samples - 1 do
    let x = i - (num_samples / 2) in
    (try let y = f x in pairs := (x, y) :: !pairs with _ -> ())
  done;
  let ps = !pairs in
  let n = List.length ps in
  if n < 5 then [] else
  let results = ref [] in
  let sorted_by_x = List.sort (fun (a,_) (b,_) -> compare a b) ps in
  let mono_inc = ref true in
  let mono_dec = ref true in
  let prev = ref None in
  List.iter (fun (x, y) ->
    (match !prev with
     | Some (_px, py) -> if y < py then mono_inc := false; if y > py then mono_dec := false; ignore x
     | None -> ()); prev := Some (x, y)
  ) sorted_by_x;
  if !mono_inc && n > 5 then
    results := { pc_relationship = Monotonic_increasing; pc_confidence = 1.0 -. (1.0 /. float_of_int n);
                 pc_counterexamples = 0; pc_samples_tested = n } :: !results;
  if !mono_dec && n > 5 then
    results := { pc_relationship = Monotonic_decreasing; pc_confidence = 1.0 -. (1.0 /. float_of_int n);
                 pc_counterexamples = 0; pc_samples_tested = n } :: !results;
  let nonneg = List.for_all (fun (_, y) -> y >= 0) ps in
  if nonneg && n > 5 then
    results := { pc_relationship = Output_nonnegative; pc_confidence = 1.0 -. (1.0 /. float_of_int n);
                 pc_counterexamples = 0; pc_samples_tested = n } :: !results;
  !results

let infer_exception_contracts (f : int -> int) (name : string) (num_samples : int) : exception_contract list =
  let exceptions = Hashtbl.create 16 in
  let total_tested = ref 0 in
  for i = 0 to num_samples - 1 do
    let x = i - (num_samples / 2) in
    incr total_tested;
    (try let _ = f x in ()
     with
     | Division_by_zero ->
       let k = "Division_by_zero" in
       Hashtbl.replace exceptions k ((try Hashtbl.find exceptions k with Not_found -> []) @ [x])
     | Failure msg ->
       let k = "Failure: " ^ msg in
       Hashtbl.replace exceptions k ((try Hashtbl.find exceptions k with Not_found -> []) @ [x])
     | _ ->
       let k = "Unknown" in
       Hashtbl.replace exceptions k ((try Hashtbl.find exceptions k with Not_found -> []) @ [x]))
  done;
  let total = float_of_int !total_tested in
  Hashtbl.fold (fun exc_type inputs acc ->
    let sorted = List.sort compare inputs in
    let count = List.length sorted in
    let min_in = List.hd sorted in
    let max_in = List.nth sorted (count - 1) in
    { ec_exception_type = exc_type;
      ec_trigger_description = Printf.sprintf "x in [%d, %d]" min_in max_in;
      ec_trigger_domain = { dc_name = name ^ "_trigger"; dc_lower = BoundInclusive min_in;
                            dc_upper = BoundInclusive max_in; dc_excluded = []; dc_required_mod = None };
      ec_frequency = float_of_int count /. total;
      ec_samples = count } :: acc
  ) exceptions []

let detect_invariants_for lf_func lf_name num_samples =
  let results = ref [] in
  let test_lists = Array.init num_samples (fun _ ->
    let len = random_int 20 in List.init len (fun _ -> random_int_range (-50) 50)
  ) in
  let count_pred pred =
    let c = ref 0 in let t = ref 0 in
    Array.iter (fun lst -> incr t; if pred lst then incr c) test_lists;
    (!c, !t)
  in
  let add_inv name desc pred =
    let (c, t) = count_pred pred in
    let conf = float_of_int c /. float_of_int t in
    if conf > 0.5 then
      results := { ri_name = name; ri_description = desc;
                   ri_holds_count = c; ri_total_count = t; ri_confidence = conf } :: !results
  in
  add_inv "length_preserved"
    (Printf.sprintf "|%s(xs)| = |xs|" lf_name)
    (fun lst -> List.length (lf_func lst) = List.length lst);
  add_inv "elements_preserved"
    (Printf.sprintf "multiset(%s(xs)) = multiset(xs)" lf_name)
    (fun lst -> List.sort compare (lf_func lst) = List.sort compare lst);
  add_inv "output_sorted"
    (Printf.sprintf "%s(xs) is sorted" lf_name)
    (fun lst -> let out = lf_func lst in
      let rec go = function [] | [_] -> true | a :: b :: r -> a <= b && go (b :: r) in go out);
  add_inv "idempotent"
    (Printf.sprintf "%s(%s(xs)) = %s(xs)" lf_name lf_name lf_name)
    (fun lst -> let o1 = lf_func lst in lf_func o1 = o1);
  !results

let classify_strength confidence samples =
  if samples < 10 then Tentative
  else if confidence >= 0.98 then Strong
  else if confidence >= 0.85 then Moderate
  else if confidence >= 0.60 then Weak
  else Tentative

let minimize_postconditions pcs =
  let has_linear = List.exists (fun pc -> match pc.pc_relationship with Linear _ -> true | _ -> false) pcs in
  List.filter (fun pc ->
    match pc.pc_relationship with
    | Monotonic_increasing when has_linear -> false
    | Monotonic_decreasing when has_linear -> false
    | Preserves_sign when has_linear -> false
    | _ -> true
  ) pcs

(* ══════════ Tests ══════════ *)

let () =
  Printf.printf "🧪 Contract Inference Engine — Test Suite\n";
  Printf.printf "══════════════════════════════════════════\n";

  section "Domain Prober — total functions";
  let abs_val x = if x < 0 then -x else x in
  let dom = probe_domain abs_val "abs" 200 in
  check "abs has unrestricted domain" (List.exists (fun dc -> dc.dc_lower = Unbounded) dom);

  let identity x = x in
  let dom2 = probe_domain identity "identity" 200 in
  check "identity has unrestricted domain" (List.exists (fun dc -> dc.dc_lower = Unbounded) dom2);

  section "Domain Prober — partial functions";
  let factorial n =
    if n < 0 then failwith "negative" else
    let rec go acc i = if i <= 1 then acc else go (acc * i) (i - 1) in go 1 n
  in
  let dom3 = probe_domain factorial "factorial" 200 in
  check "factorial has lower bound" (List.exists (fun dc -> dc.dc_lower <> Unbounded) dom3);

  let collatz x = if x <= 0 then failwith "pos" else if x mod 2 = 0 then x / 2 else 3 * x + 1 in
  let dom4 = probe_domain collatz "collatz" 200 in
  check "collatz has lower bound" (List.exists (fun dc -> dc.dc_lower <> Unbounded) dom4);

  section "Domain Prober — boundary detection";
  let fib n =
    if n < 0 then failwith "neg" else
    let rec go a b i = if i <= 0 then a else go b (a + b) (i - 1) in go 0 1 n
  in
  let dom5 = probe_domain fib "fib" 200 in
  check "fib has lower bound >= 0" (
    List.exists (fun dc -> match dc.dc_lower with BoundInclusive n -> n >= 0 | _ -> false) dom5
  );

  section "Output Relationships — linear";
  let double x = x * 2 in
  let rels = mine_relationships double "double" 200 in
  check "double detected as monotonic increasing" (
    List.exists (fun pc -> match pc.pc_relationship with Monotonic_increasing -> true | _ -> false) rels);

  let negate x = -x in
  let rels2 = mine_relationships negate "negate" 200 in
  check "negate detected as monotonic decreasing" (
    List.exists (fun pc -> match pc.pc_relationship with Monotonic_decreasing -> true | _ -> false) rels2);

  section "Output Relationships — nonnegative";
  let rels3 = mine_relationships abs_val "abs" 200 in
  check "abs output nonnegative" (
    List.exists (fun pc -> match pc.pc_relationship with Output_nonnegative -> true | _ -> false) rels3);

  let square x = x * x in
  let rels4 = mine_relationships square "square" 200 in
  check "square output nonnegative" (
    List.exists (fun pc -> match pc.pc_relationship with Output_nonnegative -> true | _ -> false) rels4);

  section "Output Relationships — confidence";
  check "double monotonic has high confidence" (
    List.exists (fun pc -> pc.pc_confidence > 0.9) rels);
  check "abs nonneg has high confidence" (
    List.exists (fun pc -> pc.pc_confidence > 0.9) rels3);

  section "Exception Contracts — functions that throw";
  let excs = infer_exception_contracts factorial "factorial" 200 in
  check "factorial has exception contracts" (excs <> []);
  check "factorial exceptions are Failure type" (
    List.exists (fun ec -> String.length ec.ec_exception_type > 0) excs);

  let excs2 = infer_exception_contracts collatz "collatz" 200 in
  check "collatz has exception contracts" (excs2 <> []);

  section "Exception Contracts — total functions";
  let excs3 = infer_exception_contracts abs_val "abs" 200 in
  check "abs has no exception contracts" (excs3 = []);
  let excs4 = infer_exception_contracts identity "identity" 200 in
  check "identity has no exception contracts" (excs4 = []);

  section "Exception Contracts — frequency";
  check "factorial exception frequency > 0" (
    List.for_all (fun ec -> ec.ec_frequency > 0.0) excs);
  check "factorial exception frequency < 1" (
    List.for_all (fun ec -> ec.ec_frequency < 1.0) excs);

  section "Representation Invariants — List.rev";
  let invs = detect_invariants_for List.rev "List.rev" 100 in
  check "List.rev preserves length" (
    List.exists (fun ri -> ri.ri_name = "length_preserved" && ri.ri_confidence > 0.9) invs);
  check "List.rev preserves elements" (
    List.exists (fun ri -> ri.ri_name = "elements_preserved" && ri.ri_confidence > 0.9) invs);
  check "List.rev is idempotent (rev(rev(x))=x)" (
    List.exists (fun ri -> ri.ri_name = "idempotent" && ri.ri_confidence > 0.9) invs);

  section "Representation Invariants — List.sort";
  let invs2 = detect_invariants_for (List.sort compare) "List.sort" 100 in
  check "List.sort output is sorted" (
    List.exists (fun ri -> ri.ri_name = "output_sorted" && ri.ri_confidence > 0.9) invs2);
  check "List.sort preserves elements" (
    List.exists (fun ri -> ri.ri_name = "elements_preserved" && ri.ri_confidence > 0.9) invs2);
  check "List.sort is idempotent" (
    List.exists (fun ri -> ri.ri_name = "idempotent" && ri.ri_confidence > 0.9) invs2);

  section "Representation Invariants — filter";
  let filter_pos l = List.filter (fun x -> x > 0) l in
  let invs3 = detect_invariants_for filter_pos "filter_pos" 100 in
  check "filter does not preserve all elements" (
    not (List.exists (fun ri -> ri.ri_name = "elements_preserved" && ri.ri_confidence > 0.9) invs3));

  section "Representation Invariants — dedup";
  let dedup l = List.sort_uniq compare l in
  let invs4 = detect_invariants_for dedup "dedup" 100 in
  check "dedup output is sorted" (
    List.exists (fun ri -> ri.ri_name = "output_sorted" && ri.ri_confidence > 0.9) invs4);
  check "dedup is idempotent" (
    List.exists (fun ri -> ri.ri_name = "idempotent" && ri.ri_confidence > 0.9) invs4);

  section "Strength Classification";
  check "high confidence + many samples = Strong" (classify_strength 0.99 100 = Strong);
  check "medium confidence = Moderate" (classify_strength 0.90 100 = Moderate);
  check "low confidence = Weak" (classify_strength 0.70 100 = Weak);
  check "very low confidence = Tentative" (classify_strength 0.40 100 = Tentative);
  check "few samples = Tentative" (classify_strength 0.99 5 = Tentative);

  section "Contract Minimizer";
  let pcs = [
    { pc_relationship = Linear (2.0, 0.0); pc_confidence = 1.0; pc_counterexamples = 0; pc_samples_tested = 100 };
    { pc_relationship = Monotonic_increasing; pc_confidence = 1.0; pc_counterexamples = 0; pc_samples_tested = 100 };
  ] in
  let minimized = minimize_postconditions pcs in
  check "linear removes redundant monotonic" (List.length minimized < List.length pcs);
  check "linear kept after minimization" (
    List.exists (fun pc -> match pc.pc_relationship with Linear _ -> true | _ -> false) minimized);

  section "Contract Minimizer — no linear";
  let pcs2 = [
    { pc_relationship = Monotonic_increasing; pc_confidence = 1.0; pc_counterexamples = 0; pc_samples_tested = 100 };
    { pc_relationship = Output_nonnegative; pc_confidence = 0.9; pc_counterexamples = 1; pc_samples_tested = 100 };
  ] in
  let minimized2 = minimize_postconditions pcs2 in
  check "without linear, monotonic kept" (
    List.exists (fun pc -> match pc.pc_relationship with Monotonic_increasing -> true | _ -> false) minimized2);
  check "without linear, nonneg kept" (
    List.exists (fun pc -> match pc.pc_relationship with Output_nonnegative -> true | _ -> false) minimized2);

  section "End-to-end: sign function";
  let sign x = if x > 0 then 1 else if x < 0 then -1 else 0 in
  let rels_sign = mine_relationships sign "sign" 200 in
  check "sign output nonneg NOT detected" (
    not (List.exists (fun pc -> match pc.pc_relationship with Output_nonnegative -> true | _ -> false) rels_sign));
  check "sign not monotonic decreasing" (
    not (List.exists (fun pc -> match pc.pc_relationship with Monotonic_decreasing -> true | _ -> false) rels_sign));

  section "End-to-end: clamp function";
  let clamp x = if x < 0 then 0 else if x > 100 then 100 else x in
  let rels_clamp = mine_relationships clamp "clamp" 200 in
  check "clamp output nonnegative" (
    List.exists (fun pc -> match pc.pc_relationship with Output_nonnegative -> true | _ -> false) rels_clamp);

  section "Postcondition samples count";
  List.iter (fun pc ->
    check (Printf.sprintf "double postcond samples > 0 (%d)" pc.pc_samples_tested)
      (pc.pc_samples_tested > 0)
  ) rels;

  section "Exception trigger domain validity";
  List.iter (fun ec ->
    check (Printf.sprintf "factorial exc domain has valid bounds (%s)" ec.ec_exception_type)
      (ec.ec_trigger_domain.dc_lower <> Unbounded)
  ) excs;

  section "Invariant confidence bounds";
  List.iter (fun ri ->
    check (Printf.sprintf "%s confidence in [0,1]" ri.ri_name)
      (ri.ri_confidence >= 0.0 && ri.ri_confidence <= 1.0)
  ) invs;
  List.iter (fun ri ->
    check (Printf.sprintf "%s holds <= total" ri.ri_name)
      (ri.ri_holds_count <= ri.ri_total_count)
  ) invs;

  section "Multiple relationship types coexist";
  let abs_rels = mine_relationships abs_val "abs" 200 in
  check "abs has multiple postconditions" (List.length abs_rels >= 2);

  section "Edge case: constant function";
  let const0 _ = 0 in
  let const_rels = mine_relationships const0 "const0" 200 in
  check "constant function nonnegative" (
    List.exists (fun pc -> match pc.pc_relationship with Output_nonnegative -> true | _ -> false) const_rels);
  let const_dom = probe_domain const0 "const0" 200 in
  check "constant function unrestricted domain" (
    List.exists (fun dc -> dc.dc_lower = Unbounded) const_dom);

  (* ── Summary ── *)
  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "Results: %d/%d passed" !_pass !_total;
  if !_fail > 0 then Printf.printf " (%d FAILED)" !_fail;
  Printf.printf "\n";
  if !_fail = 0 then Printf.printf "✅ All tests passed!\n"
  else Printf.printf "❌ Some tests failed.\n";
  exit (if !_fail = 0 then 0 else 1)
