(* ============================================================================
   contract_inference.ml - Autonomous Contract Inference Engine
   ============================================================================

   A Daikon-inspired dynamic contract inference engine for OCaml functions.
   Unlike property_discovery.ml (which finds algebraic properties like
   commutativity/idempotency), this engine discovers *behavioral contracts*:
   preconditions (valid input domains), postconditions (output guarantees),
   and representation invariants for data structures.

   Demonstrates:
   - Dynamic invariant detection (Daikon-style)
   - Input domain inference via boundary probing
   - Output relationship mining (linear, monotonic, bounded)
   - Representation invariant discovery for data structures
   - Exception contract inference (when/why functions fail)
   - Contract strength ranking and minimization
   - Counterexample-driven refinement
   - Autonomous multi-phase analysis pipeline
   - Health scoring 0-100 with confidence tiers
   - Interactive HTML dashboard generation

   7 inference engines:
   1. Domain Prober       — discovers valid input ranges via boundary search
   2. Output Relationship — mines input-output mathematical relationships
   3. Exception Contract  — maps exception conditions and error domains
   4. Invariant Detector  — finds representation invariants on data structures
   5. Contract Minimizer  — removes redundant/implied contracts
   6. Confidence Scorer   — ranks contracts by statistical confidence
   7. Insight Generator   — produces autonomous recommendations

   Usage:
     ocamlopt contract_inference.ml -o contract_inference
     ./contract_inference --demo
     ./contract_inference --dashboard
     (or) ocaml contract_inference.ml --demo
   ============================================================================ *)

(* ══════════ Random Infrastructure ══════════ *)

let _global_seed = ref 42

let _next_random () =
  _global_seed := (!_global_seed * 1103515245 + 12345) land 0x3FFFFFFF;
  !_global_seed

let random_int bound =
  if bound <= 0 then 0
  else (_next_random ()) mod bound

let random_float () =
  float_of_int (_next_random ()) /. float_of_int 0x3FFFFFFF

let random_int_range lo hi =
  if hi <= lo then lo
  else lo + random_int (hi - lo + 1)

let shuffle arr =
  let n = Array.length arr in
  for i = n - 1 downto 1 do
    let j = random_int (i + 1) in
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp
  done

(* ══════════ Core Types ══════════ *)

type value =
  | VInt of int
  | VFloat of float
  | VBool of bool
  | VString of string
  | VList of value list
  | VOption of value option
  | VTuple of value list
  | VUnit
  | VError of string

type domain_bound =
  | Unbounded
  | BoundInclusive of int
  | BoundExclusive of int

type domain_constraint = {
  dc_name: string;
  dc_lower: domain_bound;
  dc_upper: domain_bound;
  dc_excluded: int list;
  dc_required_mod: (int * int) option;  (* value mod m = r *)
}

type relationship_kind =
  | Linear of float * float           (* output = a * input + b *)
  | Quadratic of float * float * float (* output = a*x^2 + b*x + c *)
  | Monotonic_increasing
  | Monotonic_decreasing
  | Bounded of int * int               (* output in [lo, hi] *)
  | Idempotent_output                  (* f(f(x)) = f(x) output-wise *)
  | Preserves_sign
  | Output_positive
  | Output_nonnegative
  | Output_bounded_by_input            (* |output| <= |input| *)

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
  | Strong    (* always holds, high confidence *)
  | Moderate  (* usually holds, some edge cases *)
  | Weak      (* holds often but with notable exceptions *)
  | Tentative (* insufficient data *)

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

type fleet_health = {
  fh_total_functions: int;
  fh_total_contracts: int;
  fh_avg_confidence: float;
  fh_strong_count: int;
  fh_weak_count: int;
  fh_health_score: int;
  fh_insights: contract_insight list;
}

(* ══════════ Test Function Registry ══════════ *)

(* We define test functions as int->int for tractable analysis *)
type test_function = {
  tf_name: string;
  tf_desc: string;
  tf_func: int -> int;
  tf_category: string;
}

let abs_val x = if x < 0 then -x else x

let safe_div a b = if b = 0 then raise Division_by_zero else a / b

let clamp lo hi x = if x < lo then lo else if x > hi then hi else x

let factorial n =
  if n < 0 then failwith "negative factorial"
  else
    let rec go acc i = if i <= 1 then acc else go (acc * i) (i - 1) in
    go 1 n

let fibonacci n =
  if n < 0 then failwith "negative fibonacci"
  else
    let rec go a b i = if i <= 0 then a else go b (a + b) (i - 1) in
    go 0 1 n

let is_positive_int x = if x > 0 then 1 else 0

let square x = x * x

let identity x = x

let negate x = -x

let double x = x * 2

let sign x = if x > 0 then 1 else if x < 0 then -1 else 0

let collatz_step x =
  if x <= 0 then failwith "collatz requires positive"
  else if x mod 2 = 0 then x / 2 else 3 * x + 1

let triangular n =
  if n < 0 then failwith "negative triangular"
  else n * (n + 1) / 2

let test_functions = [
  { tf_name = "abs"; tf_desc = "Absolute value"; tf_func = abs_val; tf_category = "arithmetic" };
  { tf_name = "square"; tf_desc = "Square a number"; tf_func = square; tf_category = "arithmetic" };
  { tf_name = "identity"; tf_desc = "Identity function"; tf_func = identity; tf_category = "arithmetic" };
  { tf_name = "negate"; tf_desc = "Negate a number"; tf_func = negate; tf_category = "arithmetic" };
  { tf_name = "double"; tf_desc = "Double a number"; tf_func = double; tf_category = "arithmetic" };
  { tf_name = "sign"; tf_desc = "Sign function (-1, 0, 1)"; tf_func = sign; tf_category = "arithmetic" };
  { tf_name = "factorial"; tf_desc = "Factorial (n >= 0)"; tf_func = factorial; tf_category = "combinatorial" };
  { tf_name = "fibonacci"; tf_desc = "Fibonacci number"; tf_func = fibonacci; tf_category = "combinatorial" };
  { tf_name = "is_positive"; tf_desc = "1 if positive, 0 otherwise"; tf_func = is_positive_int; tf_category = "predicate" };
  { tf_name = "clamp_0_100"; tf_desc = "Clamp to [0, 100]"; tf_func = clamp 0 100; tf_category = "bounded" };
  { tf_name = "collatz_step"; tf_desc = "One Collatz step"; tf_func = collatz_step; tf_category = "dynamic" };
  { tf_name = "triangular"; tf_desc = "Triangular number"; tf_func = triangular; tf_category = "combinatorial" };
  { tf_name = "safe_div_by_2"; tf_desc = "Integer division by 2"; tf_func = (fun x -> safe_div x 2); tf_category = "arithmetic" };
]

(* ══════════ Engine 1: Domain Prober ══════════ *)

let probe_domain (f : int -> int) (name : string) (num_samples : int) : domain_constraint list =
  let successes = ref [] in
  let failures = ref [] in
  (* Test a range of inputs *)
  let test_points = Array.init num_samples (fun i ->
    let spread = num_samples / 2 in
    i - spread
  ) in
  shuffle test_points;
  Array.iter (fun x ->
    (try
      let _ = f x in
      successes := x :: !successes
    with _ ->
      failures := x :: !failures)
  ) test_points;
  (* Also probe boundary values *)
  let boundaries = [| 0; 1; -1; max_int; min_int; 100; -100; 1000; -1000 |] in
  Array.iter (fun x ->
    (try
      let _ = f x in
      if not (List.mem x !successes) then successes := x :: !successes
    with _ ->
      if not (List.mem x !failures) then failures := x :: !failures)
  ) boundaries;
  let succ_sorted = List.sort compare !successes in
  let fail_sorted = List.sort compare !failures in
  let constraints = ref [] in
  (* Infer lower bound *)
  (match fail_sorted, succ_sorted with
   | fl, sl when fl <> [] && sl <> [] ->
     let min_succ = List.hd sl in
     let neg_fails = List.filter (fun x -> x < min_succ) fl in
     if neg_fails <> [] then begin
       let lower = BoundInclusive min_succ in
       let max_succ = List.nth sl (List.length sl - 1) in
       (* Check if there's an upper bound *)
       let pos_fails = List.filter (fun x -> x > max_succ) fl in
       let upper = if pos_fails <> [] then BoundInclusive max_succ else Unbounded in
       let excluded = List.filter (fun x -> x >= min_succ && x <= max_succ) fl in
       constraints := {
         dc_name = name ^ "_domain";
         dc_lower = lower;
         dc_upper = upper;
         dc_excluded = excluded;
         dc_required_mod = None;
       } :: !constraints
     end
   | _ -> ());
  (* Check for modular constraints *)
  let succ_mods_2 = List.map (fun x -> ((x mod 2) + 2) mod 2) !successes in
  let fail_mods_2 = List.map (fun x -> ((x mod 2) + 2) mod 2) !failures in
  let succ_all_even = List.for_all (fun m -> m = 0) succ_mods_2 && List.length succ_mods_2 > 3 in
  let succ_all_odd = List.for_all (fun m -> m = 1) succ_mods_2 && List.length succ_mods_2 > 3 in
  let fail_has_even = List.exists (fun m -> m = 0) fail_mods_2 in
  let fail_has_odd = List.exists (fun m -> m = 1) fail_mods_2 in
  if succ_all_even && fail_has_odd then
    constraints := {
      dc_name = name ^ "_even_only";
      dc_lower = Unbounded; dc_upper = Unbounded;
      dc_excluded = [];
      dc_required_mod = Some (2, 0);
    } :: !constraints;
  if succ_all_odd && fail_has_even then
    constraints := {
      dc_name = name ^ "_odd_only";
      dc_lower = Unbounded; dc_upper = Unbounded;
      dc_excluded = [];
      dc_required_mod = Some (2, 1);
    } :: !constraints;
  if !constraints = [] then
    (* No domain restrictions detected — function accepts all tested inputs *)
    [{
      dc_name = name ^ "_unrestricted";
      dc_lower = Unbounded;
      dc_upper = Unbounded;
      dc_excluded = [];
      dc_required_mod = None;
    }]
  else
    !constraints

(* ══════════ Engine 2: Output Relationship Miner ══════════ *)

let mine_relationships (f : int -> int) (_name : string) (num_samples : int) : postcondition list =
  let pairs = ref [] in
  for i = 0 to num_samples - 1 do
    let x = i - (num_samples / 2) in
    (try
      let y = f x in
      pairs := (x, y) :: !pairs
    with _ -> ())
  done;
  let ps = !pairs in
  let n = List.length ps in
  if n < 5 then [] else
  let results = ref [] in
  let tested t = List.length (List.filter (fun (_, ok) -> ok) t) in
  let total t = List.length t in

  (* Test: monotonic increasing *)
  let sorted_by_x = List.sort (fun (a,_) (b,_) -> compare a b) ps in
  let mono_inc = ref true in
  let mono_dec = ref true in
  let prev = ref None in
  List.iter (fun (x, y) ->
    (match !prev with
     | Some (_px, py) ->
       if y < py then mono_inc := false;
       if y > py then mono_dec := false;
       ignore x
     | None -> ());
    prev := Some (x, y)
  ) sorted_by_x;
  if !mono_inc && n > 5 then
    results := {
      pc_relationship = Monotonic_increasing;
      pc_confidence = 1.0 -. (1.0 /. float_of_int n);
      pc_counterexamples = 0;
      pc_samples_tested = n;
    } :: !results;
  if !mono_dec && n > 5 then
    results := {
      pc_relationship = Monotonic_decreasing;
      pc_confidence = 1.0 -. (1.0 /. float_of_int n);
      pc_counterexamples = 0;
      pc_samples_tested = n;
    } :: !results;

  (* Test: output always nonnegative *)
  let nonneg_tests = List.map (fun (_, y) -> (y, y >= 0)) ps in
  let nonneg_pass = tested nonneg_tests in
  if nonneg_pass = total nonneg_tests && n > 5 then
    results := {
      pc_relationship = Output_nonnegative;
      pc_confidence = 1.0 -. (1.0 /. float_of_int n);
      pc_counterexamples = 0;
      pc_samples_tested = n;
    } :: !results
  else if nonneg_pass > 0 && total nonneg_tests - nonneg_pass <= 2 then
    results := {
      pc_relationship = Output_nonnegative;
      pc_confidence = float_of_int nonneg_pass /. float_of_int (total nonneg_tests);
      pc_counterexamples = total nonneg_tests - nonneg_pass;
      pc_samples_tested = n;
    } :: !results;

  (* Test: output always positive *)
  let pos_tests = List.map (fun (_, y) -> (y, y > 0)) ps in
  let pos_pass = tested pos_tests in
  if pos_pass = total pos_tests && n > 5 then
    results := {
      pc_relationship = Output_positive;
      pc_confidence = 1.0 -. (1.0 /. float_of_int n);
      pc_counterexamples = 0;
      pc_samples_tested = n;
    } :: !results;

  (* Test: output bounded *)
  let outputs = List.map snd ps in
  let min_out = List.fold_left min max_int outputs in
  let max_out = List.fold_left max min_int outputs in
  if max_out - min_out < 1000 && n > 10 then
    results := {
      pc_relationship = Bounded (min_out, max_out);
      pc_confidence = 0.8;
      pc_counterexamples = 0;
      pc_samples_tested = n;
    } :: !results;

  (* Test: preserves sign *)
  let sign_tests = List.map (fun (x, y) ->
    let sx = if x > 0 then 1 else if x < 0 then -1 else 0 in
    let sy = if y > 0 then 1 else if y < 0 then -1 else 0 in
    ((x, y), sx = sy)
  ) ps in
  let sign_pass = tested sign_tests in
  if sign_pass = total sign_tests && n > 5 then
    results := {
      pc_relationship = Preserves_sign;
      pc_confidence = 1.0 -. (1.0 /. float_of_int n);
      pc_counterexamples = 0;
      pc_samples_tested = n;
    } :: !results;

  (* Test: |output| <= |input| *)
  let bound_tests = List.map (fun (x, y) ->
    ((x, y), abs y <= abs x)
  ) (List.filter (fun (x, _) -> x <> 0) ps) in
  let bound_pass = tested bound_tests in
  let bound_total = total bound_tests in
  if bound_pass = bound_total && bound_total > 5 then
    results := {
      pc_relationship = Output_bounded_by_input;
      pc_confidence = 1.0 -. (1.0 /. float_of_int bound_total);
      pc_counterexamples = 0;
      pc_samples_tested = bound_total;
    } :: !results;

  (* Test: linear relationship y = a*x + b via least squares *)
  let fxs = List.map (fun (x, _) -> float_of_int x) ps in
  let fys = List.map (fun (_, y) -> float_of_int y) ps in
  let fn = float_of_int n in
  let sum_x = List.fold_left (+.) 0.0 fxs in
  let sum_y = List.fold_left (+.) 0.0 fys in
  let sum_xy = List.fold_left2 (fun acc x y -> acc +. x *. y) 0.0 fxs fys in
  let sum_xx = List.fold_left (fun acc x -> acc +. x *. x) 0.0 fxs in
  let denom = fn *. sum_xx -. sum_x *. sum_x in
  if abs_float denom > 1e-10 then begin
    let a = (fn *. sum_xy -. sum_x *. sum_y) /. denom in
    let b = (sum_y -. a *. sum_x) /. fn in
    (* Check residuals *)
    let max_residual = List.fold_left2 (fun acc x y ->
      let predicted = a *. x +. b in
      max acc (abs_float (y -. predicted))
    ) 0.0 fxs fys in
    if max_residual < 0.5 then
      results := {
        pc_relationship = Linear (a, b);
        pc_confidence = 1.0 -. (max_residual /. (fn +. 1.0));
        pc_counterexamples = 0;
        pc_samples_tested = n;
      } :: !results
  end;

  (* Test: quadratic y = a*x^2 + b*x + c via least squares *)
  let sum_x2 = sum_xx in
  let sum_x3 = List.fold_left (fun acc x -> acc +. x *. x *. x) 0.0 fxs in
  let sum_x4 = List.fold_left (fun acc x -> acc +. x *. x *. x *. x) 0.0 fxs in
  let sum_x2y = List.fold_left2 (fun acc x y -> acc +. x *. x *. y) 0.0 fxs fys in
  (* Solve 3x3 system using Cramer's rule *)
  let det3 a11 a12 a13 a21 a22 a23 a31 a32 a33 =
    a11 *. (a22 *. a33 -. a23 *. a32) -.
    a12 *. (a21 *. a33 -. a23 *. a31) +.
    a13 *. (a21 *. a32 -. a22 *. a31)
  in
  let d = det3 sum_x4 sum_x3 sum_x2 sum_x3 sum_x2 sum_x sum_x2 sum_x fn in
  if abs_float d > 1e-10 then begin
    let da = det3 sum_x2y sum_x3 sum_x2 sum_xy sum_x2 sum_x sum_y sum_x fn in
    let db = det3 sum_x4 sum_x2y sum_x2 sum_x3 sum_xy sum_x sum_x2 sum_y fn in
    let dc = det3 sum_x4 sum_x3 sum_x2y sum_x3 sum_x2 sum_xy sum_x2 sum_x sum_y in
    let qa = da /. d in
    let qb = db /. d in
    let qc = dc /. d in
    if abs_float qa > 1e-6 then begin
      let max_res = List.fold_left2 (fun acc x y ->
        let predicted = qa *. x *. x +. qb *. x +. qc in
        max acc (abs_float (y -. predicted))
      ) 0.0 fxs fys in
      if max_res < 0.5 then
        results := {
          pc_relationship = Quadratic (qa, qb, qc);
          pc_confidence = 1.0 -. (max_res /. (fn +. 1.0));
          pc_counterexamples = 0;
          pc_samples_tested = n;
        } :: !results
    end
  end;

  !results

(* ══════════ Engine 3: Exception Contract Inference ══════════ *)

let infer_exception_contracts (f : int -> int) (name : string) (num_samples : int) : exception_contract list =
  let exceptions = Hashtbl.create 16 in
  let total_tested = ref 0 in
  for i = 0 to num_samples - 1 do
    let x = i - (num_samples / 2) in
    incr total_tested;
    (try
      let _ = f x in ()
    with
    | Division_by_zero ->
      let key = "Division_by_zero" in
      let lst = try Hashtbl.find exceptions key with Not_found -> [] in
      Hashtbl.replace exceptions key (x :: lst)
    | Failure msg ->
      let key = "Failure: " ^ msg in
      let lst = try Hashtbl.find exceptions key with Not_found -> [] in
      Hashtbl.replace exceptions key (x :: lst)
    | Invalid_argument msg ->
      let key = "Invalid_argument: " ^ msg in
      let lst = try Hashtbl.find exceptions key with Not_found -> [] in
      Hashtbl.replace exceptions key (x :: lst)
    | _ ->
      let key = "Unknown_exception" in
      let lst = try Hashtbl.find exceptions key with Not_found -> [] in
      Hashtbl.replace exceptions key (x :: lst))
  done;
  let total = float_of_int !total_tested in
  Hashtbl.fold (fun exc_type inputs acc ->
    let sorted = List.sort compare inputs in
    let count = List.length sorted in
    let min_in = List.hd sorted in
    let max_in = List.nth sorted (count - 1) in
    let trigger_desc =
      if count = 1 then Printf.sprintf "x = %d" min_in
      else if min_in = max_in then Printf.sprintf "x = %d" min_in
      else Printf.sprintf "x in [%d, %d] (%d values)" min_in max_in count
    in
    {
      ec_exception_type = exc_type;
      ec_trigger_description = trigger_desc;
      ec_trigger_domain = {
        dc_name = name ^ "_" ^ exc_type ^ "_trigger";
        dc_lower = BoundInclusive min_in;
        dc_upper = BoundInclusive max_in;
        dc_excluded = [];
        dc_required_mod = None;
      };
      ec_frequency = float_of_int count /. total;
      ec_samples = count;
    } :: acc
  ) exceptions []

(* ══════════ Engine 4: Representation Invariant Detector ══════════ *)

type list_function = {
  lf_name: string;
  lf_func: int list -> int list;
}

let list_test_functions = [
  { lf_name = "List.rev"; lf_func = List.rev };
  { lf_name = "List.sort"; lf_func = List.sort compare };
  { lf_name = "List.tl_safe"; lf_func = (fun l -> match l with [] -> [] | _ :: t -> t) };
  { lf_name = "dedup"; lf_func = (fun l -> List.sort_uniq compare l) };
  { lf_name = "filter_pos"; lf_func = (fun l -> List.filter (fun x -> x > 0) l) };
]

let detect_invariants (lf : list_function) (num_samples : int) : repr_invariant list =
  let invariants = ref [] in
  let test_lists = Array.init num_samples (fun i ->
    let len = random_int 20 in
    List.init len (fun _ -> random_int_range (-50) 50 + i - i)
  ) in
  (* Invariant: length preserved *)
  let len_pres = ref 0 in
  let len_total = ref 0 in
  Array.iter (fun lst ->
    incr len_total;
    let out = lf.lf_func lst in
    if List.length out = List.length lst then incr len_pres
  ) test_lists;
  let lt = float_of_int !len_total in
  invariants := {
    ri_name = "length_preserved";
    ri_description = Printf.sprintf "|%s(xs)| = |xs|" lf.lf_name;
    ri_holds_count = !len_pres;
    ri_total_count = !len_total;
    ri_confidence = float_of_int !len_pres /. lt;
  } :: !invariants;

  (* Invariant: elements preserved (multiset equality) *)
  let elem_pres = ref 0 in
  let elem_total = ref 0 in
  Array.iter (fun lst ->
    incr elem_total;
    let out = lf.lf_func lst in
    let sorted_in = List.sort compare lst in
    let sorted_out = List.sort compare out in
    if sorted_in = sorted_out then incr elem_pres
  ) test_lists;
  invariants := {
    ri_name = "elements_preserved";
    ri_description = Printf.sprintf "multiset(%s(xs)) = multiset(xs)" lf.lf_name;
    ri_holds_count = !elem_pres;
    ri_total_count = !elem_total;
    ri_confidence = float_of_int !elem_pres /. float_of_int !elem_total;
  } :: !invariants;

  (* Invariant: output sorted *)
  let sorted_count = ref 0 in
  let sorted_total = ref 0 in
  Array.iter (fun lst ->
    incr sorted_total;
    let out = lf.lf_func lst in
    let is_sorted = let rec go = function
      | [] | [_] -> true
      | a :: b :: rest -> a <= b && go (b :: rest)
    in go out in
    if is_sorted then incr sorted_count
  ) test_lists;
  invariants := {
    ri_name = "output_sorted";
    ri_description = Printf.sprintf "%s(xs) is sorted" lf.lf_name;
    ri_holds_count = !sorted_count;
    ri_total_count = !sorted_total;
    ri_confidence = float_of_int !sorted_count /. float_of_int !sorted_total;
  } :: !invariants;

  (* Invariant: idempotent *)
  let idemp_count = ref 0 in
  let idemp_total = ref 0 in
  Array.iter (fun lst ->
    incr idemp_total;
    let out1 = lf.lf_func lst in
    let out2 = lf.lf_func out1 in
    if out1 = out2 then incr idemp_count
  ) test_lists;
  invariants := {
    ri_name = "idempotent";
    ri_description = Printf.sprintf "%s(%s(xs)) = %s(xs)" lf.lf_name lf.lf_name lf.lf_name;
    ri_holds_count = !idemp_count;
    ri_total_count = !idemp_total;
    ri_confidence = float_of_int !idemp_count /. float_of_int !idemp_total;
  } :: !invariants;

  (* Invariant: no duplicates in output *)
  let nodup_count = ref 0 in
  let nodup_total = ref 0 in
  Array.iter (fun lst ->
    incr nodup_total;
    let out = lf.lf_func lst in
    let unique = List.sort_uniq compare out in
    if List.length unique = List.length out then incr nodup_count
  ) test_lists;
  invariants := {
    ri_name = "output_unique";
    ri_description = Printf.sprintf "%s(xs) has no duplicates" lf.lf_name;
    ri_holds_count = !nodup_count;
    ri_total_count = !nodup_total;
    ri_confidence = float_of_int !nodup_count /. float_of_int !nodup_total;
  } :: !invariants;

  (* Invariant: output subset of input *)
  let subset_count = ref 0 in
  let subset_total = ref 0 in
  Array.iter (fun lst ->
    incr subset_total;
    let out = lf.lf_func lst in
    let is_subset = List.for_all (fun y -> List.mem y lst) out in
    if is_subset then incr subset_count
  ) test_lists;
  invariants := {
    ri_name = "output_subset";
    ri_description = Printf.sprintf "elements of %s(xs) ⊆ elements of xs" lf.lf_name;
    ri_holds_count = !subset_count;
    ri_total_count = !subset_total;
    ri_confidence = float_of_int !subset_count /. float_of_int !subset_total;
  } :: !invariants;

  (* Invariant: length non-increasing *)
  let lni_count = ref 0 in
  let lni_total = ref 0 in
  Array.iter (fun lst ->
    incr lni_total;
    let out = lf.lf_func lst in
    if List.length out <= List.length lst then incr lni_count
  ) test_lists;
  invariants := {
    ri_name = "length_non_increasing";
    ri_description = Printf.sprintf "|%s(xs)| <= |xs|" lf.lf_name;
    ri_holds_count = !lni_count;
    ri_total_count = !lni_total;
    ri_confidence = float_of_int !lni_count /. float_of_int !lni_total;
  } :: !invariants;

  (* Only return invariants with confidence > 0.5 *)
  List.filter (fun ri -> ri.ri_confidence > 0.5) !invariants

(* ══════════ Engine 5: Contract Minimizer ══════════ *)

let minimize_postconditions (pcs : postcondition list) : postcondition list =
  (* Remove redundant: if Linear exists, Monotonic is implied *)
  let has_linear = List.exists (fun pc -> match pc.pc_relationship with Linear _ -> true | _ -> false) pcs in
  let has_quad = List.exists (fun pc -> match pc.pc_relationship with Quadratic _ -> true | _ -> false) pcs in
  List.filter (fun pc ->
    match pc.pc_relationship with
    | Monotonic_increasing when has_linear -> false
    | Monotonic_decreasing when has_linear -> false
    | Output_nonnegative when has_quad -> false (* quadratic may imply it *)
    | Preserves_sign when has_linear -> false
    | _ -> true
  ) pcs

let minimize_invariants (invs : repr_invariant list) : repr_invariant list =
  (* If elements_preserved holds with 1.0, length_preserved is implied *)
  let has_elem_pres = List.exists (fun ri ->
    ri.ri_name = "elements_preserved" && ri.ri_confidence >= 0.99
  ) invs in
  (* If output_sorted + elements_preserved, idempotent is often implied *)
  let has_sorted = List.exists (fun ri ->
    ri.ri_name = "output_sorted" && ri.ri_confidence >= 0.99
  ) invs in
  List.filter (fun ri ->
    match ri.ri_name with
    | "length_preserved" when has_elem_pres -> false
    | "length_non_increasing" when has_elem_pres -> false
    | "output_subset" when has_elem_pres -> false
    | "idempotent" when has_sorted && has_elem_pres -> false
    | _ -> true
  ) invs

(* ══════════ Engine 6: Confidence Scorer ══════════ *)

let classify_strength (confidence : float) (samples : int) : contract_strength =
  if samples < 10 then Tentative
  else if confidence >= 0.98 then Strong
  else if confidence >= 0.85 then Moderate
  else if confidence >= 0.60 then Weak
  else Tentative

let score_contract (ic : inferred_contract) : float =
  let pc_score = match ic.ic_postconditions with
    | [] -> 0.0
    | pcs -> List.fold_left (fun acc pc -> acc +. pc.pc_confidence) 0.0 pcs
             /. float_of_int (List.length pcs)
  in
  let inv_score = match ic.ic_invariants with
    | [] -> 0.0
    | invs -> List.fold_left (fun acc ri -> acc +. ri.ri_confidence) 0.0 invs
              /. float_of_int (List.length invs)
  in
  let exc_penalty = match ic.ic_exception_contracts with
    | [] -> 0.0
    | ecs -> List.fold_left (fun acc ec -> acc +. ec.ec_frequency) 0.0 ecs
             /. float_of_int (List.length ecs)
  in
  let pre_score = match ic.ic_preconditions with
    | [] -> 0.5
    | pcs ->
      let unrestricted = List.exists (fun dc ->
        dc.dc_lower = Unbounded && dc.dc_upper = Unbounded && dc.dc_excluded = []
      ) pcs in
      if unrestricted then 1.0 else 0.7
  in
  let raw = (pc_score *. 0.35 +. inv_score *. 0.25 +. pre_score *. 0.25 +. (1.0 -. exc_penalty) *. 0.15) in
  min 1.0 (max 0.0 raw)

(* ══════════ Engine 7: Insight Generator ══════════ *)

let generate_insights (contracts : inferred_contract list) : contract_insight list =
  let insights = ref [] in
  List.iter (fun ic ->
    (* Tight domain insight *)
    List.iter (fun dc ->
      (match dc.dc_lower, dc.dc_upper with
       | BoundInclusive lo, BoundInclusive hi when hi - lo < 50 ->
         insights := TightDomain (ic.ic_function_name,
           Printf.sprintf "Very tight domain [%d, %d] — only %d valid inputs in probed range"
             lo hi (hi - lo + 1)) :: !insights
       | BoundInclusive _, Unbounded ->
         insights := TightDomain (ic.ic_function_name,
           "Has a lower bound — consider documenting minimum valid input") :: !insights
       | _ -> ())
    ) ic.ic_preconditions;

    (* Strong relationship insight *)
    List.iter (fun pc ->
      if pc.pc_confidence >= 0.99 then
        let desc = match pc.pc_relationship with
          | Linear (a, b) -> Printf.sprintf "Perfect linear relationship: y = %.1f*x + %.1f" a b
          | Quadratic (a, b, c) -> Printf.sprintf "Perfect quadratic: y = %.1f*x² + %.1f*x + %.1f" a b c
          | Monotonic_increasing -> "Strictly monotonic increasing"
          | Bounded (lo, hi) -> Printf.sprintf "Output always in [%d, %d]" lo hi
          | _ -> "Strong output guarantee"
        in
        insights := StrongRelationship (ic.ic_function_name, desc) :: !insights
    ) ic.ic_postconditions;

    (* Fragile contract *)
    if ic.ic_overall_confidence < 0.6 && ic.ic_samples_used > 20 then
      insights := FragileContract (ic.ic_function_name,
        "Low confidence despite many samples — behavior may be chaotic or state-dependent") :: !insights;

    (* Exception-heavy *)
    let exc_rate = List.fold_left (fun acc ec -> acc +. ec.ec_frequency) 0.0 ic.ic_exception_contracts in
    if exc_rate > 0.3 then
      insights := ExceptionHeavy (ic.ic_function_name,
        Printf.sprintf "%.0f%% of inputs cause exceptions — consider widening valid domain" (exc_rate *. 100.0)) :: !insights;

    (* Well-behaved *)
    if ic.ic_overall_confidence >= 0.95 && ic.ic_exception_contracts = [] then
      insights := WellBehaved ic.ic_function_name :: !insights;

  ) contracts;
  !insights

(* ══════════ Full Analysis Pipeline ══════════ *)

let analyze_function (tf : test_function) (num_samples : int) : inferred_contract =
  let preconds = probe_domain tf.tf_func tf.tf_name num_samples in
  let postconds = mine_relationships tf.tf_func tf.tf_name num_samples in
  let exc_contracts = infer_exception_contracts tf.tf_func tf.tf_name num_samples in
  let minimized_post = minimize_postconditions postconds in
  let contract = {
    ic_function_name = tf.tf_name;
    ic_preconditions = preconds;
    ic_postconditions = minimized_post;
    ic_exception_contracts = exc_contracts;
    ic_invariants = [];
    ic_strength = Tentative;
    ic_overall_confidence = 0.0;
    ic_samples_used = num_samples;
  } in
  let confidence = score_contract contract in
  let strength = classify_strength confidence num_samples in
  { contract with ic_overall_confidence = confidence; ic_strength = strength }

let analyze_list_function (lf : list_function) (num_samples : int) : inferred_contract =
  let invariants = detect_invariants lf num_samples in
  let minimized_inv = minimize_invariants invariants in
  let contract = {
    ic_function_name = lf.lf_name;
    ic_preconditions = [];
    ic_postconditions = [];
    ic_exception_contracts = [];
    ic_invariants = minimized_inv;
    ic_strength = Tentative;
    ic_overall_confidence = 0.0;
    ic_samples_used = num_samples;
  } in
  let confidence = score_contract contract in
  let strength = classify_strength confidence num_samples in
  { contract with ic_overall_confidence = confidence; ic_strength = strength }

let compute_fleet_health (contracts : inferred_contract list) : fleet_health =
  let n = List.length contracts in
  let total_contracts = List.fold_left (fun acc ic ->
    acc + List.length ic.ic_preconditions
        + List.length ic.ic_postconditions
        + List.length ic.ic_exception_contracts
        + List.length ic.ic_invariants
  ) 0 contracts in
  let avg_conf = if n = 0 then 0.0
    else List.fold_left (fun acc ic -> acc +. ic.ic_overall_confidence) 0.0 contracts /. float_of_int n in
  let strong_count = List.length (List.filter (fun ic -> ic.ic_strength = Strong) contracts) in
  let weak_count = List.length (List.filter (fun ic -> ic.ic_strength = Weak || ic.ic_strength = Tentative) contracts) in
  let health = if n = 0 then 0
    else int_of_float (avg_conf *. 70.0 +. (float_of_int strong_count /. float_of_int n) *. 30.0) in
  let insights = generate_insights contracts in
  {
    fh_total_functions = n;
    fh_total_contracts = total_contracts;
    fh_avg_confidence = avg_conf;
    fh_strong_count = strong_count;
    fh_weak_count = weak_count;
    fh_health_score = min 100 (max 0 health);
    fh_insights = insights;
  }

(* ══════════ Display Utilities ══════════ *)

let string_of_bound = function
  | Unbounded -> "∞"
  | BoundInclusive n -> string_of_int n
  | BoundExclusive n -> Printf.sprintf "%d (exclusive)" n

let string_of_relationship = function
  | Linear (a, b) -> Printf.sprintf "y = %.2f·x + %.2f" a b
  | Quadratic (a, b, c) -> Printf.sprintf "y = %.2f·x² + %.2f·x + %.2f" a b c
  | Monotonic_increasing -> "monotonic increasing"
  | Monotonic_decreasing -> "monotonic decreasing"
  | Bounded (lo, hi) -> Printf.sprintf "output ∈ [%d, %d]" lo hi
  | Idempotent_output -> "idempotent output"
  | Preserves_sign -> "preserves sign"
  | Output_positive -> "output > 0"
  | Output_nonnegative -> "output ≥ 0"
  | Output_bounded_by_input -> "|output| ≤ |input|"

let string_of_strength = function
  | Strong -> "STRONG"
  | Moderate -> "MODERATE"
  | Weak -> "WEAK"
  | Tentative -> "TENTATIVE"

let strength_emoji = function
  | Strong -> "🟢"
  | Moderate -> "🟡"
  | Weak -> "🟠"
  | Tentative -> "⚪"

let print_contract (ic : inferred_contract) =
  Printf.printf "\n╔══════════════════════════════════════════╗\n";
  Printf.printf "║ Contract: %-30s ║\n" ic.ic_function_name;
  Printf.printf "╚══════════════════════════════════════════╝\n";
  Printf.printf "  Strength: %s %s  (confidence: %.1f%%)\n"
    (strength_emoji ic.ic_strength)
    (string_of_strength ic.ic_strength)
    (ic.ic_overall_confidence *. 100.0);
  Printf.printf "  Samples: %d\n" ic.ic_samples_used;

  if ic.ic_preconditions <> [] then begin
    Printf.printf "\n  📋 Preconditions:\n";
    List.iter (fun dc ->
      Printf.printf "    • %s: [%s, %s]" dc.dc_name
        (string_of_bound dc.dc_lower) (string_of_bound dc.dc_upper);
      (match dc.dc_required_mod with
       | Some (m, r) -> Printf.printf " (requires x mod %d = %d)" m r
       | None -> ());
      if dc.dc_excluded <> [] then
        Printf.printf " excluding {%s}"
          (String.concat ", " (List.map string_of_int dc.dc_excluded));
      Printf.printf "\n"
    ) ic.ic_preconditions
  end;

  if ic.ic_postconditions <> [] then begin
    Printf.printf "\n  📊 Postconditions:\n";
    List.iter (fun pc ->
      Printf.printf "    • %s  (%.1f%% confidence, %d samples)\n"
        (string_of_relationship pc.pc_relationship)
        (pc.pc_confidence *. 100.0)
        pc.pc_samples_tested
    ) ic.ic_postconditions
  end;

  if ic.ic_exception_contracts <> [] then begin
    Printf.printf "\n  ⚠️  Exception Contracts:\n";
    List.iter (fun ec ->
      Printf.printf "    • %s when %s (%.1f%% of inputs)\n"
        ec.ec_exception_type ec.ec_trigger_description (ec.ec_frequency *. 100.0)
    ) ic.ic_exception_contracts
  end;

  if ic.ic_invariants <> [] then begin
    Printf.printf "\n  🔒 Representation Invariants:\n";
    List.iter (fun ri ->
      Printf.printf "    • %s  (%d/%d, %.1f%%)\n"
        ri.ri_description ri.ri_holds_count ri.ri_total_count (ri.ri_confidence *. 100.0)
    ) ic.ic_invariants
  end

let print_fleet_health (fh : fleet_health) =
  Printf.printf "\n╔══════════════════════════════════════════════════╗\n";
  Printf.printf "║          CONTRACT INFERENCE FLEET HEALTH         ║\n";
  Printf.printf "╠══════════════════════════════════════════════════╣\n";
  Printf.printf "║  Health Score: %3d/100                           ║\n" fh.fh_health_score;
  Printf.printf "║  Functions analyzed: %d                          ║\n" fh.fh_total_functions;
  Printf.printf "║  Total contracts: %d                             ║\n" fh.fh_total_contracts;
  Printf.printf "║  Avg confidence: %.1f%%                          ║\n" (fh.fh_avg_confidence *. 100.0);
  Printf.printf "║  Strong: %d  |  Weak/Tentative: %d               ║\n" fh.fh_strong_count fh.fh_weak_count;
  Printf.printf "╚══════════════════════════════════════════════════╝\n";
  if fh.fh_insights <> [] then begin
    Printf.printf "\n  💡 Autonomous Insights:\n";
    List.iter (fun insight ->
      match insight with
      | TightDomain (fn, desc) ->
        Printf.printf "    🎯 [%s] %s\n" fn desc
      | StrongRelationship (fn, desc) ->
        Printf.printf "    💪 [%s] %s\n" fn desc
      | FragileContract (fn, desc) ->
        Printf.printf "    ⚡ [%s] %s\n" fn desc
      | ExceptionHeavy (fn, desc) ->
        Printf.printf "    🔥 [%s] %s\n" fn desc
      | WellBehaved fn ->
        Printf.printf "    ✅ [%s] Well-behaved — total function with strong contracts\n" fn
      | RedundantContract (fn, desc) ->
        Printf.printf "    ♻️  [%s] %s\n" fn desc
      | InsufficientData (fn, desc) ->
        Printf.printf "    📉 [%s] %s\n" fn desc
    ) fh.fh_insights
  end

(* ══════════ HTML Dashboard ══════════ *)

let generate_dashboard (contracts : inferred_contract list) (fh : fleet_health) : string =
  let buf = Buffer.create 8192 in
  let add = Buffer.add_string buf in
  add "<!DOCTYPE html><html><head><meta charset='utf-8'>\n";
  add "<title>Contract Inference Dashboard</title>\n";
  add "<style>\n";
  add "body { font-family: -apple-system, BlinkMacSystemFont, sans-serif; margin: 0; padding: 20px; background: #0d1117; color: #c9d1d9; }\n";
  add ".header { text-align: center; margin-bottom: 30px; }\n";
  add ".header h1 { color: #58a6ff; font-size: 2em; }\n";
  add ".score-ring { display: inline-block; width: 120px; height: 120px; border-radius: 50%; ";
  add "border: 8px solid; line-height: 120px; text-align: center; font-size: 2em; font-weight: bold; }\n";
  add (Printf.sprintf ".score-ring { border-color: %s; color: %s; }\n"
    (if fh.fh_health_score >= 80 then "#3fb950" else if fh.fh_health_score >= 60 then "#d29922" else "#f85149")
    (if fh.fh_health_score >= 80 then "#3fb950" else if fh.fh_health_score >= 60 then "#d29922" else "#f85149"));
  add ".stats { display: flex; justify-content: center; gap: 40px; margin: 20px 0; }\n";
  add ".stat { text-align: center; } .stat-val { font-size: 1.8em; font-weight: bold; color: #58a6ff; }\n";
  add ".stat-label { color: #8b949e; font-size: 0.9em; }\n";
  add ".cards { display: grid; grid-template-columns: repeat(auto-fill, minmax(400px, 1fr)); gap: 16px; }\n";
  add ".card { background: #161b22; border: 1px solid #30363d; border-radius: 8px; padding: 16px; }\n";
  add ".card h3 { margin: 0 0 8px 0; color: #58a6ff; }\n";
  add ".badge { display: inline-block; padding: 2px 8px; border-radius: 12px; font-size: 0.8em; font-weight: bold; }\n";
  add ".badge-strong { background: #238636; color: white; }\n";
  add ".badge-moderate { background: #9e6a03; color: white; }\n";
  add ".badge-weak { background: #da3633; color: white; }\n";
  add ".badge-tentative { background: #484f58; color: white; }\n";
  add ".contract-item { margin: 6px 0; padding: 4px 8px; background: #0d1117; border-radius: 4px; font-size: 0.9em; }\n";
  add ".insight { padding: 8px 12px; margin: 6px 0; background: #161b22; border-left: 3px solid #58a6ff; border-radius: 4px; }\n";
  add ".insights-section { margin-top: 24px; }\n";
  add "</style></head><body>\n";
  add "<div class='header'>\n";
  add "<h1>🔍 Contract Inference Engine</h1>\n";
  add "<p>Autonomous Behavioral Contract Discovery</p>\n";
  add (Printf.sprintf "<div class='score-ring'>%d</div>\n" fh.fh_health_score);
  add "</div>\n";
  add "<div class='stats'>\n";
  add (Printf.sprintf "<div class='stat'><div class='stat-val'>%d</div><div class='stat-label'>Functions</div></div>\n" fh.fh_total_functions);
  add (Printf.sprintf "<div class='stat'><div class='stat-val'>%d</div><div class='stat-label'>Contracts</div></div>\n" fh.fh_total_contracts);
  add (Printf.sprintf "<div class='stat'><div class='stat-val'>%.0f%%</div><div class='stat-label'>Avg Confidence</div></div>\n" (fh.fh_avg_confidence *. 100.0));
  add (Printf.sprintf "<div class='stat'><div class='stat-val'>%d</div><div class='stat-label'>Strong</div></div>\n" fh.fh_strong_count);
  add "</div>\n";
  add "<div class='cards'>\n";
  List.iter (fun ic ->
    let badge_class = match ic.ic_strength with
      | Strong -> "badge-strong" | Moderate -> "badge-moderate"
      | Weak -> "badge-weak" | Tentative -> "badge-tentative"
    in
    add "<div class='card'>\n";
    add (Printf.sprintf "<h3>%s %s</h3>\n" (strength_emoji ic.ic_strength) ic.ic_function_name);
    add (Printf.sprintf "<span class='badge %s'>%s</span> " badge_class (string_of_strength ic.ic_strength));
    add (Printf.sprintf "<span style='color:#8b949e'>%.0f%% confidence · %d samples</span>\n"
      (ic.ic_overall_confidence *. 100.0) ic.ic_samples_used);

    if ic.ic_preconditions <> [] then begin
      add "<h4 style='color:#c9d1d9;margin:12px 0 4px'>📋 Preconditions</h4>\n";
      List.iter (fun dc ->
        add (Printf.sprintf "<div class='contract-item'>%s: [%s, %s]"
          dc.dc_name (string_of_bound dc.dc_lower) (string_of_bound dc.dc_upper));
        (match dc.dc_required_mod with
         | Some (m, r) -> add (Printf.sprintf " (x mod %d = %d)" m r)
         | None -> ());
        add "</div>\n"
      ) ic.ic_preconditions
    end;

    if ic.ic_postconditions <> [] then begin
      add "<h4 style='color:#c9d1d9;margin:12px 0 4px'>📊 Postconditions</h4>\n";
      List.iter (fun pc ->
        add (Printf.sprintf "<div class='contract-item'>%s <span style='color:#8b949e'>(%.0f%%)</span></div>\n"
          (string_of_relationship pc.pc_relationship) (pc.pc_confidence *. 100.0))
      ) ic.ic_postconditions
    end;

    if ic.ic_exception_contracts <> [] then begin
      add "<h4 style='color:#c9d1d9;margin:12px 0 4px'>⚠️ Exceptions</h4>\n";
      List.iter (fun ec ->
        add (Printf.sprintf "<div class='contract-item'>%s when %s (%.1f%%)</div>\n"
          ec.ec_exception_type ec.ec_trigger_description (ec.ec_frequency *. 100.0))
      ) ic.ic_exception_contracts
    end;

    if ic.ic_invariants <> [] then begin
      add "<h4 style='color:#c9d1d9;margin:12px 0 4px'>🔒 Invariants</h4>\n";
      List.iter (fun ri ->
        add (Printf.sprintf "<div class='contract-item'>%s <span style='color:#8b949e'>(%d/%d, %.0f%%)</span></div>\n"
          ri.ri_description ri.ri_holds_count ri.ri_total_count (ri.ri_confidence *. 100.0))
      ) ic.ic_invariants
    end;

    add "</div>\n"
  ) contracts;
  add "</div>\n";

  if fh.fh_insights <> [] then begin
    add "<div class='insights-section'>\n";
    add "<h2 style='color:#58a6ff'>💡 Autonomous Insights</h2>\n";
    List.iter (fun insight ->
      let (icon, _fn, desc) = match insight with
        | TightDomain (fn, d) -> ("🎯", fn, d)
        | StrongRelationship (fn, d) -> ("💪", fn, d)
        | FragileContract (fn, d) -> ("⚡", fn, d)
        | ExceptionHeavy (fn, d) -> ("🔥", fn, d)
        | WellBehaved fn -> ("✅", fn, "Well-behaved total function")
        | RedundantContract (fn, d) -> ("♻️", fn, d)
        | InsufficientData (fn, d) -> ("📉", fn, d)
      in
      add (Printf.sprintf "<div class='insight'>%s %s — %s</div>\n" icon _fn desc)
    ) fh.fh_insights;
    add "</div>\n"
  end;

  add "</body></html>\n";
  Buffer.contents buf

(* ══════════ Main Entry Point ══════════ *)

let () =
  let args = Array.to_list Sys.argv in
  let mode = if List.mem "--dashboard" args then "dashboard"
    else if List.mem "--demo" args then "demo"
    else "demo" in

  let num_samples = 200 in

  Printf.printf "🔍 Contract Inference Engine — Autonomous Behavioral Contract Discovery\n";
  Printf.printf "═══════════════════════════════════════════════════════════════════════\n\n";

  (* Analyze scalar functions *)
  Printf.printf "Phase 1: Analyzing %d scalar functions...\n" (List.length test_functions);
  let scalar_contracts = List.map (fun tf -> analyze_function tf num_samples) test_functions in

  (* Analyze list functions *)
  Printf.printf "Phase 2: Analyzing %d list functions...\n" (List.length list_test_functions);
  let list_contracts = List.map (fun lf -> analyze_list_function lf num_samples) list_test_functions in

  let all_contracts = scalar_contracts @ list_contracts in

  (* Print individual contracts *)
  if mode = "demo" || mode = "dashboard" then
    List.iter print_contract all_contracts;

  (* Fleet health *)
  let fh = compute_fleet_health all_contracts in
  print_fleet_health fh;

  (* Dashboard *)
  if mode = "dashboard" then begin
    let html = generate_dashboard all_contracts fh in
    let oc = open_out "contract_inference_dashboard.html" in
    output_string oc html;
    close_out oc;
    Printf.printf "\n📄 Dashboard written to contract_inference_dashboard.html\n"
  end;

  Printf.printf "\n✅ Contract inference complete. %d contracts discovered across %d functions.\n"
    fh.fh_total_contracts fh.fh_total_functions
