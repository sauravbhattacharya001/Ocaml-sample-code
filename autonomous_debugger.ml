(* ============================================================================
   autonomous_debugger.ml - Autonomous Debugging Engine
   ============================================================================

   An autonomous fault localization and debugging engine for OCaml programs.
   Given a program represented as a set of statements/components and a test
   suite with passing/failing tests, this engine automatically investigates
   bugs using multiple analysis techniques and generates fix suggestions.

   Demonstrates:
   - Spectrum-based fault localization (Tarantula, Ochiai, DStar)
   - Delta debugging for failing input minimization
   - Mutation-based fault localization (which mutations make failures pass?)
   - Suspicious pattern detection (common bug patterns)
   - Autonomous fix suggestion generation
   - Root cause chain analysis
   - Multi-phase investigation pipeline
   - Health scoring 0-100
   - Interactive HTML dashboard generation

   7 investigation engines:
   1. Spectrum Analyzer    — Tarantula/Ochiai/DStar suspiciousness scoring
   2. Delta Debugger       — minimal failing input isolation via ddmin
   3. Mutation Localizer   — identifies fix locations via targeted mutations
   4. Pattern Scanner      — detects common bug patterns in code structure
   5. Root Cause Tracer    — builds causal chains from symptoms to origins
   6. Fix Suggester        — generates concrete fix recommendations
   7. Insight Generator    — produces autonomous debugging insights

   Usage:
     ocamlopt autonomous_debugger.ml -o autonomous_debugger
     ./autonomous_debugger --demo
     ./autonomous_debugger --dashboard
     (or) ocaml autonomous_debugger.ml --demo
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

type component_kind =
  | Assignment
  | Conditional
  | Loop
  | FunctionCall
  | Return
  | Exception
  | PatternMatch

type component = {
  comp_id: int;
  comp_name: string;
  comp_kind: component_kind;
  comp_line: int;
  comp_file: string;
  comp_source: string;
}

type test_outcome = Pass | Fail | Error of string

type test_result = {
  test_id: int;
  test_name: string;
  test_outcome: test_outcome;
  covered_components: int list;  (* component ids executed *)
  test_input: string;
  test_expected: string;
  test_actual: string;
  test_duration_ms: float;
}

type suspiciousness_metric = Tarantula | Ochiai | DStar of float

type suspiciousness_score = {
  susp_component: int;
  susp_tarantula: float;
  susp_ochiai: float;
  susp_dstar: float;
  susp_rank: int;
}

type delta_result = {
  delta_original_input: string list;
  delta_minimal_input: string list;
  delta_reduction_ratio: float;
  delta_steps: int;
}

type mutation_kind =
  | NegateCondition
  | SwapOperands
  | ChangeOperator
  | RemoveStatement
  | ChangeConstant
  | SwapBranches

type mutation_result = {
  mut_component: int;
  mut_kind: mutation_kind;
  mut_description: string;
  mut_fixes_failure: bool;
  mut_new_passes: int;
  mut_new_fails: int;
}

type bug_pattern =
  | OffByOne
  | FencepostError
  | NullDeref
  | UnhandledException
  | InfiniteLoop
  | WrongOperator
  | MissingBaseCase
  | TypeCoercion
  | RaceCondition
  | ResourceLeak

type pattern_match = {
  pat_component: int;
  pat_pattern: bug_pattern;
  pat_confidence: float;
  pat_evidence: string;
}

type root_cause = {
  rc_origin_component: int;
  rc_symptom_components: int list;
  rc_chain: string list;  (* causal chain description *)
  rc_confidence: float;
  rc_category: string;
}

type fix_suggestion = {
  fix_component: int;
  fix_description: string;
  fix_code_before: string;
  fix_code_after: string;
  fix_confidence: float;
  fix_pattern: bug_pattern option;
}

type severity = Critical | High | Medium | Low | Info

type insight = {
  insight_text: string;
  insight_severity: severity;
  insight_category: string;
}

type investigation_report = {
  rpt_components: component list;
  rpt_tests: test_result list;
  rpt_suspiciousness: suspiciousness_score list;
  rpt_delta: delta_result list;
  rpt_mutations: mutation_result list;
  rpt_patterns: pattern_match list;
  rpt_root_causes: root_cause list;
  rpt_fixes: fix_suggestion list;
  rpt_insights: insight list;
  rpt_health_score: int;
  rpt_health_tier: string;
}

(* ══════════ Utility Functions ══════════ *)

let component_kind_to_string = function
  | Assignment -> "Assignment"
  | Conditional -> "Conditional"
  | Loop -> "Loop"
  | FunctionCall -> "FunctionCall"
  | Return -> "Return"
  | Exception -> "Exception"
  | PatternMatch -> "PatternMatch"

let bug_pattern_to_string = function
  | OffByOne -> "Off-by-one"
  | FencepostError -> "Fencepost error"
  | NullDeref -> "Null dereference"
  | UnhandledException -> "Unhandled exception"
  | InfiniteLoop -> "Infinite loop"
  | WrongOperator -> "Wrong operator"
  | MissingBaseCase -> "Missing base case"
  | TypeCoercion -> "Type coercion"
  | RaceCondition -> "Race condition"
  | ResourceLeak -> "Resource leak"

let mutation_kind_to_string = function
  | NegateCondition -> "Negate condition"
  | SwapOperands -> "Swap operands"
  | ChangeOperator -> "Change operator"
  | RemoveStatement -> "Remove statement"
  | ChangeConstant -> "Change constant"
  | SwapBranches -> "Swap branches"

let severity_to_string = function
  | Critical -> "CRITICAL"
  | High -> "HIGH"
  | Medium -> "MEDIUM"
  | Low -> "LOW"
  | Info -> "INFO"

let test_is_failing t = match t.test_outcome with
  | Fail | Error _ -> true
  | Pass -> false

let clamp_f lo hi x = max lo (min hi x)

(* ══════════ Engine 1: Spectrum Analyzer ══════════ *)

module SpectrumAnalyzer = struct
  (* Count pass/fail coverage for each component *)
  type coverage_stats = {
    cs_passed_covered: int;    (* # passing tests covering this component *)
    cs_passed_uncovered: int;  (* # passing tests NOT covering this component *)
    cs_failed_covered: int;    (* # failing tests covering this component *)
    cs_failed_uncovered: int;  (* # failing tests NOT covering this component *)
  }

  let compute_coverage_stats components tests =
    let total_pass = List.length (List.filter (fun t -> not (test_is_failing t)) tests) in
    let total_fail = List.length (List.filter test_is_failing tests) in
    List.map (fun comp ->
      let pc = List.length (List.filter (fun t ->
        not (test_is_failing t) && List.mem comp.comp_id t.covered_components
      ) tests) in
      let fc = List.length (List.filter (fun t ->
        test_is_failing t && List.mem comp.comp_id t.covered_components
      ) tests) in
      (comp.comp_id, {
        cs_passed_covered = pc;
        cs_passed_uncovered = total_pass - pc;
        cs_failed_covered = fc;
        cs_failed_uncovered = total_fail - fc;
      })
    ) components

  (* Tarantula: failed_ratio / (failed_ratio + passed_ratio) *)
  let tarantula stats total_pass total_fail =
    if total_fail = 0 then 0.0
    else
      let fr = float_of_int stats.cs_failed_covered /. float_of_int (max 1 total_fail) in
      let pr = float_of_int stats.cs_passed_covered /. float_of_int (max 1 total_pass) in
      if fr +. pr = 0.0 then 0.0
      else fr /. (fr +. pr)

  (* Ochiai: fc / sqrt(total_fail * (fc + pc)) *)
  let ochiai stats total_fail =
    let fc = float_of_int stats.cs_failed_covered in
    let tf = float_of_int total_fail in
    let denom = sqrt (tf *. (fc +. float_of_int stats.cs_passed_covered)) in
    if denom = 0.0 then 0.0
    else fc /. denom

  (* DStar: fc^star / (pc + fu), default star=2 *)
  let dstar ?(star=2.0) stats =
    let fc = float_of_int stats.cs_failed_covered in
    let pc = float_of_int stats.cs_passed_covered in
    let fu = float_of_int stats.cs_failed_uncovered in
    let denom = pc +. fu in
    if denom = 0.0 then
      if fc > 0.0 then 1000.0  (* very suspicious *)
      else 0.0
    else (fc ** star) /. denom

  let analyze components tests =
    let total_pass = List.length (List.filter (fun t -> not (test_is_failing t)) tests) in
    let total_fail = List.length (List.filter test_is_failing tests) in
    let stats_list = compute_coverage_stats components tests in
    let scores = List.map (fun (cid, stats) ->
      {
        susp_component = cid;
        susp_tarantula = tarantula stats total_pass total_fail;
        susp_ochiai = ochiai stats total_fail;
        susp_dstar = dstar stats;
        susp_rank = 0;  (* filled in later *)
      }
    ) stats_list in
    (* rank by Ochiai score descending *)
    let sorted = List.sort (fun a b ->
      compare b.susp_ochiai a.susp_ochiai
    ) scores in
    List.mapi (fun i s -> { s with susp_rank = i + 1 }) sorted
end

(* ══════════ Engine 2: Delta Debugger ══════════ *)

module DeltaDebugger = struct
  (* ddmin algorithm: find minimal subset that still triggers failure *)
  (* test_fn: input subset -> true if still failing *)
  let ddmin test_fn input =
    let n = List.length input in
    if n = 0 then { delta_original_input = []; delta_minimal_input = [];
                     delta_reduction_ratio = 1.0; delta_steps = 0 } else
    let arr = Array.of_list input in
    let steps = ref 0 in
    let current = ref (Array.to_list arr) in
    let granularity = ref 2 in
    let cont = ref true in
    while !cont do
      let cur_arr = Array.of_list !current in
      let len = Array.length cur_arr in
      if len <= 1 || !granularity > len then
        cont := false
      else begin
        let chunk_size = max 1 (len / !granularity) in
        let found = ref false in
        (* Try each subset (complement) *)
        let i = ref 0 in
        while !i < !granularity && not !found do
          let start_idx = !i * chunk_size in
          let end_idx = min len (start_idx + chunk_size) in
          (* Try subset *)
          let subset = Array.to_list (Array.sub cur_arr start_idx (end_idx - start_idx)) in
          incr steps;
          if List.length subset > 0 && test_fn subset then begin
            current := subset;
            granularity := max 2 (!granularity - 1);
            found := true
          end else begin
            (* Try complement *)
            let complement = List.filteri (fun idx _ ->
              idx < start_idx || idx >= end_idx
            ) (Array.to_list cur_arr) in
            incr steps;
            if List.length complement > 0 && test_fn complement then begin
              current := complement;
              granularity := max 2 (!granularity - 1);
              found := true
            end
          end;
          incr i
        done;
        if not !found then begin
          if !granularity >= len then
            cont := false
          else
            granularity := min len (!granularity * 2)
        end
      end
    done;
    let minimal = !current in
    let orig_len = float_of_int n in
    let min_len = float_of_int (List.length minimal) in
    {
      delta_original_input = input;
      delta_minimal_input = minimal;
      delta_reduction_ratio = if orig_len = 0.0 then 1.0
                              else 1.0 -. (min_len /. orig_len);
      delta_steps = !steps;
    }
end

(* ══════════ Engine 3: Mutation Localizer ══════════ *)

module MutationLocalizer = struct
  let all_mutations = [
    NegateCondition; SwapOperands; ChangeOperator;
    RemoveStatement; ChangeConstant; SwapBranches
  ]

  let applicable_mutations comp =
    match comp.comp_kind with
    | Conditional -> [NegateCondition; SwapBranches; ChangeOperator]
    | Assignment -> [SwapOperands; ChangeConstant; ChangeOperator]
    | Loop -> [NegateCondition; ChangeConstant; ChangeOperator]
    | FunctionCall -> [RemoveStatement; SwapOperands]
    | Return -> [ChangeConstant; RemoveStatement]
    | Exception -> [RemoveStatement]
    | PatternMatch -> [SwapBranches; RemoveStatement]

  (* Simulate mutation testing: does mutating comp fix failures? *)
  (* In real use, would re-run tests; here we use heuristic based on suspiciousness *)
  let simulate_mutation comp mut_kind susp_scores tests =
    let score = List.find_opt (fun s -> s.susp_component = comp.comp_id) susp_scores in
    let base_susp = match score with
      | Some s -> s.susp_ochiai
      | None -> 0.0
    in
    (* Higher suspiciousness + certain mutation types = higher fix probability *)
    let fix_boost = match mut_kind with
      | NegateCondition -> 0.3
      | ChangeOperator -> 0.25
      | ChangeConstant -> 0.2
      | SwapOperands -> 0.15
      | SwapBranches -> 0.15
      | RemoveStatement -> 0.1
    in
    let fix_prob = clamp_f 0.0 1.0 (base_susp *. (1.0 +. fix_boost)) in
    let r = random_float () in
    let total_fail = List.length (List.filter test_is_failing tests) in
    let total_pass = List.length (List.filter (fun t -> not (test_is_failing t)) tests) in
    let fixes = r < fix_prob *. 0.5 in
    {
      mut_component = comp.comp_id;
      mut_kind;
      mut_description = Printf.sprintf "%s at %s (line %d)"
        (mutation_kind_to_string mut_kind) comp.comp_name comp.comp_line;
      mut_fixes_failure = fixes;
      mut_new_passes = if fixes then total_pass + (total_fail / 2) else total_pass;
      mut_new_fails = if fixes then total_fail / 2 else total_fail;
    }

  let analyze components susp_scores tests =
    List.concat_map (fun comp ->
      let muts = applicable_mutations comp in
      List.map (fun mk ->
        simulate_mutation comp mk susp_scores tests
      ) muts
    ) components
end

(* ══════════ Engine 4: Pattern Scanner ══════════ *)

module PatternScanner = struct
  let all_patterns = [
    OffByOne; FencepostError; NullDeref; UnhandledException;
    InfiniteLoop; WrongOperator; MissingBaseCase; TypeCoercion;
    RaceCondition; ResourceLeak
  ]

  let detect_patterns_for comp susp_scores =
    let score = List.find_opt (fun s -> s.susp_component = comp.comp_id) susp_scores in
    let base_susp = match score with Some s -> s.susp_ochiai | None -> 0.0 in
    let candidates = match comp.comp_kind with
      | Loop ->
        [(OffByOne, 0.7); (FencepostError, 0.6); (InfiniteLoop, 0.5)]
      | Conditional ->
        [(WrongOperator, 0.65); (NullDeref, 0.4); (MissingBaseCase, 0.5)]
      | Assignment ->
        [(TypeCoercion, 0.3); (WrongOperator, 0.4)]
      | FunctionCall ->
        [(UnhandledException, 0.5); (NullDeref, 0.45); (ResourceLeak, 0.35)]
      | Return ->
        [(NullDeref, 0.3); (TypeCoercion, 0.25)]
      | Exception ->
        [(UnhandledException, 0.6); (ResourceLeak, 0.4)]
      | PatternMatch ->
        [(MissingBaseCase, 0.6); (WrongOperator, 0.3)]
    in
    List.filter_map (fun (pat, base_conf) ->
      let conf = clamp_f 0.0 1.0 (base_conf *. (0.5 +. base_susp)) in
      if conf > 0.25 then
        let evidence = match pat with
          | OffByOne -> Printf.sprintf "Loop at line %d: boundary condition may be off by 1" comp.comp_line
          | FencepostError -> Printf.sprintf "Loop at line %d: iteration count mismatch with boundary" comp.comp_line
          | NullDeref -> Printf.sprintf "%s at line %d: potential null/None access" comp.comp_name comp.comp_line
          | UnhandledException -> Printf.sprintf "%s at line %d: exception path not covered" comp.comp_name comp.comp_line
          | InfiniteLoop -> Printf.sprintf "Loop at line %d: termination condition may be unsatisfiable" comp.comp_line
          | WrongOperator -> Printf.sprintf "%s at line %d: operator may be incorrect (< vs <=, + vs -)" comp.comp_name comp.comp_line
          | MissingBaseCase -> Printf.sprintf "%s at line %d: recursive/match may lack a base case" comp.comp_name comp.comp_line
          | TypeCoercion -> Printf.sprintf "%s at line %d: implicit type conversion may lose precision" comp.comp_name comp.comp_line
          | RaceCondition -> Printf.sprintf "%s at line %d: concurrent access without synchronization" comp.comp_name comp.comp_line
          | ResourceLeak -> Printf.sprintf "%s at line %d: resource may not be released on all paths" comp.comp_name comp.comp_line
        in
        Some { pat_component = comp.comp_id; pat_pattern = pat;
               pat_confidence = conf; pat_evidence = evidence }
      else None
    ) candidates

  let analyze components susp_scores =
    List.concat_map (fun comp ->
      detect_patterns_for comp susp_scores
    ) components
end

(* ══════════ Engine 5: Root Cause Tracer ══════════ *)

module RootCauseTracer = struct
  (* Build causal chains from high-suspiciousness to symptoms *)
  let trace components susp_scores tests patterns =
    (* Find top suspicious components *)
    let sorted_susp = List.sort (fun a b ->
      compare b.susp_ochiai a.susp_ochiai
    ) susp_scores in
    let top_suspicious = List.filteri (fun i _ -> i < 5) sorted_susp in
    (* For each top suspect, build a causal chain *)
    List.filter_map (fun susp ->
      if susp.susp_ochiai < 0.2 then None
      else begin
        let comp = List.find_opt (fun c -> c.comp_id = susp.susp_component) components in
        match comp with
        | None -> None
        | Some c ->
          (* Find failing tests that cover this component *)
          let failing_covering = List.filter (fun t ->
            test_is_failing t && List.mem c.comp_id t.covered_components
          ) tests in
          (* Find other components also covered by these failures *)
          let symptom_ids = List.sort_uniq compare (
            List.concat_map (fun t ->
              List.filter (fun cid -> cid <> c.comp_id) t.covered_components
            ) failing_covering
          ) in
          let symptom_ids = List.filteri (fun i _ -> i < 5) symptom_ids in
          (* Build chain *)
          let related_patterns = List.filter (fun p ->
            p.pat_component = c.comp_id
          ) patterns in
          let pattern_desc = match related_patterns with
            | p :: _ -> Printf.sprintf " (likely %s)" (bug_pattern_to_string p.pat_pattern)
            | [] -> ""
          in
          let chain = [
            Printf.sprintf "Origin: %s at line %d%s" c.comp_name c.comp_line pattern_desc;
            Printf.sprintf "Suspiciousness: Ochiai=%.3f, rank #%d" susp.susp_ochiai susp.susp_rank;
            Printf.sprintf "Covered by %d/%d failing tests"
              (List.length failing_covering)
              (List.length (List.filter test_is_failing tests));
            Printf.sprintf "Propagates to %d downstream components" (List.length symptom_ids);
          ] in
          let category = match related_patterns with
            | p :: _ -> bug_pattern_to_string p.pat_pattern
            | [] -> (match c.comp_kind with
              | Loop -> "Loop logic error"
              | Conditional -> "Conditional logic error"
              | _ -> "Unknown")
          in
          Some {
            rc_origin_component = c.comp_id;
            rc_symptom_components = symptom_ids;
            rc_chain = chain;
            rc_confidence = clamp_f 0.0 1.0 (susp.susp_ochiai *. 1.2);
            rc_category = category;
          }
      end
    ) top_suspicious
end

(* ══════════ Engine 6: Fix Suggester ══════════ *)

module FixSuggester = struct
  let suggest_fix comp pattern =
    match pattern with
    | OffByOne ->
      { fix_component = comp.comp_id;
        fix_description = "Adjust loop boundary by ±1";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "(* Fix: check < vs <= in: %s *)" comp.comp_source;
        fix_confidence = 0.75;
        fix_pattern = Some OffByOne }
    | FencepostError ->
      { fix_component = comp.comp_id;
        fix_description = "Add/remove edge iteration for fencepost";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "(* Fix: verify iteration count matches elements: %s *)" comp.comp_source;
        fix_confidence = 0.7;
        fix_pattern = Some FencepostError }
    | NullDeref ->
      { fix_component = comp.comp_id;
        fix_description = "Add None/null check before access";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "(match value with Some x -> ... | None -> default) (* was: %s *)" comp.comp_source;
        fix_confidence = 0.8;
        fix_pattern = Some NullDeref }
    | UnhandledException ->
      { fix_component = comp.comp_id;
        fix_description = "Wrap in try/with for unhandled exception";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "(try %s with exn -> handle exn)" comp.comp_source;
        fix_confidence = 0.7;
        fix_pattern = Some UnhandledException }
    | InfiniteLoop ->
      { fix_component = comp.comp_id;
        fix_description = "Add progress guarantee to loop termination condition";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "(* Fix: ensure loop variant decreases: %s *)" comp.comp_source;
        fix_confidence = 0.6;
        fix_pattern = Some InfiniteLoop }
    | WrongOperator ->
      { fix_component = comp.comp_id;
        fix_description = "Check operator: < vs <=, + vs -, && vs ||";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "(* Fix: verify operator choice in: %s *)" comp.comp_source;
        fix_confidence = 0.65;
        fix_pattern = Some WrongOperator }
    | MissingBaseCase ->
      { fix_component = comp.comp_id;
        fix_description = "Add missing base case for recursion/pattern match";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "| [] -> base_value (* added base case *)\n%s" comp.comp_source;
        fix_confidence = 0.75;
        fix_pattern = Some MissingBaseCase }
    | TypeCoercion ->
      { fix_component = comp.comp_id;
        fix_description = "Use explicit conversion to prevent precision loss";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "(* Fix: explicit float_of_int/int_of_float in: %s *)" comp.comp_source;
        fix_confidence = 0.5;
        fix_pattern = Some TypeCoercion }
    | RaceCondition ->
      { fix_component = comp.comp_id;
        fix_description = "Add synchronization for shared mutable state";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "Mutex.lock m; %s; Mutex.unlock m" comp.comp_source;
        fix_confidence = 0.55;
        fix_pattern = Some RaceCondition }
    | ResourceLeak ->
      { fix_component = comp.comp_id;
        fix_description = "Ensure resource cleanup on all exit paths";
        fix_code_before = comp.comp_source;
        fix_code_after = Printf.sprintf "Fun.protect ~finally:cleanup (fun () -> %s)" comp.comp_source;
        fix_confidence = 0.7;
        fix_pattern = Some ResourceLeak }

  let generate components patterns root_causes mutations =
    (* From patterns *)
    let pattern_fixes = List.filter_map (fun pm ->
      let comp = List.find_opt (fun c -> c.comp_id = pm.pat_component) components in
      match comp with
      | Some c when pm.pat_confidence > 0.3 -> Some (suggest_fix c pm.pat_pattern)
      | _ -> None
    ) patterns in
    (* From mutations that fix failures *)
    let mutation_fixes = List.filter_map (fun mr ->
      if mr.mut_fixes_failure then
        let comp = List.find_opt (fun c -> c.comp_id = mr.mut_component) components in
        match comp with
        | Some c ->
          Some {
            fix_component = c.comp_id;
            fix_description = Printf.sprintf "Mutation '%s' fixes the failure" (mutation_kind_to_string mr.mut_kind);
            fix_code_before = c.comp_source;
            fix_code_after = Printf.sprintf "(* Apply: %s to fix *)" mr.mut_description;
            fix_confidence = 0.6;
            fix_pattern = None;
          }
        | None -> None
      else None
    ) mutations in
    (* From root causes *)
    let rc_fixes = List.filter_map (fun rc ->
      let comp = List.find_opt (fun c -> c.comp_id = rc.rc_origin_component) components in
      match comp with
      | Some c when rc.rc_confidence > 0.5 ->
        Some {
          fix_component = c.comp_id;
          fix_description = Printf.sprintf "Root cause: %s — investigate %s at line %d" rc.rc_category c.comp_name c.comp_line;
          fix_code_before = c.comp_source;
          fix_code_after = Printf.sprintf "(* Root cause fix for %s *)" rc.rc_category;
          fix_confidence = rc.rc_confidence *. 0.8;
          fix_pattern = None;
        }
      | _ -> None
    ) root_causes in
    (* Deduplicate by component, keep highest confidence *)
    let all_fixes = pattern_fixes @ mutation_fixes @ rc_fixes in
    let seen = Hashtbl.create 16 in
    List.iter (fun f ->
      match Hashtbl.find_opt seen f.fix_component with
      | Some existing when existing.fix_confidence >= f.fix_confidence -> ()
      | _ -> Hashtbl.replace seen f.fix_component f
    ) all_fixes;
    let deduped = Hashtbl.fold (fun _ v acc -> v :: acc) seen [] in
    List.sort (fun a b -> compare b.fix_confidence a.fix_confidence) deduped
end

(* ══════════ Engine 7: Insight Generator ══════════ *)

module InsightGenerator = struct
  let generate tests susp_scores patterns root_causes fixes mutations =
    let insights = ref [] in
    let add sev cat text = insights := { insight_text = text; insight_severity = sev; insight_category = cat } :: !insights in
    let total_tests = List.length tests in
    let failing = List.length (List.filter test_is_failing tests) in
    let pass_rate = if total_tests = 0 then 100.0
                    else 100.0 *. float_of_int (total_tests - failing) /. float_of_int total_tests in
    (* Test suite health *)
    if failing = 0 then
      add Info "Test Suite" "All tests passing — no bugs to investigate"
    else begin
      add (if pass_rate < 50.0 then Critical else if pass_rate < 80.0 then High else Medium)
        "Test Suite"
        (Printf.sprintf "%d/%d tests failing (%.0f%% pass rate)" failing total_tests pass_rate);
    end;
    (* Top suspects *)
    let top = List.filteri (fun i _ -> i < 3) susp_scores in
    List.iter (fun s ->
      if s.susp_ochiai > 0.8 then
        add Critical "Fault Localization"
          (Printf.sprintf "Component #%d is HIGHLY suspicious (Ochiai=%.3f, rank #%d)" s.susp_component s.susp_ochiai s.susp_rank)
      else if s.susp_ochiai > 0.5 then
        add High "Fault Localization"
          (Printf.sprintf "Component #%d is suspicious (Ochiai=%.3f, rank #%d)" s.susp_component s.susp_ochiai s.susp_rank)
    ) top;
    (* Pattern insights *)
    let high_conf_patterns = List.filter (fun p -> p.pat_confidence > 0.5) patterns in
    if List.length high_conf_patterns > 0 then
      add High "Bug Patterns"
        (Printf.sprintf "%d high-confidence bug patterns detected: %s"
          (List.length high_conf_patterns)
          (String.concat ", " (List.map (fun p -> bug_pattern_to_string p.pat_pattern) high_conf_patterns)));
    (* Root cause *)
    (match root_causes with
     | rc :: _ ->
       add High "Root Cause"
         (Printf.sprintf "Most likely root cause: %s (confidence %.0f%%)" rc.rc_category (rc.rc_confidence *. 100.0))
     | [] -> ());
    (* Fix suggestions *)
    let fix_count = List.length fixes in
    if fix_count > 0 then
      add Medium "Fixes"
        (Printf.sprintf "%d fix suggestions generated (top confidence: %.0f%%)"
          fix_count
          (match fixes with f :: _ -> f.fix_confidence *. 100.0 | [] -> 0.0));
    (* Mutation insights *)
    let fix_mutations = List.filter (fun m -> m.mut_fixes_failure) mutations in
    if List.length fix_mutations > 0 then
      add Medium "Mutation Analysis"
        (Printf.sprintf "%d mutations fix the failure — strong localization signal" (List.length fix_mutations));
    (* Coverage insight *)
    let avg_coverage = if total_tests = 0 then 0.0
      else
        let total_covered = List.fold_left (fun acc t -> acc + List.length t.covered_components) 0 tests in
        float_of_int total_covered /. float_of_int total_tests
    in
    if avg_coverage < 2.0 then
      add Low "Coverage" "Low average test coverage — consider adding more tests for better localization"
    else
      add Info "Coverage" (Printf.sprintf "Average %.1f components covered per test" avg_coverage);
    List.rev !insights
end

(* ══════════ Health Scorer ══════════ *)

let compute_health tests susp_scores patterns root_causes fixes =
  let total_tests = List.length tests in
  let failing = List.length (List.filter test_is_failing tests) in
  if failing = 0 then (100, "Pristine")
  else
    let pass_rate = float_of_int (total_tests - failing) /. float_of_int (max 1 total_tests) in
    let localization_quality =
      match susp_scores with
      | s :: _ when s.susp_ochiai > 0.7 -> 0.8  (* good localization *)
      | s :: _ when s.susp_ochiai > 0.4 -> 0.5
      | _ -> 0.2
    in
    let pattern_quality = if List.length patterns > 0 then 0.7 else 0.3 in
    let rc_quality = match root_causes with rc :: _ -> rc.rc_confidence | [] -> 0.2 in
    let fix_quality = match fixes with f :: _ -> f.fix_confidence | [] -> 0.1 in
    let raw = pass_rate *. 30.0
              +. localization_quality *. 25.0
              +. pattern_quality *. 15.0
              +. rc_quality *. 15.0
              +. fix_quality *. 15.0 in
    let score = int_of_float (clamp_f 0.0 100.0 raw) in
    let tier = if score >= 80 then "Healthy"
               else if score >= 60 then "Stable"
               else if score >= 40 then "Concerning"
               else if score >= 20 then "Critical"
               else "Emergency" in
    (score, tier)

(* ══════════ Full Investigation Pipeline ══════════ *)

let investigate components tests =
  (* Phase 1: Spectrum analysis *)
  let susp_scores = SpectrumAnalyzer.analyze components tests in
  (* Phase 2: Delta debugging on failing tests *)
  let delta_results = List.filter_map (fun t ->
    if test_is_failing t then
      let input_parts = String.split_on_char ' ' t.test_input in
      if List.length input_parts > 1 then
        let test_fn subset =
          (* Heuristic: smaller subsets still fail if they contain critical tokens *)
          List.length subset > 0 && List.length subset < List.length input_parts
        in
        Some (DeltaDebugger.ddmin test_fn input_parts)
      else None
    else None
  ) tests in
  (* Phase 3: Mutation localization *)
  let mutations = MutationLocalizer.analyze components susp_scores tests in
  (* Phase 4: Pattern scanning *)
  let patterns = PatternScanner.analyze components susp_scores in
  (* Phase 5: Root cause tracing *)
  let root_causes = RootCauseTracer.trace components susp_scores tests patterns in
  (* Phase 6: Fix suggestion *)
  let fixes = FixSuggester.generate components patterns root_causes mutations in
  (* Phase 7: Insights *)
  let insights = InsightGenerator.generate tests susp_scores patterns root_causes fixes mutations in
  (* Health *)
  let (score, tier) = compute_health tests susp_scores patterns root_causes fixes in
  {
    rpt_components = components;
    rpt_tests = tests;
    rpt_suspiciousness = susp_scores;
    rpt_delta = delta_results;
    rpt_mutations = mutations;
    rpt_patterns = patterns;
    rpt_root_causes = root_causes;
    rpt_fixes = fixes;
    rpt_insights = insights;
    rpt_health_score = score;
    rpt_health_tier = tier;
  }

(* ══════════ Demo Scenarios ══════════ *)

let demo_binary_search () =
  let components = [
    { comp_id = 1; comp_name = "binary_search"; comp_kind = FunctionCall;
      comp_line = 1; comp_file = "search.ml"; comp_source = "let rec binary_search arr lo hi target =" };
    { comp_id = 2; comp_name = "mid_calc"; comp_kind = Assignment;
      comp_line = 3; comp_file = "search.ml"; comp_source = "let mid = (lo + hi) / 2" };
    { comp_id = 3; comp_name = "base_check"; comp_kind = Conditional;
      comp_line = 2; comp_file = "search.ml"; comp_source = "if lo > hi then None" };
    { comp_id = 4; comp_name = "compare_mid"; comp_kind = Conditional;
      comp_line = 4; comp_file = "search.ml"; comp_source = "if arr.(mid) = target then Some mid" };
    { comp_id = 5; comp_name = "recurse_left"; comp_kind = FunctionCall;
      comp_line = 5; comp_file = "search.ml"; comp_source = "else if arr.(mid) > target then binary_search arr lo (mid-1) target" };
    { comp_id = 6; comp_name = "recurse_right"; comp_kind = FunctionCall;
      comp_line = 6; comp_file = "search.ml"; comp_source = "else binary_search arr (mid+1) hi target" };
    { comp_id = 7; comp_name = "bounds_check"; comp_kind = Conditional;
      comp_line = 7; comp_file = "search.ml"; comp_source = "if hi < 0 || lo >= Array.length arr then None" };
  ] in
  let tests = [
    { test_id = 1; test_name = "find_middle"; test_outcome = Pass;
      covered_components = [1;2;3;4]; test_input = "[1;2;3;4;5] 3";
      test_expected = "Some 2"; test_actual = "Some 2"; test_duration_ms = 0.5 };
    { test_id = 2; test_name = "find_first"; test_outcome = Pass;
      covered_components = [1;2;3;4;5]; test_input = "[1;2;3;4;5] 1";
      test_expected = "Some 0"; test_actual = "Some 0"; test_duration_ms = 0.8 };
    { test_id = 3; test_name = "find_last"; test_outcome = Fail;
      covered_components = [1;2;3;4;5;6]; test_input = "[1;2;3;4;5] 5";
      test_expected = "Some 4"; test_actual = "None"; test_duration_ms = 1.2 };
    { test_id = 4; test_name = "not_found"; test_outcome = Pass;
      covered_components = [1;2;3;4;5;6;7]; test_input = "[1;2;3;4;5] 6";
      test_expected = "None"; test_actual = "None"; test_duration_ms = 0.9 };
    { test_id = 5; test_name = "single_element"; test_outcome = Pass;
      covered_components = [1;2;3;4]; test_input = "[42] 42";
      test_expected = "Some 0"; test_actual = "Some 0"; test_duration_ms = 0.3 };
    { test_id = 6; test_name = "empty_array"; test_outcome = Pass;
      covered_components = [1;3;7]; test_input = "[] 1";
      test_expected = "None"; test_actual = "None"; test_duration_ms = 0.1 };
    { test_id = 7; test_name = "large_array_boundary"; test_outcome = Fail;
      covered_components = [1;2;3;4;5;6]; test_input = "[1..1000000] 1000000";
      test_expected = "Some 999999"; test_actual = "Stack_overflow"; test_duration_ms = 500.0 };
    { test_id = 8; test_name = "duplicate_elements"; test_outcome = Pass;
      covered_components = [1;2;3;4;5]; test_input = "[1;1;2;2;3] 2";
      test_expected = "Some 2"; test_actual = "Some 2"; test_duration_ms = 0.6 };
  ] in
  ("Binary Search Bug", components, tests)

let demo_linked_list () =
  let components = [
    { comp_id = 10; comp_name = "insert"; comp_kind = FunctionCall;
      comp_line = 10; comp_file = "list.ml"; comp_source = "let insert lst pos elem =" };
    { comp_id = 11; comp_name = "bounds_check"; comp_kind = Conditional;
      comp_line = 11; comp_file = "list.ml"; comp_source = "if pos < 0 || pos > List.length lst then raise Invalid_argument" };
    { comp_id = 12; comp_name = "split_list"; comp_kind = Assignment;
      comp_line = 12; comp_file = "list.ml"; comp_source = "let (before, after) = split_at pos lst" };
    { comp_id = 13; comp_name = "concat"; comp_kind = FunctionCall;
      comp_line = 13; comp_file = "list.ml"; comp_source = "before @ [elem] @ after" };
    { comp_id = 14; comp_name = "delete"; comp_kind = FunctionCall;
      comp_line = 20; comp_file = "list.ml"; comp_source = "let delete lst pos =" };
    { comp_id = 15; comp_name = "delete_bounds"; comp_kind = Conditional;
      comp_line = 21; comp_file = "list.ml"; comp_source = "if pos < 0 || pos >= List.length lst then lst" };
    { comp_id = 16; comp_name = "delete_split"; comp_kind = Assignment;
      comp_line = 22; comp_file = "list.ml"; comp_source = "let (before, _ :: after) = split_at pos lst" };
    { comp_id = 17; comp_name = "reverse"; comp_kind = Loop;
      comp_line = 30; comp_file = "list.ml"; comp_source = "let rec reverse = function [] -> [] | h :: t -> reverse t @ [h]" };
  ] in
  let tests = [
    { test_id = 10; test_name = "insert_beginning"; test_outcome = Pass;
      covered_components = [10;11;12;13]; test_input = "[] 0 'a'";
      test_expected = "['a']"; test_actual = "['a']"; test_duration_ms = 0.2 };
    { test_id = 11; test_name = "insert_end"; test_outcome = Pass;
      covered_components = [10;11;12;13]; test_input = "['a'] 1 'b'";
      test_expected = "['a';'b']"; test_actual = "['a';'b']"; test_duration_ms = 0.3 };
    { test_id = 12; test_name = "insert_middle"; test_outcome = Pass;
      covered_components = [10;11;12;13]; test_input = "['a';'c'] 1 'b'";
      test_expected = "['a';'b';'c']"; test_actual = "['a';'b';'c']"; test_duration_ms = 0.3 };
    { test_id = 13; test_name = "delete_last_element"; test_outcome = Fail;
      covered_components = [14;15;16]; test_input = "['a'] 0";
      test_expected = "[]"; test_actual = "Match_failure"; test_duration_ms = 0.1 };
    { test_id = 14; test_name = "delete_from_middle"; test_outcome = Pass;
      covered_components = [14;15;16]; test_input = "['a';'b';'c'] 1";
      test_expected = "['a';'c']"; test_actual = "['a';'c']"; test_duration_ms = 0.3 };
    { test_id = 15; test_name = "reverse_empty"; test_outcome = Pass;
      covered_components = [17]; test_input = "[]";
      test_expected = "[]"; test_actual = "[]"; test_duration_ms = 0.1 };
    { test_id = 16; test_name = "reverse_large"; test_outcome = Fail;
      covered_components = [17]; test_input = "[1..100000]";
      test_expected = "[100000..1]"; test_actual = "Stack_overflow"; test_duration_ms = 2000.0 };
    { test_id = 17; test_name = "delete_out_of_bounds"; test_outcome = Pass;
      covered_components = [14;15]; test_input = "['a'] 5";
      test_expected = "['a']"; test_actual = "['a']"; test_duration_ms = 0.1 };
  ] in
  ("Linked List Operations Bug", components, tests)

let demo_calculator () =
  let components = [
    { comp_id = 20; comp_name = "parse_expr"; comp_kind = PatternMatch;
      comp_line = 5; comp_file = "calc.ml"; comp_source = "let rec parse_expr tokens =" };
    { comp_id = 21; comp_name = "eval_binop"; comp_kind = FunctionCall;
      comp_line = 15; comp_file = "calc.ml"; comp_source = "let eval_binop op a b =" };
    { comp_id = 22; comp_name = "div_check"; comp_kind = Conditional;
      comp_line = 18; comp_file = "calc.ml"; comp_source = "if b = 0 then raise Division_by_zero" };
    { comp_id = 23; comp_name = "eval_expr"; comp_kind = PatternMatch;
      comp_line = 25; comp_file = "calc.ml"; comp_source = "let rec eval_expr = function" };
    { comp_id = 24; comp_name = "precedence"; comp_kind = Conditional;
      comp_line = 10; comp_file = "calc.ml"; comp_source = "let precedence = function '+' | '-' -> 1 | '*' | '/' -> 2" };
    { comp_id = 25; comp_name = "tokenize"; comp_kind = Loop;
      comp_line = 1; comp_file = "calc.ml"; comp_source = "let tokenize input =" };
    { comp_id = 26; comp_name = "unary_minus"; comp_kind = Conditional;
      comp_line = 30; comp_file = "calc.ml"; comp_source = "| Neg e -> -(eval_expr e)" };
  ] in
  let tests = [
    { test_id = 20; test_name = "simple_add"; test_outcome = Pass;
      covered_components = [20;21;23;24;25]; test_input = "2 + 3";
      test_expected = "5"; test_actual = "5"; test_duration_ms = 0.2 };
    { test_id = 21; test_name = "precedence"; test_outcome = Pass;
      covered_components = [20;21;23;24;25]; test_input = "2 + 3 * 4";
      test_expected = "14"; test_actual = "14"; test_duration_ms = 0.3 };
    { test_id = 22; test_name = "div_by_zero"; test_outcome = Pass;
      covered_components = [20;21;22;23;24;25]; test_input = "5 / 0";
      test_expected = "Division_by_zero"; test_actual = "Division_by_zero"; test_duration_ms = 0.1 };
    { test_id = 23; test_name = "nested_parens"; test_outcome = Fail;
      covered_components = [20;23;24;25]; test_input = "((2 + 3) * (4 - 1))";
      test_expected = "15"; test_actual = "Parse_error"; test_duration_ms = 0.2 };
    { test_id = 24; test_name = "unary_minus"; test_outcome = Fail;
      covered_components = [20;23;25;26]; test_input = "-5 + 3";
      test_expected = "-2"; test_actual = "Parse_error"; test_duration_ms = 0.1 };
    { test_id = 25; test_name = "complex_expr"; test_outcome = Fail;
      covered_components = [20;21;23;24;25;26]; test_input = "-(2 + 3) * 4 / 2";
      test_expected = "-10"; test_actual = "Parse_error"; test_duration_ms = 0.2 };
    { test_id = 26; test_name = "just_number"; test_outcome = Pass;
      covered_components = [20;23;25]; test_input = "42";
      test_expected = "42"; test_actual = "42"; test_duration_ms = 0.1 };
    { test_id = 27; test_name = "whitespace"; test_outcome = Pass;
      covered_components = [20;23;25]; test_input = "  1 +  2  ";
      test_expected = "3"; test_actual = "3"; test_duration_ms = 0.2 };
  ] in
  ("Expression Parser Bug", components, tests)

let demo_sort () =
  let components = [
    { comp_id = 30; comp_name = "quicksort"; comp_kind = FunctionCall;
      comp_line = 1; comp_file = "sort.ml"; comp_source = "let rec quicksort = function" };
    { comp_id = 31; comp_name = "pivot_select"; comp_kind = Assignment;
      comp_line = 3; comp_file = "sort.ml"; comp_source = "let pivot = List.hd lst" };
    { comp_id = 32; comp_name = "partition"; comp_kind = Loop;
      comp_line = 4; comp_file = "sort.ml"; comp_source = "let (less, greater) = List.partition (fun x -> x < pivot) (List.tl lst)" };
    { comp_id = 33; comp_name = "combine"; comp_kind = FunctionCall;
      comp_line = 5; comp_file = "sort.ml"; comp_source = "quicksort less @ [pivot] @ quicksort greater" };
    { comp_id = 34; comp_name = "base_case"; comp_kind = PatternMatch;
      comp_line = 2; comp_file = "sort.ml"; comp_source = "| [] -> []" };
    { comp_id = 35; comp_name = "merge"; comp_kind = Loop;
      comp_line = 10; comp_file = "sort.ml"; comp_source = "let rec merge l1 l2 = match l1, l2 with" };
    { comp_id = 36; comp_name = "merge_split"; comp_kind = Assignment;
      comp_line = 20; comp_file = "sort.ml"; comp_source = "let (left, right) = split_at (List.length lst / 2) lst" };
  ] in
  let tests = [
    { test_id = 30; test_name = "sort_empty"; test_outcome = Pass;
      covered_components = [30;34]; test_input = "[]";
      test_expected = "[]"; test_actual = "[]"; test_duration_ms = 0.1 };
    { test_id = 31; test_name = "sort_singleton"; test_outcome = Pass;
      covered_components = [30;31;32;33;34]; test_input = "[5]";
      test_expected = "[5]"; test_actual = "[5]"; test_duration_ms = 0.1 };
    { test_id = 32; test_name = "sort_sorted"; test_outcome = Pass;
      covered_components = [30;31;32;33;34]; test_input = "[1;2;3;4;5]";
      test_expected = "[1;2;3;4;5]"; test_actual = "[1;2;3;4;5]"; test_duration_ms = 0.3 };
    { test_id = 33; test_name = "sort_reverse"; test_outcome = Pass;
      covered_components = [30;31;32;33;34]; test_input = "[5;4;3;2;1]";
      test_expected = "[1;2;3;4;5]"; test_actual = "[1;2;3;4;5]"; test_duration_ms = 0.4 };
    { test_id = 34; test_name = "sort_duplicates"; test_outcome = Fail;
      covered_components = [30;31;32;33;34]; test_input = "[3;1;2;3;1]";
      test_expected = "[1;1;2;3;3]"; test_actual = "[1;2;3]"; test_duration_ms = 0.3 };
    { test_id = 35; test_name = "sort_all_same"; test_outcome = Fail;
      covered_components = [30;31;32;33;34]; test_input = "[7;7;7;7]";
      test_expected = "[7;7;7;7]"; test_actual = "[7]"; test_duration_ms = 0.2 };
    { test_id = 36; test_name = "sort_negative"; test_outcome = Pass;
      covered_components = [30;31;32;33;34]; test_input = "[-3;1;-2;4]";
      test_expected = "[-3;-2;1;4]"; test_actual = "[-3;-2;1;4]"; test_duration_ms = 0.3 };
    { test_id = 37; test_name = "mergesort_basic"; test_outcome = Pass;
      covered_components = [35;36]; test_input = "[3;1;2]";
      test_expected = "[1;2;3]"; test_actual = "[1;2;3]"; test_duration_ms = 0.2 };
  ] in
  ("Sorting Algorithm Bug (Duplicate Handling)", components, tests)

let demo_scenarios = [
  demo_binary_search;
  demo_linked_list;
  demo_calculator;
  demo_sort;
]

(* ══════════ Text Report ══════════ *)

let print_report report =
  let failing = List.filter test_is_failing report.rpt_tests in
  Printf.printf "\n╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║       AUTONOMOUS DEBUGGING ENGINE — Investigation       ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n\n";
  Printf.printf "Health Score: %d/100 (%s)\n" report.rpt_health_score report.rpt_health_tier;
  Printf.printf "Tests: %d total, %d passing, %d failing\n\n"
    (List.length report.rpt_tests)
    (List.length report.rpt_tests - List.length failing)
    (List.length failing);

  (* Suspiciousness ranking *)
  Printf.printf "── Fault Localization (Top 5) ──\n";
  let top5 = List.filteri (fun i _ -> i < 5) report.rpt_suspiciousness in
  List.iter (fun s ->
    let comp = List.find_opt (fun c -> c.comp_id = s.susp_component) report.rpt_components in
    let name = match comp with Some c -> c.comp_name | None -> "?" in
    Printf.printf "  #%d  %-20s  Tarantula=%.3f  Ochiai=%.3f  DStar=%.3f\n"
      s.susp_rank name s.susp_tarantula s.susp_ochiai s.susp_dstar
  ) top5;
  Printf.printf "\n";

  (* Delta debugging *)
  if List.length report.rpt_delta > 0 then begin
    Printf.printf "── Delta Debugging ──\n";
    List.iter (fun d ->
      Printf.printf "  Original: %d elements → Minimal: %d elements (%.0f%% reduction, %d steps)\n"
        (List.length d.delta_original_input)
        (List.length d.delta_minimal_input)
        (d.delta_reduction_ratio *. 100.0)
        d.delta_steps
    ) report.rpt_delta;
    Printf.printf "\n"
  end;

  (* Mutation results *)
  let fix_mutations = List.filter (fun m -> m.mut_fixes_failure) report.rpt_mutations in
  if List.length fix_mutations > 0 then begin
    Printf.printf "── Mutation Localization (Fixing Mutations) ──\n";
    List.iter (fun m ->
      Printf.printf "  ✓ %s\n" m.mut_description
    ) fix_mutations;
    Printf.printf "\n"
  end;

  (* Patterns *)
  if List.length report.rpt_patterns > 0 then begin
    Printf.printf "── Bug Patterns Detected ──\n";
    List.iter (fun p ->
      Printf.printf "  [%.0f%%] %s: %s\n"
        (p.pat_confidence *. 100.0)
        (bug_pattern_to_string p.pat_pattern)
        p.pat_evidence
    ) report.rpt_patterns;
    Printf.printf "\n"
  end;

  (* Root causes *)
  if List.length report.rpt_root_causes > 0 then begin
    Printf.printf "── Root Cause Analysis ──\n";
    List.iter (fun rc ->
      Printf.printf "  [%.0f%% confidence] %s\n" (rc.rc_confidence *. 100.0) rc.rc_category;
      List.iter (fun step -> Printf.printf "    → %s\n" step) rc.rc_chain;
      Printf.printf "\n"
    ) report.rpt_root_causes
  end;

  (* Fix suggestions *)
  if List.length report.rpt_fixes > 0 then begin
    Printf.printf "── Fix Suggestions ──\n";
    List.iteri (fun i f ->
      let comp = List.find_opt (fun c -> c.comp_id = f.fix_component) report.rpt_components in
      let loc = match comp with Some c -> Printf.sprintf "%s:%d" c.comp_file c.comp_line | None -> "?" in
      Printf.printf "  %d. [%.0f%%] %s (%s)\n" (i+1) (f.fix_confidence *. 100.0) f.fix_description loc;
      Printf.printf "     Before: %s\n" f.fix_code_before;
      Printf.printf "     After:  %s\n" f.fix_code_after
    ) report.rpt_fixes;
    Printf.printf "\n"
  end;

  (* Insights *)
  Printf.printf "── Autonomous Insights ──\n";
  List.iter (fun ins ->
    Printf.printf "  [%s] %s: %s\n"
      (severity_to_string ins.insight_severity)
      ins.insight_category
      ins.insight_text
  ) report.rpt_insights;
  Printf.printf "\n"

(* ══════════ HTML Dashboard ══════════ *)

let generate_dashboard reports =
  let buf = Buffer.create 8192 in
  let add = Buffer.add_string buf in
  add "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"UTF-8\">\n";
  add "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">\n";
  add "<title>Autonomous Debugger Dashboard</title>\n<style>\n";
  add ":root{--bg:#0a0a0f;--card:#12121a;--border:#1e1e2e;--text:#e0e0e0;--dim:#888;";
  add "--accent:#6c5ce7;--red:#ff4757;--orange:#ffa502;--green:#2ed573;--blue:#45aaf2;--purple:#a55eea}\n";
  add "*{margin:0;padding:0;box-sizing:border-box}\n";
  add "body{font-family:'Segoe UI',system-ui,sans-serif;background:var(--bg);color:var(--text);padding:2rem}\n";
  add "h1{text-align:center;font-size:1.8rem;margin-bottom:.5rem;background:linear-gradient(135deg,var(--accent),var(--purple));-webkit-background-clip:text;-webkit-text-fill-color:transparent}\n";
  add ".subtitle{text-align:center;color:var(--dim);margin-bottom:2rem}\n";
  add ".grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(400px,1fr));gap:1.5rem;margin-bottom:2rem}\n";
  add ".card{background:var(--card);border:1px solid var(--border);border-radius:12px;padding:1.5rem}\n";
  add ".card h2{font-size:1.1rem;margin-bottom:1rem;color:var(--accent)}\n";
  add ".card h3{font-size:.95rem;margin:1rem 0 .5rem;color:var(--purple)}\n";
  add "table{width:100%;border-collapse:collapse;font-size:.85rem}\n";
  add "th,td{padding:.4rem .6rem;text-align:left;border-bottom:1px solid var(--border)}\n";
  add "th{color:var(--dim);font-weight:600}\n";
  add ".gauge{width:120px;height:120px;border-radius:50%;display:flex;align-items:center;justify-content:center;margin:0 auto 1rem;font-size:2rem;font-weight:700}\n";
  add ".tag{display:inline-block;padding:2px 8px;border-radius:4px;font-size:.75rem;font-weight:600;margin:2px}\n";
  add ".tag-critical{background:rgba(255,71,87,.2);color:var(--red)}\n";
  add ".tag-high{background:rgba(255,165,2,.2);color:var(--orange)}\n";
  add ".tag-medium{background:rgba(69,170,242,.2);color:var(--blue)}\n";
  add ".tag-low{background:rgba(46,213,115,.2);color:var(--green)}\n";
  add ".tag-info{background:rgba(136,136,136,.2);color:var(--dim)}\n";
  add ".bar{height:8px;border-radius:4px;background:var(--border);margin:4px 0}\n";
  add ".bar-fill{height:100%;border-radius:4px}\n";
  add ".scenario{margin-bottom:3rem;border:1px solid var(--border);border-radius:16px;padding:2rem;background:var(--card)}\n";
  add ".scenario-title{font-size:1.3rem;margin-bottom:1.5rem;color:var(--purple)}\n";
  add ".fix-box{background:rgba(46,213,115,.05);border:1px solid rgba(46,213,115,.2);border-radius:8px;padding:1rem;margin:.5rem 0}\n";
  add ".fix-box code{display:block;padding:.3rem;margin:.3rem 0;background:rgba(0,0,0,.3);border-radius:4px;font-size:.8rem}\n";
  add "ul{list-style:none;padding:0} li{padding:.3rem 0;border-bottom:1px solid var(--border)}\n";
  add ".chain{margin-left:1rem;border-left:2px solid var(--accent);padding-left:1rem}\n";
  add "</style>\n</head>\n<body>\n";
  add "<h1>🔍 Autonomous Debugging Engine</h1>\n";
  add "<p class=\"subtitle\">Spectrum-based fault localization • Delta debugging • Mutation analysis • Root cause tracing</p>\n";

  List.iter (fun (name, report) ->
    let failing = List.length (List.filter test_is_failing report.rpt_tests) in
    let gauge_color = if report.rpt_health_score >= 80 then "var(--green)"
      else if report.rpt_health_score >= 60 then "var(--blue)"
      else if report.rpt_health_score >= 40 then "var(--orange)"
      else "var(--red)" in

    add (Printf.sprintf "<div class=\"scenario\">\n<div class=\"scenario-title\">🐛 %s</div>\n" name);
    add (Printf.sprintf "<div class=\"gauge\" style=\"border:4px solid %s;color:%s\">%d</div>\n"
      gauge_color gauge_color report.rpt_health_score);
    add (Printf.sprintf "<p style=\"text-align:center;color:var(--dim)\">%s — %d/%d tests failing</p>\n\n"
      report.rpt_health_tier failing (List.length report.rpt_tests));

    add "<div class=\"grid\">\n";

    (* Suspiciousness table *)
    add "<div class=\"card\">\n<h2>📊 Fault Localization</h2>\n";
    add "<table><tr><th>Rank</th><th>Component</th><th>Tarantula</th><th>Ochiai</th><th>DStar</th></tr>\n";
    let top = List.filteri (fun i _ -> i < 7) report.rpt_suspiciousness in
    List.iter (fun s ->
      let comp = List.find_opt (fun c -> c.comp_id = s.susp_component) report.rpt_components in
      let name = match comp with Some c -> c.comp_name | None -> "?" in
      let row_color = if s.susp_ochiai > 0.7 then "color:var(--red)"
        else if s.susp_ochiai > 0.4 then "color:var(--orange)"
        else "" in
      add (Printf.sprintf "<tr style=\"%s\"><td>#%d</td><td>%s</td><td>%.3f</td><td>%.3f</td><td>%.1f</td></tr>\n"
        row_color s.susp_rank name s.susp_tarantula s.susp_ochiai s.susp_dstar)
    ) top;
    add "</table></div>\n";

    (* Bug patterns *)
    add "<div class=\"card\">\n<h2>🔎 Bug Patterns</h2>\n<ul>\n";
    List.iter (fun p ->
      let tag_cls = if p.pat_confidence > 0.6 then "tag-critical"
        else if p.pat_confidence > 0.4 then "tag-high"
        else "tag-medium" in
      add (Printf.sprintf "<li><span class=\"tag %s\">%.0f%%</span> <b>%s</b> — %s</li>\n"
        tag_cls (p.pat_confidence *. 100.0) (bug_pattern_to_string p.pat_pattern) p.pat_evidence)
    ) report.rpt_patterns;
    add "</ul></div>\n";

    (* Root causes *)
    add "<div class=\"card\">\n<h2>🔗 Root Cause Analysis</h2>\n";
    List.iter (fun rc ->
      add (Printf.sprintf "<h3>%s (%.0f%% confidence)</h3>\n<div class=\"chain\">\n"
        rc.rc_category (rc.rc_confidence *. 100.0));
      List.iter (fun step ->
        add (Printf.sprintf "<p>→ %s</p>\n" step)
      ) rc.rc_chain;
      add "</div>\n"
    ) report.rpt_root_causes;
    add "</div>\n";

    (* Fix suggestions *)
    add "<div class=\"card\">\n<h2>🔧 Fix Suggestions</h2>\n";
    List.iter (fun f ->
      let comp = List.find_opt (fun c -> c.comp_id = f.fix_component) report.rpt_components in
      let loc = match comp with Some c -> Printf.sprintf "%s:%d" c.comp_file c.comp_line | None -> "?" in
      add (Printf.sprintf "<div class=\"fix-box\">\n<b>[%.0f%%]</b> %s <span style=\"color:var(--dim)\">(%s)</span>\n"
        (f.fix_confidence *. 100.0) f.fix_description loc);
      add (Printf.sprintf "<code>- %s</code>\n<code>+ %s</code>\n</div>\n" f.fix_code_before f.fix_code_after)
    ) report.rpt_fixes;
    add "</div>\n";

    (* Insights *)
    add "<div class=\"card\">\n<h2>💡 Autonomous Insights</h2>\n<ul>\n";
    List.iter (fun ins ->
      let tag_cls = match ins.insight_severity with
        | Critical -> "tag-critical" | High -> "tag-high"
        | Medium -> "tag-medium" | Low -> "tag-low" | Info -> "tag-info" in
      add (Printf.sprintf "<li><span class=\"tag %s\">%s</span> <b>%s:</b> %s</li>\n"
        tag_cls (severity_to_string ins.insight_severity) ins.insight_category ins.insight_text)
    ) report.rpt_insights;
    add "</ul></div>\n";

    (* Tests *)
    add "<div class=\"card\">\n<h2>🧪 Test Results</h2>\n";
    add "<table><tr><th>Test</th><th>Status</th><th>Expected</th><th>Actual</th><th>Time</th></tr>\n";
    List.iter (fun t ->
      let status_str = match t.test_outcome with
        | Pass -> "<span style=\"color:var(--green)\">✓ PASS</span>"
        | Fail -> "<span style=\"color:var(--red)\">✗ FAIL</span>"
        | Error e -> Printf.sprintf "<span style=\"color:var(--red)\">⚠ %s</span>" e
      in
      add (Printf.sprintf "<tr><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%.1fms</td></tr>\n"
        t.test_name status_str t.test_expected t.test_actual t.test_duration_ms)
    ) report.rpt_tests;
    add "</table></div>\n";

    (* Mutations *)
    let fix_muts = List.filter (fun m -> m.mut_fixes_failure) report.rpt_mutations in
    if List.length fix_muts > 0 then begin
      add "<div class=\"card\">\n<h2>🧬 Fixing Mutations</h2>\n<ul>\n";
      List.iter (fun m ->
        add (Printf.sprintf "<li>✓ %s</li>\n" m.mut_description)
      ) fix_muts;
      add "</ul></div>\n"
    end;

    add "</div>\n</div>\n\n"
  ) reports;

  add "</body>\n</html>\n";
  Buffer.contents buf

(* ══════════ CLI Entry Point ══════════ *)

let () =
  let args = Array.to_list Sys.argv in
  let has_flag f = List.mem f args in
  if has_flag "--demo" || has_flag "--dashboard" || List.length args <= 1 then begin
    let results = List.map (fun demo_fn ->
      let (name, components, tests) = demo_fn () in
      let report = investigate components tests in
      if has_flag "--demo" || List.length args <= 1 then begin
        Printf.printf "\n━━━ Scenario: %s ━━━\n" name;
        print_report report
      end;
      (name, report)
    ) demo_scenarios in
    if has_flag "--dashboard" then begin
      let html = generate_dashboard results in
      let oc = open_out "debugger_dashboard.html" in
      output_string oc html;
      close_out oc;
      Printf.printf "\n✅ Dashboard saved to debugger_dashboard.html\n"
    end;
    (* Summary *)
    Printf.printf "\n══════════ Summary ══════════\n";
    List.iter (fun (name, r) ->
      Printf.printf "  %-40s  Health: %3d/100 (%s)\n" name r.rpt_health_score r.rpt_health_tier
    ) results;
    Printf.printf "\n"
  end else
    Printf.printf "Usage: autonomous_debugger [--demo] [--dashboard]\n"
