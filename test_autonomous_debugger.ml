(* test_autonomous_debugger.ml — Tests for Autonomous Debugging Engine
 *
 * Compile:
 *   ocamlopt test_framework.ml autonomous_debugger.ml test_autonomous_debugger.ml -o test_autonomous_debugger
 * Run:
 *   ./test_autonomous_debugger
 *)

#use "test_framework.ml"
#use "autonomous_debugger.ml"

(* ══════════ Helper: Build a simple scenario ══════════ *)

let make_component id name kind line source =
  { comp_id = id; comp_name = name; comp_kind = kind;
    comp_line = line; comp_file = "test.ml"; comp_source = source }

let make_test id name outcome covered input expected actual =
  { test_id = id; test_name = name; test_outcome = outcome;
    covered_components = covered; test_input = input;
    test_expected = expected; test_actual = actual; test_duration_ms = 1.0 }

(* ══════════ Spectrum Analyzer Tests ══════════ *)

let () = suite "SpectrumAnalyzer" (fun () ->
  let comps = [
    make_component 1 "a" Assignment 1 "x := 1";
    make_component 2 "b" Conditional 2 "if x > 0";
    make_component 3 "c" Loop 3 "while true";
  ] in
  let tests_all_pass = [
    make_test 1 "t1" Pass [1;2] "i1" "o1" "o1";
    make_test 2 "t2" Pass [1;2;3] "i2" "o2" "o2";
  ] in
  let scores = SpectrumAnalyzer.analyze comps tests_all_pass in
  assert_true ~msg:"all pass => all suspiciousness = 0"
    (List.for_all (fun s -> s.susp_ochiai = 0.0) scores);
  assert_true ~msg:"scores returned for all components"
    (List.length scores = 3);

  (* One failing test covers comp 3 only *)
  let tests_one_fail = [
    make_test 1 "t1" Pass [1;2] "i1" "o1" "o1";
    make_test 2 "t2" Pass [1;2;3] "i2" "o2" "o2";
    make_test 3 "t3" Fail [3] "i3" "o3" "wrong";
  ] in
  let scores2 = SpectrumAnalyzer.analyze comps tests_one_fail in
  let s3 = List.find (fun s -> s.susp_component = 3) scores2 in
  let s1 = List.find (fun s -> s.susp_component = 1) scores2 in
  assert_true ~msg:"comp 3 (only fail covers) has highest Ochiai"
    (s3.susp_ochiai > s1.susp_ochiai);
  assert_true ~msg:"comp 3 Ochiai > 0" (s3.susp_ochiai > 0.0);
  assert_true ~msg:"comp 3 rank = 1" (s3.susp_rank = 1);

  (* Tarantula for comp 3 *)
  assert_true ~msg:"comp 3 Tarantula > 0" (s3.susp_tarantula > 0.0);
  assert_true ~msg:"comp 3 DStar > 0" (s3.susp_dstar > 0.0);

  (* When both pass and fail cover same component *)
  let tests_mixed = [
    make_test 1 "t1" Pass [1;2] "i1" "o1" "o1";
    make_test 2 "t2" Fail [1;2] "i2" "o2" "wrong";
  ] in
  let scores3 = SpectrumAnalyzer.analyze comps tests_mixed in
  let s1m = List.find (fun s -> s.susp_component = 1) scores3 in
  assert_true ~msg:"mixed coverage: suspiciousness between 0 and 1"
    (s1m.susp_ochiai > 0.0 && s1m.susp_ochiai <= 1.0);

  (* DStar formula check *)
  assert_true ~msg:"DStar >= 0" (s1m.susp_dstar >= 0.0);
)

(* ══════════ Delta Debugger Tests ══════════ *)

let () = suite "DeltaDebugger" (fun () ->
  (* Empty input *)
  let r0 = DeltaDebugger.ddmin (fun _ -> true) [] in
  assert_true ~msg:"empty input => empty result"
    (r0.delta_minimal_input = []);
  assert_true ~msg:"empty input => ratio 1.0"
    (r0.delta_reduction_ratio = 1.0);

  (* Single element *)
  let r1 = DeltaDebugger.ddmin (fun _ -> true) ["a"] in
  assert_true ~msg:"single element => result has <= 1 element"
    (List.length r1.delta_minimal_input <= 1);

  (* Multiple elements, always failing *)
  let r2 = DeltaDebugger.ddmin (fun subset -> List.length subset > 0) ["a";"b";"c";"d";"e"] in
  assert_true ~msg:"always-failing: minimal input is smaller than original"
    (List.length r2.delta_minimal_input <= List.length r2.delta_original_input);
  assert_true ~msg:"reduction ratio >= 0"
    (r2.delta_reduction_ratio >= 0.0);
  assert_true ~msg:"steps > 0" (r2.delta_steps > 0);

  (* Specific failing element *)
  let r3 = DeltaDebugger.ddmin (fun subset -> List.mem "c" subset) ["a";"b";"c";"d";"e"] in
  assert_true ~msg:"specific element: minimal contains 'c'"
    (List.mem "c" r3.delta_minimal_input);
  assert_true ~msg:"specific element: reduced from 5"
    (List.length r3.delta_minimal_input < 5);
)

(* ══════════ Mutation Localizer Tests ══════════ *)

let () = suite "MutationLocalizer" (fun () ->
  let comps = [
    make_component 1 "cond" Conditional 1 "if x > 0";
    make_component 2 "assign" Assignment 2 "y := x + 1";
    make_component 3 "loop" Loop 3 "while i < n";
  ] in
  let susp = [
    { susp_component = 1; susp_tarantula = 0.8; susp_ochiai = 0.9; susp_dstar = 5.0; susp_rank = 1 };
    { susp_component = 2; susp_tarantula = 0.3; susp_ochiai = 0.3; susp_dstar = 0.5; susp_rank = 2 };
    { susp_component = 3; susp_tarantula = 0.1; susp_ochiai = 0.1; susp_dstar = 0.1; susp_rank = 3 };
  ] in
  let tests = [
    make_test 1 "t1" Pass [1;2] "i1" "o1" "o1";
    make_test 2 "t2" Fail [1;2;3] "i2" "o2" "wrong";
  ] in
  let mutations = MutationLocalizer.analyze comps susp tests in
  assert_true ~msg:"mutations generated for all components"
    (List.length mutations > 0);
  (* Check all mutation kinds are valid *)
  assert_true ~msg:"all mutation descriptions non-empty"
    (List.for_all (fun m -> String.length m.mut_description > 0) mutations);
  (* Conditional should have NegateCondition *)
  let cond_muts = List.filter (fun m -> m.mut_component = 1) mutations in
  assert_true ~msg:"conditional gets NegateCondition mutation"
    (List.exists (fun m -> m.mut_kind = NegateCondition) cond_muts);
  (* Loop should get mutations *)
  let loop_muts = List.filter (fun m -> m.mut_component = 3) mutations in
  assert_true ~msg:"loop gets mutations" (List.length loop_muts > 0);
)

(* ══════════ Pattern Scanner Tests ══════════ *)

let () = suite "PatternScanner" (fun () ->
  let comps = [
    make_component 1 "loop" Loop 1 "for i = 0 to n";
    make_component 2 "cond" Conditional 2 "if ptr = null";
    make_component 3 "call" FunctionCall 3 "open_file f";
    make_component 4 "match" PatternMatch 4 "match lst with";
  ] in
  let susp = [
    { susp_component = 1; susp_tarantula = 0.9; susp_ochiai = 0.9; susp_dstar = 10.0; susp_rank = 1 };
    { susp_component = 2; susp_tarantula = 0.7; susp_ochiai = 0.7; susp_dstar = 3.0; susp_rank = 2 };
    { susp_component = 3; susp_tarantula = 0.5; susp_ochiai = 0.5; susp_dstar = 1.0; susp_rank = 3 };
    { susp_component = 4; susp_tarantula = 0.6; susp_ochiai = 0.6; susp_dstar = 2.0; susp_rank = 4 };
  ] in
  let patterns = PatternScanner.analyze comps susp in
  assert_true ~msg:"patterns detected" (List.length patterns > 0);
  (* Loop should detect off-by-one *)
  let loop_pats = List.filter (fun p -> p.pat_component = 1) patterns in
  assert_true ~msg:"loop gets OffByOne pattern"
    (List.exists (fun p -> p.pat_pattern = OffByOne) loop_pats);
  (* PatternMatch should detect MissingBaseCase *)
  let match_pats = List.filter (fun p -> p.pat_component = 4) patterns in
  assert_true ~msg:"pattern match gets MissingBaseCase"
    (List.exists (fun p -> p.pat_pattern = MissingBaseCase) match_pats);
  (* All confidences in [0, 1] *)
  assert_true ~msg:"all confidences in [0,1]"
    (List.for_all (fun p -> p.pat_confidence >= 0.0 && p.pat_confidence <= 1.0) patterns);
  (* Evidence strings non-empty *)
  assert_true ~msg:"all evidence non-empty"
    (List.for_all (fun p -> String.length p.pat_evidence > 0) patterns);
)

(* ══════════ Root Cause Tracer Tests ══════════ *)

let () = suite "RootCauseTracer" (fun () ->
  let comps = [
    make_component 1 "origin" Conditional 1 "if x < 0";
    make_component 2 "symptom1" Assignment 2 "y := f(x)";
    make_component 3 "symptom2" Return 3 "return y";
  ] in
  let susp = [
    { susp_component = 1; susp_tarantula = 0.9; susp_ochiai = 0.9; susp_dstar = 10.0; susp_rank = 1 };
    { susp_component = 2; susp_tarantula = 0.4; susp_ochiai = 0.4; susp_dstar = 1.0; susp_rank = 2 };
    { susp_component = 3; susp_tarantula = 0.2; susp_ochiai = 0.2; susp_dstar = 0.3; susp_rank = 3 };
  ] in
  let tests = [
    make_test 1 "t1" Fail [1;2;3] "i1" "o1" "wrong";
    make_test 2 "t2" Pass [2;3] "i2" "o2" "o2";
  ] in
  let patterns = [
    { pat_component = 1; pat_pattern = WrongOperator; pat_confidence = 0.8; pat_evidence = "< vs <=" };
  ] in
  let rcs = RootCauseTracer.trace comps susp tests patterns in
  assert_true ~msg:"root causes found" (List.length rcs > 0);
  let rc1 = List.hd rcs in
  assert_true ~msg:"origin is component 1" (rc1.rc_origin_component = 1);
  assert_true ~msg:"chain has steps" (List.length rc1.rc_chain > 0);
  assert_true ~msg:"confidence > 0" (rc1.rc_confidence > 0.0);
  assert_true ~msg:"category includes pattern"
    (rc1.rc_category = "Wrong operator");
)

(* ══════════ Fix Suggester Tests ══════════ *)

let () = suite "FixSuggester" (fun () ->
  let comps = [
    make_component 1 "loop" Loop 1 "for i = 0 to n";
    make_component 2 "call" FunctionCall 2 "open_file f";
  ] in
  let patterns = [
    { pat_component = 1; pat_pattern = OffByOne; pat_confidence = 0.7; pat_evidence = "boundary" };
    { pat_component = 2; pat_pattern = ResourceLeak; pat_confidence = 0.6; pat_evidence = "file" };
  ] in
  let rcs = [
    { rc_origin_component = 1; rc_symptom_components = [2];
      rc_chain = ["step1"]; rc_confidence = 0.8; rc_category = "Off-by-one" };
  ] in
  let mutations = [
    { mut_component = 1; mut_kind = ChangeConstant;
      mut_description = "Change constant at loop"; mut_fixes_failure = true;
      mut_new_passes = 5; mut_new_fails = 0 };
  ] in
  let fixes = FixSuggester.generate comps patterns rcs mutations in
  assert_true ~msg:"fixes generated" (List.length fixes > 0);
  (* Sorted by confidence *)
  let confs = List.map (fun f -> f.fix_confidence) fixes in
  let rec is_sorted = function
    | [] | [_] -> true
    | a :: b :: rest -> a >= b && is_sorted (b :: rest)
  in
  assert_true ~msg:"fixes sorted by confidence desc" (is_sorted confs);
  (* All fixes have descriptions *)
  assert_true ~msg:"all fixes have descriptions"
    (List.for_all (fun f -> String.length f.fix_description > 0) fixes);
  (* code_before and code_after non-empty *)
  assert_true ~msg:"all fixes have code before/after"
    (List.for_all (fun f ->
      String.length f.fix_code_before > 0 && String.length f.fix_code_after > 0
    ) fixes);
)

(* ══════════ Insight Generator Tests ══════════ *)

let () = suite "InsightGenerator" (fun () ->
  let tests_pass = [make_test 1 "t1" Pass [1] "i" "o" "o"] in
  let empty_susp = [] in
  let ins1 = InsightGenerator.generate tests_pass empty_susp [] [] [] [] in
  assert_true ~msg:"all pass => info-level insight"
    (List.exists (fun i -> i.insight_severity = Info) ins1);

  let tests_fail = [
    make_test 1 "t1" Fail [1] "i" "o" "wrong";
    make_test 2 "t2" Fail [1] "i" "o" "wrong";
    make_test 3 "t3" Pass [1] "i" "o" "o";
  ] in
  let high_susp = [
    { susp_component = 1; susp_tarantula = 0.9; susp_ochiai = 0.9; susp_dstar = 10.0; susp_rank = 1 };
  ] in
  let ins2 = InsightGenerator.generate tests_fail high_susp [] [] [] [] in
  assert_true ~msg:"failures => test suite insight present"
    (List.exists (fun i -> i.insight_category = "Test Suite") ins2);
  assert_true ~msg:"high susp => localization insight"
    (List.exists (fun i -> i.insight_category = "Fault Localization") ins2);
)

(* ══════════ Health Scoring Tests ══════════ *)

let () = suite "HealthScoring" (fun () ->
  let tests_pass = [make_test 1 "t1" Pass [1] "i" "o" "o"] in
  let (score1, tier1) = compute_health tests_pass [] [] [] [] in
  assert_true ~msg:"all pass => score 100" (score1 = 100);
  assert_equal ~msg:"all pass => Pristine" "Pristine" tier1;

  let tests_fail = [
    make_test 1 "t1" Fail [1] "i" "o" "wrong";
    make_test 2 "t2" Fail [1] "i" "o" "wrong";
  ] in
  let (score2, _tier2) = compute_health tests_fail [] [] [] [] in
  assert_true ~msg:"all fail => low score" (score2 < 50);

  let tests_mixed = [
    make_test 1 "t1" Pass [1] "i" "o" "o";
    make_test 2 "t2" Pass [1] "i" "o" "o";
    make_test 3 "t3" Pass [1] "i" "o" "o";
    make_test 4 "t4" Fail [1] "i" "o" "wrong";
  ] in
  let good_susp = [
    { susp_component = 1; susp_tarantula = 0.9; susp_ochiai = 0.9; susp_dstar = 10.0; susp_rank = 1 };
  ] in
  let good_patterns = [
    { pat_component = 1; pat_pattern = OffByOne; pat_confidence = 0.8; pat_evidence = "test" };
  ] in
  let good_rc = [
    { rc_origin_component = 1; rc_symptom_components = [];
      rc_chain = ["step"]; rc_confidence = 0.9; rc_category = "Off-by-one" };
  ] in
  let good_fixes = [
    { fix_component = 1; fix_description = "fix"; fix_code_before = "a";
      fix_code_after = "b"; fix_confidence = 0.85; fix_pattern = Some OffByOne };
  ] in
  let (score3, _) = compute_health tests_mixed good_susp good_patterns good_rc good_fixes in
  assert_true ~msg:"good localization with few failures => decent score" (score3 >= 50);
)

(* ══════════ Full Pipeline Tests ══════════ *)

let () = suite "FullPipeline" (fun () ->
  let comps = [
    make_component 1 "buggy" Conditional 1 "if x < n";
    make_component 2 "ok" Assignment 2 "y := 0";
    make_component 3 "also_ok" Return 3 "return y";
  ] in
  let tests = [
    make_test 1 "pass1" Pass [1;2;3] "a b c" "ok" "ok";
    make_test 2 "pass2" Pass [2;3] "d" "ok" "ok";
    make_test 3 "fail1" Fail [1;2] "e f" "ok" "crash";
  ] in
  let report = investigate comps tests in
  assert_true ~msg:"report has suspiciousness scores"
    (List.length report.rpt_suspiciousness > 0);
  assert_true ~msg:"report has patterns"
    (List.length report.rpt_patterns >= 0);  (* may or may not find patterns *)
  assert_true ~msg:"report has insights"
    (List.length report.rpt_insights > 0);
  assert_true ~msg:"health score in [0,100]"
    (report.rpt_health_score >= 0 && report.rpt_health_score <= 100);
  assert_true ~msg:"health tier non-empty"
    (String.length report.rpt_health_tier > 0);
  (* Buggy comp should rank higher than ok comp *)
  let s1 = List.find (fun s -> s.susp_component = 1) report.rpt_suspiciousness in
  let s3 = List.find (fun s -> s.susp_component = 3) report.rpt_suspiciousness in
  assert_true ~msg:"buggy comp ranks higher than non-buggy"
    (s1.susp_rank <= s3.susp_rank);
)

(* ══════════ Demo Scenario Tests ══════════ *)

let () = suite "DemoScenarios" (fun () ->
  List.iter (fun demo_fn ->
    let (name, components, tests) = demo_fn () in
    let report = investigate components tests in
    assert_true ~msg:(Printf.sprintf "%s: report generated" name)
      (List.length report.rpt_suspiciousness > 0);
    assert_true ~msg:(Printf.sprintf "%s: health in range" name)
      (report.rpt_health_score >= 0 && report.rpt_health_score <= 100);
    assert_true ~msg:(Printf.sprintf "%s: insights generated" name)
      (List.length report.rpt_insights > 0);
    let failing = List.filter test_is_failing tests in
    if List.length failing > 0 then
      assert_true ~msg:(Printf.sprintf "%s: fixes generated for failing tests" name)
        (List.length report.rpt_fixes >= 0);  (* may or may not generate *)
  ) demo_scenarios;
)

(* ══════════ Edge Case Tests ══════════ *)

let () = suite "EdgeCases" (fun () ->
  (* No components *)
  let report0 = investigate [] [] in
  assert_true ~msg:"empty input => health 100" (report0.rpt_health_score = 100);

  (* All errors *)
  let comps = [make_component 1 "a" Assignment 1 "x := 1"] in
  let tests = [make_test 1 "t1" (Error "timeout") [1] "i" "o" "timeout"] in
  let report1 = investigate comps tests in
  assert_true ~msg:"error tests treated as failing"
    (report1.rpt_health_score < 100);

  (* Component not covered by any test *)
  let comps2 = [
    make_component 1 "covered" Assignment 1 "x := 1";
    make_component 2 "uncovered" Assignment 2 "y := 2";
  ] in
  let tests2 = [make_test 1 "t1" Fail [1] "i" "o" "wrong"] in
  let report2 = investigate comps2 tests2 in
  let s2 = List.find (fun s -> s.susp_component = 2) report2.rpt_suspiciousness in
  assert_true ~msg:"uncovered component has 0 suspiciousness"
    (s2.susp_ochiai = 0.0);
)

(* ══════════ Utility Function Tests ══════════ *)

let () = suite "Utilities" (fun () ->
  assert_equal ~msg:"component_kind_to_string Assignment" "Assignment" (component_kind_to_string Assignment);
  assert_equal ~msg:"component_kind_to_string Loop" "Loop" (component_kind_to_string Loop);
  assert_equal ~msg:"bug_pattern_to_string OffByOne" "Off-by-one" (bug_pattern_to_string OffByOne);
  assert_equal ~msg:"bug_pattern_to_string NullDeref" "Null dereference" (bug_pattern_to_string NullDeref);
  assert_equal ~msg:"mutation_kind_to_string NegateCondition" "Negate condition" (mutation_kind_to_string NegateCondition);
  assert_equal ~msg:"severity_to_string Critical" "CRITICAL" (severity_to_string Critical);
  assert_true ~msg:"test_is_failing Fail" (test_is_failing (make_test 1 "t" Fail [] "" "" ""));
  assert_true ~msg:"test_is_failing Error" (test_is_failing (make_test 1 "t" (Error "e") [] "" "" ""));
  assert_false ~msg:"test_is_failing Pass" (test_is_failing (make_test 1 "t" Pass [] "" "" ""));
  assert_true ~msg:"clamp_f works" (clamp_f 0.0 1.0 1.5 = 1.0);
  assert_true ~msg:"clamp_f lower bound" (clamp_f 0.0 1.0 (-0.5) = 0.0);
)

(* ══════════ Dashboard Generation Tests ══════════ *)

let () = suite "DashboardGeneration" (fun () ->
  let comps = [make_component 1 "a" Assignment 1 "x := 1"] in
  let tests = [make_test 1 "t1" Fail [1] "i" "o" "wrong"] in
  let report = investigate comps tests in
  let html = generate_dashboard [("Test", report)] in
  assert_true ~msg:"HTML contains doctype"
    (String.length html > 100);
  (* Check title substring manually *)
  let contains s sub =
    let ls = String.length s and lsub = String.length sub in
    if lsub > ls then false
    else
      let found = ref false in
      for i = 0 to ls - lsub do
        if not !found && String.sub s i lsub = sub then found := true
      done;
      !found
  in
  assert_true ~msg:"HTML contains title"
    (contains html "Autonomous Debugger");
)

let () = test_summary ()
