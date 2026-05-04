(* ============================================================================
   test_fuzzing_engine.ml - Tests for Coverage-Guided Fuzzing Engine
   ============================================================================
   Self-contained test file that inlines core logic from fuzzing_engine.ml
   ============================================================================ *)

(* ── Test Framework ─────────────────────────────────────────────────────── *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0
let current_suite = ref ""

let assert_true msg cond =
  incr tests_run;
  if cond then (incr tests_passed; Printf.printf "  ✓ %s\n" msg)
  else (incr tests_failed; Printf.printf "  ✗ FAIL: %s\n" msg)

let assert_equal msg expected actual =
  incr tests_run;
  if expected = actual then (incr tests_passed; Printf.printf "  ✓ %s\n" msg)
  else (incr tests_failed; Printf.printf "  ✗ FAIL: %s (expected %s, got %s)\n" msg expected actual)

let assert_false msg cond = assert_true msg (not cond)

let suite name fn =
  current_suite := name;
  Printf.printf "\n── %s ──\n" name;
  fn ()

let test_summary () =
  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "Results: %d/%d passed" !tests_passed !tests_run;
  if !tests_failed > 0 then Printf.printf " (%d FAILED)" !tests_failed;
  Printf.printf "\n══════════════════════════════════════════\n";
  if !tests_failed > 0 then exit 1

(* ══════════ Inlined Core from fuzzing_engine.ml ══════════ *)

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

let random_bool () =
  random_int 2 = 0

let clamp_f lo hi x = Float.min hi (Float.max lo x)
let clamp_i lo hi x = min hi (max lo x)

let string_contains s sub =
  let ls = String.length s and lsub = String.length sub in
  if lsub > ls then false
  else begin
    let found = ref false in
    for i = 0 to ls - lsub do
      if not !found && String.sub s i lsub = sub then found := true
    done;
    !found
  end

type mutation_strategy =
  | BitFlip | ByteShuffle | ArithBoundary | Splice
  | DictInsert | Havoc | Truncate | Extend | SwapBytes | Negate

type crash_kind =
  | CrashException of string | CrashTimeout | CrashAssertion
  | CrashDivZero | CrashOutOfBounds

type coverage_edge = { edge_src : int; edge_dst : int }

type corpus_entry = {
  ce_id : int;
  ce_input : int array;
  ce_coverage : coverage_edge list;
  ce_energy : float;
  ce_depth : int;
  ce_origin_strategy : mutation_strategy option;
  ce_found_at : int;
}

type crash_record = {
  cr_id : int;
  cr_input : int array;
  cr_minimized_input : int array option;
  cr_kind : crash_kind;
  cr_signature : string;
  cr_strategy : mutation_strategy option;
  cr_found_at : int;
}

type campaign_stats = {
  cs_total_execs : int;
  cs_coverage_count : int;
  cs_crash_count : int;
  cs_unique_crashes : int;
  cs_corpus_size : int;
  cs_exec_per_sec : float;
  cs_coverage_history : (int * int) list;
  cs_strategy_hits : (mutation_strategy * int) list;
}

type insight_severity = Info | Warning | Critical

type insight = {
  ins_category : string;
  ins_message : string;
  ins_severity : insight_severity;
}

type campaign_result = {
  res_target : string;
  res_stats : campaign_stats;
  res_corpus : corpus_entry list;
  res_crashes : crash_record list;
  res_insights : insight list;
  res_health_score : int;
  res_health_tier : string;
}

let strategy_to_string = function
  | BitFlip -> "BitFlip" | ByteShuffle -> "ByteShuffle"
  | ArithBoundary -> "ArithBoundary" | Splice -> "Splice"
  | DictInsert -> "DictInsert" | Havoc -> "Havoc"
  | Truncate -> "Truncate" | Extend -> "Extend"
  | SwapBytes -> "SwapBytes" | Negate -> "Negate"

let crash_kind_to_string = function
  | CrashException s -> Printf.sprintf "Exception(%s)" s
  | CrashTimeout -> "Timeout" | CrashAssertion -> "Assertion"
  | CrashDivZero -> "DivisionByZero" | CrashOutOfBounds -> "OutOfBounds"

let severity_to_string = function
  | Info -> "INFO" | Warning -> "WARNING" | Critical -> "CRITICAL"

let input_to_string arr =
  let n = Array.length arr in
  if n = 0 then "[]"
  else if n <= 10 then
    Printf.sprintf "[%s]"
      (String.concat ";" (Array.to_list (Array.map string_of_int arr)))
  else
    Printf.sprintf "[%s;...+%d]"
      (String.concat ";" (List.map string_of_int
        (Array.to_list (Array.sub arr 0 8))))
      (n - 8)

(* ── Corpus Manager ─────────────────────────────────────────────────────── *)

module CorpusManager = struct
  type t = {
    mutable entries : corpus_entry list;
    mutable next_id : int;
    mutable seen_sigs : string list;
  }

  let create () = { entries = []; next_id = 1; seen_sigs = [] }

  let coverage_signature edges =
    let sorted = List.sort (fun a b ->
      let c = compare a.edge_src b.edge_src in
      if c <> 0 then c else compare a.edge_dst b.edge_dst
    ) edges in
    String.concat "|" (List.map (fun e ->
      Printf.sprintf "%d->%d" e.edge_src e.edge_dst
    ) sorted)

  let has_new_coverage corpus edges =
    let sig_ = coverage_signature edges in
    not (List.mem sig_ corpus.seen_sigs)

  let add corpus input edges strategy exec_num =
    let sig_ = coverage_signature edges in
    if List.mem sig_ corpus.seen_sigs then false
    else begin
      let entry = {
        ce_id = corpus.next_id;
        ce_input = Array.copy input;
        ce_coverage = edges;
        ce_energy = 1.0;
        ce_depth = 0;
        ce_origin_strategy = strategy;
        ce_found_at = exec_num;
      } in
      corpus.next_id <- corpus.next_id + 1;
      corpus.entries <- entry :: corpus.entries;
      corpus.seen_sigs <- sig_ :: corpus.seen_sigs;
      true
    end

  let pick_seed corpus =
    match corpus.entries with
    | [] -> None
    | entries ->
      let total_energy = List.fold_left (fun acc e -> acc +. e.ce_energy) 0.0 entries in
      if total_energy < 1e-9 then Some (List.hd entries)
      else begin
        let r = random_float () *. total_energy in
        let rec pick acc = function
          | [] -> List.hd entries
          | e :: rest ->
            let acc' = acc +. e.ce_energy in
            if acc' >= r then e else pick acc' rest
        in
        Some (pick 0.0 entries)
      end

  let boost_energy corpus entry_id bonus =
    corpus.entries <- List.map (fun e ->
      if e.ce_id = entry_id then { e with ce_energy = e.ce_energy +. bonus }
      else e
    ) corpus.entries

  let decay_all corpus factor =
    corpus.entries <- List.map (fun e ->
      { e with ce_energy = e.ce_energy *. factor }
    ) corpus.entries

  let size corpus = List.length corpus.entries
end

(* ── Mutation Engine ────────────────────────────────────────────────────── *)

module MutationEngine = struct
  let all_strategies = [
    BitFlip; ByteShuffle; ArithBoundary; Splice;
    DictInsert; Havoc; Truncate; Extend; SwapBytes; Negate
  ]

  let pick_strategy () =
    let idx = random_int (List.length all_strategies) in
    List.nth all_strategies idx

  let mutate_bit_flip input =
    let n = Array.length input in
    if n = 0 then [|random_int_range (-128) 127|]
    else begin
      let result = Array.copy input in
      let pos = random_int n in
      let bit = 1 lsl (random_int 8) in
      result.(pos) <- result.(pos) lxor bit;
      result
    end

  let mutate_byte_shuffle input =
    let n = Array.length input in
    if n < 2 then input
    else begin
      let result = Array.copy input in
      let i = random_int n in
      let j = random_int n in
      let tmp = result.(i) in
      result.(i) <- result.(j);
      result.(j) <- tmp;
      result
    end

  let mutate_arith_boundary input =
    let n = Array.length input in
    if n = 0 then [|0|]
    else begin
      let result = Array.copy input in
      let pos = random_int n in
      let boundaries = [|0; 1; -1; max_int; min_int; 127; -128; 255; 256; 65535; -32768|] in
      result.(pos) <- boundaries.(random_int (Array.length boundaries));
      result
    end

  let mutate_splice input1 input2 =
    let n1 = Array.length input1 and n2 = Array.length input2 in
    if n1 = 0 then input2
    else if n2 = 0 then input1
    else begin
      let cut1 = random_int n1 in
      let cut2 = random_int n2 in
      let len = cut1 + (n2 - cut2) in
      if len = 0 then [|0|]
      else begin
        let result = Array.make len 0 in
        Array.blit input1 0 result 0 cut1;
        Array.blit input2 cut2 result cut1 (n2 - cut2);
        result
      end
    end

  let mutate_dict_insert input dict =
    match dict with
    | [] -> input
    | _ ->
      let word = List.nth dict (random_int (List.length dict)) in
      let n = Array.length input in
      let wn = Array.length word in
      let pos = if n = 0 then 0 else random_int n in
      let result = Array.make (n + wn) 0 in
      Array.blit input 0 result 0 pos;
      Array.blit word 0 result pos wn;
      if pos < n then Array.blit input pos result (pos + wn) (n - pos);
      result

  let mutate_havoc input =
    let n = Array.length input in
    if n = 0 then [|random_int_range (-128) 127|]
    else begin
      let result = Array.copy input in
      let ops = random_int_range 1 5 in
      for _ = 1 to ops do
        let pos = random_int (Array.length result) in
        result.(pos) <- random_int_range (-1000) 1000
      done;
      result
    end

  let mutate_truncate input =
    let n = Array.length input in
    if n <= 1 then [||]
    else Array.sub input 0 (random_int_range 1 (n - 1))

  let mutate_extend input =
    let n = Array.length input in
    let ext = random_int_range 1 5 in
    let result = Array.make (n + ext) 0 in
    Array.blit input 0 result 0 n;
    for i = n to n + ext - 1 do
      result.(i) <- random_int_range (-128) 127
    done;
    result

  let mutate_swap input =
    let n = Array.length input in
    if n < 4 then input
    else begin
      let result = Array.copy input in
      let i = random_int (n - 1) in
      let j = random_int (n - 1) in
      let len = min 2 (min (n - i) (n - j)) in
      for k = 0 to len - 1 do
        let tmp = result.(i + k) in
        result.(i + k) <- result.(j + k);
        result.(j + k) <- tmp
      done;
      result
    end

  let mutate_negate input =
    let n = Array.length input in
    if n = 0 then [|0|]
    else begin
      let result = Array.copy input in
      let pos = random_int n in
      result.(pos) <- - result.(pos);
      result
    end

  let mutate strategy input corpus_entries dict =
    match strategy with
    | BitFlip -> mutate_bit_flip input
    | ByteShuffle -> mutate_byte_shuffle input
    | ArithBoundary -> mutate_arith_boundary input
    | Splice ->
      let other = match corpus_entries with
        | [] -> input
        | entries ->
          let e = List.nth entries (random_int (List.length entries)) in
          e.ce_input
      in
      mutate_splice input other
    | DictInsert -> mutate_dict_insert input dict
    | Havoc -> mutate_havoc input
    | Truncate -> mutate_truncate input
    | Extend -> mutate_extend input
    | SwapBytes -> mutate_swap input
    | Negate -> mutate_negate input
end

(* ── Coverage Tracker ───────────────────────────────────────────────────── *)

module CoverageTracker = struct
  type t = {
    mutable all_edges : (int * int, bool) Hashtbl.t;
    mutable total_count : int;
  }

  let create () = { all_edges = Hashtbl.create 256; total_count = 0 }

  let record tracker edges =
    let new_found = ref 0 in
    List.iter (fun e ->
      let key = (e.edge_src, e.edge_dst) in
      if not (Hashtbl.mem tracker.all_edges key) then begin
        Hashtbl.replace tracker.all_edges key true;
        incr new_found
      end
    ) edges;
    tracker.total_count <- Hashtbl.length tracker.all_edges;
    !new_found

  let count tracker = tracker.total_count
  let has_edge tracker src dst = Hashtbl.mem tracker.all_edges (src, dst)
end

(* ── Crash Analyzer ─────────────────────────────────────────────────────── *)

module CrashAnalyzer = struct
  type t = {
    mutable crashes : crash_record list;
    mutable next_id : int;
    mutable seen_sigs : string list;
  }

  let create () = { crashes = []; next_id = 1; seen_sigs = [] }

  let classify_exn exn_msg =
    if string_contains exn_msg "Division_by_zero" then CrashDivZero
    else if string_contains exn_msg "Assert" then CrashAssertion
    else if string_contains exn_msg "index out of bounds"
         || string_contains exn_msg "Invalid_argument" then CrashOutOfBounds
    else CrashException exn_msg

  let make_signature kind input =
    let kind_str = crash_kind_to_string kind in
    let len = Array.length input in
    Printf.sprintf "%s:len=%d" kind_str len

  let record analyzer input kind strategy exec_num =
    let sig_ = make_signature kind input in
    if List.mem sig_ analyzer.seen_sigs then false
    else begin
      let cr = {
        cr_id = analyzer.next_id;
        cr_input = Array.copy input;
        cr_minimized_input = None;
        cr_kind = kind;
        cr_signature = sig_;
        cr_strategy = strategy;
        cr_found_at = exec_num;
      } in
      analyzer.next_id <- analyzer.next_id + 1;
      analyzer.crashes <- cr :: analyzer.crashes;
      analyzer.seen_sigs <- sig_ :: analyzer.seen_sigs;
      true
    end

  let unique_count analyzer = List.length analyzer.crashes
  let all_crashes analyzer = List.rev analyzer.crashes
end

(* ── Minimizer ──────────────────────────────────────────────────────────── *)

module Minimizer = struct
  let minimize test_fn input max_rounds =
    let n = Array.length input in
    if n <= 1 then input
    else begin
      let current = ref (Array.copy input) in
      let round = ref 0 in
      while !round < max_rounds do
        let improved = ref false in
        let len = Array.length !current in
        if len <= 1 then round := max_rounds
        else begin
          let i = ref 0 in
          while !i < Array.length !current do
            let candidate_len = Array.length !current - 1 in
            if candidate_len >= 0 then begin
              let candidate = Array.make candidate_len 0 in
              let pos = ref 0 in
              Array.iteri (fun j v ->
                if j <> !i then begin
                  if !pos < candidate_len then candidate.(!pos) <- v;
                  incr pos
                end
              ) !current;
              if test_fn candidate then begin
                current := candidate;
                improved := true
              end else
                incr i
            end else incr i
          done;
          if not !improved then round := max_rounds
          else incr round
        end
      done;
      !current
    end
end

(* ── Insight Generator ──────────────────────────────────────────────────── *)

module InsightGen = struct
  let generate stats corpus crashes =
    let insights = ref [] in
    let add cat msg sev =
      insights := { ins_category = cat; ins_message = msg; ins_severity = sev } :: !insights in

    if stats.cs_coverage_count = 0 then
      add "Coverage" "No edges covered" Warning
    else if stats.cs_coverage_count < 5 then
      add "Coverage" (Printf.sprintf "Low coverage (%d edges)" stats.cs_coverage_count) Warning
    else
      add "Coverage" (Printf.sprintf "Covered %d unique edges across %d corpus entries"
        stats.cs_coverage_count (List.length corpus)) Info;

    if stats.cs_unique_crashes > 0 then
      add "Crashes" (Printf.sprintf "Found %d unique crash signatures"
        stats.cs_unique_crashes) Critical
    else
      add "Crashes" "No crashes found" Info;

    let effective = List.filter (fun (_, hits) -> hits > 0) stats.cs_strategy_hits in
    if effective = [] then
      add "Mutations" "No strategy discovered new coverage" Warning
    else begin
      let sorted = List.sort (fun (_, a) (_, b) -> compare b a) effective in
      let top_name, top_hits = List.hd sorted in
      add "Mutations" (Printf.sprintf "Most effective: %s (%d hits)"
        (strategy_to_string top_name) top_hits) Info
    end;

    if stats.cs_corpus_size < 3 then
      add "Corpus" "Very small corpus" Warning
    else
      add "Corpus" (Printf.sprintf "Corpus grew to %d entries" stats.cs_corpus_size) Info;

    let minimized = List.filter (fun cr ->
      match cr.cr_minimized_input with
      | Some m -> Array.length m < Array.length cr.cr_input
      | None -> false
    ) crashes in
    if List.length minimized > 0 then
      add "Minimizer" (Printf.sprintf "Minimized %d/%d crash inputs"
        (List.length minimized) (List.length crashes)) Info;

    List.rev !insights
end

(* ── Health Scoring ─────────────────────────────────────────────────────── *)

let compute_health stats crashes =
  let cov_score = if stats.cs_coverage_count >= 20 then 30.0
    else if stats.cs_coverage_count >= 10 then 25.0
    else if stats.cs_coverage_count >= 5 then 20.0
    else if stats.cs_coverage_count > 0 then 10.0
    else 0.0 in
  let corpus_score = clamp_f 0.0 20.0 (float_of_int stats.cs_corpus_size *. 2.0) in
  let crash_score = if stats.cs_unique_crashes >= 5 then 30.0
    else if stats.cs_unique_crashes >= 3 then 25.0
    else if stats.cs_unique_crashes >= 1 then 15.0
    else 5.0 in
  let min_success = List.length (List.filter (fun cr ->
    match cr.cr_minimized_input with
    | Some m -> Array.length m < Array.length cr.cr_input | None -> false
  ) crashes) in
  let min_score = clamp_f 0.0 10.0 (float_of_int min_success *. 3.0) in
  let active = List.length (List.filter (fun (_, h) -> h > 0) stats.cs_strategy_hits) in
  let strat_score = clamp_f 0.0 10.0 (float_of_int active *. 2.0) in
  let total = clamp_i 0 100 (int_of_float (cov_score +. corpus_score +. crash_score +. min_score +. strat_score)) in
  let tier = if total >= 80 then "Excellent"
    else if total >= 60 then "Good"
    else if total >= 40 then "Fair"
    else if total >= 20 then "Poor"
    else "Critical" in
  (total, tier)

(* ══════════════════════════════════════════════════════════════════════════ *)
(* ── TESTS ──────────────────────────────────────────────────────────────── *)
(* ══════════════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n🔬 Fuzzing Engine - Test Suite\n"
let () = Printf.printf "══════════════════════════════════════════\n"

(* ── Random Infrastructure Tests ────────────────────────────────────────── *)

let () = suite "RandomInfrastructure" (fun () ->
  _global_seed := 42;
  let v1 = _next_random () in
  let v2 = _next_random () in
  assert_true "next_random produces different values" (v1 <> v2);

  _global_seed := 42;
  let a = _next_random () in
  _global_seed := 42;
  let b = _next_random () in
  assert_true "deterministic with same seed" (a = b);

  let r = random_int_range 5 10 in
  assert_true "random_int_range in bounds" (r >= 5 && r <= 10);

  let r2 = random_int_range 10 10 in
  assert_true "random_int_range equal bounds" (r2 = 10);

  let r3 = random_int 0 in
  assert_true "random_int 0 returns 0" (r3 = 0);

  _global_seed := 100;
  let f = random_float () in
  assert_true "random_float in [0,1]" (f >= 0.0 && f <= 1.0);

  _global_seed := 200;
  let bools = List.init 50 (fun _ -> random_bool ()) in
  assert_true "random_bool produces both values"
    (List.mem true bools && List.mem false bools)
)

(* ── Utility Tests ──────────────────────────────────────────────────────── *)

let () = suite "Utilities" (fun () ->
  assert_true "clamp_f lower" (clamp_f 0.0 1.0 (-0.5) = 0.0);
  assert_true "clamp_f upper" (clamp_f 0.0 1.0 1.5 = 1.0);
  assert_true "clamp_f in range" (clamp_f 0.0 1.0 0.5 = 0.5);
  assert_true "clamp_i lower" (clamp_i 0 100 (-10) = 0);
  assert_true "clamp_i upper" (clamp_i 0 100 150 = 100);
  assert_true "string_contains found" (string_contains "hello world" "world");
  assert_false "string_contains not found" (string_contains "hello" "xyz");
  assert_false "string_contains empty haystack" (string_contains "" "a");
  assert_true "string_contains empty needle" (string_contains "hello" "");

  assert_equal "strategy BitFlip" "BitFlip" (strategy_to_string BitFlip);
  assert_equal "strategy Havoc" "Havoc" (strategy_to_string Havoc);
  assert_equal "crash DivZero" "DivisionByZero" (crash_kind_to_string CrashDivZero);
  assert_equal "crash Exception" "Exception(test)" (crash_kind_to_string (CrashException "test"));
  assert_equal "severity INFO" "INFO" (severity_to_string Info);
  assert_equal "severity CRITICAL" "CRITICAL" (severity_to_string Critical);

  assert_equal "input_to_string empty" "[]" (input_to_string [||]);
  assert_equal "input_to_string one" "[42]" (input_to_string [|42|]);
  assert_true "input_to_string long has ..." (string_contains (input_to_string (Array.make 20 1)) "...")
)

(* ── Corpus Manager Tests ───────────────────────────────────────────────── *)

let () = suite "CorpusManager" (fun () ->
  let c = CorpusManager.create () in
  assert_true "empty corpus size 0" (CorpusManager.size c = 0);

  let edges1 = [{ edge_src = 1; edge_dst = 2 }] in
  let added = CorpusManager.add c [|1; 2; 3|] edges1 None 1 in
  assert_true "first add succeeds" added;
  assert_true "size is 1" (CorpusManager.size c = 1);

  let added2 = CorpusManager.add c [|4; 5; 6|] edges1 None 2 in
  assert_false "duplicate coverage rejected" added2;

  let edges2 = [{ edge_src = 3; edge_dst = 4 }] in
  let added3 = CorpusManager.add c [|7; 8|] edges2 (Some BitFlip) 3 in
  assert_true "new coverage accepted" added3;
  assert_true "size is 2" (CorpusManager.size c = 2);

  assert_true "has_new_coverage for new edges"
    (CorpusManager.has_new_coverage c [{ edge_src = 5; edge_dst = 6 }]);
  assert_false "no new coverage for existing edges"
    (CorpusManager.has_new_coverage c edges1);

  _global_seed := 42;
  let seed = CorpusManager.pick_seed c in
  assert_true "pick_seed returns Some" (seed <> None);

  CorpusManager.boost_energy c 1 5.0;
  let entry = List.find (fun e -> e.ce_id = 1) c.entries in
  assert_true "boost_energy works" (entry.ce_energy > 5.0);

  CorpusManager.decay_all c 0.5;
  let entry2 = List.find (fun e -> e.ce_id = 1) c.entries in
  assert_true "decay_all reduces energy" (entry2.ce_energy < entry.ce_energy);

  let empty = CorpusManager.create () in
  let no_seed = CorpusManager.pick_seed empty in
  assert_true "pick_seed empty returns None" (no_seed = None);

  let sig1 = CorpusManager.coverage_signature edges1 in
  let sig2 = CorpusManager.coverage_signature edges2 in
  assert_true "different edges different signatures" (sig1 <> sig2);

  let sig_same = CorpusManager.coverage_signature edges1 in
  assert_true "same edges same signature" (sig1 = sig_same)
)

(* ── Mutation Engine Tests ──────────────────────────────────────────────── *)

let () = suite "MutationEngine" (fun () ->
  _global_seed := 42;

  (* BitFlip *)
  let input = [|10; 20; 30|] in
  let flipped = MutationEngine.mutate_bit_flip input in
  assert_true "bit_flip changes something" (flipped <> input);
  assert_true "bit_flip preserves length" (Array.length flipped = Array.length input);

  (* BitFlip on empty *)
  let flipped_empty = MutationEngine.mutate_bit_flip [||] in
  assert_true "bit_flip empty produces singleton" (Array.length flipped_empty = 1);

  (* ByteShuffle *)
  let shuffled = MutationEngine.mutate_byte_shuffle [|1; 2; 3; 4|] in
  assert_true "byte_shuffle preserves length" (Array.length shuffled = 4);

  (* ByteShuffle short *)
  let sh_short = MutationEngine.mutate_byte_shuffle [|1|] in
  assert_true "byte_shuffle single unchanged" (sh_short = [|1|]);

  (* ArithBoundary *)
  let arith = MutationEngine.mutate_arith_boundary [|5; 10|] in
  assert_true "arith_boundary preserves length" (Array.length arith = 2);

  let arith_empty = MutationEngine.mutate_arith_boundary [||] in
  assert_true "arith_boundary empty -> singleton" (Array.length arith_empty = 1);

  (* Splice *)
  let spliced = MutationEngine.mutate_splice [|1; 2; 3|] [|4; 5; 6|] in
  assert_true "splice produces non-empty" (Array.length spliced > 0);

  let spliced_empty = MutationEngine.mutate_splice [||] [|1; 2|] in
  assert_true "splice empty+non-empty" (Array.length spliced_empty > 0);

  (* DictInsert *)
  let dict = [[|99; 100|]; [|42|]] in
  let inserted = MutationEngine.mutate_dict_insert [|1; 2|] dict in
  assert_true "dict_insert grows input" (Array.length inserted > 2);

  let no_dict = MutationEngine.mutate_dict_insert [|1|] [] in
  assert_true "dict_insert empty dict unchanged" (no_dict = [|1|]);

  (* Havoc *)
  let havoc = MutationEngine.mutate_havoc [|10; 20; 30|] in
  assert_true "havoc preserves length" (Array.length havoc = 3);

  let havoc_empty = MutationEngine.mutate_havoc [||] in
  assert_true "havoc empty -> singleton" (Array.length havoc_empty = 1);

  (* Truncate *)
  let trunc = MutationEngine.mutate_truncate [|1; 2; 3; 4|] in
  assert_true "truncate shorter" (Array.length trunc < 4);

  let trunc_short = MutationEngine.mutate_truncate [|1|] in
  assert_true "truncate single -> empty" (Array.length trunc_short = 0);

  (* Extend *)
  let extended = MutationEngine.mutate_extend [|1; 2|] in
  assert_true "extend longer" (Array.length extended > 2);

  (* SwapBytes *)
  let swapped = MutationEngine.mutate_swap [|1; 2; 3; 4; 5|] in
  assert_true "swap preserves length" (Array.length swapped = 5);

  let swap_short = MutationEngine.mutate_swap [|1; 2|] in
  assert_true "swap short unchanged" (Array.length swap_short = 2);

  (* Negate *)
  let negated = MutationEngine.mutate_negate [|5; -3; 7|] in
  assert_true "negate preserves length" (Array.length negated = 3);

  let negate_empty = MutationEngine.mutate_negate [||] in
  assert_true "negate empty -> singleton" (Array.length negate_empty = 1);

  (* pick_strategy *)
  _global_seed := 42;
  let strategies = List.init 20 (fun _ -> MutationEngine.pick_strategy ()) in
  let unique = List.sort_uniq compare strategies in
  assert_true "pick_strategy has diversity" (List.length unique > 1);

  (* mutate dispatch *)
  let corpus_entries = [{ ce_id = 1; ce_input = [|9; 8; 7|]; ce_coverage = [];
    ce_energy = 1.0; ce_depth = 0; ce_origin_strategy = None; ce_found_at = 0 }] in
  let m = MutationEngine.mutate Splice [|1; 2; 3|] corpus_entries [] in
  assert_true "mutate Splice returns array" (Array.length m >= 0)
)

(* ── Coverage Tracker Tests ─────────────────────────────────────────────── *)

let () = suite "CoverageTracker" (fun () ->
  let t = CoverageTracker.create () in
  assert_true "initial count 0" (CoverageTracker.count t = 0);

  let edges = [{ edge_src = 1; edge_dst = 2 }; { edge_src = 3; edge_dst = 4 }] in
  let new_count = CoverageTracker.record t edges in
  assert_true "first record finds 2 new" (new_count = 2);
  assert_true "count is 2" (CoverageTracker.count t = 2);

  let new_count2 = CoverageTracker.record t edges in
  assert_true "duplicate edges finds 0 new" (new_count2 = 0);

  let edges2 = [{ edge_src = 1; edge_dst = 2 }; { edge_src = 5; edge_dst = 6 }] in
  let new_count3 = CoverageTracker.record t edges2 in
  assert_true "partial new edges finds 1" (new_count3 = 1);
  assert_true "count is 3" (CoverageTracker.count t = 3);

  assert_true "has_edge 1->2" (CoverageTracker.has_edge t 1 2);
  assert_false "no edge 9->10" (CoverageTracker.has_edge t 9 10);

  let empty_new = CoverageTracker.record t [] in
  assert_true "empty edges 0 new" (empty_new = 0)
)

(* ── Crash Analyzer Tests ───────────────────────────────────────────────── *)

let () = suite "CrashAnalyzer" (fun () ->
  let a = CrashAnalyzer.create () in
  assert_true "initial count 0" (CrashAnalyzer.unique_count a = 0);

  let added = CrashAnalyzer.record a [|1; 2|] CrashDivZero (Some ArithBoundary) 10 in
  assert_true "first crash recorded" added;
  assert_true "unique count 1" (CrashAnalyzer.unique_count a = 1);

  let added2 = CrashAnalyzer.record a [|3; 4|] CrashDivZero None 20 in
  assert_false "same signature rejected" added2;

  let added3 = CrashAnalyzer.record a [|5|] CrashDivZero None 30 in
  assert_true "different length = different sig" added3;

  let added4 = CrashAnalyzer.record a [|1; 2|] CrashAssertion None 40 in
  assert_true "different kind = different sig" added4;

  let all = CrashAnalyzer.all_crashes a in
  assert_true "all_crashes returns all" (List.length all = 3);

  (* classify_exn *)
  let k1 = CrashAnalyzer.classify_exn "Division_by_zero" in
  assert_true "classify Division_by_zero" (k1 = CrashDivZero);

  let k2 = CrashAnalyzer.classify_exn "Assert_failure" in
  assert_true "classify Assert" (k2 = CrashAssertion);

  let k3 = CrashAnalyzer.classify_exn "Invalid_argument(\"index out of bounds\")" in
  assert_true "classify out of bounds" (k3 = CrashOutOfBounds);

  let k4 = CrashAnalyzer.classify_exn "Failure(\"something\")" in
  assert_true "classify generic exception" (match k4 with CrashException _ -> true | _ -> false);

  let sig_ = CrashAnalyzer.make_signature CrashDivZero [|1; 2; 3|] in
  assert_true "signature includes kind and length"
    (string_contains sig_ "DivisionByZero" && string_contains sig_ "len=3")
)

(* ── Minimizer Tests ────────────────────────────────────────────────────── *)

let () = suite "Minimizer" (fun () ->
  (* Always-crashing: minimize to 0 elements *)
  let m1 = Minimizer.minimize (fun _ -> true) [|1; 2; 3; 4; 5|] 10 in
  assert_true "always-crashing minimizes to small" (Array.length m1 <= 1);

  (* Never-crashing: keeps original *)
  let m2 = Minimizer.minimize (fun _ -> false) [|1; 2; 3|] 10 in
  assert_true "never-crashing keeps original" (Array.length m2 = 3);

  (* Crash needs specific element *)
  let m3 = Minimizer.minimize
    (fun inp -> Array.exists (fun x -> x = 42) inp)
    [|10; 20; 42; 30; 40|] 10 in
  assert_true "specific element preserved" (Array.exists (fun x -> x = 42) m3);
  assert_true "minimized from 5" (Array.length m3 < 5);

  (* Single element *)
  let m4 = Minimizer.minimize (fun _ -> true) [|99|] 10 in
  assert_true "single element stays" (Array.length m4 <= 1);

  (* Empty input *)
  let m5 = Minimizer.minimize (fun _ -> true) [||] 10 in
  assert_true "empty input stays empty" (Array.length m5 = 0)
)

(* ── Insight Generator Tests ────────────────────────────────────────────── *)

let () = suite "InsightGenerator" (fun () ->
  let stats_good = {
    cs_total_execs = 100; cs_coverage_count = 25;
    cs_crash_count = 5; cs_unique_crashes = 3;
    cs_corpus_size = 10; cs_exec_per_sec = 100.0;
    cs_coverage_history = [(0, 5); (50, 15); (100, 25)];
    cs_strategy_hits = [(BitFlip, 3); (Havoc, 2); (Negate, 0)];
  } in
  let crashes = [{
    cr_id = 1; cr_input = [|1; 2; 3; 4; 5|];
    cr_minimized_input = Some [|3|];
    cr_kind = CrashDivZero; cr_signature = "test";
    cr_strategy = Some BitFlip; cr_found_at = 10;
  }] in
  let corpus = [{ ce_id = 1; ce_input = [|0|]; ce_coverage = [];
    ce_energy = 1.0; ce_depth = 0; ce_origin_strategy = None; ce_found_at = 0 }] in
  let insights = InsightGen.generate stats_good corpus crashes in
  assert_true "has coverage insight"
    (List.exists (fun i -> i.ins_category = "Coverage") insights);
  assert_true "has crash insight"
    (List.exists (fun i -> i.ins_category = "Crashes") insights);
  assert_true "has mutations insight"
    (List.exists (fun i -> i.ins_category = "Mutations") insights);
  assert_true "has corpus insight"
    (List.exists (fun i -> i.ins_category = "Corpus") insights);
  assert_true "has minimizer insight"
    (List.exists (fun i -> i.ins_category = "Minimizer") insights);

  (* No crashes *)
  let stats_clean = { stats_good with cs_unique_crashes = 0; cs_crash_count = 0 } in
  let ins2 = InsightGen.generate stats_clean corpus [] in
  assert_true "no crashes: info level"
    (List.exists (fun i -> i.ins_category = "Crashes" && i.ins_severity = Info) ins2);

  (* Zero coverage *)
  let stats_zero = { stats_good with cs_coverage_count = 0 } in
  let ins3 = InsightGen.generate stats_zero corpus [] in
  assert_true "zero coverage: warning"
    (List.exists (fun i -> i.ins_category = "Coverage" && i.ins_severity = Warning) ins3);

  (* Low coverage *)
  let stats_low = { stats_good with cs_coverage_count = 3 } in
  let ins4 = InsightGen.generate stats_low corpus [] in
  assert_true "low coverage: warning"
    (List.exists (fun i -> i.ins_category = "Coverage" && i.ins_severity = Warning) ins4);

  (* Small corpus *)
  let stats_small = { stats_good with cs_corpus_size = 2 } in
  let ins5 = InsightGen.generate stats_small corpus [] in
  assert_true "small corpus: warning"
    (List.exists (fun i -> i.ins_category = "Corpus" && i.ins_severity = Warning) ins5);

  (* No effective strategies *)
  let stats_no_strat = { stats_good with cs_strategy_hits = [(BitFlip, 0); (Havoc, 0)] } in
  let ins6 = InsightGen.generate stats_no_strat corpus [] in
  assert_true "no effective strategies: warning"
    (List.exists (fun i -> i.ins_category = "Mutations" && i.ins_severity = Warning) ins6)
)

(* ── Health Scoring Tests ───────────────────────────────────────────────── *)

let () = suite "HealthScoring" (fun () ->
  let stats_excellent = {
    cs_total_execs = 1000; cs_coverage_count = 30;
    cs_crash_count = 10; cs_unique_crashes = 5;
    cs_corpus_size = 15; cs_exec_per_sec = 500.0;
    cs_coverage_history = []; cs_strategy_hits = [(BitFlip, 5); (Havoc, 3); (Negate, 2)];
  } in
  let crashes_min = List.init 3 (fun i -> {
    cr_id = i; cr_input = [|1; 2; 3|]; cr_minimized_input = Some [|1|];
    cr_kind = CrashDivZero; cr_signature = ""; cr_strategy = None; cr_found_at = 0;
  }) in
  let (score1, tier1) = compute_health stats_excellent crashes_min in
  assert_true "excellent score >= 80" (score1 >= 80);
  assert_equal "excellent tier" "Excellent" tier1;

  let stats_poor = {
    cs_total_execs = 100; cs_coverage_count = 1;
    cs_crash_count = 0; cs_unique_crashes = 0;
    cs_corpus_size = 1; cs_exec_per_sec = 50.0;
    cs_coverage_history = []; cs_strategy_hits = [(BitFlip, 0)];
  } in
  let (score2, _) = compute_health stats_poor [] in
  assert_true "poor score < 40" (score2 < 40);

  let stats_mid = {
    cs_total_execs = 500; cs_coverage_count = 12;
    cs_crash_count = 2; cs_unique_crashes = 1;
    cs_corpus_size = 5; cs_exec_per_sec = 200.0;
    cs_coverage_history = []; cs_strategy_hits = [(BitFlip, 2); (Havoc, 1)];
  } in
  let (score3, _) = compute_health stats_mid [] in
  assert_true "mid score in range" (score3 >= 20 && score3 <= 80);

  (* Score always in [0, 100] *)
  let stats_zero = {
    cs_total_execs = 0; cs_coverage_count = 0;
    cs_crash_count = 0; cs_unique_crashes = 0;
    cs_corpus_size = 0; cs_exec_per_sec = 0.0;
    cs_coverage_history = []; cs_strategy_hits = [];
  } in
  let (score4, _) = compute_health stats_zero [] in
  assert_true "zero score >= 0" (score4 >= 0);
  assert_true "zero score <= 100" (score4 <= 100)
)

(* ── Integration Tests with Demo Targets ────────────────────────────────── *)

let target_simple_crash input =
  let edges = [{ edge_src = 1; edge_dst = 2 }] in
  if Array.length input > 0 && input.(0) = 42 then begin
    failwith "crash_on_42"
  end;
  if Array.length input > 1 then
    edges @ [{ edge_src = 2; edge_dst = 3 }]
  else
    edges

let target_no_crash input =
  let n = Array.length input in
  let edges = [{ edge_src = 10; edge_dst = 11 }] in
  if n > 3 then edges @ [{ edge_src = 11; edge_dst = 12 }]
  else edges

let target_div_zero input =
  let edges = [{ edge_src = 20; edge_dst = 21 }] in
  if Array.length input >= 2 then begin
    let _ = input.(0) / input.(1) in
    edges @ [{ edge_src = 21; edge_dst = 22 }]
  end else edges

let () = suite "IntegrationSimpleCrash" (fun () ->
  _global_seed := 42;
  let ft = { ft_name = "simple_crash"; ft_func = target_simple_crash; ft_dict = [[|42|]] } in
  let seeds = [[|0|]; [|42|]] in
  let (stats, corpus, crashes) = Campaign.run ft 200 seeds in
  assert_true "integration: executed" (stats.cs_total_execs = 200);
  assert_true "integration: has coverage" (stats.cs_coverage_count > 0);
  assert_true "integration: has corpus" (List.length corpus > 0);
  (* With [|42|] as a dict entry, we should find the crash *)
  assert_true "integration: found crashes" (List.length crashes > 0 || stats.cs_crash_count > 0)
)

let () = suite "IntegrationNoCrash" (fun () ->
  _global_seed := 100;
  let ft = { ft_name = "no_crash"; ft_func = target_no_crash; ft_dict = [] } in
  let seeds = [[|0|]] in
  let (stats, _, crashes) = Campaign.run ft 100 seeds in
  assert_true "no-crash: executed" (stats.cs_total_execs = 100);
  assert_true "no-crash: no unique crashes" (List.length crashes = 0)
)

let () = suite "IntegrationDivZero" (fun () ->
  _global_seed := 42;
  let ft = { ft_name = "div_zero"; ft_func = target_div_zero; ft_dict = [[|1; 0|]] } in
  let seeds = [[|1; 0|]; [|5; 3|]] in
  let (stats, _, _) = Campaign.run ft 200 seeds in
  assert_true "div-zero: has crashes" (stats.cs_crash_count > 0)
)

(* ── Campaign Stats Tests ───────────────────────────────────────────────── *)

let () = suite "CampaignStats" (fun () ->
  _global_seed := 42;
  let target = { ft_name = "test";
    ft_func = (fun inp ->
      let edges = [{ edge_src = 0; edge_dst = 1 }] in
      if Array.length inp > 2 then
        edges @ [{ edge_src = 1; edge_dst = 2 }]
      else edges
    );
    ft_dict = [] } in
  let (stats, corpus, _) = Campaign.run target 50 [[|0|]] in
  assert_true "stats total_execs correct" (stats.cs_total_execs = 50);
  assert_true "stats coverage > 0" (stats.cs_coverage_count > 0);
  assert_true "stats corpus_size matches" (stats.cs_corpus_size = List.length corpus);
  assert_true "stats has strategy_hits" (List.length stats.cs_strategy_hits > 0)
)

(* ── End-to-End Health Scoring Tests ────────────────────────────────────── *)

let () = suite "EndToEndHealth" (fun () ->
  _global_seed := 42;
  let ft = { ft_name = "e2e";
    ft_func = (fun inp ->
      let n = Array.length inp in
      let edges = [{ edge_src = 0; edge_dst = 1 }] in
      if n > 0 && inp.(0) = 0 then failwith "crash";
      if n > 2 then edges @ [{ edge_src = 1; edge_dst = 2 }]
      else if n > 4 then edges @ [{ edge_src = 1; edge_dst = 3 }]
      else edges
    );
    ft_dict = [[|0|]] } in
  let seeds = [[|1|]; [|0|]] in
  let (stats, _, crashes) = Campaign.run ft 300 seeds in
  let insights = InsightGen.generate stats [] crashes in
  let (score, tier) = compute_health stats crashes in
  assert_true "e2e score in range" (score >= 0 && score <= 100);
  assert_true "e2e tier non-empty" (String.length tier > 0);
  assert_true "e2e insights generated" (List.length insights > 0)
)

type fuzz_target = {
  ft_name : string;
  ft_func : int array -> coverage_edge list;
  ft_dict : int array list;
}

(* ── Campaign Module (inlined for integration tests) ────────────────────── *)

module Campaign = struct
  let run target max_iterations seeds =
    let corpus = CorpusManager.create () in
    let tracker = CoverageTracker.create () in
    let analyzer = CrashAnalyzer.create () in
    let strategy_hits = Hashtbl.create 16 in

    List.iter (fun s ->
      Hashtbl.replace strategy_hits s 0
    ) MutationEngine.all_strategies;

    List.iter (fun seed ->
      let edges = try target.ft_func seed with _ -> [] in
      let _ = CoverageTracker.record tracker edges in
      let _ = CorpusManager.add corpus seed edges None 0 in
      ()
    ) seeds;

    if CorpusManager.size corpus = 0 then begin
      let default_seed = [|0|] in
      let edges = try target.ft_func default_seed with _ -> [] in
      let _ = CoverageTracker.record tracker edges in
      let _ = CorpusManager.add corpus default_seed edges None 0 in
      ()
    end;

    let coverage_history = ref [(0, CoverageTracker.count tracker)] in
    let total_crashes = ref 0 in

    for exec_num = 1 to max_iterations do
      let seed_entry = match CorpusManager.pick_seed corpus with
        | Some e -> e | None -> List.hd corpus.entries in
      let strategy = MutationEngine.pick_strategy () in
      let mutated = MutationEngine.mutate strategy seed_entry.ce_input
        corpus.entries target.ft_dict in

      let edges, crashed =
        try
          let e = target.ft_func mutated in
          (e, None)
        with
        | Division_by_zero -> ([], Some CrashDivZero)
        | Invalid_argument msg ->
          ([], Some (if string_contains msg "index" then CrashOutOfBounds
                     else CrashException msg))
        | Assert_failure _ -> ([], Some CrashAssertion)
        | exn -> ([], Some (CrashAnalyzer.classify_exn (Printexc.to_string exn)))
      in

      let new_edges = CoverageTracker.record tracker edges in

      if new_edges > 0 then begin
        let _ = CorpusManager.add corpus mutated edges (Some strategy) exec_num in
        CorpusManager.boost_energy corpus seed_entry.ce_id 0.5;
        let prev = try Hashtbl.find strategy_hits strategy with Not_found -> 0 in
        Hashtbl.replace strategy_hits strategy (prev + 1);
        coverage_history := (exec_num, CoverageTracker.count tracker) :: !coverage_history
      end;

      (match crashed with
       | Some kind ->
         incr total_crashes;
         let _ = CrashAnalyzer.record analyzer mutated kind (Some strategy) exec_num in
         ()
       | None -> ());

      if exec_num mod 100 = 0 then
        CorpusManager.decay_all corpus 0.95
    done;

    let crashes = List.map (fun cr ->
      let minimized = Minimizer.minimize (fun inp ->
        try let _ = target.ft_func inp in false
        with _ -> true
      ) cr.cr_input 10 in
      { cr with cr_minimized_input = Some minimized }
    ) (CrashAnalyzer.all_crashes analyzer) in

    let strat_hits = List.map (fun s ->
      (s, try Hashtbl.find strategy_hits s with Not_found -> 0)
    ) MutationEngine.all_strategies in

    let stats = {
      cs_total_execs = max_iterations;
      cs_coverage_count = CoverageTracker.count tracker;
      cs_crash_count = !total_crashes;
      cs_unique_crashes = CrashAnalyzer.unique_count analyzer;
      cs_corpus_size = CorpusManager.size corpus;
      cs_exec_per_sec = float_of_int max_iterations;
      cs_coverage_history = List.rev !coverage_history;
      cs_strategy_hits = strat_hits;
    } in

    (stats, List.rev corpus.entries, crashes)
end

(* ── Coverage Signature Edge Cases ──────────────────────────────────────── *)

let () = suite "CoverageSignatureEdgeCases" (fun () ->
  let sig_empty = CorpusManager.coverage_signature [] in
  assert_equal "empty edges empty sig" "" sig_empty;

  let sig_one = CorpusManager.coverage_signature [{ edge_src = 1; edge_dst = 2 }] in
  assert_true "single edge sig" (String.length sig_one > 0);

  (* Order independence *)
  let edges_a = [{ edge_src = 1; edge_dst = 2 }; { edge_src = 3; edge_dst = 4 }] in
  let edges_b = [{ edge_src = 3; edge_dst = 4 }; { edge_src = 1; edge_dst = 2 }] in
  let sig_a = CorpusManager.coverage_signature edges_a in
  let sig_b = CorpusManager.coverage_signature edges_b in
  assert_equal "order-independent signatures" sig_a sig_b
)

let () = Printf.printf "\n";
  test_summary ()
