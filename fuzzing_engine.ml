(* ============================================================================
   fuzzing_engine.ml - Coverage-Guided Fuzzing Engine
   ============================================================================

   An autonomous coverage-guided fuzzing engine for discovering crashes,
   edge cases, and unexpected behaviors in OCaml functions. Unlike
   quickcheck.ml (random property-based testing) or contract_inference.ml
   (behavioral contracts), this engine uses mutation-based input generation
   with branch/path coverage feedback to explore deep program states.

   Demonstrates:
   - Mutation-based input generation (10 strategies)
   - Coverage-guided seed selection (edge coverage bitmaps)
   - Crash deduplication and classification
   - Delta-debugging-inspired input minimization
   - Energy-based mutation scheduling
   - Campaign orchestration with statistics
   - Autonomous insight generation
   - Health scoring 0-100
   - Interactive HTML dashboard generation

   7 fuzzing engines:
   1. Corpus Manager       — seed corpus management, dedup by coverage sig
   2. Mutation Engine       — 10 mutation strategies with energy scheduling
   3. Coverage Tracker      — edge coverage bitmaps, new-coverage detection
   4. Crash Analyzer        — crash capture, dedup by signature, classification
   5. Minimizer             — delta-debugging input minimization
   6. Campaign Orchestrator — run campaigns, track stats (exec/s, coverage)
   7. Insight Generator     — autonomous findings, health scoring 0-100

   Usage:
     ocamlopt fuzzing_engine.ml -o fuzzing_engine
     ./fuzzing_engine --demo
     ./fuzzing_engine --dashboard
     (or) ocaml fuzzing_engine.ml --demo
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

let random_bool () =
  random_int 2 = 0

let shuffle arr =
  let n = Array.length arr in
  for i = n - 1 downto 1 do
    let j = random_int (i + 1) in
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp
  done

(* ══════════ Utility Helpers ══════════ *)

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

let _sparkline values =
  let blocks = [|"▁";"▂";"▃";"▄";"▅";"▆";"▇";"█"|] in
  if values = [] then ""
  else begin
    let mn = List.fold_left min max_float values in
    let mx = List.fold_left max (-.max_float) values in
    let range = mx -. mn in
    String.concat "" (List.map (fun v ->
      let idx = if range < 1e-9 then 3
        else clamp_i 0 7 (int_of_float ((v -. mn) /. range *. 7.0)) in
      blocks.(idx)
    ) values)
  end

(* ══════════ Core Types ══════════ *)

type mutation_strategy =
  | BitFlip
  | ByteShuffle
  | ArithBoundary
  | Splice
  | DictInsert
  | Havoc
  | Truncate
  | Extend
  | SwapBytes
  | Negate

type crash_kind =
  | CrashException of string
  | CrashTimeout
  | CrashAssertion
  | CrashDivZero
  | CrashOutOfBounds

type coverage_edge = {
  edge_src : int;
  edge_dst : int;
}

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

type fuzz_target = {
  ft_name : string;
  ft_func : int array -> coverage_edge list;
  ft_dict : int array list;
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

(* ══════════ String Conversions ══════════ *)

let strategy_to_string = function
  | BitFlip -> "BitFlip" | ByteShuffle -> "ByteShuffle"
  | ArithBoundary -> "ArithBoundary" | Splice -> "Splice"
  | DictInsert -> "DictInsert" | Havoc -> "Havoc"
  | Truncate -> "Truncate" | Extend -> "Extend"
  | SwapBytes -> "SwapBytes" | Negate -> "Negate"

let crash_kind_to_string = function
  | CrashException s -> Printf.sprintf "Exception(%s)" s
  | CrashTimeout -> "Timeout"
  | CrashAssertion -> "Assertion"
  | CrashDivZero -> "DivisionByZero"
  | CrashOutOfBounds -> "OutOfBounds"

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

(* ══════════ Engine 1: Corpus Manager ══════════ *)

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
      (* Energy-proportional selection *)
      let total_energy = List.fold_left (fun acc e -> acc +. e.ce_energy) 0.0 entries in
      if total_energy < 1e-9 then Some (List.hd entries)
      else begin
        let r = random_float () *. total_energy in
        let rec pick acc = function
          | [] -> List.hd entries
          | e :: rest ->
            let acc' = acc +. e.ce_energy in
            if acc' >= r then e
            else pick acc' rest
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

(* ══════════ Engine 2: Mutation Engine ══════════ *)

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

(* ══════════ Engine 3: Coverage Tracker ══════════ *)

module CoverageTracker = struct
  type t = {
    mutable all_edges : (int * int, bool) Hashtbl.t;
    mutable total_count : int;
  }

  let create () = {
    all_edges = Hashtbl.create 256;
    total_count = 0;
  }

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

  let has_edge tracker src dst =
    Hashtbl.mem tracker.all_edges (src, dst)
end

(* ══════════ Engine 4: Crash Analyzer ══════════ *)

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

(* ══════════ Engine 5: Minimizer ══════════ *)

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
          (* Try removing each element *)
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

(* ══════════ Engine 6: Campaign Orchestrator ══════════ *)

module Campaign = struct
  let run target max_iterations seeds =
    let corpus = CorpusManager.create () in
    let tracker = CoverageTracker.create () in
    let analyzer = CrashAnalyzer.create () in
    let strategy_hits = Hashtbl.create 16 in

    (* Initialize strategy hit counters *)
    List.iter (fun s ->
      Hashtbl.replace strategy_hits s 0
    ) MutationEngine.all_strategies;

    (* Seed the corpus *)
    List.iter (fun seed ->
      let edges = try target.ft_func seed with _ -> [] in
      let _ = CoverageTracker.record tracker edges in
      let _ = CorpusManager.add corpus seed edges None 0 in
      ()
    ) seeds;

    (* If no seeds, add a default *)
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
      (* Pick a seed *)
      let seed_entry = match CorpusManager.pick_seed corpus with
        | Some e -> e | None -> List.hd corpus.entries in

      (* Pick strategy and mutate *)
      let strategy = MutationEngine.pick_strategy () in
      let mutated = MutationEngine.mutate strategy seed_entry.ce_input
        corpus.entries target.ft_dict in

      (* Execute the target *)
      let edges, crashed =
        try
          let e = target.ft_func mutated in
          (e, None)
        with
        | Division_by_zero ->
          ([], Some CrashDivZero)
        | Invalid_argument msg ->
          ([], Some (if string_contains msg "index" then CrashOutOfBounds
                     else CrashException msg))
        | Assert_failure _ ->
          ([], Some CrashAssertion)
        | exn ->
          ([], Some (CrashAnalyzer.classify_exn (Printexc.to_string exn)))
      in

      (* Track coverage *)
      let new_edges = CoverageTracker.record tracker edges in

      (* If new coverage found, add to corpus *)
      if new_edges > 0 then begin
        let _ = CorpusManager.add corpus mutated edges (Some strategy) exec_num in
        CorpusManager.boost_energy corpus seed_entry.ce_id 0.5;
        let prev = try Hashtbl.find strategy_hits strategy with Not_found -> 0 in
        Hashtbl.replace strategy_hits strategy (prev + 1);
        coverage_history := (exec_num, CoverageTracker.count tracker) :: !coverage_history
      end;

      (* Record crash *)
      (match crashed with
       | Some kind ->
         incr total_crashes;
         let _ = CrashAnalyzer.record analyzer mutated kind (Some strategy) exec_num in
         ()
       | None -> ());

      (* Periodic energy decay *)
      if exec_num mod 100 = 0 then
        CorpusManager.decay_all corpus 0.95
    done;

    (* Minimize crash inputs *)
    let crashes = List.map (fun cr ->
      let minimized = Minimizer.minimize (fun inp ->
        try let _ = target.ft_func inp in false
        with _ -> true
      ) cr.cr_input 10 in
      { cr with cr_minimized_input = Some minimized }
    ) (CrashAnalyzer.all_crashes analyzer) in

    (* Build strategy hits list *)
    let strat_hits = List.map (fun s ->
      (s, try Hashtbl.find strategy_hits s with Not_found -> 0)
    ) MutationEngine.all_strategies in

    let stats = {
      cs_total_execs = max_iterations;
      cs_coverage_count = CoverageTracker.count tracker;
      cs_crash_count = !total_crashes;
      cs_unique_crashes = CrashAnalyzer.unique_count analyzer;
      cs_corpus_size = CorpusManager.size corpus;
      cs_exec_per_sec = float_of_int max_iterations;  (* simplified *)
      cs_coverage_history = List.rev !coverage_history;
      cs_strategy_hits = strat_hits;
    } in

    (stats, List.rev corpus.entries, crashes)
end

(* ══════════ Engine 7: Insight Generator ══════════ *)

module InsightGen = struct
  let generate stats corpus crashes =
    let insights = ref [] in
    let add cat msg sev =
      insights := { ins_category = cat; ins_message = msg; ins_severity = sev } :: !insights in

    (* Coverage analysis *)
    if stats.cs_coverage_count = 0 then
      add "Coverage" "No edges covered — target may not instrument coverage" Warning
    else if stats.cs_coverage_count < 5 then
      add "Coverage" (Printf.sprintf "Low coverage (%d edges) — consider adding more diverse seeds"
        stats.cs_coverage_count) Warning
    else
      add "Coverage" (Printf.sprintf "Covered %d unique edges across %d corpus entries"
        stats.cs_coverage_count (List.length corpus)) Info;

    (* Coverage plateau detection *)
    (match stats.cs_coverage_history with
     | [] -> ()
     | history ->
       let last_exec, _ = List.nth history (List.length history - 1) in
       let mid_point = stats.cs_total_execs / 2 in
       let mid_cov = List.fold_left (fun best (e, c) ->
         if e <= mid_point && e > fst best then (e, c) else best
       ) (0, 0) history in
       let final_cov = stats.cs_coverage_count in
       if snd mid_cov > 0 && final_cov = snd mid_cov && last_exec > mid_point then
         add "Coverage" "Coverage plateaued in the second half — mutation strategies may be exhausted" Warning);

    (* Crash analysis *)
    if stats.cs_unique_crashes > 0 then begin
      add "Crashes" (Printf.sprintf "Found %d unique crash signatures from %d total crashes"
        stats.cs_unique_crashes stats.cs_crash_count) Critical;
      (* Classify by kind *)
      let kinds = List.map (fun cr -> crash_kind_to_string cr.cr_kind) crashes in
      let unique_kinds = List.sort_uniq String.compare kinds in
      List.iter (fun k ->
        let count = List.length (List.filter (fun s -> s = k) kinds) in
        add "Crashes" (Printf.sprintf "%s: %d occurrences" k count) Warning
      ) unique_kinds
    end else
      add "Crashes" "No crashes found — target appears robust to fuzzing" Info;

    (* Strategy effectiveness *)
    let effective = List.filter (fun (_, hits) -> hits > 0) stats.cs_strategy_hits in
    if effective = [] then
      add "Mutations" "No mutation strategy discovered new coverage" Warning
    else begin
      let sorted = List.sort (fun (_, a) (_, b) -> compare b a) effective in
      let top_name, top_hits = List.hd sorted in
      add "Mutations" (Printf.sprintf "Most effective strategy: %s (%d new-coverage hits)"
        (strategy_to_string top_name) top_hits) Info
    end;

    (* Corpus health *)
    if stats.cs_corpus_size < 3 then
      add "Corpus" "Very small corpus — fuzzer struggled to find diverse inputs" Warning
    else
      add "Corpus" (Printf.sprintf "Corpus grew to %d diverse entries" stats.cs_corpus_size) Info;

    (* Minimization effectiveness *)
    let minimized = List.filter (fun cr ->
      match cr.cr_minimized_input with
      | Some m -> Array.length m < Array.length cr.cr_input
      | None -> false
    ) crashes in
    if List.length minimized > 0 then
      add "Minimizer" (Printf.sprintf "Successfully minimized %d/%d crash inputs"
        (List.length minimized) (List.length crashes)) Info;

    List.rev !insights
end

(* ══════════ Health Scoring ══════════ *)

let compute_health stats crashes =
  (* Base: 70 points for coverage growth *)
  let cov_score = if stats.cs_coverage_count >= 20 then 30.0
    else if stats.cs_coverage_count >= 10 then 25.0
    else if stats.cs_coverage_count >= 5 then 20.0
    else if stats.cs_coverage_count > 0 then 10.0
    else 0.0 in

  (* Corpus diversity: up to 20 points *)
  let corpus_score = clamp_f 0.0 20.0 (float_of_int stats.cs_corpus_size *. 2.0) in

  (* Crash discovery: up to 30 points (finding crashes is good!) *)
  let crash_score = if stats.cs_unique_crashes >= 5 then 30.0
    else if stats.cs_unique_crashes >= 3 then 25.0
    else if stats.cs_unique_crashes >= 1 then 15.0
    else 5.0 in

  (* Minimization success: up to 10 points *)
  let min_success = List.length (List.filter (fun cr ->
    match cr.cr_minimized_input with
    | Some m -> Array.length m < Array.length cr.cr_input | None -> false
  ) crashes) in
  let min_score = clamp_f 0.0 10.0 (float_of_int min_success *. 3.0) in

  (* Strategy diversity: up to 10 points *)
  let active = List.length (List.filter (fun (_, h) -> h > 0) stats.cs_strategy_hits) in
  let strat_score = clamp_f 0.0 10.0 (float_of_int active *. 2.0) in

  let total = clamp_i 0 100 (int_of_float (cov_score +. corpus_score +. crash_score +. min_score +. strat_score)) in
  let tier = if total >= 80 then "Excellent"
    else if total >= 60 then "Good"
    else if total >= 40 then "Fair"
    else if total >= 20 then "Poor"
    else "Critical" in
  (total, tier)

(* ══════════ Demo Targets ══════════ *)

(* Target 1: Key=Value parser *)
let target_kv_parser input =
  let n = Array.length input in
  let edges = ref [] in
  let add_edge s d = edges := { edge_src = s; edge_dst = d } :: !edges in
  add_edge 100 101;  (* entry *)
  if n = 0 then begin
    add_edge 101 102;  (* empty input *)
    !edges
  end else begin
    add_edge 101 103;  (* non-empty *)
    let has_eq = Array.exists (fun x -> x = 61) input in  (* '=' = 61 *)
    if has_eq then begin
      add_edge 103 104;  (* has separator *)
      let eq_pos = ref (-1) in
      Array.iteri (fun i x -> if x = 61 && !eq_pos = -1 then eq_pos := i) input;
      if !eq_pos = 0 then begin
        add_edge 104 105;  (* empty key *)
        if n = 1 then add_edge 105 106  (* key=, no value -> crash-like *)
      end else begin
        add_edge 104 107;  (* valid key *)
        if !eq_pos = n - 1 then
          add_edge 107 108  (* empty value *)
        else
          add_edge 107 109  (* full pair *)
      end
    end else begin
      add_edge 103 110;  (* no separator *)
      (* Crash on negative values *)
      if Array.exists (fun x -> x < 0) input then
        failwith "negative_byte_in_parser"
    end;
    !edges
  end

(* Target 2: Arithmetic evaluator *)
let target_arith_eval input =
  let n = Array.length input in
  let edges = ref [] in
  let add_edge s d = edges := { edge_src = s; edge_dst = d } :: !edges in
  add_edge 200 201;
  if n = 0 then begin add_edge 201 202; !edges end
  else begin
    add_edge 201 203;
    let a = input.(0) in
    let b = if n > 1 then input.(1) else 1 in
    let op = if n > 2 then input.(2) mod 4 else 0 in
    (match op with
     | 0 -> add_edge 203 204; let _ = a + b in ()
     | 1 -> add_edge 203 205; let _ = a - b in ()
     | 2 -> add_edge 203 206; let _ = a * b in ()
     | 3 -> add_edge 203 207;
       if b = 0 then (add_edge 207 208; raise Division_by_zero)
       else (add_edge 207 209; let _ = a / b in ())
     | _ -> add_edge 203 210);
    !edges
  end

(* Target 3: Bracket matcher *)
let target_bracket_matcher input =
  let n = Array.length input in
  let edges = ref [] in
  let add_edge s d = edges := { edge_src = s; edge_dst = d } :: !edges in
  add_edge 300 301;
  if n = 0 then begin add_edge 301 302; !edges end
  else begin
    add_edge 301 303;
    let depth = ref 0 in
    let max_depth = ref 0 in
    Array.iter (fun x ->
      let c = x mod 3 in  (* 0=open, 1=close, 2=other *)
      if c = 0 then begin
        incr depth;
        if !depth > !max_depth then max_depth := !depth;
        add_edge 303 304
      end else if c = 1 then begin
        decr depth;
        if !depth < 0 then begin
          add_edge 303 305;  (* unmatched close *)
          failwith "unmatched_close_bracket"
        end;
        add_edge 303 306
      end else
        add_edge 303 307
    ) input;
    if !depth > 0 then add_edge 303 308;  (* unclosed *)
    if !max_depth > 5 then add_edge 303 309;  (* deep nesting *)
    !edges
  end

(* Target 4: Base64-like encoder *)
let target_base64 input =
  let n = Array.length input in
  let edges = ref [] in
  let add_edge s d = edges := { edge_src = s; edge_dst = d } :: !edges in
  add_edge 400 401;
  if n = 0 then begin add_edge 401 402; !edges end
  else begin
    add_edge 401 403;
    (* Encode: map each byte to a 6-bit range *)
    let encoded = Array.map (fun x ->
      let v = abs x mod 64 in
      add_edge 403 (404 + v / 16);  (* bucket edges *)
      v
    ) input in
    (* Decode back *)
    let _ = Array.map (fun x ->
      if x >= 64 then begin
        add_edge 403 408;
        failwith "invalid_base64_char"
      end;
      add_edge 403 409;
      x
    ) encoded in
    if n mod 3 <> 0 then add_edge 403 410;  (* padding needed *)
    !edges
  end

(* Target 5: Tokenizer *)
let target_tokenizer input =
  let n = Array.length input in
  let edges = ref [] in
  let add_edge s d = edges := { edge_src = s; edge_dst = d } :: !edges in
  add_edge 500 501;
  if n = 0 then begin add_edge 501 502; !edges end
  else begin
    add_edge 501 503;
    let state = ref 0 in  (* 0=start, 1=in_number, 2=in_word, 3=in_string *)
    Array.iter (fun x ->
      let v = abs x mod 128 in
      (match !state with
       | 0 ->
         if v >= 48 && v <= 57 then (state := 1; add_edge 503 504)
         else if v >= 65 && v <= 90 then (state := 2; add_edge 503 505)
         else if v = 34 then (state := 3; add_edge 503 506)
         else if v = 0 then (add_edge 503 507; failwith "null_byte_in_input")
         else add_edge 503 508
       | 1 ->
         if v >= 48 && v <= 57 then add_edge 504 504
         else (state := 0; add_edge 504 503)
       | 2 ->
         if v >= 65 && v <= 90 then add_edge 505 505
         else (state := 0; add_edge 505 503)
       | 3 ->
         if v = 34 then (state := 0; add_edge 506 503)
         else if v = 92 then add_edge 506 509  (* escape *)
         else add_edge 506 506
       | _ -> add_edge 503 510)
    ) input;
    if !state = 3 then begin
      add_edge 506 511;  (* unterminated string *)
      failwith "unterminated_string_literal"
    end;
    !edges
  end

(* Target 6: Mini state machine *)
let target_state_machine input =
  let n = Array.length input in
  let edges = ref [] in
  let add_edge s d = edges := { edge_src = s; edge_dst = d } :: !edges in
  add_edge 600 601;
  if n = 0 then begin add_edge 601 602; !edges end
  else begin
    add_edge 601 603;
    let state = ref 0 in
    let steps = ref 0 in
    Array.iter (fun x ->
      incr steps;
      if !steps > 50 then (add_edge 603 604; failwith "infinite_loop_detected");
      let cmd = abs x mod 5 in
      (match !state, cmd with
       | 0, 0 -> state := 1; add_edge 603 610
       | 0, 1 -> state := 2; add_edge 603 611
       | 1, 0 -> state := 0; add_edge 610 603
       | 1, 2 -> state := 3; add_edge 610 612
       | 2, 1 -> state := 0; add_edge 611 603
       | 2, 3 -> state := 3; add_edge 611 612
       | 3, 4 -> state := 0; add_edge 612 603
       | 3, _ -> add_edge 612 613; failwith "invalid_transition_from_state_3"
       | _, _ -> add_edge 603 614)
    ) input;
    !edges
  end

(* Target 7: Date validator *)
let target_date_validator input =
  let n = Array.length input in
  let edges = ref [] in
  let add_edge s d = edges := { edge_src = s; edge_dst = d } :: !edges in
  add_edge 700 701;
  if n < 3 then begin add_edge 701 702; !edges end
  else begin
    add_edge 701 703;
    let year = abs input.(0) in
    let month = abs input.(1) mod 13 in
    let day = abs input.(2) mod 32 in
    if month = 0 then begin add_edge 703 704; failwith "invalid_month_zero" end;
    add_edge 703 705;
    let days_in_month = [|0;31;28;31;30;31;30;31;31;30;31;30;31|] in
    let max_day = if month = 2 && year mod 4 = 0 && (year mod 100 <> 0 || year mod 400 = 0)
      then (add_edge 705 706; 29)
      else (add_edge 705 707; days_in_month.(month)) in
    if day = 0 then begin add_edge 707 708; failwith "invalid_day_zero" end;
    if day > max_day then begin add_edge 707 709; failwith "day_exceeds_month" end;
    add_edge 707 710;
    if year > 9999 then add_edge 710 711;
    !edges
  end

(* Target 8: Sort with edge cases *)
let target_sort input =
  let n = Array.length input in
  let edges = ref [] in
  let add_edge s d = edges := { edge_src = s; edge_dst = d } :: !edges in
  add_edge 800 801;
  if n = 0 then begin add_edge 801 802; !edges end
  else if n = 1 then begin add_edge 801 803; !edges end
  else begin
    add_edge 801 804;
    (* Simple bubble sort with instrumented edges *)
    let arr = Array.copy input in
    let swapped = ref true in
    let passes = ref 0 in
    while !swapped do
      swapped := false;
      incr passes;
      if !passes > n + 1 then begin
        add_edge 804 805;
        failwith "sort_exceeded_pass_limit"
      end;
      for i = 0 to Array.length arr - 2 do
        if arr.(i) > arr.(i + 1) then begin
          let tmp = arr.(i) in
          arr.(i) <- arr.(i + 1);
          arr.(i + 1) <- tmp;
          swapped := true;
          add_edge 804 806  (* swap *)
        end else
          add_edge 804 807  (* no swap *)
      done
    done;
    (* Check if was already sorted *)
    let was_sorted = Array.to_list input = Array.to_list arr in
    if was_sorted then add_edge 804 808 else add_edge 804 809;
    if n > 10 then add_edge 804 810;
    !edges
  end

let demo_targets = [
  { ft_name = "kv_parser";
    ft_func = target_kv_parser;
    ft_dict = [ [|61|]; [|61; 0|]; [|0; 61|] ] };
  { ft_name = "arith_eval";
    ft_func = target_arith_eval;
    ft_dict = [ [|0|]; [|0; 0; 3|] ] };
  { ft_name = "bracket_matcher";
    ft_func = target_bracket_matcher;
    ft_dict = [ [|0; 0; 0; 0; 0; 0|]; [|1; 1|] ] };
  { ft_name = "base64_codec";
    ft_func = target_base64;
    ft_dict = [ [|0; 0; 0|]; [|255|] ] };
  { ft_name = "tokenizer";
    ft_func = target_tokenizer;
    ft_dict = [ [|34|]; [|34; 92; 34|]; [|0|] ] };
  { ft_name = "state_machine";
    ft_func = target_state_machine;
    ft_dict = [ [|0; 2; 4|]; [|1; 3; 4|] ] };
  { ft_name = "date_validator";
    ft_func = target_date_validator;
    ft_dict = [ [|2024; 2; 29|]; [|0; 0; 0|] ] };
  { ft_name = "sort";
    ft_func = target_sort;
    ft_dict = [ [|5; 3; 1; 4; 2|]; [|1; 2; 3|] ] };
]

(* ══════════ Run Full Campaign ══════════ *)

let run_campaign target max_iters =
  let seeds = [|0|] :: [|1; 2; 3|] :: target.ft_dict in
  let (stats, corpus, crashes) = Campaign.run target max_iters seeds in
  let insights = InsightGen.generate stats corpus crashes in
  let (health, tier) = compute_health stats crashes in
  {
    res_target = target.ft_name;
    res_stats = stats;
    res_corpus = corpus;
    res_crashes = crashes;
    res_insights = insights;
    res_health_score = health;
    res_health_tier = tier;
  }

(* ══════════ Print Report ══════════ *)

let print_result r =
  Printf.printf "\n┌─────────────────────────────────────────────\n";
  Printf.printf "│ Target: %s\n" r.res_target;
  Printf.printf "├─────────────────────────────────────────────\n";
  Printf.printf "│ Executions:     %d\n" r.res_stats.cs_total_execs;
  Printf.printf "│ Coverage:       %d edges\n" r.res_stats.cs_coverage_count;
  Printf.printf "│ Corpus:         %d entries\n" r.res_stats.cs_corpus_size;
  Printf.printf "│ Crashes:        %d total, %d unique\n"
    r.res_stats.cs_crash_count r.res_stats.cs_unique_crashes;
  Printf.printf "│ Health:         %d/100 (%s)\n" r.res_health_score r.res_health_tier;
  Printf.printf "└─────────────────────────────────────────────\n";

  (* Top strategies *)
  let effective = List.filter (fun (_, h) -> h > 0) r.res_stats.cs_strategy_hits in
  if effective <> [] then begin
    let sorted = List.sort (fun (_, a) (_, b) -> compare b a) effective in
    Printf.printf "  Strategy effectiveness:\n";
    List.iter (fun (s, h) ->
      Printf.printf "    %-15s %d hits\n" (strategy_to_string s) h
    ) (if List.length sorted > 5 then
         List.filteri (fun i _ -> i < 5) sorted
       else sorted)
  end;

  (* Crashes *)
  if r.res_crashes <> [] then begin
    Printf.printf "  Crashes found:\n";
    List.iter (fun cr ->
      let min_str = match cr.cr_minimized_input with
        | Some m -> Printf.sprintf " → minimized: %s" (input_to_string m)
        | None -> "" in
      Printf.printf "    [%s] %s%s\n"
        (crash_kind_to_string cr.cr_kind) (input_to_string cr.cr_input) min_str
    ) r.res_crashes
  end;

  (* Insights *)
  if r.res_insights <> [] then begin
    Printf.printf "  Insights:\n";
    List.iter (fun ins ->
      let icon = match ins.ins_severity with
        | Critical -> "🔴" | Warning -> "🟡" | Info -> "🟢" in
      Printf.printf "    %s [%s] %s\n" icon ins.ins_category ins.ins_message
    ) r.res_insights
  end

(* ══════════ HTML Dashboard ══════════ *)

let generate_dashboard results =
  let buf = Buffer.create 8192 in
  let p s = Buffer.add_string buf s; Buffer.add_char buf '\n' in
  p "<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"UTF-8\">";
  p "<title>Fuzzing Engine Dashboard</title>";
  p "<style>";
  p "body{font-family:system-ui,-apple-system,sans-serif;margin:0;padding:20px;background:#0d1117;color:#c9d1d9}";
  p ".card{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:16px;margin:12px 0}";
  p "h1{color:#58a6ff;border-bottom:1px solid #30363d;padding-bottom:8px}";
  p "h2{color:#79c0ff;margin-top:0}";
  p "table{width:100%;border-collapse:collapse;margin:8px 0}";
  p "th,td{padding:8px 12px;text-align:left;border-bottom:1px solid #21262d}";
  p "th{color:#8b949e;font-weight:600}";
  p ".gauge{display:inline-block;width:60px;height:60px;border-radius:50%;text-align:center;line-height:60px;font-weight:bold;font-size:18px}";
  p ".excellent{background:#238636;color:#fff} .good{background:#1f6feb;color:#fff}";
  p ".fair{background:#d29922;color:#000} .poor{background:#da3633;color:#fff}";
  p ".critical{background:#8b0000;color:#fff}";
  p ".bar{height:20px;border-radius:4px;margin:2px 0}";
  p ".grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(300px,1fr));gap:16px}";
  p ".tag{display:inline-block;padding:2px 8px;border-radius:4px;font-size:12px;margin:2px}";
  p ".tag-crash{background:#da3633;color:#fff} .tag-info{background:#238636;color:#fff}";
  p ".tag-warn{background:#d29922;color:#000}";
  p "</style></head><body>";
  p "<h1>🔬 Coverage-Guided Fuzzing Engine Dashboard</h1>";

  (* Summary *)
  p "<div class=\"grid\">";
  let total_execs = List.fold_left (fun acc r -> acc + r.res_stats.cs_total_execs) 0 results in
  let total_crashes = List.fold_left (fun acc r -> acc + r.res_stats.cs_unique_crashes) 0 results in
  let total_cov = List.fold_left (fun acc r -> acc + r.res_stats.cs_coverage_count) 0 results in
  p (Printf.sprintf "<div class=\"card\"><h2>📊 Overview</h2><p>Targets: %d | Executions: %d | Edges: %d | Unique Crashes: %d</p></div>"
    (List.length results) total_execs total_cov total_crashes);

  (* Per-target cards *)
  List.iter (fun r ->
    let tier_class = String.lowercase_ascii r.res_health_tier in
    p (Printf.sprintf "<div class=\"card\"><h2>%s</h2>" r.res_target);
    p (Printf.sprintf "<span class=\"gauge %s\">%d</span>" tier_class r.res_health_score);
    p (Printf.sprintf "<p>Execs: %d | Coverage: %d edges | Corpus: %d | Crashes: %d unique</p>"
      r.res_stats.cs_total_execs r.res_stats.cs_coverage_count
      r.res_stats.cs_corpus_size r.res_stats.cs_unique_crashes);

    (* Strategy bar chart *)
    let effective = List.filter (fun (_, h) -> h > 0) r.res_stats.cs_strategy_hits in
    if effective <> [] then begin
      let max_h = List.fold_left (fun acc (_, h) -> max acc h) 1 effective in
      p "<h3 style=\"color:#8b949e\">Mutation Strategies</h3>";
      List.iter (fun (s, h) ->
        let pct = float_of_int h /. float_of_int max_h *. 100.0 in
        p (Printf.sprintf "<div style=\"display:flex;align-items:center;gap:8px\"><span style=\"width:120px;font-size:12px\">%s</span><div class=\"bar\" style=\"width:%.0f%%;background:#58a6ff\"></div><span style=\"font-size:12px\">%d</span></div>"
          (strategy_to_string s) pct h)
      ) (List.sort (fun (_, a) (_, b) -> compare b a) effective)
    end;

    (* Crash table *)
    if r.res_crashes <> [] then begin
      p "<h3 style=\"color:#8b949e\">Crashes</h3><table><tr><th>Type</th><th>Input</th><th>Minimized</th></tr>";
      List.iter (fun cr ->
        let min_str = match cr.cr_minimized_input with
          | Some m -> input_to_string m | None -> "—" in
        p (Printf.sprintf "<tr><td><span class=\"tag tag-crash\">%s</span></td><td><code>%s</code></td><td><code>%s</code></td></tr>"
          (crash_kind_to_string cr.cr_kind) (input_to_string cr.cr_input) min_str)
      ) r.res_crashes;
      p "</table>"
    end;

    (* Coverage chart (simple SVG) *)
    (match r.res_stats.cs_coverage_history with
     | [] | [_] -> ()
     | history ->
       let max_exec = float_of_int (fst (List.nth history (List.length history - 1))) in
       let max_cov = float_of_int (List.fold_left (fun acc (_, c) -> max acc c) 1 history) in
       let w = 400.0 and h = 100.0 in
       p (Printf.sprintf "<h3 style=\"color:#8b949e\">Coverage Growth</h3><svg width=\"%.0f\" height=\"%.0f\" style=\"background:#0d1117;border:1px solid #30363d;border-radius:4px\">" w (h +. 10.0));
       let points = List.map (fun (e, c) ->
         let x = if max_exec > 0.0 then float_of_int e /. max_exec *. w else 0.0 in
         let y = h -. (float_of_int c /. max_cov *. h) in
         Printf.sprintf "%.1f,%.1f" x y
       ) history in
       p (Printf.sprintf "<polyline fill=\"none\" stroke=\"#58a6ff\" stroke-width=\"2\" points=\"%s\"/>"
         (String.concat " " points));
       p "</svg>");

    (* Insights *)
    if r.res_insights <> [] then begin
      p "<h3 style=\"color:#8b949e\">Insights</h3>";
      List.iter (fun ins ->
        let tag_cls = match ins.ins_severity with
          | Critical -> "tag-crash" | Warning -> "tag-warn" | Info -> "tag-info" in
        p (Printf.sprintf "<div><span class=\"tag %s\">%s</span> [%s] %s</div>"
          tag_cls (severity_to_string ins.ins_severity) ins.ins_category ins.ins_message)
      ) r.res_insights
    end;
    p "</div>"
  ) results;

  p "</div></body></html>";
  Buffer.contents buf

(* ══════════ Main Entry Point ══════════ *)

let () =
  let args = Array.to_list Sys.argv in
  let mode = if List.mem "--dashboard" args then "dashboard"
    else if List.mem "--demo" args then "demo"
    else "demo" in

  let max_iters = 500 in

  Printf.printf "🔬 Coverage-Guided Fuzzing Engine — Autonomous Crash Discovery\n";
  Printf.printf "══════════════════════════════════════════════════════════════\n\n";

  Printf.printf "Running %d fuzzing campaigns (%d iterations each)...\n\n"
    (List.length demo_targets) max_iters;

  let results = List.map (fun target ->
    Printf.printf "  Fuzzing %s..." target.ft_name;
    let r = run_campaign target max_iters in
    Printf.printf " done (%d edges, %d crashes)\n"
      r.res_stats.cs_coverage_count r.res_stats.cs_unique_crashes;
    r
  ) demo_targets in

  Printf.printf "\n";
  List.iter print_result results;

  (* Fleet summary *)
  let avg_health = List.fold_left (fun acc r -> acc + r.res_health_score) 0 results
    / (max 1 (List.length results)) in
  Printf.printf "\n═══════════════════════════════════════════════\n";
  Printf.printf "Fleet Health: %d/100\n" avg_health;
  Printf.printf "═══════════════════════════════════════════════\n";

  if mode = "dashboard" then begin
    let html = generate_dashboard results in
    let oc = open_out "fuzzing_engine_dashboard.html" in
    output_string oc html;
    close_out oc;
    Printf.printf "\n📄 Dashboard written to fuzzing_engine_dashboard.html\n"
  end;

  Printf.printf "\n✅ Fuzzing complete. %d targets analyzed.\n" (List.length results)
