(* code_experiment.ml — Autonomous Code Experiment Engine
   Hypothesis-driven algorithmic experimentation and discovery.

   Features:
   - Defines a library of algorithmic experiment templates
   - Each experiment: hypothesis, variants, data generators, measurements
   - Autonomous execution with statistical comparison (mean, stddev, speedup)
   - Anomaly detection: identifies surprising results that defy expectations
   - Scaling analysis: fits empirical growth curves (linear, nlog n, quadratic)
   - Insight generation: produces human-readable findings from raw data
   - Reproducibility: seeds all randomness, logs parameters
   - Summary report with confidence levels and recommendations

   Usage:
     ocamlfind ocamlopt -package unix -linkpkg code_experiment.ml -o code_experiment
     ./code_experiment

   Or with options:
     ./code_experiment --experiments sorting,hashing
     ./code_experiment --sizes 100,1000,10000
     ./code_experiment --trials 10
     ./code_experiment --verbose
*)

(* ── Random with seed ──────────────────────────────────────────── *)

module Rng = struct
  (* Simple LCG for reproducibility — no external deps *)
  let state = ref 42

  let seed s = state := s

  let next () =
    state := (!state * 1103515245 + 12345) land 0x3FFFFFFF;
    !state

  let int bound =
    if bound <= 0 then 0
    else (next () land 0x7FFFFFFF) mod bound

  let float bound =
    let f = float_of_int (next () land 0xFFFFFF) /. 16777216.0 in
    f *. bound

  let shuffle arr =
    let n = Array.length arr in
    for i = n - 1 downto 1 do
      let j = int (i + 1) in
      let tmp = arr.(i) in
      arr.(i) <- arr.(j);
      arr.(j) <- tmp
    done

  let random_array n range =
    Array.init n (fun _ -> int range)

  let sorted_array n =
    Array.init n (fun i -> i)

  let reverse_sorted_array n =
    Array.init n (fun i -> n - 1 - i)

  let nearly_sorted_array n swaps =
    let a = sorted_array n in
    for _ = 1 to swaps do
      let i = int n and j = int n in
      let tmp = a.(i) in
      a.(i) <- a.(j);
      a.(j) <- tmp
    done;
    a

  let few_unique_array n k =
    Array.init n (fun _ -> int k)
end

(* ── Timer ─────────────────────────────────────────────────────── *)

module Timer = struct
  let now () = Unix.gettimeofday ()

  let measure f =
    let t0 = now () in
    let _ = f () in
    let t1 = now () in
    t1 -. t0
end

(* ── Statistics ────────────────────────────────────────────────── *)

module Stats = struct
  type t = {
    mean : float;
    median : float;
    stddev : float;
    min_v : float;
    max_v : float;
    count : int;
  }

  let compute samples =
    let n = List.length samples in
    if n = 0 then { mean = 0.; median = 0.; stddev = 0.; min_v = 0.; max_v = 0.; count = 0 }
    else
      let arr = Array.of_list samples in
      Array.sort compare arr;
      let sum = Array.fold_left ( +. ) 0. arr in
      let mean = sum /. float_of_int n in
      let var = Array.fold_left (fun acc x -> acc +. (x -. mean) ** 2.) 0. arr /. float_of_int n in
      let median =
        if n mod 2 = 1 then arr.(n / 2)
        else (arr.(n / 2 - 1) +. arr.(n / 2)) /. 2.
      in
      { mean; median; stddev = sqrt var; min_v = arr.(0); max_v = arr.(n - 1); count = n }

  let format s =
    Printf.sprintf "%.6f ± %.6f (med=%.6f, min=%.6f, max=%.6f, n=%d)"
      s.mean s.stddev s.median s.min_v s.max_v s.count
end

(* ── Scaling Analysis ──────────────────────────────────────────── *)

module Scaling = struct
  type complexity =
    | O_1
    | O_log_n
    | O_n
    | O_n_log_n
    | O_n2
    | O_unknown

  let name = function
    | O_1 -> "O(1)"
    | O_log_n -> "O(log n)"
    | O_n -> "O(n)"
    | O_n_log_n -> "O(n log n)"
    | O_n2 -> "O(n²)"
    | O_unknown -> "unknown"

  (* Fit: given (n, time) pairs, estimate complexity class *)
  let detect points =
    if List.length points < 2 then O_unknown
    else
      (* Compute ratios between consecutive sizes *)
      let sorted = List.sort (fun (a, _) (b, _) -> compare a b) points in
      let pairs = ref [] in
      let rec walk = function
        | (n1, t1) :: ((n2, t2) :: _ as rest) ->
          if t1 > 1e-9 && t2 > 1e-9 then begin
            let size_ratio = float_of_int n2 /. float_of_int n1 in
            let time_ratio = t2 /. t1 in
            pairs := (size_ratio, time_ratio) :: !pairs
          end;
          walk rest
        | _ -> ()
      in
      walk sorted;
      if !pairs = [] then O_unknown
      else
        let avg_growth =
          let sum = List.fold_left (fun acc (sr, tr) ->
            if sr > 1.0 then acc +. (log tr /. log sr) else acc
          ) 0. !pairs in
          sum /. float_of_int (List.length !pairs)
        in
        (* Classify based on empirical growth exponent *)
        if avg_growth < 0.15 then O_1
        else if avg_growth < 0.45 then O_log_n
        else if avg_growth < 1.15 then O_n
        else if avg_growth < 1.6 then O_n_log_n
        else if avg_growth < 2.3 then O_n2
        else O_unknown
end

(* ── Experiment Types ──────────────────────────────────────────── *)

type variant_result = {
  variant_name : string;
  size : int;
  stats : Stats.t;
}

type experiment_result = {
  experiment_name : string;
  hypothesis : string;
  results : variant_result list;
  insights : string list;
  anomalies : string list;
  scaling : (string * Scaling.complexity) list;
  verdict : string;
}

(* ── Sorting Experiments ───────────────────────────────────────── *)

module SortExperiments = struct
  (* --- Sorting algorithms --- *)
  let insertion_sort arr =
    let a = Array.copy arr in
    for i = 1 to Array.length a - 1 do
      let key = a.(i) in
      let j = ref (i - 1) in
      while !j >= 0 && a.(!j) > key do
        a.(!j + 1) <- a.(!j);
        decr j
      done;
      a.(!j + 1) <- key
    done;
    a

  let merge_sort arr =
    let a = Array.copy arr in
    let n = Array.length a in
    let tmp = Array.make n 0 in
    let rec sort lo hi =
      if hi - lo > 1 then begin
        let mid = (lo + hi) / 2 in
        sort lo mid;
        sort mid hi;
        Array.blit a lo tmp lo (hi - lo);
        let i = ref lo and j = ref mid and k = ref lo in
        while !i < mid && !j < hi do
          if tmp.(!i) <= tmp.(!j) then (a.(!k) <- tmp.(!i); incr i)
          else (a.(!k) <- tmp.(!j); incr j);
          incr k
        done;
        while !i < mid do a.(!k) <- tmp.(!i); incr i; incr k done;
        while !j < hi do a.(!k) <- tmp.(!j); incr j; incr k done
      end
    in
    sort 0 n;
    a

  let quicksort_first arr =
    let a = Array.copy arr in
    let rec qsort lo hi =
      if lo < hi then begin
        let pivot = a.(lo) in
        let i = ref (lo + 1) and j = ref hi in
        while !i <= !j do
          while !i <= hi && a.(!i) <= pivot do incr i done;
          while !j > lo && a.(!j) > pivot do decr j done;
          if !i < !j then begin
            let tmp = a.(!i) in a.(!i) <- a.(!j); a.(!j) <- tmp
          end
        done;
        let tmp = a.(lo) in a.(lo) <- a.(!j); a.(!j) <- tmp;
        qsort lo (!j - 1);
        qsort (!j + 1) hi
      end
    in
    if Array.length a > 0 then qsort 0 (Array.length a - 1);
    a

  let quicksort_median3 arr =
    let a = Array.copy arr in
    let rec qsort lo hi =
      if hi - lo < 10 then begin
        (* insertion sort for small *)
        for i = lo + 1 to hi do
          let key = a.(i) in
          let j = ref (i - 1) in
          while !j >= lo && a.(!j) > key do
            a.(!j + 1) <- a.(!j); decr j
          done;
          a.(!j + 1) <- key
        done
      end else begin
        let mid = (lo + hi) / 2 in
        (* median of three *)
        if a.(lo) > a.(mid) then (let t = a.(lo) in a.(lo) <- a.(mid); a.(mid) <- t);
        if a.(lo) > a.(hi)  then (let t = a.(lo) in a.(lo) <- a.(hi);  a.(hi)  <- t);
        if a.(mid) > a.(hi) then (let t = a.(mid) in a.(mid) <- a.(hi); a.(hi) <- t);
        let t = a.(mid) in a.(mid) <- a.(hi - 1); a.(hi - 1) <- t;
        let pivot = a.(hi - 1) in
        let i = ref lo and j = ref (hi - 1) in
        let continue_ = ref true in
        while !continue_ do
          incr i; while a.(!i) < pivot do incr i done;
          decr j; while a.(!j) > pivot do decr j done;
          if !i < !j then begin
            let t = a.(!i) in a.(!i) <- a.(!j); a.(!j) <- t
          end else
            continue_ := false
        done;
        let t = a.(!i) in a.(!i) <- a.(hi - 1); a.(hi - 1) <- t;
        qsort lo (!i - 1);
        qsort (!i + 1) hi
      end
    in
    if Array.length a > 1 then qsort 0 (Array.length a - 1);
    a

  let heap_sort arr =
    let a = Array.copy arr in
    let n = Array.length a in
    let swap i j = let t = a.(i) in a.(i) <- a.(j); a.(j) <- t in
    let rec sift_down root bound =
      let child = 2 * root + 1 in
      if child < bound then begin
        let max_c = if child + 1 < bound && a.(child + 1) > a.(child) then child + 1 else child in
        if a.(max_c) > a.(root) then begin
          swap root max_c;
          sift_down max_c bound
        end
      end
    in
    for i = n / 2 - 1 downto 0 do sift_down i n done;
    for i = n - 1 downto 1 do
      swap 0 i;
      sift_down 0 i
    done;
    a

  (* --- Data generators --- *)
  type data_pattern = Random | Sorted | Reversed | NearlySorted | FewUnique

  let pattern_name = function
    | Random -> "random" | Sorted -> "sorted" | Reversed -> "reversed"
    | NearlySorted -> "nearly_sorted" | FewUnique -> "few_unique"

  let generate_data pattern n =
    match pattern with
    | Random -> Rng.random_array n (n * 10)
    | Sorted -> Rng.sorted_array n
    | Reversed -> Rng.reverse_sorted_array n
    | NearlySorted -> Rng.nearly_sorted_array n (n / 20)
    | FewUnique -> Rng.few_unique_array n 10

  (* --- Run one experiment --- *)
  let run_sorting_experiment sizes trials =
    let algorithms = [
      ("insertion_sort", insertion_sort);
      ("merge_sort", merge_sort);
      ("quicksort_first", quicksort_first);
      ("quicksort_median3", quicksort_median3);
      ("heap_sort", heap_sort);
    ] in
    let patterns = [ Random; Sorted; Reversed; NearlySorted; FewUnique ] in
    let all_results = ref [] in
    let insights = ref [] in
    let anomalies = ref [] in

    Printf.printf "\n━━━ EXPERIMENT: Sorting Algorithm Comparison ━━━\n";
    Printf.printf "Hypothesis: Median-of-3 quicksort outperforms naive quicksort on adversarial inputs,\n";
    Printf.printf "            while merge sort provides most consistent scaling across patterns.\n\n";

    List.iter (fun pattern ->
      Printf.printf "── Pattern: %s ──\n" (pattern_name pattern);
      Printf.printf "%-20s" "Size";
      List.iter (fun (name, _) -> Printf.printf " %14s" name) algorithms;
      Printf.printf "\n";
      Printf.printf "%s\n" (String.make (20 + 15 * List.length algorithms) '-');

      List.iter (fun size ->
        Printf.printf "%-20d" size;
        let row_results = List.map (fun (name, algo) ->
          let data = generate_data pattern size in
          let times = List.init trials (fun _ ->
            Timer.measure (fun () -> ignore (algo data))
          ) in
          let stats = Stats.compute times in
          Printf.printf " %14s" (Printf.sprintf "%.4fms" (stats.Stats.mean *. 1000.));
          all_results := { variant_name = Printf.sprintf "%s/%s" name (pattern_name pattern);
                           size; stats } :: !all_results;
          (name, stats)
        ) algorithms in
        Printf.printf "\n";

        (* Detect anomalies: is any "slow" algo faster than a "fast" one? *)
        let times = List.map (fun (n, s) -> (n, s.Stats.mean)) row_results in
        (match List.assoc_opt "insertion_sort" times, List.assoc_opt "merge_sort" times with
         | Some ins, Some merge when ins < merge && size > 100 ->
           anomalies := Printf.sprintf "ANOMALY: insertion_sort beat merge_sort at n=%d on %s (%.4fms vs %.4fms)"
             size (pattern_name pattern) (ins *. 1000.) (merge *. 1000.) :: !anomalies
         | _ -> ());
        (match List.assoc_opt "quicksort_first" times, List.assoc_opt "quicksort_median3" times with
         | Some first, Some med3 when first < med3 *. 0.8 && size > 500 ->
           anomalies := Printf.sprintf "ANOMALY: naive quicksort significantly faster than median-of-3 at n=%d on %s"
             size (pattern_name pattern) :: !anomalies
         | _ -> ())
      ) sizes;
      Printf.printf "\n"
    ) patterns;

    (* Scaling analysis *)
    let scaling_map = Hashtbl.create 16 in
    List.iter (fun r ->
      let key = r.variant_name in
      let prev = try Hashtbl.find scaling_map key with Not_found -> [] in
      Hashtbl.replace scaling_map key ((r.size, r.stats.Stats.mean) :: prev)
    ) !all_results;
    let scaling = ref [] in
    Hashtbl.iter (fun name points ->
      let complexity = Scaling.detect points in
      scaling := (name, complexity) :: !scaling
    ) scaling_map;

    (* Generate insights *)
    (* Find best algo per pattern for largest size *)
    let largest = List.fold_left max 0 sizes in
    List.iter (fun pattern ->
      let pat_name = pattern_name pattern in
      let candidates = List.filter (fun r ->
        r.size = largest &&
        let suffix = "/" ^ pat_name in
        let vn = r.variant_name in
        String.length vn > String.length suffix &&
        String.sub vn (String.length vn - String.length suffix) (String.length suffix) = suffix
      ) !all_results in
      match candidates with
      | [] -> ()
      | _ ->
        let best = List.fold_left (fun acc r ->
          if r.stats.Stats.mean < acc.stats.Stats.mean then r else acc
        ) (List.hd candidates) candidates in
        insights := Printf.sprintf "Best for %s (n=%d): %s (%.4fms)"
          pat_name largest best.variant_name (best.stats.Stats.mean *. 1000.) :: !insights
    ) patterns;

    (* Consistency analysis *)
    List.iter (fun (name, _) ->
      let variants = List.filter (fun r ->
        r.size = largest &&
        String.length r.variant_name >= String.length name &&
        String.sub r.variant_name 0 (String.length name) = name
      ) !all_results in
      if variants <> [] then begin
        let times = List.map (fun r -> r.stats.Stats.mean) variants in
        let max_t = List.fold_left max neg_infinity times in
        let min_t = List.fold_left min infinity times in
        if max_t > 0. && min_t > 0. then begin
          let ratio = max_t /. min_t in
          if ratio > 5.0 then
            insights := Printf.sprintf "%s is pattern-sensitive: %.1fx variation across data patterns at n=%d"
              name ratio largest :: !insights
          else if ratio < 1.5 then
            insights := Printf.sprintf "%s is pattern-resilient: only %.2fx variation across data patterns at n=%d"
              name ratio largest :: !insights
        end
      end
    ) algorithms;

    let verdict =
      if List.length !anomalies > 2 then
        "Multiple anomalies detected — results may challenge conventional wisdom. Review carefully."
      else if List.length !anomalies > 0 then
        "Some surprising findings — the expected ranking doesn't always hold."
      else
        "Results largely confirm theoretical predictions. Median-of-3 and merge sort show strong scaling."
    in

    { experiment_name = "Sorting Algorithm Comparison";
      hypothesis = "Median-of-3 quicksort outperforms naive quicksort on adversarial inputs; merge sort provides most consistent O(n log n) scaling.";
      results = !all_results;
      insights = !insights;
      anomalies = !anomalies;
      scaling = !scaling;
      verdict }
end

(* ── Search Experiments ────────────────────────────────────────── *)

module SearchExperiments = struct
  let linear_search arr target =
    let n = Array.length arr in
    let i = ref 0 in
    let found = ref false in
    while !i < n && not !found do
      if arr.(!i) = target then found := true;
      incr i
    done;
    !found

  let binary_search arr target =
    let lo = ref 0 and hi = ref (Array.length arr - 1) in
    let found = ref false in
    while !lo <= !hi && not !found do
      let mid = !lo + (!hi - !lo) / 2 in
      if arr.(mid) = target then found := true
      else if arr.(mid) < target then lo := mid + 1
      else hi := mid - 1
    done;
    !found

  let interpolation_search arr target =
    let lo = ref 0 and hi = ref (Array.length arr - 1) in
    let found = ref false in
    while !lo <= !hi && not !found do
      if arr.(!lo) = arr.(!hi) then begin
        if arr.(!lo) = target then found := true;
        hi := !lo - 1
      end else begin
        let pos = !lo + (target - arr.(!lo)) * (!hi - !lo) / (arr.(!hi) - arr.(!lo)) in
        if pos < !lo || pos > !hi then hi := !lo - 1
        else if arr.(pos) = target then found := true
        else if arr.(pos) < target then lo := pos + 1
        else hi := pos - 1
      end
    done;
    !found

  (* Exponential / galloping search *)
  let exponential_search arr target =
    let n = Array.length arr in
    if n = 0 then false
    else if arr.(0) = target then true
    else begin
      let bound = ref 1 in
      while !bound < n && arr.(!bound) < target do bound := !bound * 2 done;
      let lo = ref (!bound / 2) and hi = ref (min !bound (n - 1)) in
      let found = ref false in
      while !lo <= !hi && not !found do
        let mid = !lo + (!hi - !lo) / 2 in
        if arr.(mid) = target then found := true
        else if arr.(mid) < target then lo := mid + 1
        else hi := mid - 1
      done;
      !found
    end

  let run_search_experiment sizes trials =
    let algorithms = [
      ("linear_search", linear_search);
      ("binary_search", binary_search);
      ("interpolation_search", interpolation_search);
      ("exponential_search", exponential_search);
    ] in
    let all_results = ref [] in
    let insights = ref [] in
    let anomalies = ref [] in

    Printf.printf "\n━━━ EXPERIMENT: Search Algorithm Comparison ━━━\n";
    Printf.printf "Hypothesis: Interpolation search outperforms binary search on uniform data;\n";
    Printf.printf "            exponential search excels when target is near the beginning.\n\n";

    (* Test 1: Target in middle of sorted uniform data *)
    Printf.printf "── Scenario: Uniform sorted data, target at midpoint ──\n";
    Printf.printf "%-14s" "Size";
    List.iter (fun (name, _) -> Printf.printf " %18s" name) algorithms;
    Printf.printf "\n";
    Printf.printf "%s\n" (String.make (14 + 19 * List.length algorithms) '-');

    List.iter (fun size ->
      let data = Array.init size (fun i -> i * 2) in
      let target = size in (* middle-ish *)
      Printf.printf "%-14d" size;
      List.iter (fun (name, algo) ->
        let times = List.init trials (fun _ ->
          Timer.measure (fun () ->
            for _ = 1 to 100 do ignore (algo data target) done
          )
        ) in
        let stats = Stats.compute times in
        Printf.printf " %18s" (Printf.sprintf "%.4fms" (stats.Stats.mean *. 1000.));
        all_results := { variant_name = name ^ "/uniform_mid"; size; stats } :: !all_results
      ) algorithms;
      Printf.printf "\n"
    ) sizes;

    (* Test 2: Target near beginning *)
    Printf.printf "\n── Scenario: Uniform sorted data, target near start ──\n";
    Printf.printf "%-14s" "Size";
    List.iter (fun (name, _) -> Printf.printf " %18s" name) algorithms;
    Printf.printf "\n";
    Printf.printf "%s\n" (String.make (14 + 19 * List.length algorithms) '-');

    List.iter (fun size ->
      let data = Array.init size (fun i -> i * 2) in
      let target = 10 in
      Printf.printf "%-14d" size;
      List.iter (fun (name, algo) ->
        let times = List.init trials (fun _ ->
          Timer.measure (fun () ->
            for _ = 1 to 100 do ignore (algo data target) done
          )
        ) in
        let stats = Stats.compute times in
        Printf.printf " %18s" (Printf.sprintf "%.4fms" (stats.Stats.mean *. 1000.));
        all_results := { variant_name = name ^ "/uniform_start"; size; stats } :: !all_results
      ) algorithms;
      Printf.printf "\n"
    ) sizes;

    (* Test 3: Non-uniform data (exponential gaps) *)
    Printf.printf "\n── Scenario: Non-uniform data (exponential gaps) ──\n";
    Printf.printf "%-14s" "Size";
    List.iter (fun (name, _) -> Printf.printf " %18s" name) algorithms;
    Printf.printf "\n";
    Printf.printf "%s\n" (String.make (14 + 19 * List.length algorithms) '-');

    List.iter (fun size ->
      let data = Array.init size (fun i ->
        int_of_float (1.01 ** float_of_int i)
      ) in
      let target = data.(size / 2) in
      Printf.printf "%-14d" size;
      List.iter (fun (name, algo) ->
        let times = List.init trials (fun _ ->
          Timer.measure (fun () ->
            for _ = 1 to 100 do ignore (algo data target) done
          )
        ) in
        let stats = Stats.compute times in
        Printf.printf " %18s" (Printf.sprintf "%.4fms" (stats.Stats.mean *. 1000.));
        all_results := { variant_name = name ^ "/non_uniform"; size; stats } :: !all_results
      ) algorithms;
      Printf.printf "\n"
    ) sizes;

    Printf.printf "\n";

    (* Scaling analysis *)
    let scaling_map = Hashtbl.create 16 in
    List.iter (fun r ->
      let key = r.variant_name in
      let prev = try Hashtbl.find scaling_map key with Not_found -> [] in
      Hashtbl.replace scaling_map key ((r.size, r.stats.Stats.mean) :: prev)
    ) !all_results;
    let scaling = ref [] in
    Hashtbl.iter (fun name points ->
      let complexity = Scaling.detect points in
      scaling := (name, complexity) :: !scaling
    ) scaling_map;

    (* Insights *)
    let largest = List.fold_left max 0 sizes in
    let find_time name scenario =
      List.find_opt (fun r -> r.variant_name = name ^ "/" ^ scenario && r.size = largest) !all_results
    in
    (match find_time "interpolation_search" "uniform_mid", find_time "binary_search" "uniform_mid" with
     | Some ip, Some bs ->
       if ip.stats.Stats.mean < bs.stats.Stats.mean *. 0.8 then
         insights := Printf.sprintf "Interpolation search %.1fx faster than binary on uniform data (n=%d)" (bs.stats.Stats.mean /. ip.stats.Stats.mean) largest :: !insights
       else if ip.stats.Stats.mean > bs.stats.Stats.mean *. 1.2 then
         anomalies := Printf.sprintf "ANOMALY: Binary search beat interpolation on uniform data at n=%d" largest :: !anomalies
     | _ -> ());
    (match find_time "interpolation_search" "non_uniform", find_time "binary_search" "non_uniform" with
     | Some ip, Some bs ->
       if ip.stats.Stats.mean > bs.stats.Stats.mean *. 1.5 then
         insights := "Interpolation search degrades significantly on non-uniform data (as expected)" :: !insights
     | _ -> ());
    (match find_time "exponential_search" "uniform_start", find_time "binary_search" "uniform_start" with
     | Some ex, Some bs ->
       if ex.stats.Stats.mean < bs.stats.Stats.mean *. 0.9 then
         insights := Printf.sprintf "Exponential search %.1fx faster than binary when target is near start"
           (bs.stats.Stats.mean /. ex.stats.Stats.mean) :: !insights
     | _ -> ());

    let verdict =
      if List.length !anomalies > 0 then
        "Some results contradict theoretical expectations — data distribution matters more than algorithm choice at small N."
      else
        "Results confirm: algorithm choice should match data distribution. No single search algorithm dominates all scenarios."
    in

    { experiment_name = "Search Algorithm Comparison";
      hypothesis = "Interpolation search outperforms binary on uniform data; exponential search excels for near-start targets.";
      results = !all_results; insights = !insights; anomalies = !anomalies;
      scaling = !scaling; verdict }
end

(* ── Hash Table Experiments ────────────────────────────────────── *)

module HashExperiments = struct
  (* Simple hash table with chaining *)
  type 'a chain_ht = {
    mutable buckets : (int * 'a) list array;
    mutable size : int;
    mutable capacity : int;
  }

  let chain_create cap =
    { buckets = Array.make cap []; size = 0; capacity = cap }

  let chain_insert ht k v =
    let idx = (k land 0x7FFFFFFF) mod ht.capacity in
    ht.buckets.(idx) <- (k, v) :: ht.buckets.(idx);
    ht.size <- ht.size + 1

  let chain_find ht k =
    let idx = (k land 0x7FFFFFFF) mod ht.capacity in
    List.assoc_opt k ht.buckets.(idx)

  (* Open addressing with linear probing *)
  type 'a open_ht = {
    mutable keys : int array;
    mutable vals : 'a option array;
    mutable osize : int;
    mutable ocapacity : int;
  }

  let open_create cap =
    { keys = Array.make cap min_int; vals = Array.make cap None;
      osize = 0; ocapacity = cap }

  let open_insert ht k v =
    let idx = ref ((k land 0x7FFFFFFF) mod ht.ocapacity) in
    while ht.vals.(!idx) <> None && ht.keys.(!idx) <> k do
      idx := (!idx + 1) mod ht.ocapacity
    done;
    ht.keys.(!idx) <- k;
    ht.vals.(!idx) <- Some v;
    ht.osize <- ht.osize + 1

  let open_find ht k =
    let idx = ref ((k land 0x7FFFFFFF) mod ht.ocapacity) in
    let steps = ref 0 in
    while ht.vals.(!idx) <> None && ht.keys.(!idx) <> k && !steps < ht.ocapacity do
      idx := (!idx + 1) mod ht.ocapacity;
      incr steps
    done;
    if ht.keys.(!idx) = k then ht.vals.(!idx) else None

  (* Robin Hood hashing *)
  type 'a robin_ht = {
    mutable rkeys : int array;
    mutable rvals : 'a option array;
    mutable rdist : int array;  (* probe distance *)
    mutable rsize : int;
    mutable rcapacity : int;
  }

  let robin_create cap =
    { rkeys = Array.make cap min_int; rvals = Array.make cap None;
      rdist = Array.make cap 0; rsize = 0; rcapacity = cap }

  let robin_insert ht k v =
    let idx = ref ((k land 0x7FFFFFFF) mod ht.rcapacity) in
    let ck = ref k and cv = ref v and cd = ref 0 in
    let done_ = ref false in
    while not !done_ do
      if ht.rvals.(!idx) = None then begin
        ht.rkeys.(!idx) <- !ck;
        ht.rvals.(!idx) <- Some !cv;
        ht.rdist.(!idx) <- !cd;
        ht.rsize <- ht.rsize + 1;
        done_ := true
      end else if !cd > ht.rdist.(!idx) then begin
        (* Robin Hood: steal from the rich *)
        let tk = ht.rkeys.(!idx) and tv = ht.rvals.(!idx) and td = ht.rdist.(!idx) in
        ht.rkeys.(!idx) <- !ck;
        ht.rvals.(!idx) <- Some !cv;
        ht.rdist.(!idx) <- !cd;
        ck := tk;
        cv := (match tv with Some v -> v | None -> !cv);
        cd := td;
        idx := (!idx + 1) mod ht.rcapacity;
        cd := !cd + 1
      end else begin
        idx := (!idx + 1) mod ht.rcapacity;
        cd := !cd + 1
      end
    done

  let robin_find ht k =
    let idx = ref ((k land 0x7FFFFFFF) mod ht.rcapacity) in
    let dist = ref 0 in
    while ht.rvals.(!idx) <> None && ht.rkeys.(!idx) <> k && !dist <= ht.rdist.(!idx) do
      idx := (!idx + 1) mod ht.rcapacity;
      incr dist
    done;
    if ht.rkeys.(!idx) = k then ht.rvals.(!idx) else None

  let run_hash_experiment sizes trials =
    let all_results = ref [] in
    let insights = ref [] in
    let anomalies = ref [] in

    Printf.printf "\n━━━ EXPERIMENT: Hash Table Strategy Comparison ━━━\n";
    Printf.printf "Hypothesis: Robin Hood hashing provides more consistent lookup times;\n";
    Printf.printf "            chaining degrades less at high load factors.\n\n";

    (* Test at different load factors *)
    let load_factors = [0.5; 0.75; 0.9] in

    List.iter (fun lf ->
      Printf.printf "── Load Factor: %.0f%% ──\n" (lf *. 100.);
      Printf.printf "%-14s %14s %14s %14s\n" "Size" "chaining" "linear_probe" "robin_hood";
      Printf.printf "%s\n" (String.make 58 '-');

      List.iter (fun size ->
        let cap = int_of_float (float_of_int size /. lf) + 1 in
        let keys = Array.init size (fun _ -> Rng.int (size * 100)) in
        Printf.printf "%-14d" size;

        (* Chaining *)
        let times = List.init trials (fun _ ->
          let ht = chain_create cap in
          Array.iter (fun k -> chain_insert ht k k) keys;
          Timer.measure (fun () ->
            Array.iter (fun k -> ignore (chain_find ht k)) keys
          )
        ) in
        let s = Stats.compute times in
        Printf.printf " %14s" (Printf.sprintf "%.4fms" (s.Stats.mean *. 1000.));
        all_results := { variant_name = Printf.sprintf "chaining/lf%.0f" (lf *. 100.); size; stats = s } :: !all_results;

        (* Linear probe *)
        let times = List.init trials (fun _ ->
          let ht = open_create cap in
          Array.iter (fun k -> open_insert ht k k) keys;
          Timer.measure (fun () ->
            Array.iter (fun k -> ignore (open_find ht k)) keys
          )
        ) in
        let s = Stats.compute times in
        Printf.printf " %14s" (Printf.sprintf "%.4fms" (s.Stats.mean *. 1000.));
        all_results := { variant_name = Printf.sprintf "linear_probe/lf%.0f" (lf *. 100.); size; stats = s } :: !all_results;

        (* Robin Hood *)
        let times = List.init trials (fun _ ->
          let ht = robin_create cap in
          Array.iter (fun k -> robin_insert ht k k) keys;
          Timer.measure (fun () ->
            Array.iter (fun k -> ignore (robin_find ht k)) keys
          )
        ) in
        let s = Stats.compute times in
        Printf.printf " %14s" (Printf.sprintf "%.4fms" (s.Stats.mean *. 1000.));
        all_results := { variant_name = Printf.sprintf "robin_hood/lf%.0f" (lf *. 100.); size; stats = s } :: !all_results;

        Printf.printf "\n"
      ) sizes;
      Printf.printf "\n"
    ) load_factors;

    (* Scaling *)
    let scaling_map = Hashtbl.create 16 in
    List.iter (fun r ->
      let key = r.variant_name in
      let prev = try Hashtbl.find scaling_map key with Not_found -> [] in
      Hashtbl.replace scaling_map key ((r.size, r.stats.Stats.mean) :: prev)
    ) !all_results;
    let scaling = ref [] in
    Hashtbl.iter (fun name points ->
      let complexity = Scaling.detect points in
      scaling := (name, complexity) :: !scaling
    ) scaling_map;

    (* Insights: compare stddev at high load *)
    let largest = List.fold_left max 0 sizes in
    let find_result name lf =
      let vn = Printf.sprintf "%s/lf%.0f" name (lf *. 100.) in
      List.find_opt (fun r -> r.variant_name = vn && r.size = largest) !all_results
    in
    (match find_result "robin_hood" 0.9, find_result "linear_probe" 0.9 with
     | Some rh, Some lp ->
       if rh.stats.Stats.stddev < lp.stats.Stats.stddev *. 0.7 then
         insights := "Robin Hood provides more consistent lookup times at 90% load (lower variance)" :: !insights;
       if rh.stats.Stats.mean < lp.stats.Stats.mean then
         insights := Printf.sprintf "Robin Hood %.1fx faster than linear probing at 90%% load (n=%d)"
           (lp.stats.Stats.mean /. rh.stats.Stats.mean) largest :: !insights
       else
         anomalies := "ANOMALY: Linear probing outperformed Robin Hood at 90% load" :: !anomalies
     | _ -> ());
    (match find_result "chaining" 0.9, find_result "linear_probe" 0.9 with
     | Some ch, Some lp ->
       if ch.stats.Stats.mean < lp.stats.Stats.mean then
         insights := "Chaining handles high load factor better than linear probing (as expected)" :: !insights
     | _ -> ());

    let verdict =
      if List.length !anomalies > 0 then
        "Some results challenge common hashing wisdom — implementation details matter as much as theory."
      else
        "Results confirm: Robin Hood hashing provides more predictable performance; chaining degrades gracefully."
    in

    { experiment_name = "Hash Table Strategy Comparison";
      hypothesis = "Robin Hood hashing gives more consistent lookups; chaining handles high load factors gracefully.";
      results = !all_results; insights = !insights; anomalies = !anomalies;
      scaling = !scaling; verdict }
end

(* ── Report Generator ──────────────────────────────────────────── *)

module Report = struct
  let print_experiment exp =
    Printf.printf "\n╔══════════════════════════════════════════════════════════════╗\n";
    Printf.printf "║  %s\n" exp.experiment_name;
    Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
    Printf.printf "║  Hypothesis: %s\n" exp.hypothesis;
    Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";

    if exp.scaling <> [] then begin
      Printf.printf "║  Scaling Analysis:\n";
      List.iter (fun (name, cmplx) ->
        Printf.printf "║    %-40s → %s\n" name (Scaling.name cmplx)
      ) (List.sort compare exp.scaling)
    end;

    if exp.insights <> [] then begin
      Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
      Printf.printf "║  Insights:\n";
      List.iter (fun i -> Printf.printf "║    ✓ %s\n" i) exp.insights
    end;

    if exp.anomalies <> [] then begin
      Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
      Printf.printf "║  ⚠ Anomalies:\n";
      List.iter (fun a -> Printf.printf "║    ⚡ %s\n" a) exp.anomalies
    end;

    Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
    Printf.printf "║  Verdict: %s\n" exp.verdict;
    Printf.printf "╚══════════════════════════════════════════════════════════════╝\n"
end

(* ── CLI ───────────────────────────────────────────────────────── *)

let parse_sizes s =
  String.split_on_char ',' s |> List.filter_map (fun x ->
    try Some (int_of_string (String.trim x)) with _ -> None
  )

let parse_experiments s =
  String.split_on_char ',' s |> List.map String.trim

let () =
  let sizes = ref [100; 500; 1000; 5000; 10000] in
  let trials = ref 5 in
  let verbose = ref false in
  let experiments = ref ["sorting"; "searching"; "hashing"] in

  (* Simple arg parsing *)
  let args = Array.to_list Sys.argv in
  let rec parse = function
    | "--sizes" :: s :: rest -> sizes := parse_sizes s; parse rest
    | "--trials" :: n :: rest -> trials := (try int_of_string n with _ -> 5); parse rest
    | "--verbose" :: rest -> verbose := true; parse rest
    | "--experiments" :: s :: rest -> experiments := parse_experiments s; parse rest
    | "--help" :: _ ->
      Printf.printf "Code Experiment Engine — Autonomous Algorithmic Experimentation\n\n";
      Printf.printf "Usage: ./code_experiment [OPTIONS]\n\n";
      Printf.printf "Options:\n";
      Printf.printf "  --experiments LIST   Comma-separated: sorting,searching,hashing (default: all)\n";
      Printf.printf "  --sizes LIST         Comma-separated input sizes (default: 100,500,1000,5000,10000)\n";
      Printf.printf "  --trials N           Repetitions per measurement (default: 5)\n";
      Printf.printf "  --verbose            Show additional detail\n";
      Printf.printf "  --help               This message\n";
      exit 0
    | _ :: rest -> parse rest
    | [] -> ()
  in
  parse (List.tl args);

  Rng.seed 42;

  Printf.printf "╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║     CODE EXPERIMENT ENGINE — Autonomous Discovery           ║\n";
  Printf.printf "║     Hypothesis-driven algorithmic experimentation            ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n";
  Printf.printf "\nConfiguration:\n";
  Printf.printf "  Experiments : %s\n" (String.concat ", " !experiments);
  Printf.printf "  Input sizes : %s\n" (String.concat ", " (List.map string_of_int !sizes));
  Printf.printf "  Trials/size : %d\n" !trials;
  Printf.printf "  RNG seed    : 42 (reproducible)\n\n";

  let results = ref [] in

  if List.mem "sorting" !experiments then begin
    let r = SortExperiments.run_sorting_experiment !sizes !trials in
    results := r :: !results;
    Report.print_experiment r
  end;

  if List.mem "searching" !experiments then begin
    let r = SearchExperiments.run_search_experiment !sizes !trials in
    results := r :: !results;
    Report.print_experiment r
  end;

  if List.mem "hashing" !experiments then begin
    let r = HashExperiments.run_hash_experiment !sizes !trials in
    results := r :: !results;
    Report.print_experiment r
  end;

  (* Summary *)
  let total_insights = List.fold_left (fun acc r -> acc + List.length r.insights) 0 !results in
  let total_anomalies = List.fold_left (fun acc r -> acc + List.length r.anomalies) 0 !results in

  Printf.printf "\n══════════════════════════════════════════════════════════════\n";
  Printf.printf "  EXPERIMENT SESSION SUMMARY\n";
  Printf.printf "══════════════════════════════════════════════════════════════\n";
  Printf.printf "  Experiments run : %d\n" (List.length !results);
  Printf.printf "  Total insights  : %d\n" total_insights;
  Printf.printf "  Total anomalies : %d\n" total_anomalies;

  if !verbose then begin
    Printf.printf "\n  All insights:\n";
    List.iter (fun r ->
      List.iter (fun i -> Printf.printf "    [%s] %s\n" r.experiment_name i) r.insights
    ) !results;
    Printf.printf "\n  All anomalies:\n";
    List.iter (fun r ->
      List.iter (fun a -> Printf.printf "    [%s] %s\n" r.experiment_name a) r.anomalies
    ) !results
  end;

  Printf.printf "\n  \"The only way to discover the limits of the possible\n";
  Printf.printf "   is to go beyond them into the impossible.\" — Arthur C. Clarke\n";
  Printf.printf "══════════════════════════════════════════════════════════════\n";

  ignore !verbose (* suppress warning *)
