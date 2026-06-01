(* anomaly_detector.ml — Streaming anomaly detection via EWMA + adaptive thresholds.
 *
 * A lightweight agentic building block for OCaml systems that need to
 * detect unusual values in real-time data streams without requiring batch
 * processing or heavy statistical libraries.
 *
 * Algorithms implemented:
 *   1. EWMA (Exponentially Weighted Moving Average) detector
 *      - Tracks a smoothed mean and variance with configurable decay (alpha)
 *      - Flags values deviating beyond k standard deviations
 *      - Adapts thresholds as the stream evolves
 *
 *   2. Sliding-window Z-score detector
 *      - Maintains a fixed window of recent values
 *      - Computes exact mean/stddev over the window
 *      - Flags outliers beyond z_threshold
 *
 *   3. IQR (Interquartile Range) detector
 *      - Maintains sorted window for percentile computation
 *      - Flags values outside Q1 - k*IQR .. Q3 + k*IQR
 *
 * All three are pure, dependency-free OCaml (stdlib only).
 *
 * API:
 *   EWMA:
 *     create_ewma ?alpha ?k ()       -> ewma_state
 *     update_ewma state value        -> ewma_state * anomaly option
 *     is_anomaly_ewma state value    -> bool
 *     ewma_mean state                -> float
 *     ewma_stddev state              -> float
 *
 *   Sliding window:
 *     create_window ?size ?z_threshold ()  -> window_state
 *     update_window state value            -> window_state * anomaly option
 *
 *   IQR:
 *     create_iqr ?size ?k ()   -> iqr_state
 *     update_iqr state value   -> iqr_state * anomaly option
 *
 *   Shared:
 *     anomaly record: { value; expected; deviation; score; timestamp }
 *)

(* ── Types ─────────────────────────────────────────────────────────── *)

type anomaly = {
  value     : float;
  expected  : float;
  deviation : float;   (* how many stddevs away *)
  score     : float;   (* 0-1 normalized severity *)
  timestamp : int;     (* observation index *)
}

(* ── EWMA Detector ─────────────────────────────────────────────────── *)

type ewma_state = {
  alpha    : float;   (* smoothing factor, 0 < alpha <= 1 *)
  k        : float;   (* threshold in stddevs *)
  mean     : float;
  variance : float;
  count    : int;
  initialized : bool;
}

let create_ewma ?(alpha=0.3) ?(k=3.0) () =
  { alpha; k; mean = 0.0; variance = 0.0; count = 0; initialized = false }

let ewma_mean st = st.mean
let ewma_stddev st = sqrt st.variance

let update_ewma st value =
  if not st.initialized then
    let st' = { st with mean = value; variance = 0.0; count = 1; initialized = true } in
    (st', None)
  else
    let diff = value -. st.mean in
    let new_mean = st.mean +. st.alpha *. diff in
    let new_var = (1.0 -. st.alpha) *. (st.variance +. st.alpha *. diff *. diff) in
    let stddev = sqrt new_var in
    let st' = { st with mean = new_mean; variance = new_var; count = st.count + 1 } in
    if st.count >= 3 && stddev > 0.0 then
      let deviation = abs_float diff /. stddev in
      if deviation > st.k then
        let score = Float.min 1.0 ((deviation -. st.k) /. st.k) in
        let anom = { value; expected = st.mean; deviation; score; timestamp = st'.count } in
        (st', Some anom)
      else
        (st', None)
    else
      (st', None)

let is_anomaly_ewma st value =
  if not st.initialized || st.count < 3 then false
  else
    let stddev = sqrt st.variance in
    if stddev <= 0.0 then false
    else abs_float (value -. st.mean) /. stddev > st.k

(* ── Sliding Window Z-Score Detector ──────────────────────────────── *)

type window_state = {
  buffer      : float array;
  w_size      : int;
  z_threshold : float;
  pos         : int;
  filled      : bool;
  w_count     : int;
}

let create_window ?(size=50) ?(z_threshold=3.0) () =
  { buffer = Array.make size 0.0; w_size = size; z_threshold;
    pos = 0; filled = false; w_count = 0 }

let window_stats st =
  let n = if st.filled then st.w_size else st.pos in
  if n = 0 then (0.0, 0.0)
  else begin
    let sum = ref 0.0 in
    for i = 0 to n - 1 do sum := !sum +. st.buffer.(i) done;
    let mean = !sum /. float_of_int n in
    let var_sum = ref 0.0 in
    for i = 0 to n - 1 do
      let d = st.buffer.(i) -. mean in
      var_sum := !var_sum +. d *. d
    done;
    let stddev = sqrt (!var_sum /. float_of_int n) in
    (mean, stddev)
  end

let update_window st value =
  let new_pos = (st.pos + 1) mod st.w_size in
  let new_filled = st.filled || st.pos = st.w_size - 1 in
  let n = if st.filled then st.w_size else st.pos in
  (* Check anomaly BEFORE inserting *)
  let anomaly =
    if n >= 5 then
      let (mean, stddev) = window_stats st in
      if stddev > 0.0 then
        let deviation = abs_float (value -. mean) /. stddev in
        if deviation > st.z_threshold then
          let score = Float.min 1.0 ((deviation -. st.z_threshold) /. st.z_threshold) in
          Some { value; expected = mean; deviation; score; timestamp = st.w_count + 1 }
        else None
      else None
    else None
  in
  st.buffer.(st.pos) <- value;
  let st' = { st with pos = new_pos; filled = new_filled; w_count = st.w_count + 1 } in
  (st', anomaly)

(* ── IQR Detector ─────────────────────────────────────────────────── *)

type iqr_state = {
  iqr_buffer : float array;
  iqr_size   : int;
  iqr_k      : float;
  iqr_pos    : int;
  iqr_filled : bool;
  iqr_count  : int;
}

let create_iqr ?(size=50) ?(k=1.5) () =
  { iqr_buffer = Array.make size 0.0; iqr_size = size; iqr_k = k;
    iqr_pos = 0; iqr_filled = false; iqr_count = 0 }

let percentile_of sorted p =
  let n = Array.length sorted in
  if n = 0 then 0.0
  else
    let idx = p *. float_of_int (n - 1) in
    let lo = int_of_float (floor idx) in
    let hi = min (lo + 1) (n - 1) in
    let frac = idx -. float_of_int lo in
    sorted.(lo) *. (1.0 -. frac) +. sorted.(hi) *. frac

let update_iqr st value =
  let n = if st.iqr_filled then st.iqr_size else st.iqr_pos in
  let anomaly =
    if n >= 8 then begin
      let sorted = Array.sub st.iqr_buffer 0 n in
      Array.sort compare sorted;
      let q1 = percentile_of sorted 0.25 in
      let q3 = percentile_of sorted 0.75 in
      let iqr = q3 -. q1 in
      let lower = q1 -. st.iqr_k *. iqr in
      let upper = q3 +. st.iqr_k *. iqr in
      if value < lower || value > upper then
        let median = percentile_of sorted 0.5 in
        let deviation = if iqr > 0.0 then abs_float (value -. median) /. iqr else 0.0 in
        let score = Float.min 1.0 (deviation /. (st.iqr_k *. 2.0)) in
        Some { value; expected = median; deviation; score; timestamp = st.iqr_count + 1 }
      else None
    end else None
  in
  st.iqr_buffer.(st.iqr_pos) <- value;
  let new_pos = (st.iqr_pos + 1) mod st.iqr_size in
  let new_filled = st.iqr_filled || st.iqr_pos = st.iqr_size - 1 in
  let st' = { st with iqr_pos = new_pos; iqr_filled = new_filled; iqr_count = st.iqr_count + 1 } in
  (st', anomaly)

(* ── Formatting ────────────────────────────────────────────────────── *)

let format_anomaly a =
  Printf.sprintf "[ANOMALY t=%d] value=%.4f expected=%.4f deviation=%.2fσ score=%.3f"
    a.timestamp a.value a.expected a.deviation a.score

(* ── Demo ──────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Streaming Anomaly Detection Demo ===\n\n";

  (* EWMA demo *)
  Printf.printf "── EWMA Detector (alpha=0.3, k=3.0) ──\n";
  let normal_data = [| 10.1; 9.8; 10.2; 9.9; 10.0; 10.1; 9.7; 10.3; 9.9; 10.0;
                       10.1; 9.8; 10.2; 10.0; 9.9; 10.1; 10.0; 9.8; 10.2; 9.9 |] in
  let spikes = [| 10.0; 10.1; 9.9; 10.0; 25.0; 10.0; 9.9; 10.1; 10.0; -5.0 |] in
  let ewma = create_ewma ~alpha:0.3 ~k:3.0 () in
  let ewma = Array.fold_left (fun st v ->
    let (st', _) = update_ewma st v in st'
  ) ewma normal_data in
  Printf.printf "  After 20 normal points: mean=%.4f stddev=%.4f\n"
    (ewma_mean ewma) (ewma_stddev ewma);
  let _ewma = Array.fold_left (fun st v ->
    let (st', anom) = update_ewma st v in
    (match anom with
     | Some a -> Printf.printf "  %s\n" (format_anomaly a)
     | None -> Printf.printf "  t=%d value=%.1f — normal\n" (st'.count) v);
    st'
  ) ewma spikes in

  (* Sliding window demo *)
  Printf.printf "\n── Sliding Window Z-Score (size=10, z=2.5) ──\n";
  let win = create_window ~size:10 ~z_threshold:2.5 () in
  let stream = [| 5.0; 5.1; 4.9; 5.0; 5.2; 4.8; 5.0; 5.1; 4.9; 5.0;
                  5.1; 4.9; 5.0; 12.0; 5.0; 5.1; 4.9; 5.0; -3.0; 5.0 |] in
  let _win = Array.fold_left (fun st v ->
    let (st', anom) = update_window st v in
    (match anom with
     | Some a -> Printf.printf "  %s\n" (format_anomaly a)
     | None -> ());
    st'
  ) win stream in

  (* IQR demo *)
  Printf.printf "\n── IQR Detector (size=15, k=1.5) ──\n";
  let iqr = create_iqr ~size:15 ~k:1.5 () in
  let iqr_stream = [| 100.0; 101.0; 99.0; 100.5; 99.5; 100.2; 100.8; 99.2;
                      100.0; 100.1; 99.9; 100.3; 150.0; 100.0; 99.0; 50.0 |] in
  let _iqr = Array.fold_left (fun st v ->
    let (st', anom) = update_iqr st v in
    (match anom with
     | Some a -> Printf.printf "  %s\n" (format_anomaly a)
     | None -> ());
    st'
  ) iqr iqr_stream in

  Printf.printf "\n=== Summary ===\n";
  Printf.printf "Three complementary detectors for different use cases:\n";
  Printf.printf "  • EWMA: best for stationary streams with gradual drift\n";
  Printf.printf "  • Window Z-Score: best for recent-context anomalies\n";
  Printf.printf "  • IQR: robust to skewed distributions, resistant to outlier contamination\n";
  Printf.printf "\nAll are O(1) per update (IQR O(n log n) for window sort).\n"
