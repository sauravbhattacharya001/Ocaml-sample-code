(* test_signal_processing.ml — Tests for signal processing module *)


#use "test_framework.ml";;

let assert_float ~msg ~eps expected actual =
  incr tests_run;
  if Float.abs (expected -. actual) < eps then (
    incr tests_passed;
    Printf.printf "  ✓ %s\n" msg
  ) else
    Printf.printf "  ✗ %s (expected %.6f, got %.6f)\n" msg expected actual

let assert_int ~msg expected actual =
  incr tests_run;
  if expected = actual then (
    incr tests_passed;
    Printf.printf "  ✓ %s\n" msg
  ) else
    Printf.printf "  ✗ %s (expected %d, got %d)\n" msg expected actual

open Signal_processing

(* ── Complex arithmetic tests ────────────────────────────────────── *)

let test_complex () =
  print_endline "\n── Complex arithmetic ──";
  let a = complex 3.0 4.0 in
  let b = complex 1.0 2.0 in

  assert_float ~msg:"complex magnitude" ~eps:1e-10 5.0 (cmag a);
  assert_float ~msg:"complex mag_sq" ~eps:1e-10 25.0 (cmag_sq a);

  let sum = cadd a b in
  assert_float ~msg:"add re" ~eps:1e-10 4.0 sum.re;
  assert_float ~msg:"add im" ~eps:1e-10 6.0 sum.im;

  let diff = csub a b in
  assert_float ~msg:"sub re" ~eps:1e-10 2.0 diff.re;
  assert_float ~msg:"sub im" ~eps:1e-10 2.0 diff.im;

  let prod = cmul a b in
  (* (3+4i)(1+2i) = 3+6i+4i+8i² = 3+10i-8 = -5+10i *)
  assert_float ~msg:"mul re" ~eps:1e-10 (-5.0) prod.re;
  assert_float ~msg:"mul im" ~eps:1e-10 10.0 prod.im;

  let quot = cdiv a b in
  (* (3+4i)/(1+2i) = (3+4i)(1-2i)/(1+4) = (3-6i+4i-8i²)/5 = (11-2i)/5 *)
  assert_float ~msg:"div re" ~eps:1e-10 2.2 quot.re;
  assert_float ~msg:"div im" ~eps:1e-10 (-0.4) quot.im;

  let c = cconj a in
  assert_float ~msg:"conj im" ~eps:1e-10 (-4.0) c.im;

  let n = cneg a in
  assert_float ~msg:"neg re" ~eps:1e-10 (-3.0) n.re;
  assert_float ~msg:"neg im" ~eps:1e-10 (-4.0) n.im;

  (* cexp(0) = 1+0i *)
  let e0 = cexp 0.0 in
  assert_float ~msg:"cexp(0) re" ~eps:1e-10 1.0 e0.re;
  assert_float ~msg:"cexp(0) im" ~eps:1e-10 0.0 e0.im;

  (* cexp(π) = -1+0i *)
  let ep = cexp pi in
  assert_float ~msg:"cexp(pi) re" ~eps:1e-10 (-1.0) ep.re;
  assert_float ~msg:"cexp(pi) im" ~eps:1e-6 0.0 ep.im;

  (* cphase *)
  assert_float ~msg:"phase of 1+i" ~eps:1e-10
    (pi /. 4.0) (cphase (complex 1.0 1.0));

  (* to_string *)
  let s = complex_to_string (complex 1.0 (-2.0)) in
  assert_true ~msg:"to_string contains minus" (String.length s > 0)

(* ── Utility tests ───────────────────────────────────────────────── *)

let test_utility () =
  print_endline "\n── Utility ──";
  assert_int ~msg:"next_pow2 1" 1 (next_pow2 1);
  assert_int ~msg:"next_pow2 3" 4 (next_pow2 3);
  assert_int ~msg:"next_pow2 4" 4 (next_pow2 4);
  assert_int ~msg:"next_pow2 5" 8 (next_pow2 5);
  assert_int ~msg:"next_pow2 128" 128 (next_pow2 128);

  assert_true ~msg:"is_pow2 1" (is_pow2 1);
  assert_true ~msg:"is_pow2 4" (is_pow2 4);
  assert_true ~msg:"is_pow2 1024" (is_pow2 1024);
  assert_true ~msg:"!is_pow2 3" (not (is_pow2 3));
  assert_true ~msg:"!is_pow2 0" (not (is_pow2 0));

  (* zero_pad *)
  let s = [| cone; cone |] in
  let padded = zero_pad s 4 in
  assert_int ~msg:"zero_pad length" 4 (Array.length padded);
  assert_float ~msg:"zero_pad [0]" ~eps:1e-10 1.0 padded.(0).re;
  assert_float ~msg:"zero_pad [3]" ~eps:1e-10 0.0 padded.(3).re;

  (* zero_pad shorter *)
  let shorter = zero_pad s 2 in
  assert_int ~msg:"zero_pad no growth" 2 (Array.length shorter)

(* ── FFT tests ───────────────────────────────────────────────────── *)

let test_fft () =
  print_endline "\n── FFT ──";

  (* FFT of constant signal: all energy in bin 0 *)
  let dc = Array.make 8 (complex_of_float 1.0) in
  let spec = fft dc in
  assert_float ~msg:"DC signal bin 0 magnitude" ~eps:1e-10 8.0 (cmag spec.(0));
  assert_float ~msg:"DC signal bin 1 magnitude" ~eps:1e-10 0.0 (cmag spec.(1));

  (* FFT of single impulse: flat spectrum *)
  let impulse = Array.make 8 czero in
  impulse.(0) <- cone;
  let spec = fft impulse in
  for k = 0 to 7 do
    assert_float ~msg:(Printf.sprintf "impulse bin %d mag" k)
      ~eps:1e-10 1.0 (cmag spec.(k))
  done;

  (* FFT→IFFT roundtrip *)
  let signal = Array.init 16 (fun i -> complex_of_float (sin (2.0 *. pi *. 3.0 *. float_of_int i /. 16.0))) in
  let recovered = ifft (fft signal) in
  let max_err = ref 0.0 in
  for i = 0 to 15 do
    let err = abs_float (signal.(i).re -. recovered.(i).re) in
    if err > !max_err then max_err := err
  done;
  assert_true ~msg:"FFT→IFFT roundtrip error < 1e-10" (!max_err < 1e-10);

  (* FFT of real signal *)
  let real_sig = [| 1.0; 0.0; -1.0; 0.0 |] in
  let spec = fft_real real_sig in
  assert_int ~msg:"fft_real output length is power of 2" 4 (Array.length spec);

  (* Non-power-of-2 throws *)
  assert_raises ~msg:"fft_in_place non-pow2 raises" (fun () ->
    let bad = Array.make 6 czero in
    fft_in_place bad);

  (* Single element FFT *)
  let single = [| complex_of_float 42.0 |] in
  fft_in_place single;
  assert_float ~msg:"single element FFT" ~eps:1e-10 42.0 single.(0).re

(* ── Spectral analysis tests ─────────────────────────────────────── *)

let test_spectral () =
  print_endline "\n── Spectral analysis ──";

  (* Pure sine should have a dominant peak *)
  let sig4 = sine_wave ~freq:4.0 ~sample_rate:64 ~duration:1.0 () in
  let spec = fft_real sig4 in

  let dom = dominant_frequency spec in
  (* At sr=64, bin k corresponds to freq k*64/N Hz *)
  let dom_hz = float_of_int dom *. 64.0 /. float_of_int (Array.length spec) in
  assert_float ~msg:"dominant freq ≈ 4 Hz" ~eps:1.0 4.0 dom_hz;

  (* Spectral centroid of pure sine should be near its frequency bin *)
  let centroid = spectral_centroid spec in
  assert_true ~msg:"centroid > 0" (centroid > 0.0);

  (* Magnitude spectrum non-negative *)
  let mags = magnitude_spectrum spec in
  let all_positive = Array.for_all (fun m -> m >= 0.0) mags in
  assert_true ~msg:"magnitude spectrum >= 0" all_positive;

  (* Power spectrum non-negative *)
  let pows = power_spectrum spec in
  let all_positive = Array.for_all (fun p -> p >= 0.0) pows in
  assert_true ~msg:"power spectrum >= 0" all_positive;

  (* Phase spectrum values in [-π, π] *)
  let phases = phase_spectrum spec in
  let in_range = Array.for_all (fun p -> p >= -.pi && p <= pi) phases in
  assert_true ~msg:"phase in [-π, π]" in_range;

  (* find_peaks returns sorted desc by magnitude *)
  let peaks = find_peaks ~threshold:0.0 spec in
  let rec is_desc = function
    | [] | [_] -> true
    | (_, a) :: ((_, b) :: _ as rest) -> a >= b && is_desc rest
  in
  assert_true ~msg:"peaks sorted desc" (is_desc peaks)

(* ── Windowing tests ─────────────────────────────────────────────── *)

let test_windowing () =
  print_endline "\n── Windowing ──";
  let n = 64 in

  (* Hamming: symmetric, endpoints near 0.08, midpoint near 1.0 *)
  let h = hamming_window n in
  assert_int ~msg:"hamming length" n (Array.length h);
  assert_float ~msg:"hamming[0] ≈ 0.08" ~eps:0.01 0.08 h.(0);
  assert_float ~msg:"hamming[n/2] ≈ 1.0" ~eps:0.01 1.0 h.(n / 2);
  assert_float ~msg:"hamming symmetric" ~eps:1e-10 h.(0) h.(n - 1);

  (* Hann: endpoints are 0 *)
  let h = hann_window n in
  assert_float ~msg:"hann[0] = 0" ~eps:1e-10 0.0 h.(0);
  assert_float ~msg:"hann[n-1] = 0" ~eps:1e-10 0.0 h.(n - 1);
  assert_true ~msg:"hann midpoint > 0.9" (h.(n / 2) > 0.9);

  (* Blackman: endpoints near 0 *)
  let b = blackman_window n in
  assert_true ~msg:"blackman[0] < 0.01" (b.(0) < 0.01);
  assert_true ~msg:"blackman symmetric" (Float.abs (b.(0) -. b.(n - 1)) < 1e-10);

  (* Flat-top *)
  let ft = flat_top_window n in
  assert_int ~msg:"flat-top length" n (Array.length ft);
  assert_true ~msg:"flat-top symmetric" (Float.abs (ft.(0) -. ft.(n - 1)) < 1e-10);

  (* Rectangular: all ones *)
  let r = rectangular_window n in
  assert_true ~msg:"rectangular all 1.0"
    (Array.for_all (fun x -> x = 1.0) r);

  (* apply_window *)
  let signal = Array.make 4 cone in
  let win = [| 0.5; 1.0; 1.0; 0.5 |] in
  let windowed = apply_window win signal in
  assert_float ~msg:"windowed[0]" ~eps:1e-10 0.5 windowed.(0).re;
  assert_float ~msg:"windowed[1]" ~eps:1e-10 1.0 windowed.(1).re

(* ── Convolution tests ───────────────────────────────────────────── *)

let test_convolution () =
  print_endline "\n── Convolution ──";

  (* Convolve with impulse: identity *)
  let x = [| 1.0; 2.0; 3.0; 4.0 |] in
  let impulse = [| 1.0 |] in
  let result = convolve x impulse in
  assert_int ~msg:"convolve with impulse length" 4 (Array.length result);
  assert_float ~msg:"convolve[0] = 1" ~eps:1e-6 1.0 result.(0);
  assert_float ~msg:"convolve[3] = 4" ~eps:1e-6 4.0 result.(3);

  (* Convolve output length *)
  let h = [| 0.5; 0.5 |] in
  let result = convolve x h in
  assert_int ~msg:"convolve length = lx + lh - 1" 5 (Array.length result);

  (* Convolve with averaging kernel *)
  assert_float ~msg:"avg convolve[0]" ~eps:1e-6 0.5 result.(0);
  assert_float ~msg:"avg convolve[1]" ~eps:1e-6 1.5 result.(1);

  (* Circular convolution length = max(lx, lh) *)
  let circ = circular_convolve x h in
  assert_int ~msg:"circular length" 4 (Array.length circ);

  (* Cross-correlation length *)
  let cc = cross_correlate x x in
  assert_int ~msg:"cross-corr length" 7 (Array.length cc);

  (* Autocorrelation peak at lag 0 *)
  let ac = autocorrelate x in
  let peak = ac.(Array.length x - 1) in (* lag-0 in full correlation *)
  assert_true ~msg:"autocorr peak > 0" (peak > 0.0)

(* ── Signal generator tests ──────────────────────────────────────── *)

let test_generators () =
  print_endline "\n── Signal generators ──";
  let sr = 100 in
  let dur = 0.1 in
  let n = 10 in (* 100 * 0.1 *)

  (* Sine wave: correct length *)
  let s = sine_wave ~freq:10.0 ~sample_rate:sr ~duration:dur () in
  assert_int ~msg:"sine length" n (Array.length s);
  (* sin(0) = 0 *)
  assert_float ~msg:"sine[0] ≈ 0" ~eps:1e-10 0.0 s.(0);

  (* Sine with amplitude *)
  let s = sine_wave ~freq:10.0 ~amplitude:2.0 ~sample_rate:sr ~duration:dur () in
  assert_true ~msg:"sine amplitude bounded" (Array.for_all (fun x -> abs_float x <= 2.001) s);

  (* Square wave: values are +A or -A *)
  let sq = square_wave ~freq:10.0 ~sample_rate:sr ~duration:dur () in
  assert_int ~msg:"square length" n (Array.length sq);
  assert_true ~msg:"square values ±1"
    (Array.for_all (fun x -> abs_float (abs_float x -. 1.0) < 1e-10) sq);

  (* Sawtooth: values in [-1, 1] *)
  let sw = sawtooth_wave ~freq:10.0 ~sample_rate:sr ~duration:dur () in
  assert_true ~msg:"sawtooth in [-1, 1]"
    (Array.for_all (fun x -> x >= -1.001 && x <= 1.001) sw);

  (* Triangle: values in [-1, 1] *)
  let tr = triangle_wave ~freq:10.0 ~sample_rate:sr ~duration:dur () in
  assert_true ~msg:"triangle in [-1, 1]"
    (Array.for_all (fun x -> x >= -1.001 && x <= 1.001) tr);

  (* White noise: correct length *)
  let wn = white_noise ~sample_rate:sr ~duration:dur () in
  assert_int ~msg:"noise length" n (Array.length wn);

  (* Chirp: correct length *)
  let ch = chirp ~f0:10.0 ~f1:50.0 ~sample_rate:sr ~duration:dur () in
  assert_int ~msg:"chirp length" n (Array.length ch)

(* ── Time-domain analysis tests ──────────────────────────────────── *)

let test_time_domain () =
  print_endline "\n── Time-domain analysis ──";

  (* Zero-crossing rate of pure sine *)
  let s = sine_wave ~freq:1.0 ~sample_rate:1000 ~duration:1.0 () in
  let zcr = zero_crossing_rate s in
  (* 1 Hz sine crosses zero ~2 times per period, ~2 crossings in 999 gaps *)
  assert_true ~msg:"zcr > 0 for sine" (zcr > 0.0);
  assert_true ~msg:"zcr < 0.01 for 1Hz/1000sr" (zcr < 0.01);

  (* ZCR of empty / single *)
  assert_float ~msg:"zcr empty" ~eps:1e-10 0.0 (zero_crossing_rate [||]);
  assert_float ~msg:"zcr single" ~eps:1e-10 0.0 (zero_crossing_rate [| 1.0 |]);

  (* RMS *)
  let dc = Array.make 4 3.0 in
  assert_float ~msg:"rms of constant 3" ~eps:1e-10 3.0 (rms dc);
  assert_float ~msg:"rms empty" ~eps:1e-10 0.0 (rms [||]);

  (* Energy *)
  assert_float ~msg:"energy [1;2;3]" ~eps:1e-10 14.0 (energy [| 1.0; 2.0; 3.0 |]);
  assert_float ~msg:"energy empty" ~eps:1e-10 0.0 (energy [||]);

  (* Peak-to-peak *)
  assert_float ~msg:"p2p [-3, 5]" ~eps:1e-10 8.0
    (peak_to_peak [| -3.0; 0.0; 5.0; 2.0 |]);
  assert_float ~msg:"p2p empty" ~eps:1e-10 0.0 (peak_to_peak [||]);
  assert_float ~msg:"p2p constant" ~eps:1e-10 0.0 (peak_to_peak [| 1.0; 1.0 |])

(* ── Filtering tests ─────────────────────────────────────────────── *)

let test_filtering () =
  print_endline "\n── Filtering ──";

  (* Moving average *)
  let s = [| 1.0; 3.0; 5.0; 7.0; 9.0 |] in
  let ma = moving_average s 3 in
  assert_int ~msg:"MA length" 3 (Array.length ma);
  assert_float ~msg:"MA[0] = avg(1,3,5)" ~eps:1e-10 3.0 ma.(0);
  assert_float ~msg:"MA[1] = avg(3,5,7)" ~eps:1e-10 5.0 ma.(1);
  assert_float ~msg:"MA[2] = avg(5,7,9)" ~eps:1e-10 7.0 ma.(2);

  (* MA invalid k *)
  assert_raises ~msg:"MA k=0 raises" (fun () ->
    ignore (moving_average s 0));
  assert_raises ~msg:"MA k>n raises" (fun () ->
    ignore (moving_average s 10));

  (* Exponential MA *)
  let ema = exponential_ma s 1.0 in
  (* alpha=1.0 → output = input *)
  assert_float ~msg:"EMA alpha=1 passthrough" ~eps:1e-10 9.0 ema.(4);

  let ema = exponential_ma s 0.5 in
  assert_float ~msg:"EMA[0] = s[0]" ~eps:1e-10 1.0 ema.(0);
  assert_true ~msg:"EMA smooths" (ema.(1) < s.(1));

  (* EMA invalid alpha *)
  assert_raises ~msg:"EMA alpha=0 raises" (fun () ->
    ignore (exponential_ma s 0.0));
  assert_raises ~msg:"EMA alpha=1.5 raises" (fun () ->
    ignore (exponential_ma s 1.5));

  (* EMA empty *)
  let ema_empty = exponential_ma [||] 0.5 in
  assert_int ~msg:"EMA empty" 0 (Array.length ema_empty)

(* ── Integration test: detect frequencies ─────────────────────────── *)

let test_integration () =
  print_endline "\n── Integration: frequency detection ──";

  (* Generate signal with known frequencies: 10 Hz and 30 Hz *)
  let sr = 256 in
  let dur = 1.0 in
  let s10 = sine_wave ~freq:10.0 ~sample_rate:sr ~duration:dur () in
  let s30 = sine_wave ~freq:30.0 ~amplitude:0.5 ~sample_rate:sr ~duration:dur () in
  let mixed = Array.init (Array.length s10) (fun i -> s10.(i) +. s30.(i)) in

  (* Apply Hann window to reduce spectral leakage *)
  let win = hann_window (Array.length mixed) in
  let windowed = Array.init (Array.length mixed) (fun i ->
    complex_of_float (mixed.(i) *. win.(i))) in

  let spec = fft windowed in
  let peaks = find_peaks ~threshold:10.0 spec in

  (* Should find at least 2 peaks near 10 Hz and 30 Hz *)
  assert_true ~msg:"found >= 2 peaks" (List.length peaks >= 2);

  (* First peak (largest) should be near 10 Hz *)
  let (bin1, _) = List.hd peaks in
  let hz1 = float_of_int bin1 *. float_of_int sr /. float_of_int (Array.length spec) in
  assert_true ~msg:"peak 1 near 10 Hz" (abs_float (hz1 -. 10.0) < 2.0);

  (* FFT→IFFT with window: roundtrip preserves signal *)
  let spec2 = fft (Array.map complex_of_float s10) in
  let rec2 = ifft spec2 in
  let err = ref 0.0 in
  for i = 0 to Array.length s10 - 1 do
    let e = abs_float (s10.(i) -. rec2.(i).re) in
    if e > !err then err := e
  done;
  assert_true ~msg:"roundtrip error < 1e-8" (!err < 1e-8)

(* ── Run all tests ───────────────────────────────────────────────── *)

let () =
  print_endline "=== Signal Processing Tests ===";
  test_complex ();
  test_utility ();
  test_fft ();
  test_spectral ();
  test_windowing ();
  test_convolution ();
  test_generators ();
  test_time_domain ();
  test_filtering ();
  test_integration ();
  test_summary ()
