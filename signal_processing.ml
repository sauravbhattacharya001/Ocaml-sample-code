(* Signal Processing — FFT, convolution, spectral analysis, and windowing   *)
(* Demonstrates complex arithmetic, divide-and-conquer (Cooley-Tukey FFT), *)
(* array manipulation, higher-order functions for signal generation, and    *)
(* practical DSP algorithms commonly used in audio/image processing.       *)
(* Features: FFT/IFFT (radix-2 Cooley-Tukey), linear/circular convolution,*)
(* power spectrum & magnitude, windowing (Hamming/Hann/Blackman/flat-top), *)
(* signal generators (sine/square/sawtooth/triangle/white noise/chirp),    *)
(* zero-crossing rate, autocorrelation, spectral centroid, peak detection. *)

(* ── Complex numbers ──────────────────────────────────────────────── *)

type complex = { re : float; im : float }

let complex re im = { re; im }
let complex_of_float x = { re = x; im = 0.0 }

let cadd a b = { re = a.re +. b.re; im = a.im +. b.im }
let csub a b = { re = a.re -. b.re; im = a.im -. b.im }
let cmul a b = { re = a.re *. b.re -. a.im *. b.im;
                 im = a.re *. b.im +. a.im *. b.re }
let cdiv a b =
  let denom = b.re *. b.re +. b.im *. b.im in
  { re = (a.re *. b.re +. a.im *. b.im) /. denom;
    im = (a.im *. b.re -. a.re *. b.im) /. denom }

let cneg a = { re = -. a.re; im = -. a.im }
let cconj a = { re = a.re; im = -. a.im }
let cmag a = sqrt (a.re *. a.re +. a.im *. a.im)
let cphase a = atan2 a.im a.re
let cmag_sq a = a.re *. a.re +. a.im *. a.im

let cexp theta = { re = cos theta; im = sin theta }

let czero = { re = 0.0; im = 0.0 }
let cone  = { re = 1.0; im = 0.0 }

let complex_to_string c =
  if c.im >= 0.0 then Printf.sprintf "%.4f+%.4fi" c.re c.im
  else Printf.sprintf "%.4f%.4fi" c.re c.im

(* ── Utility ──────────────────────────────────────────────────────── *)

let pi = 4.0 *. atan 1.0

(** Next power of two >= n *)
let next_pow2 n =
  let rec go p = if p >= n then p else go (p * 2) in
  if n <= 1 then 1 else go 1

(** Is n a power of two? *)
let is_pow2 n = n > 0 && n land (n - 1) = 0

(** Pad signal with zeros to length len *)
let zero_pad signal len =
  let n = Array.length signal in
  if n >= len then signal
  else Array.init len (fun i -> if i < n then signal.(i) else czero)

(* ── FFT (Cooley-Tukey, radix-2, decimation-in-time) ─────────────── *)

(** In-place iterative Cooley-Tukey FFT.  Input length must be a power of 2.
    [inverse] = true performs the inverse FFT (scales by 1/N). *)
let fft_in_place ?(inverse=false) buf =
  let n = Array.length buf in
  if n <= 1 then ()
  else begin
    if not (is_pow2 n) then
      invalid_arg "fft_in_place: length must be a power of 2";

    (* Bit-reversal permutation *)
    let log_n = int_of_float (log (float_of_int n) /. log 2.0 +. 0.5) in
    for i = 0 to n - 1 do
      let j = ref 0 in
      for bit = 0 to log_n - 1 do
        if i land (1 lsl bit) <> 0 then
          j := !j lor (1 lsl (log_n - 1 - bit))
      done;
      if !j > i then begin
        let tmp = buf.(i) in
        buf.(i) <- buf.(!j);
        buf.(!j) <- tmp
      end
    done;

    (* Butterfly operations *)
    let sign = if inverse then 1.0 else -1.0 in
    let half_size = ref 1 in
    while !half_size < n do
      let size = !half_size * 2 in
      let angle = sign *. pi /. float_of_int !half_size in
      let wn = cexp angle in
      let j = ref 0 in
      while !j < n do
        let w = ref cone in
        for k = 0 to !half_size - 1 do
          let u = buf.(!j + k) in
          let t = cmul !w buf.(!j + k + !half_size) in
          buf.(!j + k)              <- cadd u t;
          buf.(!j + k + !half_size) <- csub u t;
          w := cmul !w wn
        done;
        j := !j + size
      done;
      half_size := size
    done;

    (* Scale for inverse *)
    if inverse then begin
      let scale = 1.0 /. float_of_int n in
      for i = 0 to n - 1 do
        buf.(i) <- { re = buf.(i).re *. scale;
                     im = buf.(i).im *. scale }
      done
    end
  end

(** Forward FFT: returns frequency-domain representation. *)
let fft signal =
  let n = next_pow2 (Array.length signal) in
  let buf = zero_pad signal n in
  fft_in_place buf;
  buf

(** Inverse FFT: returns time-domain signal. *)
let ifft spectrum =
  let buf = Array.copy spectrum in
  fft_in_place ~inverse:true buf;
  buf

(** FFT of real-valued signal (float array → complex array). *)
let fft_real signal =
  fft (Array.map complex_of_float signal)

(* ── Spectral analysis ────────────────────────────────────────────── *)

(** Magnitude spectrum: |X[k]| for each frequency bin. *)
let magnitude_spectrum spectrum =
  Array.map cmag spectrum

(** Power spectrum: |X[k]|² for each frequency bin. *)
let power_spectrum spectrum =
  Array.map cmag_sq spectrum

(** Phase spectrum: arg(X[k]) in radians. *)
let phase_spectrum spectrum =
  Array.map cphase spectrum

(** Spectral centroid: weighted mean of frequencies.
    Returns a value in [0, n/2] representing the "brightness" of the signal. *)
let spectral_centroid spectrum =
  let n = Array.length spectrum in
  let half = n / 2 in
  let num = ref 0.0 in
  let den = ref 0.0 in
  for k = 0 to half do
    let mag = cmag spectrum.(k) in
    num := !num +. float_of_int k *. mag;
    den := !den +. mag
  done;
  if !den = 0.0 then 0.0 else !num /. !den

(** Find peaks in magnitude spectrum above threshold.
    Returns list of (bin_index, magnitude) pairs sorted by magnitude desc. *)
let find_peaks ?(threshold=0.0) spectrum =
  let mags = magnitude_spectrum spectrum in
  let n = Array.length mags / 2 in  (* only positive frequencies *)
  let peaks = ref [] in
  for i = 1 to n - 2 do
    if mags.(i) > mags.(i-1) && mags.(i) > mags.(i+1) && mags.(i) > threshold then
      peaks := (i, mags.(i)) :: !peaks
  done;
  List.sort (fun (_, a) (_, b) -> compare b a) !peaks

(** Dominant frequency bin index (index of max magnitude in positive spectrum). *)
let dominant_frequency spectrum =
  let mags = magnitude_spectrum spectrum in
  let n = Array.length mags / 2 in
  let best_k = ref 0 in
  let best_m = ref 0.0 in
  for k = 1 to n - 1 do
    if mags.(k) > !best_m then begin
      best_k := k;
      best_m := mags.(k)
    end
  done;
  !best_k

(* ── Windowing functions ──────────────────────────────────────────── *)

(** Apply a window function to a signal (element-wise multiply). *)
let apply_window window signal =
  let n = Array.length signal in
  Array.init n (fun i ->
    { re = signal.(i).re *. window.(i);
      im = signal.(i).im *. window.(i) })

(** Hamming window: w(n) = 0.54 - 0.46·cos(2πn/(N-1)) *)
let hamming_window n =
  Array.init n (fun i ->
    0.54 -. 0.46 *. cos (2.0 *. pi *. float_of_int i /. float_of_int (n - 1)))

(** Hann window: w(n) = 0.5·(1 - cos(2πn/(N-1))) *)
let hann_window n =
  Array.init n (fun i ->
    0.5 *. (1.0 -. cos (2.0 *. pi *. float_of_int i /. float_of_int (n - 1))))

(** Blackman window: w(n) = 0.42 - 0.5·cos(2πn/(N-1)) + 0.08·cos(4πn/(N-1)) *)
let blackman_window n =
  let nm1 = float_of_int (n - 1) in
  Array.init n (fun i ->
    let x = float_of_int i in
    0.42 -. 0.5 *. cos (2.0 *. pi *. x /. nm1)
    +. 0.08 *. cos (4.0 *. pi *. x /. nm1))

(** Flat-top window: optimised for amplitude accuracy in spectrum analysis. *)
let flat_top_window n =
  let nm1 = float_of_int (n - 1) in
  Array.init n (fun i ->
    let x = float_of_int i in
    let a0 = 0.21557895 in
    let a1 = 0.41663158 in
    let a2 = 0.277263158 in
    let a3 = 0.083578947 in
    let a4 = 0.006947368 in
    a0 -. a1 *. cos (2.0 *. pi *. x /. nm1)
    +. a2 *. cos (4.0 *. pi *. x /. nm1)
    -. a3 *. cos (6.0 *. pi *. x /. nm1)
    +. a4 *. cos (8.0 *. pi *. x /. nm1))

(** Rectangular window (no windowing — all ones). *)
let rectangular_window n =
  Array.make n 1.0

(* ── Convolution ──────────────────────────────────────────────────── *)

(** Linear convolution via FFT: y = x * h.
    Pads inputs to avoid circular aliasing (length = len(x) + len(h) - 1). *)
let convolve x h =
  let lx = Array.length x in
  let lh = Array.length h in
  let out_len = lx + lh - 1 in
  let n = next_pow2 out_len in
  let xc = Array.init n (fun i -> if i < lx then complex_of_float x.(i) else czero) in
  let hc = Array.init n (fun i -> if i < lh then complex_of_float h.(i) else czero) in
  fft_in_place xc;
  fft_in_place hc;
  let yc = Array.init n (fun i -> cmul xc.(i) hc.(i)) in
  fft_in_place ~inverse:true yc;
  Array.init out_len (fun i -> yc.(i).re)

(** Circular convolution: wraps around to length N. *)
let circular_convolve x h =
  let n = max (Array.length x) (Array.length h) in
  let np = next_pow2 n in
  let xc = Array.init np (fun i ->
    if i < Array.length x then complex_of_float x.(i) else czero) in
  let hc = Array.init np (fun i ->
    if i < Array.length h then complex_of_float h.(i) else czero) in
  fft_in_place xc;
  fft_in_place hc;
  let yc = Array.init np (fun i -> cmul xc.(i) hc.(i)) in
  fft_in_place ~inverse:true yc;
  Array.init n (fun i -> yc.(i).re)

(** Cross-correlation of two real signals via FFT. *)
let cross_correlate x y =
  let lx = Array.length x in
  let ly = Array.length y in
  let out_len = lx + ly - 1 in
  let n = next_pow2 out_len in
  let xc = Array.init n (fun i -> if i < lx then complex_of_float x.(i) else czero) in
  let yc = Array.init n (fun i -> if i < ly then complex_of_float y.(i) else czero) in
  fft_in_place xc;
  fft_in_place yc;
  (* Correlation = IFFT(X · conj(Y)) *)
  let rc = Array.init n (fun i -> cmul xc.(i) (cconj yc.(i))) in
  fft_in_place ~inverse:true rc;
  Array.init out_len (fun i -> rc.(i).re)

(** Autocorrelation: cross-correlation of a signal with itself. *)
let autocorrelate signal = cross_correlate signal signal

(* ── Signal generators ────────────────────────────────────────────── *)

(** Generate a sine wave: A·sin(2πft + φ).
    @param freq      frequency in Hz
    @param sample_rate samples per second
    @param duration  length in seconds
    @param amplitude peak amplitude (default 1.0)
    @param phase     initial phase in radians (default 0.0) *)
let sine_wave ?(amplitude=1.0) ?(phase=0.0) ~freq ~sample_rate ~duration () =
  let n = int_of_float (float_of_int sample_rate *. duration) in
  Array.init n (fun i ->
    let t = float_of_int i /. float_of_int sample_rate in
    amplitude *. sin (2.0 *. pi *. freq *. t +. phase))

(** Generate a square wave (+amplitude / -amplitude). *)
let square_wave ?(amplitude=1.0) ?(duty=0.5) ~freq ~sample_rate ~duration () =
  let n = int_of_float (float_of_int sample_rate *. duration) in
  Array.init n (fun i ->
    let t = float_of_int i /. float_of_int sample_rate in
    let phase = mod_float (t *. freq) 1.0 in
    if phase < duty then amplitude else -. amplitude)

(** Generate a sawtooth wave: rises linearly from -A to +A each period. *)
let sawtooth_wave ?(amplitude=1.0) ~freq ~sample_rate ~duration () =
  let n = int_of_float (float_of_int sample_rate *. duration) in
  Array.init n (fun i ->
    let t = float_of_int i /. float_of_int sample_rate in
    let phase = mod_float (t *. freq) 1.0 in
    amplitude *. (2.0 *. phase -. 1.0))

(** Generate a triangle wave: linearly rises and falls. *)
let triangle_wave ?(amplitude=1.0) ~freq ~sample_rate ~duration () =
  let n = int_of_float (float_of_int sample_rate *. duration) in
  Array.init n (fun i ->
    let t = float_of_int i /. float_of_int sample_rate in
    let phase = mod_float (t *. freq) 1.0 in
    amplitude *. (2.0 *. abs_float (2.0 *. phase -. 1.0) -. 1.0))

(** Generate white noise: uniformly distributed random values in [-A, +A]. *)
let white_noise ?(amplitude=1.0) ~sample_rate ~duration () =
  let n = int_of_float (float_of_int sample_rate *. duration) in
  Array.init n (fun _ ->
    amplitude *. (2.0 *. Random.float 1.0 -. 1.0))

(** Generate a chirp (swept-frequency sine): freq sweeps from f0 to f1. *)
let chirp ?(amplitude=1.0) ~f0 ~f1 ~sample_rate ~duration () =
  let n = int_of_float (float_of_int sample_rate *. duration) in
  let rate = (f1 -. f0) /. duration in
  Array.init n (fun i ->
    let t = float_of_int i /. float_of_int sample_rate in
    amplitude *. sin (2.0 *. pi *. (f0 *. t +. 0.5 *. rate *. t *. t)))

(* ── Time-domain analysis ─────────────────────────────────────────── *)

(** Zero-crossing rate: fraction of adjacent samples that change sign.
    Higher values indicate higher-frequency or noisier content. *)
let zero_crossing_rate signal =
  let n = Array.length signal in
  if n <= 1 then 0.0
  else begin
    let count = ref 0 in
    for i = 1 to n - 1 do
      if (signal.(i) >= 0.0 && signal.(i-1) < 0.0) ||
         (signal.(i) < 0.0 && signal.(i-1) >= 0.0) then
        incr count
    done;
    float_of_int !count /. float_of_int (n - 1)
  end

(** Root-mean-square energy of a signal. *)
let rms signal =
  let n = Array.length signal in
  if n = 0 then 0.0
  else begin
    let sum = ref 0.0 in
    for i = 0 to n - 1 do
      sum := !sum +. signal.(i) *. signal.(i)
    done;
    sqrt (!sum /. float_of_int n)
  end

(** Signal energy: sum of x[n]². *)
let energy signal =
  let sum = ref 0.0 in
  Array.iter (fun x -> sum := !sum +. x *. x) signal;
  !sum

(** Peak-to-peak amplitude: max(x) - min(x). *)
let peak_to_peak signal =
  if Array.length signal = 0 then 0.0
  else begin
    let lo = ref infinity in
    let hi = ref neg_infinity in
    Array.iter (fun x ->
      if x < !lo then lo := x;
      if x > !hi then hi := x) signal;
    !hi -. !lo
  end

(* ── Filtering ────────────────────────────────────────────────────── *)

(** Simple moving average filter with window size k. *)
let moving_average signal k =
  let n = Array.length signal in
  if k <= 0 then invalid_arg "moving_average: k must be positive";
  if k > n then invalid_arg "moving_average: k larger than signal length";
  let result = Array.make (n - k + 1) 0.0 in
  let sum = ref 0.0 in
  for i = 0 to k - 1 do sum := !sum +. signal.(i) done;
  result.(0) <- !sum /. float_of_int k;
  for i = 1 to n - k do
    sum := !sum -. signal.(i - 1) +. signal.(i + k - 1);
    result.(i) <- !sum /. float_of_int k
  done;
  result

(** Exponential moving average: y[n] = α·x[n] + (1-α)·y[n-1].
    alpha in (0, 1]; higher alpha = more responsive. *)
let exponential_ma signal alpha =
  if alpha <= 0.0 || alpha > 1.0 then
    invalid_arg "exponential_ma: alpha must be in (0, 1]";
  let n = Array.length signal in
  if n = 0 then [||]
  else begin
    let result = Array.make n signal.(0) in
    for i = 1 to n - 1 do
      result.(i) <- alpha *. signal.(i) +. (1.0 -. alpha) *. result.(i-1)
    done;
    result
  end

(* ── Pretty printing ──────────────────────────────────────────────── *)

(** Print a signal as a simple ASCII waveform. *)
let print_waveform ?(width=60) ?(height=10) signal =
  let n = Array.length signal in
  if n = 0 then print_endline "(empty signal)"
  else begin
    let lo = ref infinity in
    let hi = ref neg_infinity in
    Array.iter (fun x ->
      if x < !lo then lo := x;
      if x > !hi then hi := x) signal;
    let range = !hi -. !lo in
    let range = if range = 0.0 then 1.0 else range in
    let rows = Array.init height (fun _ -> Bytes.make width ' ') in
    for col = 0 to width - 1 do
      let idx = col * n / width in
      let row = int_of_float
        (float_of_int (height - 1) *.
         (1.0 -. (signal.(idx) -. !lo) /. range)) in
      let row = max 0 (min (height - 1) row) in
      Bytes.set rows.(row) col '*'
    done;
    Array.iter (fun row -> print_endline (Bytes.to_string row)) rows
  end

(* ── Demo ─────────────────────────────────────────────────────────── *)

let () =
  print_endline "=== Signal Processing Module ===\n";

  (* Generate a test signal: 10 Hz sine + 25 Hz sine *)
  let sr = 128 in
  let dur = 1.0 in
  let s1 = sine_wave ~freq:10.0 ~sample_rate:sr ~duration:dur () in
  let s2 = sine_wave ~freq:25.0 ~amplitude:0.5 ~sample_rate:sr ~duration:dur () in
  let mixed = Array.init (Array.length s1) (fun i -> s1.(i) +. s2.(i)) in

  Printf.printf "Signal length: %d samples (sr=%d Hz, %.1fs)\n" (Array.length mixed) sr dur;
  Printf.printf "RMS energy: %.4f\n" (rms mixed);
  Printf.printf "Peak-to-peak: %.4f\n" (peak_to_peak mixed);
  Printf.printf "Zero-crossing rate: %.4f\n\n" (zero_crossing_rate mixed);

  (* FFT analysis *)
  let spectrum = fft_real mixed in
  Printf.printf "FFT output length: %d bins\n" (Array.length spectrum);
  Printf.printf "Dominant frequency bin: %d\n" (dominant_frequency spectrum);
  Printf.printf "Spectral centroid: %.2f\n\n" (spectral_centroid spectrum);

  (* Peaks *)
  let peaks = find_peaks ~threshold:5.0 spectrum in
  Printf.printf "Spectral peaks (above threshold 5.0):\n";
  List.iter (fun (bin, mag) ->
    let freq_hz = float_of_int bin *. float_of_int sr /. float_of_int (Array.length spectrum) in
    Printf.printf "  Bin %d (%.1f Hz): magnitude %.2f\n" bin freq_hz mag
  ) peaks;

  (* Roundtrip: IFFT(FFT(x)) ≈ x *)
  let recovered = ifft spectrum in
  let max_err = ref 0.0 in
  for i = 0 to Array.length mixed - 1 do
    let err = abs_float (mixed.(i) -. recovered.(i).re) in
    if err > !max_err then max_err := err
  done;
  Printf.printf "\nFFT→IFFT roundtrip max error: %.2e\n" !max_err;

  (* Convolution *)
  let kernel = [| 0.25; 0.5; 0.25 |] in
  let smoothed = convolve mixed kernel in
  Printf.printf "Convolution: %d samples * %d kernel → %d output\n"
    (Array.length mixed) (Array.length kernel) (Array.length smoothed);

  (* Waveform *)
  print_endline "\nFirst 64 samples (mixed signal):";
  let short = Array.sub mixed 0 (min 64 (Array.length mixed)) in
  print_waveform ~width:64 ~height:8 short;

  (* Window demo *)
  let win = hamming_window 8 in
  Printf.printf "\nHamming window (8 samples): [%s]\n"
    (String.concat "; " (Array.to_list (Array.map (Printf.sprintf "%.3f") win)));

  print_endline "\nDone."
