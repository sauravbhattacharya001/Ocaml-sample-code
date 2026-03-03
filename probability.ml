(* Probability Monad & Monte Carlo Simulation                              *)
(* ═══════════════════════════════════════════════════════════════════════ *)
(* Demonstrates monadic programming in OCaml through a probabilistic DSL. *)
(* Features:                                                               *)
(*   • Probability monad with bind, return, map, join                     *)
(*   • Common distributions: uniform, bernoulli, normal, exponential,     *)
(*     poisson, geometric, binomial                                       *)
(*   • Monte Carlo integration and Pi estimation                          *)
(*   • Statistical analysis: mean, variance, stddev, percentiles, CI      *)
(*   • Histogram rendering for terminal visualization                     *)
(*   • Composable probabilistic programs via monadic style                *)
(*   • Markov chain simulation with stationary distribution              *)
(*   • Bayesian inference via rejection sampling                          *)

(* ── Random state ─────────────────────────────────────────────────── *)

(* Seed the PRNG for reproducibility in tests *)
let seed rng_seed = Random.init rng_seed
let () = Random.self_init ()

(* ── Probability Monad ────────────────────────────────────────────── *)

(* A probabilistic computation is a function from unit to a sampled value.
   This is the simplest representation — a "sampling monad" where each
   invocation draws a fresh sample. *)

type 'a dist = unit -> 'a

(* Monadic return: a distribution that always produces the same value *)
let return (x : 'a) : 'a dist = fun () -> x

(* Monadic bind: sample from d, then feed the result to f *)
let bind (d : 'a dist) (f : 'a -> 'b dist) : 'b dist =
  fun () ->
    let x = d () in
    (f x) ()

(* Infix bind operator *)
let ( >>= ) = bind

(* Map: apply a pure function to a distribution *)
let map (f : 'a -> 'b) (d : 'a dist) : 'b dist =
  fun () -> f (d ())

(* Infix map operator *)
let ( <$> ) = map

(* Applicative apply: combine two distributions *)
let apply (df : ('a -> 'b) dist) (da : 'a dist) : 'b dist =
  fun () ->
    let f = df () in
    let a = da () in
    f a

let ( <*> ) = apply

(* Join: flatten nested distributions *)
let join (dd : 'a dist dist) : 'a dist =
  fun () -> (dd ()) ()

(* Conditional: if-then-else in the probability monad *)
let if_dist (cond : bool dist) (then_d : 'a dist) (else_d : 'a dist) : 'a dist =
  cond >>= fun b -> if b then then_d else else_d

(* ── Primitive Distributions ──────────────────────────────────────── *)

(* Uniform float in [lo, hi) *)
let uniform (lo : float) (hi : float) : float dist =
  fun () -> lo +. Random.float (hi -. lo)

(* Uniform integer in [lo, hi] inclusive *)
let uniform_int (lo : int) (hi : int) : int dist =
  fun () -> lo + Random.int (hi - lo + 1)

(* Bernoulli: true with probability p *)
let bernoulli (p : float) : bool dist =
  fun () -> Random.float 1.0 < p

(* Coin flip: fair bernoulli *)
let coin : bool dist = bernoulli 0.5

(* Discrete: choose from weighted options.
   Weights are automatically normalized. *)
let discrete (choices : ('a * float) list) : 'a dist =
  let total = List.fold_left (fun acc (_, w) -> acc +. w) 0.0 choices in
  if total <= 0.0 then failwith "discrete: total weight must be positive";
  fun () ->
    let r = Random.float total in
    let rec pick cumulative = function
      | [] -> fst (List.hd choices) (* fallback — shouldn't happen *)
      | (x, w) :: rest ->
        let cumulative' = cumulative +. w in
        if r < cumulative' then x
        else pick cumulative' rest
    in
    pick 0.0 choices

(* Normal distribution using Box-Muller transform *)
let normal (mu : float) (sigma : float) : float dist =
  fun () ->
    let u1 = Random.float 1.0 in
    let u2 = Random.float 1.0 in
    (* Avoid log(0) *)
    let u1 = if u1 < 1e-15 then 1e-15 else u1 in
    let z = sqrt (-2.0 *. log u1) *. cos (2.0 *. Float.pi *. u2) in
    mu +. sigma *. z

(* Standard normal: mean=0, stddev=1 *)
let standard_normal : float dist = normal 0.0 1.0

(* Exponential distribution with rate parameter lambda *)
let exponential (lambda : float) : float dist =
  if lambda <= 0.0 then failwith "exponential: lambda must be positive";
  fun () ->
    let u = Random.float 1.0 in
    let u = if u < 1e-15 then 1e-15 else u in
    -. (log u) /. lambda

(* Poisson distribution using Knuth's algorithm *)
let poisson (lambda : float) : int dist =
  if lambda <= 0.0 then failwith "poisson: lambda must be positive";
  fun () ->
    let l = exp (-.lambda) in
    let rec loop k p =
      if p < l then k - 1
      else loop (k + 1) (p *. Random.float 1.0)
    in
    loop 0 1.0

(* Geometric distribution: number of trials until first success *)
let geometric (p : float) : int dist =
  if p <= 0.0 || p > 1.0 then failwith "geometric: p must be in (0, 1]";
  fun () ->
    let rec loop count =
      if Random.float 1.0 < p then count
      else loop (count + 1)
    in
    loop 1

(* Binomial distribution: number of successes in n trials *)
let binomial (n : int) (p : float) : int dist =
  if n < 0 then failwith "binomial: n must be non-negative";
  if p < 0.0 || p > 1.0 then failwith "binomial: p must be in [0, 1]";
  fun () ->
    let count = ref 0 in
    for _ = 1 to n do
      if Random.float 1.0 < p then incr count
    done;
    !count

(* ── Sampling ─────────────────────────────────────────────────────── *)

(* Draw a single sample *)
let sample (d : 'a dist) : 'a = d ()

(* Draw n samples *)
let samples (n : int) (d : 'a dist) : 'a list =
  List.init n (fun _ -> d ())

(* Draw n samples into an array (more efficient for large n) *)
let sample_array (n : int) (d : 'a dist) : 'a array =
  Array.init n (fun _ -> d ())

(* ── Statistics ───────────────────────────────────────────────────── *)

(* Mean of float samples *)
let mean (xs : float array) : float =
  let n = Array.length xs in
  if n = 0 then 0.0
  else
    let sum = Array.fold_left ( +. ) 0.0 xs in
    sum /. float_of_int n

(* Variance (population) *)
let variance (xs : float array) : float =
  let n = Array.length xs in
  if n <= 1 then 0.0
  else
    let m = mean xs in
    let sum_sq = Array.fold_left (fun acc x -> acc +. (x -. m) ** 2.0) 0.0 xs in
    sum_sq /. float_of_int n

(* Standard deviation *)
let stddev (xs : float array) : float = sqrt (variance xs)

(* Minimum and maximum *)
let min_max (xs : float array) : float * float =
  if Array.length xs = 0 then (0.0, 0.0)
  else
    Array.fold_left
      (fun (lo, hi) x -> (min lo x, max hi x))
      (xs.(0), xs.(0)) xs

(* Percentile (linear interpolation) *)
let percentile (xs : float array) (p : float) : float =
  let n = Array.length xs in
  if n = 0 then 0.0
  else begin
    let sorted = Array.copy xs in
    Array.sort compare sorted;
    let idx = p *. float_of_int (n - 1) in
    let lo = int_of_float (floor idx) in
    let hi = min (lo + 1) (n - 1) in
    let frac = idx -. float_of_int lo in
    sorted.(lo) *. (1.0 -. frac) +. sorted.(hi) *. frac
  end

(* Median *)
let median (xs : float array) : float = percentile xs 0.5

(* Confidence interval using normal approximation *)
let confidence_interval (xs : float array) (confidence : float) : float * float * float =
  let n = Array.length xs in
  if n = 0 then (0.0, 0.0, 0.0)
  else
    let m = mean xs in
    let s = stddev xs in
    (* z-score for common confidence levels *)
    let z = match confidence with
      | c when abs_float (c -. 0.90) < 0.001 -> 1.645
      | c when abs_float (c -. 0.95) < 0.001 -> 1.960
      | c when abs_float (c -. 0.99) < 0.001 -> 2.576
      | _ -> 1.960 (* default to 95% *)
    in
    let margin = z *. s /. sqrt (float_of_int n) in
    (m, m -. margin, m +. margin)

(* Summary statistics *)
type summary = {
  count : int;
  s_mean : float;
  s_stddev : float;
  s_min : float;
  s_max : float;
  s_median : float;
  p25 : float;
  p75 : float;
  ci95_lo : float;
  ci95_hi : float;
}

let summarize (xs : float array) : summary =
  let lo, hi = min_max xs in
  let m, ci_lo, ci_hi = confidence_interval xs 0.95 in
  {
    count = Array.length xs;
    s_mean = m;
    s_stddev = stddev xs;
    s_min = lo;
    s_max = hi;
    s_median = median xs;
    p25 = percentile xs 0.25;
    p75 = percentile xs 0.75;
    ci95_lo = ci_lo;
    ci95_hi = ci_hi;
  }

let print_summary (s : summary) : unit =
  Printf.printf "  n       = %d\n" s.count;
  Printf.printf "  mean    = %.4f\n" s.s_mean;
  Printf.printf "  stddev  = %.4f\n" s.s_stddev;
  Printf.printf "  min     = %.4f\n" s.s_min;
  Printf.printf "  max     = %.4f\n" s.s_max;
  Printf.printf "  median  = %.4f\n" s.s_median;
  Printf.printf "  Q1      = %.4f\n" s.p25;
  Printf.printf "  Q3      = %.4f\n" s.p75;
  Printf.printf "  95%% CI  = [%.4f, %.4f]\n" s.ci95_lo s.ci95_hi

(* ── Histogram ────────────────────────────────────────────────────── *)

(* Render a simple ASCII histogram *)
let histogram ?(bins=20) ?(width=50) (xs : float array) : string =
  let n = Array.length xs in
  if n = 0 then "(empty)"
  else
    let lo, hi = min_max xs in
    let range = hi -. lo in
    if range < 1e-15 then
      Printf.sprintf "[all values = %.4f] count=%d" lo n
    else
      let bin_width = range /. float_of_int bins in
      let counts = Array.make bins 0 in
      Array.iter (fun x ->
        let idx = int_of_float ((x -. lo) /. bin_width) in
        let idx = min idx (bins - 1) in  (* clamp last value *)
        counts.(idx) <- counts.(idx) + 1
      ) xs;
      let max_count = Array.fold_left max 0 counts in
      let buf = Buffer.create 256 in
      for i = 0 to bins - 1 do
        let lo_edge = lo +. float_of_int i *. bin_width in
        let bar_len =
          if max_count > 0
          then counts.(i) * width / max_count
          else 0
        in
        let bar = String.make bar_len '#' in
        Buffer.add_string buf
          (Printf.sprintf "%8.3f |%-*s| %d\n" lo_edge width bar counts.(i))
      done;
      Buffer.contents buf

(* ── Monte Carlo Methods ──────────────────────────────────────────── *)

(* Estimate Pi by counting random points inside the unit circle.
   Points are sampled uniformly from [0,1)×[0,1) and we check
   if x²+y² < 1. The ratio ≈ π/4. *)
let estimate_pi (n : int) : float =
  let inside = ref 0 in
  for _ = 1 to n do
    let x = Random.float 1.0 in
    let y = Random.float 1.0 in
    if x *. x +. y *. y < 1.0 then incr inside
  done;
  4.0 *. float_of_int !inside /. float_of_int n

(* Monte Carlo integration: estimate ∫[a,b] f(x) dx
   by sampling uniformly and averaging f(x) * (b - a). *)
let integrate (f : float -> float) (a : float) (b : float) (n : int) : float =
  let sum = ref 0.0 in
  for _ = 1 to n do
    let x = a +. Random.float (b -. a) in
    sum := !sum +. f x
  done;
  (b -. a) *. !sum /. float_of_int n

(* Monte Carlo integration with variance estimation *)
let integrate_with_error (f : float -> float) (a : float) (b : float) (n : int) : float * float =
  let xs = Array.init n (fun _ ->
    let x = a +. Random.float (b -. a) in
    f x
  ) in
  let m = mean xs in
  let s = stddev xs in
  let integral = (b -. a) *. m in
  let error = (b -. a) *. s /. sqrt (float_of_int n) in
  (integral, error)

(* ── Markov Chain ─────────────────────────────────────────────────── *)

(* A Markov chain with n states and an n×n transition matrix.
   transition.(i).(j) = P(next = j | current = i). *)
type markov_chain = {
  n_states : int;
  transition : float array array;
}

(* Validate that each row sums to ~1.0 *)
let validate_chain (mc : markov_chain) : bool =
  Array.for_all (fun row ->
    let s = Array.fold_left ( +. ) 0.0 row in
    abs_float (s -. 1.0) < 1e-6
  ) mc.transition

(* Create a Markov chain from a transition matrix *)
let make_chain (matrix : float array array) : markov_chain =
  let n = Array.length matrix in
  if n = 0 then failwith "make_chain: empty matrix";
  Array.iter (fun row ->
    if Array.length row <> n then failwith "make_chain: non-square matrix"
  ) matrix;
  let mc = { n_states = n; transition = matrix } in
  if not (validate_chain mc) then failwith "make_chain: rows must sum to 1.0";
  mc

(* Sample the next state given current state *)
let next_state (mc : markov_chain) (state : int) : int =
  let r = Random.float 1.0 in
  let row = mc.transition.(state) in
  let rec pick cumul i =
    if i >= mc.n_states then mc.n_states - 1
    else
      let cumul' = cumul +. row.(i) in
      if r < cumul' then i
      else pick cumul' (i + 1)
  in
  pick 0.0 0

(* Simulate a chain for n steps, returning the state sequence *)
let simulate_chain (mc : markov_chain) (start : int) (n : int) : int list =
  let rec loop state steps acc =
    if steps = 0 then List.rev (state :: acc)
    else
      let next = next_state mc state in
      loop next (steps - 1) (state :: acc)
  in
  loop start n []

(* Estimate stationary distribution by running the chain and counting visits *)
let estimate_stationary (mc : markov_chain) ?(burn_in=1000) (n : int) : float array =
  let counts = Array.make mc.n_states 0 in
  let state = ref (Random.int mc.n_states) in
  (* Burn-in: discard initial samples *)
  for _ = 1 to burn_in do
    state := next_state mc !state
  done;
  (* Collect samples *)
  for _ = 1 to n do
    state := next_state mc !state;
    counts.(!state) <- counts.(!state) + 1
  done;
  Array.map (fun c -> float_of_int c /. float_of_int n) counts

(* ── Bayesian Inference (Rejection Sampling) ──────────────────────── *)

(* Rejection sampling: given a prior distribution and a likelihood function
   (which returns true if the observation is consistent with the parameter),
   sample from the posterior distribution. *)
let rejection_sample
    (prior : 'a dist)
    (likelihood : 'a -> bool)
    (n : int)
  : 'a list =
  let results = ref [] in
  let accepted = ref 0 in
  while !accepted < n do
    let theta = prior () in
    if likelihood theta then begin
      results := theta :: !results;
      incr accepted
    end
  done;
  List.rev !results

(* ── Composable Examples ──────────────────────────────────────────── *)

(* Simulate rolling n dice and summing the results *)
let dice_sum (n : int) : int dist =
  let single_die = uniform_int 1 6 in
  fun () ->
    let total = ref 0 in
    for _ = 1 to n do
      total := !total + single_die ()
    done;
    !total

(* Random walk: starting at 0, each step is +1 or -1 with equal probability *)
let random_walk (steps : int) : int dist =
  fun () ->
    let pos = ref 0 in
    for _ = 1 to steps do
      if (coin ()) then incr pos else decr pos
    done;
    !pos

(* Birthday paradox: how many people until a birthday collision? *)
let birthday_collision : int dist =
  fun () ->
    let seen = Hashtbl.create 50 in
    let rec loop n =
      let day = Random.int 365 in
      if Hashtbl.mem seen day then n
      else begin
        Hashtbl.replace seen day ();
        loop (n + 1)
      end
    in
    loop 1

(* Gambler's ruin: start with $start, bet $1 each round.
   Win with probability p. Game ends at $0 (ruin) or $goal. *)
let gamblers_ruin (start : int) (goal : int) (p : float) : bool dist =
  fun () ->
    let money = ref start in
    while !money > 0 && !money < goal do
      if Random.float 1.0 < p then incr money else decr money
    done;
    !money >= goal  (* true = reached goal *)

(* ── Tests ────────────────────────────────────────────────────────── *)

let () =
  let pass = ref 0 in
  let fail = ref 0 in
  let total = ref 0 in

  let check name cond =
    incr total;
    if cond then begin
      incr pass;
      Printf.printf "  ✓ %s\n" name
    end else begin
      incr fail;
      Printf.printf "  ✗ %s\n" name
    end
  in

  let section name =
    Printf.printf "\n── %s ──\n" name
  in

  (* Use fixed seed for reproducibility *)
  seed 42;

  (* ── Monad laws ── *)
  section "Monad Laws";

  (* Left identity: return x >>= f  ≡  f x *)
  seed 42;
  let lhs = (return 5 >>= fun x -> return (x * 2)) () in
  seed 42;
  let rhs = (return (5 * 2)) () in
  check "left identity" (lhs = rhs);

  (* Right identity: m >>= return  ≡  m *)
  seed 42;
  let m = uniform 0.0 1.0 in
  let lhs2 = (m >>= return) () in
  seed 42;
  let rhs2 = m () in
  check "right identity" (abs_float (lhs2 -. rhs2) < 1e-15);

  (* Associativity: (m >>= f) >>= g  ≡  m >>= (fun x -> f x >>= g) *)
  let f x = return (x + 1) in
  let g x = return (x * 3) in
  seed 42;
  let lhs3 = ((return 7 >>= f) >>= g) () in
  seed 42;
  let rhs3 = (return 7 >>= (fun x -> f x >>= g)) () in
  check "associativity" (lhs3 = rhs3);

  (* ── Map and Apply ── *)
  section "Functor and Applicative";

  seed 42;
  let doubled = ((fun x -> x * 2) <$> uniform_int 1 6) () in
  check "map produces valid range" (doubled >= 2 && doubled <= 12);

  seed 42;
  let added = (return ( + ) <*> uniform_int 0 5 <*> uniform_int 0 5) () in
  check "apply combines distributions" (added >= 0 && added <= 10);

  check "join flattens" (
    seed 42;
    let nested = return (return 42) in
    (join nested) () = 42
  );

  (* ── Distributions ── *)
  section "Uniform Distribution";

  seed 42;
  let u_samples = sample_array 10000 (uniform 2.0 5.0) in
  let u_mean = mean u_samples in
  check "uniform mean ≈ 3.5" (abs_float (u_mean -. 3.5) < 0.1);
  let u_lo, u_hi = min_max u_samples in
  check "uniform min ≥ 2.0" (u_lo >= 2.0);
  check "uniform max < 5.0" (u_hi < 5.0);

  section "Normal Distribution";

  seed 42;
  let n_samples = sample_array 10000 (normal 10.0 2.0) in
  let n_stats = summarize n_samples in
  check "normal mean ≈ 10.0" (abs_float (n_stats.s_mean -. 10.0) < 0.1);
  check "normal stddev ≈ 2.0" (abs_float (n_stats.s_stddev -. 2.0) < 0.2);

  section "Bernoulli Distribution";

  seed 42;
  let b_samples = sample_array 10000 (bernoulli 0.3) in
  let b_true = Array.fold_left (fun acc x -> if x then acc + 1 else acc) 0 b_samples in
  let b_rate = float_of_int b_true /. 10000.0 in
  check "bernoulli(0.3) rate ≈ 0.3" (abs_float (b_rate -. 0.3) < 0.03);

  section "Exponential Distribution";

  seed 42;
  let exp_samples = sample_array 10000 (exponential 0.5) in
  let exp_mean = mean exp_samples in
  check "exponential(0.5) mean ≈ 2.0" (abs_float (exp_mean -. 2.0) < 0.2);

  section "Poisson Distribution";

  seed 42;
  let pois_samples = sample_array 10000 (poisson 5.0) in
  let pois_mean = mean (Array.map float_of_int pois_samples) in
  check "poisson(5) mean ≈ 5.0" (abs_float (pois_mean -. 5.0) < 0.2);

  section "Geometric Distribution";

  seed 42;
  let geo_samples = sample_array 10000 (geometric 0.25) in
  let geo_mean = mean (Array.map float_of_int geo_samples) in
  check "geometric(0.25) mean ≈ 4.0" (abs_float (geo_mean -. 4.0) < 0.3);

  section "Binomial Distribution";

  seed 42;
  let bin_samples = sample_array 10000 (binomial 20 0.3) in
  let bin_mean = mean (Array.map float_of_int bin_samples) in
  check "binomial(20, 0.3) mean ≈ 6.0" (abs_float (bin_mean -. 6.0) < 0.2);

  section "Discrete Distribution";

  seed 42;
  let die = discrete [("one", 1.0); ("two", 1.0); ("three", 1.0);
                       ("four", 1.0); ("five", 1.0); ("six", 1.0)] in
  let d_samples = sample_array 6000 die in
  let ones = Array.fold_left (fun acc x -> if x = "one" then acc + 1 else acc) 0 d_samples in
  let one_rate = float_of_int ones /. 6000.0 in
  check "discrete die each face ≈ 1/6" (abs_float (one_rate -. (1.0 /. 6.0)) < 0.03);

  (* ── Statistics ── *)
  section "Statistics Functions";

  let xs = [| 1.0; 2.0; 3.0; 4.0; 5.0 |] in
  check "mean of [1..5] = 3" (abs_float (mean xs -. 3.0) < 1e-10);
  check "variance of [1..5] = 2" (abs_float (variance xs -. 2.0) < 1e-10);
  check "median of [1..5] = 3" (abs_float (median xs -. 3.0) < 1e-10);
  check "percentile 0.0 = min" (abs_float (percentile xs 0.0 -. 1.0) < 1e-10);
  check "percentile 1.0 = max" (abs_float (percentile xs 1.0 -. 5.0) < 1e-10);

  let m, lo, hi = confidence_interval xs 0.95 in
  check "CI contains mean" (lo <= m && m <= hi);
  check "CI lower < upper" (lo < hi);

  check "empty array mean = 0" (mean [||] = 0.0);
  check "single element variance = 0" (variance [| 42.0 |] = 0.0);

  let summary = summarize [| 10.0; 20.0; 30.0; 40.0; 50.0 |] in
  check "summary count = 5" (summary.count = 5);
  check "summary mean = 30" (abs_float (summary.s_mean -. 30.0) < 1e-10);
  check "summary min = 10" (abs_float (summary.s_min -. 10.0) < 1e-10);
  check "summary max = 50" (abs_float (summary.s_max -. 50.0) < 1e-10);

  (* ── Histogram ── *)
  section "Histogram";

  let hist = histogram ~bins:5 ~width:30 [| 1.0; 1.5; 2.0; 2.5; 3.0; 3.5; 4.0 |] in
  check "histogram is non-empty" (String.length hist > 0);
  check "histogram contains bins" (String.contains hist '|');
  check "empty histogram" (histogram [||] = "(empty)");
  check "constant histogram" (String.length (histogram [| 5.0; 5.0; 5.0 |]) > 0);

  (* ── Monte Carlo ── *)
  section "Monte Carlo Methods";

  seed 42;
  let pi_est = estimate_pi 100000 in
  check "Pi estimate ≈ 3.14" (abs_float (pi_est -. Float.pi) < 0.02);

  (* ∫[0,1] x² dx = 1/3 *)
  seed 42;
  let integral = integrate (fun x -> x *. x) 0.0 1.0 100000 in
  check "∫x² dx ≈ 1/3" (abs_float (integral -. (1.0 /. 3.0)) < 0.01);

  seed 42;
  let integral2, error = integrate_with_error (fun x -> x *. x) 0.0 1.0 10000 in
  check "integral with error is close" (abs_float (integral2 -. (1.0 /. 3.0)) < 0.02);
  check "error estimate is positive" (error > 0.0);

  (* ── Markov Chain ── *)
  section "Markov Chain";

  let weather = make_chain [|
    [| 0.7; 0.3 |];  (* sunny → sunny=70%, rainy=30% *)
    [| 0.4; 0.6 |];  (* rainy → sunny=40%, rainy=60% *)
  |] in
  check "chain validation passes" (validate_chain weather);

  seed 42;
  let path = simulate_chain weather 0 10 in
  check "chain path has 11 elements" (List.length path = 11);
  check "chain path starts at 0" (List.hd path = 0);
  check "chain states in range" (List.for_all (fun s -> s >= 0 && s < 2) path);

  seed 42;
  let stationary = estimate_stationary weather ~burn_in:500 50000 in
  (* Analytic: P(sunny) = 4/7 ≈ 0.571, P(rainy) = 3/7 ≈ 0.429 *)
  check "stationary sunny ≈ 4/7" (abs_float (stationary.(0) -. (4.0 /. 7.0)) < 0.02);
  check "stationary rainy ≈ 3/7" (abs_float (stationary.(1) -. (3.0 /. 7.0)) < 0.02);

  check "invalid chain detected" (
    try
      let _ = make_chain [| [| 0.5; 0.3 |]; [| 0.4; 0.6 |] |] in false
    with Failure _ -> true
  );

  (* ── Rejection Sampling ── *)
  section "Bayesian Inference (Rejection Sampling)";

  (* Example: estimate the bias of a coin given observed flips.
     Prior: uniform(0, 1) for the bias.
     Observation: 7 heads out of 10 flips.
     Posterior should peak near 0.7. *)
  seed 42;
  let posterior = rejection_sample
    (uniform 0.0 1.0)
    (fun p ->
      (* Simulate 10 flips with bias p and check if we get 7 heads *)
      let heads = ref 0 in
      for _ = 1 to 10 do
        if Random.float 1.0 < p then incr heads
      done;
      !heads = 7)
    1000
  in
  let post_mean = mean (Array.of_list posterior) in
  check "posterior mean ≈ 0.7 (coin bias)" (abs_float (post_mean -. 0.7) < 0.1);

  (* ── Composable Programs ── *)
  section "Composable Probabilistic Programs";

  seed 42;
  let ds = samples 1000 (dice_sum 3) in
  let ds_mean = mean (Array.of_list (List.map float_of_int ds)) in
  check "3d6 mean ≈ 10.5" (abs_float (ds_mean -. 10.5) < 0.5);
  check "3d6 range [3, 18]" (
    List.for_all (fun x -> x >= 3 && x <= 18) ds
  );

  seed 42;
  let walks = sample_array 10000 (map float_of_int (random_walk 100)) in
  let walk_mean = mean walks in
  check "random walk mean ≈ 0" (abs_float walk_mean < 1.0);

  seed 42;
  let collisions = sample_array 5000 (map float_of_int birthday_collision) in
  let bday_mean = mean collisions in
  (* Expected: ~24.6 people for a collision *)
  check "birthday paradox mean ≈ 24-25" (bday_mean > 22.0 && bday_mean < 27.0);

  seed 42;
  let wins = sample_array 5000 (gamblers_ruin 50 100 0.5) in
  let win_rate = mean (Array.map (fun b -> if b then 1.0 else 0.0) wins) in
  (* With fair odds: P(reach $100 | start=$50) = 0.5 *)
  check "gambler's ruin fair game win rate ≈ 0.5" (abs_float (win_rate -. 0.5) < 0.03);

  (* ── If-Dist ── *)
  section "Conditional Distribution";

  seed 42;
  let weather_bonus =
    if_dist (bernoulli 0.7)
      (return 100.0)   (* sunny: $100 *)
      (return 20.0)    (* rainy: $20 *)
  in
  let wb_samples = sample_array 10000 weather_bonus in
  let wb_mean = mean wb_samples in
  (* Expected: 0.7 * 100 + 0.3 * 20 = 76 *)
  check "conditional mean ≈ 76" (abs_float (wb_mean -. 76.0) < 2.0);

  (* ── Summary ── *)
  Printf.printf "\n══════════════════════════════════════\n";
  Printf.printf "Results: %d/%d passed" !pass !total;
  if !fail > 0 then Printf.printf " (%d FAILED)" !fail;
  Printf.printf "\n══════════════════════════════════════\n";

  (* Demo: show a histogram *)
  Printf.printf "\n── Demo: Normal(0, 1) Histogram ──\n";
  seed 42;
  let demo_samples = sample_array 5000 standard_normal in
  Printf.printf "%s\n" (histogram ~bins:15 ~width:40 demo_samples);

  Printf.printf "── Demo: Summary Statistics ──\n";
  print_summary (summarize demo_samples);

  Printf.printf "\n── Demo: Pi Estimate ──\n";
  seed 42;
  Printf.printf "  π ≈ %.6f (100k samples)\n" (estimate_pi 100000);

  if !fail > 0 then exit 1
