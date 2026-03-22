(* ============================================================================
 * Microbenchmark Framework for OCaml
 * ============================================================================
 *
 * A lightweight benchmarking framework that measures function performance
 * with statistical analysis. Features:
 *   - Automatic iteration count calibration
 *   - Mean, median, std deviation, min/max statistics
 *   - Comparison between multiple implementations
 *   - Warmup runs to stabilize caches
 *   - ASCII bar chart output
 *   - Parameterized benchmarks (vary input size)
 *
 * Usage:
 *   ocamlfind ocamlopt -package unix -linkpkg benchmark.ml -o benchmark
 *   ./benchmark
 *
 * Or interpreted:
 *   ocamlfind ocamlopt -package unix -linkpkg benchmark.ml -o benchmark && ./benchmark
 * ============================================================================ *)

(* --------------------------------------------------------------------------
 * Timer — high-resolution wall-clock via Unix.gettimeofday
 * -------------------------------------------------------------------------- *)
module Timer = struct
  let now () = Unix.gettimeofday ()

  let time_it f =
    let t0 = now () in
    let result = f () in
    let t1 = now () in
    (result, t1 -. t0)

  let time_seconds f =
    let (_, dt) = time_it f in
    dt
end

(* --------------------------------------------------------------------------
 * Statistics — compute summary stats from a list of floats
 * -------------------------------------------------------------------------- *)
module Stats = struct
  type t = {
    mean   : float;
    median : float;
    stddev : float;
    min_v  : float;
    max_v  : float;
    p5     : float;  (* 5th percentile *)
    p95    : float;  (* 95th percentile *)
    count  : int;
  }

  let sorted xs =
    let a = Array.of_list xs in
    Array.sort compare a;
    a

  let percentile arr p =
    let n = Array.length arr in
    if n = 0 then 0.0
    else
      let idx = (float_of_int (n - 1)) *. p in
      let lo = int_of_float (floor idx) in
      let hi = min (lo + 1) (n - 1) in
      let frac = idx -. float_of_int lo in
      arr.(lo) *. (1.0 -. frac) +. arr.(hi) *. frac

  let compute xs =
    let n = List.length xs in
    if n = 0 then {
      mean = 0.; median = 0.; stddev = 0.;
      min_v = 0.; max_v = 0.; p5 = 0.; p95 = 0.; count = 0
    }
    else
      let sum = List.fold_left (+.) 0.0 xs in
      let mean = sum /. float_of_int n in
      let variance =
        List.fold_left (fun acc x -> acc +. (x -. mean) *. (x -. mean)) 0.0 xs
        /. float_of_int n
      in
      let stddev = sqrt variance in
      let arr = sorted xs in
      let median = percentile arr 0.5 in
      let p5 = percentile arr 0.05 in
      let p95 = percentile arr 0.95 in
      {
        mean; median; stddev;
        min_v = arr.(0);
        max_v = arr.(Array.length arr - 1);
        p5; p95;
        count = n;
      }
end

(* --------------------------------------------------------------------------
 * Display helpers
 * -------------------------------------------------------------------------- *)
module Display = struct
  let format_duration secs =
    if secs < 1e-6 then Printf.sprintf "%.1f ns" (secs *. 1e9)
    else if secs < 1e-3 then Printf.sprintf "%.1f μs" (secs *. 1e6)
    else if secs < 1.0 then Printf.sprintf "%.2f ms" (secs *. 1e3)
    else Printf.sprintf "%.3f s" secs

  let bar_chart entries max_width =
    (* entries: (label, value) list *)
    let max_val = List.fold_left (fun acc (_, v) -> max acc v) 0.0 entries in
    let max_label =
      List.fold_left (fun acc (l, _) -> max acc (String.length l)) 0 entries
    in
    List.iter (fun (label, value) ->
      let bar_len =
        if max_val <= 0.0 then 0
        else int_of_float (value /. max_val *. float_of_int max_width)
      in
      let bar = String.make (max 1 bar_len) '#' in
      Printf.printf "  %-*s │ %s %s\n" max_label label bar (format_duration value)
    ) entries

  let print_stats name (s : Stats.t) =
    Printf.printf "  %-20s  mean=%s  median=%s  σ=%s  [%s .. %s]  n=%d\n"
      name
      (format_duration s.mean)
      (format_duration s.median)
      (format_duration s.stddev)
      (format_duration s.min_v)
      (format_duration s.max_v)
      s.count

  let separator () =
    Printf.printf "%s\n" (String.make 72 '─')
end

(* --------------------------------------------------------------------------
 * Benchmark engine
 * -------------------------------------------------------------------------- *)
module Bench = struct
  type config = {
    warmup_iters : int;
    min_samples  : int;
    max_samples  : int;
    min_time     : float;  (* minimum total benchmark time in seconds *)
  }

  let default_config = {
    warmup_iters = 5;
    min_samples  = 10;
    max_samples  = 200;
    min_time     = 1.0;
  }

  (* Run warmup to stabilize caches / JIT *)
  let warmup cfg f =
    for _ = 1 to cfg.warmup_iters do
      ignore (f ())
    done

  (* Calibrate: figure out how many inner iterations to get measurable time *)
  let calibrate f =
    let target = 0.001 in (* target ~1ms per sample *)
    let rec go iters =
      let t = Timer.time_seconds (fun () ->
        for _ = 1 to iters do ignore (f ()) done
      ) in
      if t >= target || iters >= 1_000_000 then
        (iters, t /. float_of_int iters)
      else
        go (iters * 10)
    in
    go 1

  (* Collect samples *)
  let measure cfg f =
    warmup cfg f;
    let (inner_iters, _) = calibrate f in
    let rec collect acc elapsed n =
      if n >= cfg.max_samples then acc
      else if n >= cfg.min_samples && elapsed >= cfg.min_time then acc
      else
        let t = Timer.time_seconds (fun () ->
          for _ = 1 to inner_iters do ignore (f ()) done
        ) in
        let per_iter = t /. float_of_int inner_iters in
        collect (per_iter :: acc) (elapsed +. t) (n + 1)
    in
    let samples = collect [] 0.0 0 in
    Stats.compute samples

  type bench_result = {
    name  : string;
    stats : Stats.t;
  }

  (* Run a single benchmark *)
  let run ?(config = default_config) name f =
    Printf.printf "  Benchmarking: %s..." name;
    flush stdout;
    let stats = measure config f in
    Printf.printf " done\n";
    { name; stats }

  (* Run a group of benchmarks and display comparison *)
  let group ?(config = default_config) group_name benchmarks =
    Printf.printf "\n";
    Display.separator ();
    Printf.printf "  Benchmark Group: %s\n" group_name;
    Display.separator ();
    let results = List.map (fun (name, f) ->
      run ~config name f
    ) benchmarks in
    Printf.printf "\n  Results:\n";
    List.iter (fun r -> Display.print_stats r.name r.stats) results;
    (* Bar chart *)
    Printf.printf "\n  Comparison (lower is better):\n";
    let entries = List.map (fun r -> (r.name, r.stats.mean)) results in
    Display.bar_chart entries 40;
    (* Fastest *)
    (match results with
     | [] -> ()
     | _ ->
       let fastest = List.fold_left (fun best r ->
         if r.stats.mean < best.stats.mean then r else best
       ) (List.hd results) results in
       let slowest = List.fold_left (fun worst r ->
         if r.stats.mean > worst.stats.mean then r else worst
       ) (List.hd results) results in
       if List.length results > 1 then
         Printf.printf "\n  Winner: %s (%.1fx faster than %s)\n"
           fastest.name
           (slowest.stats.mean /. fastest.stats.mean)
           slowest.name);
    results

  (* Parameterized benchmark — run the same function with varying input sizes *)
  let parametric ?(config = default_config) name sizes make_fn =
    Printf.printf "\n";
    Display.separator ();
    Printf.printf "  Parametric Benchmark: %s\n" name;
    Display.separator ();
    let results = List.map (fun size ->
      let f = make_fn size in
      let label = Printf.sprintf "n=%d" size in
      run ~config label f
    ) sizes in
    Printf.printf "\n  Scaling:\n";
    List.iter (fun r -> Display.print_stats r.name r.stats) results;
    Printf.printf "\n  Time vs Size:\n";
    let entries = List.map (fun r -> (r.name, r.stats.mean)) results in
    Display.bar_chart entries 40;
    (* Show scaling factor between consecutive sizes *)
    let rec show_scaling = function
      | a :: (b :: _ as rest) ->
        if a.stats.mean > 0.0 then
          Printf.printf "  %s → %s: %.2fx\n"
            a.name b.name (b.stats.mean /. a.stats.mean);
        show_scaling rest
      | _ -> ()
    in
    show_scaling results;
    results
end

(* ============================================================================
 * Demo benchmarks
 * ============================================================================ *)

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
  let rec sort a lo hi =
    if hi - lo <= 1 then ()
    else
      let mid = lo + (hi - lo) / 2 in
      sort a lo mid;
      sort a mid hi;
      let left = Array.sub a lo (mid - lo) in
      let right = Array.sub a mid (hi - mid) in
      let i = ref 0 and j = ref 0 and k = ref lo in
      while !i < Array.length left && !j < Array.length right do
        if left.(!i) <= right.(!j) then
          (a.(!k) <- left.(!i); incr i)
        else
          (a.(!k) <- right.(!j); incr j);
        incr k
      done;
      while !i < Array.length left do
        a.(!k) <- left.(!i); incr i; incr k
      done;
      while !j < Array.length right do
        a.(!k) <- right.(!j); incr j; incr k
      done
  in
  let a = Array.copy arr in
  sort a 0 (Array.length a);
  a

(* --- Data structure operations --- *)
let list_rev_manual lst =
  let rec go acc = function
    | [] -> acc
    | x :: xs -> go (x :: acc) xs
  in
  go [] lst

(* --- String operations --- *)
let string_concat_naive n =
  let s = ref "" in
  for _ = 1 to n do
    s := !s ^ "x"
  done;
  !s

let string_concat_buffer n =
  let buf = Buffer.create n in
  for _ = 1 to n do
    Buffer.add_char buf 'x'
  done;
  Buffer.contents buf

(* --- Hash table vs Map --- *)
module IntMap = Map.Make(Int)

let hashtbl_insert n =
  let tbl = Hashtbl.create n in
  for i = 0 to n - 1 do
    Hashtbl.replace tbl i i
  done;
  tbl

let map_insert n =
  let m = ref IntMap.empty in
  for i = 0 to n - 1 do
    m := IntMap.add i i !m
  done;
  !m

(* --- Fibonacci --- *)
let rec fib_naive n =
  if n <= 1 then n
  else fib_naive (n - 1) + fib_naive (n - 2)

let fib_tail n =
  let rec go a b i =
    if i = 0 then a
    else go b (a + b) (i - 1)
  in
  go 0 1 n

(* ============================================================================
 * Main — run all demo benchmarks
 * ============================================================================ *)
let () =
  Printf.printf "\n";
  Printf.printf "  ╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "  ║     OCaml Microbenchmark Framework — Demo Suite         ║\n";
  Printf.printf "  ╚══════════════════════════════════════════════════════════╝\n";

  (* 1. Sorting comparison *)
  let n = 1000 in
  let data = Array.init n (fun _ -> Random.int 10000) in
  ignore (Bench.group "Sorting (n=1000)"
    [ ("Insertion Sort", fun () -> insertion_sort data);
      ("Merge Sort",     fun () -> merge_sort data);
      ("Array.sort",     fun () -> let a = Array.copy data in Array.sort compare a; a);
    ]);

  (* 2. String concatenation *)
  ignore (Bench.group "String Concat (n=500)"
    [ ("Naive (^)",  fun () -> string_concat_naive 500);
      ("Buffer",     fun () -> string_concat_buffer 500);
    ]);

  (* 3. Fibonacci *)
  ignore (Bench.group "Fibonacci(25)"
    [ ("Naive recursive", fun () -> fib_naive 25);
      ("Tail recursive",  fun () -> fib_tail 25);
    ]);

  (* 4. List reversal *)
  let big_list = List.init 10000 (fun i -> i) in
  ignore (Bench.group "List Reverse (n=10000)"
    [ ("Manual tail-rec", fun () -> list_rev_manual big_list);
      ("List.rev",        fun () -> List.rev big_list);
    ]);

  (* 5. Map vs Hashtbl *)
  ignore (Bench.group "Map vs Hashtbl Insert (n=1000)"
    [ ("Hashtbl", fun () -> hashtbl_insert 1000);
      ("IntMap",  fun () -> map_insert 1000);
    ]);

  (* 6. Parametric: sorting scaling *)
  ignore (Bench.parametric "Array.sort Scaling"
    [100; 500; 1000; 5000; 10000]
    (fun n ->
      let data = Array.init n (fun _ -> Random.int 100000) in
      fun () -> let a = Array.copy data in Array.sort compare a; a));

  Printf.printf "\n  Done! All benchmarks complete.\n\n"
