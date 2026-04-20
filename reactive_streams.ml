(* Reactive Stream Processor
   ========================
   Functional Reactive Programming (FRP) with event streams, combinators,
   backpressure, windowing, and an interactive REPL.

   Features:
   - Event streams with typed payloads (Int, Float, String, Bool, List, Record)
   - 15+ stream combinators: map, filter, scan, merge, zip, flatMap, take, drop,
     throttle, debounce, buffer, window, distinct, groupBy, sample
   - Backpressure strategies: Drop, Buffer, LatestOnly
   - Time-windowed aggregation (tumbling & sliding windows)
   - Stream topology visualization (ASCII DAG)
   - Built-in sources: counter, random, sine, fibonacci, csv
   - Sinks: print, count, sum, avg, histogram, collect, file
   - Interactive REPL with pipeline DSL

   Usage: ocamlfind ocamlopt -package unix -linkpkg reactive_streams.ml -o reactive_streams
          (or just: ocaml reactive_streams.ml for bytecode)

   REPL commands:
     source counter 1 10        -- integers 1..10
     source random 100 20       -- 20 random ints 0..99
     source sine 0.1 50         -- 50 sine samples, step=0.1
     source fib 15              -- first 15 fibonacci numbers
     source csv "data.csv"      -- load CSV as record stream
     source words "hello world" -- word stream from text

     pipe map (*2)              -- double each value
     pipe filter (>5)           -- keep values > 5
     pipe scan (+) 0            -- running sum
     pipe take 10               -- first 10 elements
     pipe drop 5                -- skip first 5
     pipe distinct              -- remove consecutive duplicates
     pipe buffer 3              -- group into chunks of 3
     pipe window tumbling 5     -- tumbling window of size 5
     pipe window sliding 3 1    -- sliding window size=3 step=1
     pipe throttle 2            -- keep every 2nd element
     pipe flatmap split         -- split strings into chars
     pipe groupby mod3          -- group by value mod 3

     sink print                 -- print each event
     sink count                 -- count events
     sink sum                   -- sum numeric events
     sink avg                   -- average of numeric events
     sink histogram 5           -- ASCII histogram with 5 bins
     sink collect               -- collect into list
     sink stats                 -- min/max/mean/stddev

     run                        -- execute the pipeline
     show                       -- show pipeline topology (ASCII DAG)
     reset                      -- clear pipeline
     merge                      -- merge last two sources
     zip                        -- zip last two sources
     demo <name>                -- run a built-in demo
     help                       -- show commands
     quit                       -- exit
*)

(* ===== Value Types ===== *)
type value =
  | VInt of int
  | VFloat of float
  | VString of string
  | VBool of bool
  | VList of value list
  | VRecord of (string * value) list
  | VNone

let value_to_string = function
  | VInt n -> string_of_int n
  | VFloat f -> Printf.sprintf "%.4f" f
  | VString s -> s
  | VBool b -> string_of_bool b
  | VList vs ->
    let inner = List.map (function
      | VInt n -> string_of_int n
      | VFloat f -> Printf.sprintf "%.4f" f
      | VString s -> "\"" ^ s ^ "\""
      | VBool b -> string_of_bool b
      | _ -> "...") vs in
    "[" ^ String.concat "; " inner ^ "]"
  | VRecord fields ->
    let field_strs = List.map (fun (k, v) ->
      k ^ "=" ^ (match v with
        | VInt n -> string_of_int n
        | VFloat f -> Printf.sprintf "%.4f" f
        | VString s -> "\"" ^ s ^ "\""
        | _ -> "?")) fields in
    "{" ^ String.concat ", " field_strs ^ "}"
  | VNone -> "none"

let value_to_float = function
  | VInt n -> float_of_int n
  | VFloat f -> f
  | VString s -> (try float_of_string s with _ -> 0.0)
  | VBool b -> if b then 1.0 else 0.0
  | _ -> 0.0

let value_to_int v = int_of_float (value_to_float v)

(* ===== Event ===== *)
type event = {
  timestamp: int;    (* logical clock *)
  payload: value;
  tag: string;       (* source/operator label *)
}

let make_event ?(tag="") ts payload = { timestamp = ts; payload; tag }

(* ===== Stream (lazy list of events) ===== *)
type stream = event list

(* ===== Backpressure ===== *)
type backpressure = Drop of int | Buffer of int | LatestOnly

let apply_backpressure bp events =
  match bp with
  | Drop n -> if List.length events > n then
      let rec take_n acc i = function
        | [] -> List.rev acc
        | x :: xs -> if i >= n then List.rev acc else take_n (x :: acc) (i+1) xs
      in take_n [] 0 events
    else events
  | Buffer n ->
    let len = List.length events in
    if len > n then
      let skip = len - n in
      let rec drop_n i = function
        | [] -> []
        | _ :: xs when i < skip -> drop_n (i+1) xs
        | rest -> rest
      in drop_n 0 events
    else events
  | LatestOnly ->
    match List.rev events with
    | [] -> []
    | last :: _ -> [last]

(* ===== Sources ===== *)
let source_counter start stop =
  let rec aux n ts acc =
    if n > stop then List.rev acc
    else aux (n+1) (ts+1) (make_event ~tag:"counter" ts (VInt n) :: acc)
  in aux start 0 []

let source_random bound count =
  Random.self_init ();
  let rec aux i ts acc =
    if i >= count then List.rev acc
    else aux (i+1) (ts+1) (make_event ~tag:"random" ts (VInt (Random.int bound)) :: acc)
  in aux 0 0 []

let source_sine step count =
  let rec aux i ts acc =
    if i >= count then List.rev acc
    else
      let v = sin (float_of_int i *. step) in
      aux (i+1) (ts+1) (make_event ~tag:"sine" ts (VFloat v) :: acc)
  in aux 0 0 []

let source_fibonacci count =
  let rec aux a b i ts acc =
    if i >= count then List.rev acc
    else aux b (a+b) (i+1) (ts+1) (make_event ~tag:"fib" ts (VInt a) :: acc)
  in aux 0 1 0 0 []

let source_words text =
  let words = String.split_on_char ' ' text in
  List.mapi (fun i w -> make_event ~tag:"words" i (VString w)) words

let source_range start stop step_val =
  let rec aux n ts acc =
    if (step_val > 0.0 && n > stop) || (step_val < 0.0 && n < stop) then List.rev acc
    else aux (n +. step_val) (ts+1) (make_event ~tag:"range" ts (VFloat n) :: acc)
  in aux start 0 []

(* ===== Combinators ===== *)
let stream_map f tag events =
  List.map (fun e -> { e with payload = f e.payload; tag }) events

let stream_filter pred events =
  List.filter (fun e -> pred e.payload) events

let stream_scan f init tag events =
  let _, result = List.fold_left (fun (acc, out) e ->
    let acc' = f acc e.payload in
    (acc', { e with payload = acc'; tag } :: out)
  ) (init, []) events in
  List.rev result

let stream_take n events =
  let rec aux i acc = function
    | [] -> List.rev acc
    | x :: xs -> if i >= n then List.rev acc else aux (i+1) (x :: acc) xs
  in aux 0 [] events

let stream_drop n events =
  let rec aux i = function
    | [] -> []
    | _ :: xs when i < n -> aux (i+1) xs
    | rest -> rest
  in aux 0 events

let stream_distinct events =
  let rec aux prev acc = function
    | [] -> List.rev acc
    | e :: rest ->
      let s = value_to_string e.payload in
      if s = prev then aux prev acc rest
      else aux s (e :: acc) rest
  in match events with
  | [] -> []
  | e :: rest -> aux (value_to_string e.payload) [e] rest

let stream_buffer n events =
  let rec aux chunk chunk_len ts acc = function
    | [] -> if chunk_len = 0 then List.rev acc
      else List.rev (make_event ~tag:"buffer" ts (VList (List.rev chunk)) :: acc)
    | e :: rest ->
      let chunk' = e.payload :: chunk in
      let chunk_len' = chunk_len + 1 in
      if chunk_len' >= n then
        aux [] 0 (ts+1) (make_event ~tag:"buffer" ts (VList (List.rev chunk')) :: acc) rest
      else
        aux chunk' chunk_len' ts acc rest
  in aux [] 0 0 [] events

let stream_window_tumbling size events =
  stream_buffer size events

let stream_window_sliding size step events =
  let arr = Array.of_list events in
  let len = Array.length arr in
  let rec aux i ts acc =
    if i + size > len then List.rev acc
    else
      let window = Array.to_list (Array.sub arr i size) in
      let vals = List.map (fun e -> e.payload) window in
      aux (i + step) (ts+1) (make_event ~tag:"window" ts (VList vals) :: acc)
  in aux 0 0 []

let stream_throttle n events =
  List.filteri (fun i _ -> i mod n = 0) events

let stream_merge a b =
  let rec aux acc xs ys = match xs, ys with
    | [], rest | rest, [] -> List.rev acc @ rest
    | x :: xs', y :: ys' ->
      if x.timestamp <= y.timestamp then aux (x :: acc) xs' ys
      else aux (y :: acc) xs ys'
  in aux [] a b

let stream_zip a b =
  List.map2 (fun x y ->
    make_event ~tag:"zip" x.timestamp (VList [x.payload; y.payload])
  ) a b

let stream_flatmap f tag events =
  List.concat_map (fun e ->
    let results = f e.payload in
    List.mapi (fun i v -> make_event ~tag (e.timestamp * 100 + i) v) results
  ) events

let stream_group_by key_fn events =
  let tbl = Hashtbl.create 16 in
  List.iter (fun e ->
    let k = key_fn e.payload in
    let prev = try Hashtbl.find tbl k with Not_found -> [] in
    Hashtbl.replace tbl k (e :: prev)
  ) events;
  let groups = Hashtbl.fold (fun k vs acc ->
    let vals = List.rev_map (fun e -> e.payload) vs in
    (k, VList vals) :: acc
  ) tbl [] in
  List.mapi (fun i (k, v) ->
    make_event ~tag:("group:" ^ k) i (VRecord [("key", VString k); ("values", v)])
  ) (List.sort compare groups)

let stream_sample n events =
  stream_throttle n events

(* ===== Sinks ===== *)
let sink_print events =
  List.iter (fun e ->
    Printf.printf "[t=%d] %s\n" e.timestamp (value_to_string e.payload)
  ) events

let sink_count events =
  Printf.printf "Count: %d\n" (List.length events)

let sink_sum events =
  let s = List.fold_left (fun acc e -> acc +. value_to_float e.payload) 0.0 events in
  Printf.printf "Sum: %.4f\n" s

let sink_avg events =
  let n = List.length events in
  if n = 0 then Printf.printf "Avg: N/A (empty stream)\n"
  else begin
    let s = List.fold_left (fun acc e -> acc +. value_to_float e.payload) 0.0 events in
    Printf.printf "Avg: %.4f\n" (s /. float_of_int n)
  end

let sink_stats events =
  (* Single-pass collection of count, sum, min, max; then one pass for variance *)
  let n, s, mn, mx =
    List.fold_left (fun (cnt, sm, lo, hi) e ->
      let v = value_to_float e.payload in
      (cnt + 1, sm +. v, min lo v, max hi v)
    ) (0, 0.0, infinity, neg_infinity) events
  in
  if n = 0 then Printf.printf "Stats: N/A (empty stream)\n"
  else begin
    let mean = s /. float_of_int n in
    let var = List.fold_left (fun acc e ->
      let v = value_to_float e.payload in
      acc +. (v -. mean) ** 2.0) 0.0 events /. float_of_int n in
    let stddev = sqrt var in
    Printf.printf "Stats: n=%d  min=%.4f  max=%.4f  mean=%.4f  stddev=%.4f\n" n mn mx mean stddev
  end

let sink_histogram bins events =
  let vals = List.map (fun e -> value_to_float e.payload) events in
  match vals with
  | [] -> Printf.printf "Histogram: N/A (empty stream)\n"
  | _ ->
    let mn = List.fold_left min infinity vals in
    let mx = List.fold_left max neg_infinity vals in
    let range = mx -. mn in
    let bin_width = if range = 0.0 then 1.0 else range /. float_of_int bins in
    let counts = Array.make bins 0 in
    List.iter (fun v ->
      let idx = int_of_float ((v -. mn) /. bin_width) in
      let idx = min idx (bins - 1) in
      counts.(idx) <- counts.(idx) + 1
    ) vals;
    let max_count = Array.fold_left max 0 counts in
    let bar_max = 40 in
    Printf.printf "\n  Histogram (%d bins)\n" bins;
    Printf.printf "  %s\n" (String.make 50 '-');
    for i = 0 to bins - 1 do
      let lo = mn +. float_of_int i *. bin_width in
      let hi = lo +. bin_width in
      let bar_len = if max_count = 0 then 0 else counts.(i) * bar_max / max_count in
      Printf.printf "  %7.2f-%7.2f |%s %d\n" lo hi (String.make bar_len '#') counts.(i)
    done;
    Printf.printf "  %s\n\n" (String.make 50 '-')

let sink_collect events =
  let vals = List.map (fun e -> e.payload) events in
  Printf.printf "Collected: %s\n" (value_to_string (VList vals))

(* ===== Pipeline ===== *)
type operator =
  | OpMap of string * (value -> value)
  | OpFilter of string * (value -> bool)
  | OpScan of string * (value -> value -> value) * value
  | OpTake of int
  | OpDrop of int
  | OpDistinct
  | OpBuffer of int
  | OpWindowTumbling of int
  | OpWindowSliding of int * int
  | OpThrottle of int
  | OpFlatMap of string * (value -> value list)
  | OpGroupBy of string * (value -> string)
  | OpSample of int

type sink_type =
  | SinkPrint | SinkCount | SinkSum | SinkAvg
  | SinkHistogram of int | SinkCollect | SinkStats

type source_def =
  | SCounter of int * int
  | SRandom of int * int
  | SSine of float * int
  | SFib of int
  | SWords of string
  | SRange of float * float * float
  | SLiteral of value list

type pipeline = {
  sources: source_def list;
  operators: operator list;
  sink: sink_type;
  backpressure: backpressure option;
}

let empty_pipeline = {
  sources = [];
  operators = [];
  sink = SinkPrint;
  backpressure = None;
}

let generate_source = function
  | SCounter (a, b) -> source_counter a b
  | SRandom (b, c) -> source_random b c
  | SSine (s, c) -> source_sine s c
  | SFib n -> source_fibonacci n
  | SWords t -> source_words t
  | SRange (a, b, s) -> source_range a b s
  | SLiteral vals -> List.mapi (fun i v -> make_event ~tag:"literal" i v) vals

let apply_operator events = function
  | OpMap (name, f) -> stream_map f name events
  | OpFilter (name, f) -> stream_filter f events
  | OpScan (name, f, init) -> stream_scan f init name events
  | OpTake n -> stream_take n events
  | OpDrop n -> stream_drop n events
  | OpDistinct -> stream_distinct events
  | OpBuffer n -> stream_buffer n events
  | OpWindowTumbling n -> stream_window_tumbling n events
  | OpWindowSliding (s, step) -> stream_window_sliding s step events
  | OpThrottle n -> stream_throttle n events
  | OpFlatMap (name, f) -> stream_flatmap f name events
  | OpGroupBy (name, f) -> stream_group_by f events
  | OpSample n -> stream_sample n events

let run_sink events = function
  | SinkPrint -> sink_print events
  | SinkCount -> sink_count events
  | SinkSum -> sink_sum events
  | SinkAvg -> sink_avg events
  | SinkHistogram n -> sink_histogram n events
  | SinkCollect -> sink_collect events
  | SinkStats -> sink_stats events

let run_pipeline p =
  (* Generate and merge all sources *)
  let events = match p.sources with
    | [] -> Printf.printf "Error: No source defined\n"; []
    | [s] -> generate_source s
    | sources ->
      List.fold_left (fun acc s -> stream_merge acc (generate_source s)) [] sources
  in
  (* Apply backpressure if set *)
  let events = match p.backpressure with
    | None -> events
    | Some bp -> apply_backpressure bp events
  in
  (* Apply operators in order *)
  let events = List.fold_left apply_operator events p.operators in
  (* Run sink *)
  run_sink events p.sink;
  List.length events

(* ===== Topology Visualization ===== *)
let source_name = function
  | SCounter (a, b) -> Printf.sprintf "counter(%d..%d)" a b
  | SRandom (b, c) -> Printf.sprintf "random(0..%d, n=%d)" b c
  | SSine (s, c) -> Printf.sprintf "sine(step=%.2f, n=%d)" s c
  | SFib n -> Printf.sprintf "fib(n=%d)" n
  | SWords _ -> "words(...)"
  | SRange (a, b, s) -> Printf.sprintf "range(%.1f..%.1f, step=%.1f)" a b s
  | SLiteral vs -> Printf.sprintf "literal(n=%d)" (List.length vs)

let operator_name = function
  | OpMap (n, _) -> "map(" ^ n ^ ")"
  | OpFilter (n, _) -> "filter(" ^ n ^ ")"
  | OpScan (n, _, _) -> "scan(" ^ n ^ ")"
  | OpTake n -> Printf.sprintf "take(%d)" n
  | OpDrop n -> Printf.sprintf "drop(%d)" n
  | OpDistinct -> "distinct"
  | OpBuffer n -> Printf.sprintf "buffer(%d)" n
  | OpWindowTumbling n -> Printf.sprintf "window_tumbling(%d)" n
  | OpWindowSliding (s, st) -> Printf.sprintf "window_sliding(%d,%d)" s st
  | OpThrottle n -> Printf.sprintf "throttle(%d)" n
  | OpFlatMap (n, _) -> "flatmap(" ^ n ^ ")"
  | OpGroupBy (n, _) -> "groupby(" ^ n ^ ")"
  | OpSample n -> Printf.sprintf "sample(%d)" n

let sink_name = function
  | SinkPrint -> "print"
  | SinkCount -> "count"
  | SinkSum -> "sum"
  | SinkAvg -> "avg"
  | SinkHistogram n -> Printf.sprintf "histogram(%d)" n
  | SinkCollect -> "collect"
  | SinkStats -> "stats"

let show_topology p =
  Printf.printf "\n  Pipeline Topology\n";
  Printf.printf "  %s\n" (String.make 40 '=');
  let sources = p.sources in
  let n_src = List.length sources in
  if n_src = 0 then Printf.printf "  (no sources)\n"
  else begin
    List.iteri (fun i s ->
      Printf.printf "  [SRC %d] %s\n" i (source_name s);
      if i < n_src - 1 then Printf.printf "    |  \\\n"
      else if n_src > 1 then Printf.printf "    |  / (merged)\n"
      else Printf.printf "    |\n"
    ) sources;
    (match p.backpressure with
     | None -> ()
     | Some (Drop n) -> Printf.printf "    v\n  [BP] drop(limit=%d)\n    |\n" n
     | Some (Buffer n) -> Printf.printf "    v\n  [BP] buffer(limit=%d)\n    |\n" n
     | Some LatestOnly -> Printf.printf "    v\n  [BP] latest_only\n    |\n");
    List.iter (fun op ->
      Printf.printf "    v\n  [OP] %s\n" (operator_name op)
    ) p.operators;
    Printf.printf "    v\n  [SINK] %s\n" (sink_name p.sink)
  end;
  Printf.printf "  %s\n\n" (String.make 40 '=')

(* ===== Expression Parser for REPL ===== *)
let parse_map_expr s =
  let s = String.trim s in
  if String.length s >= 4 && s.[0] = '(' && s.[String.length s - 1] = ')' then
    let inner = String.sub s 1 (String.length s - 2) in
    let inner = String.trim inner in
    (* Patterns: *N, +N, -N, /N, ^N, abs, neg, tostring *)
    if inner = "abs" then Some ("abs", fun v -> VFloat (abs_float (value_to_float v)))
    else if inner = "neg" then Some ("neg", fun v -> VFloat (-. (value_to_float v)))
    else if inner = "tostring" then Some ("tostring", fun v -> VString (value_to_string v))
    else if inner = "sqrt" then Some ("sqrt", fun v -> VFloat (sqrt (value_to_float v)))
    else if inner = "floor" then Some ("floor", fun v -> VInt (int_of_float (floor (value_to_float v))))
    else if inner = "ceil" then Some ("ceil", fun v -> VInt (int_of_float (ceil (value_to_float v))))
    else if String.length inner >= 2 then begin
      let op = inner.[0] in
      let num_str = String.trim (String.sub inner 1 (String.length inner - 1)) in
      try
        let n = float_of_string num_str in
        match op with
        | '*' -> Some (inner, fun v -> VFloat (value_to_float v *. n))
        | '+' -> Some (inner, fun v -> VFloat (value_to_float v +. n))
        | '-' -> Some (inner, fun v -> VFloat (value_to_float v -. n))
        | '/' -> Some (inner, fun v -> VFloat (value_to_float v /. n))
        | '^' -> Some (inner, fun v -> VFloat (value_to_float v ** n))
        | '%' -> Some (inner, fun v -> VInt (value_to_int v mod int_of_float n))
        | _ -> None
      with _ -> None
    end
    else None
  else None

let parse_filter_expr s =
  let s = String.trim s in
  if String.length s >= 4 && s.[0] = '(' && s.[String.length s - 1] = ')' then
    let inner = String.sub s 1 (String.length s - 2) in
    let inner = String.trim inner in
    if inner = "even" then Some ("even", fun v -> value_to_int v mod 2 = 0)
    else if inner = "odd" then Some ("odd", fun v -> value_to_int v mod 2 <> 0)
    else if inner = "positive" then Some ("positive", fun v -> value_to_float v > 0.0)
    else if inner = "negative" then Some ("negative", fun v -> value_to_float v < 0.0)
    else if String.length inner >= 2 then begin
      let try_parse () =
        if inner.[0] = '>' && inner.[1] = '=' then
          let n = float_of_string (String.trim (String.sub inner 2 (String.length inner - 2))) in
          Some (inner, fun v -> value_to_float v >= n)
        else if inner.[0] = '<' && inner.[1] = '=' then
          let n = float_of_string (String.trim (String.sub inner 2 (String.length inner - 2))) in
          Some (inner, fun v -> value_to_float v <= n)
        else if inner.[0] = '!' && inner.[1] = '=' then
          let n = float_of_string (String.trim (String.sub inner 2 (String.length inner - 2))) in
          Some (inner, fun v -> value_to_float v <> n)
        else if inner.[0] = '>' then
          let n = float_of_string (String.trim (String.sub inner 1 (String.length inner - 1))) in
          Some (inner, fun v -> value_to_float v > n)
        else if inner.[0] = '<' then
          let n = float_of_string (String.trim (String.sub inner 1 (String.length inner - 1))) in
          Some (inner, fun v -> value_to_float v < n)
        else if inner.[0] = '=' then
          let n = float_of_string (String.trim (String.sub inner 1 (String.length inner - 1))) in
          Some (inner, fun v -> value_to_float v = n)
        else None
      in
      (try try_parse () with _ -> None)
    end
    else None
  else None

let parse_scan_expr s =
  let s = String.trim s in
  if String.length s >= 3 && s.[0] = '(' && s.[String.length s - 1] = ')' then
    let inner = String.sub s 1 (String.length s - 2) in
    let inner = String.trim inner in
    if inner = "+" then Some ("+", (fun a b -> VFloat (value_to_float a +. value_to_float b)))
    else if inner = "*" then Some ("*", (fun a b -> VFloat (value_to_float a *. value_to_float b)))
    else if inner = "max" then Some ("max", (fun a b -> VFloat (max (value_to_float a) (value_to_float b))))
    else if inner = "min" then Some ("min", (fun a b -> VFloat (min (value_to_float a) (value_to_float b))))
    else None
  else None

(* ===== Built-in Demos ===== *)
let run_demo name =
  match name with
  | "fibonacci-stats" ->
    Printf.printf "\n=== Demo: Fibonacci Statistics ===\n";
    let p = { sources = [SFib 20]; operators = []; sink = SinkStats; backpressure = None } in
    ignore (run_pipeline p);
    let p2 = { sources = [SFib 20]; operators = [OpFilter ("even", fun v -> value_to_int v mod 2 = 0)]; sink = SinkPrint; backpressure = None } in
    Printf.printf "\nEven Fibonacci numbers:\n";
    ignore (run_pipeline p2)
  | "sine-analysis" ->
    Printf.printf "\n=== Demo: Sine Wave Analysis ===\n";
    let p = { sources = [SSine (0.2, 30)]; operators = []; sink = SinkHistogram 8; backpressure = None } in
    ignore (run_pipeline p)
  | "random-pipeline" ->
    Printf.printf "\n=== Demo: Random Number Pipeline ===\n";
    Printf.printf "random(0..100, n=50) -> filter(>50) -> map(*2) -> stats\n\n";
    let p = { sources = [SRandom (100, 50)];
      operators = [
        OpFilter (">50", fun v -> value_to_float v > 50.0);
        OpMap ("*2", fun v -> VFloat (value_to_float v *. 2.0));
      ];
      sink = SinkStats; backpressure = None } in
    ignore (run_pipeline p)
  | "windowed-avg" ->
    Printf.printf "\n=== Demo: Windowed Average ===\n";
    Printf.printf "counter(1..20) -> window_sliding(5,1) -> map(avg) -> print\n\n";
    let p = { sources = [SCounter (1, 20)];
      operators = [
        OpWindowSliding (5, 1);
        OpMap ("avg", fun v -> match v with
          | VList vs ->
            let s = List.fold_left (fun acc x -> acc +. value_to_float x) 0.0 vs in
            VFloat (s /. float_of_int (List.length vs))
          | _ -> v);
      ];
      sink = SinkPrint; backpressure = None } in
    ignore (run_pipeline p)
  | "merge-streams" ->
    Printf.printf "\n=== Demo: Merge Two Streams ===\n";
    Printf.printf "merge(counter(1..5), counter(100..105)) -> print\n\n";
    let p = { sources = [SCounter (1, 5); SCounter (100, 105)];
      operators = []; sink = SinkPrint; backpressure = None } in
    ignore (run_pipeline p)
  | "backpressure" ->
    Printf.printf "\n=== Demo: Backpressure Strategies ===\n";
    let src = [SRandom (1000, 100)] in
    Printf.printf "\nDrop (limit 10): ";
    let p1 = { sources = src; operators = []; sink = SinkCount; backpressure = Some (Drop 10) } in
    ignore (run_pipeline p1);
    Printf.printf "Buffer (limit 20): ";
    let p2 = { sources = src; operators = []; sink = SinkCount; backpressure = Some (Buffer 20) } in
    ignore (run_pipeline p2);
    Printf.printf "LatestOnly: ";
    let p3 = { sources = src; operators = []; sink = SinkCount; backpressure = Some LatestOnly } in
    ignore (run_pipeline p3)
  | "groupby" ->
    Printf.printf "\n=== Demo: Group By (mod 3) ===\n";
    Printf.printf "counter(1..12) -> groupby(mod3) -> print\n\n";
    let p = { sources = [SCounter (1, 12)];
      operators = [OpGroupBy ("mod3", fun v -> string_of_int (value_to_int v mod 3))];
      sink = SinkPrint; backpressure = None } in
    ignore (run_pipeline p)
  | _ -> Printf.printf "Unknown demo: %s\n" name;
    Printf.printf "Available demos: fibonacci-stats, sine-analysis, random-pipeline, windowed-avg, merge-streams, backpressure, groupby\n"

(* ===== REPL ===== *)
let split_words s =
  let buf = Buffer.create 16 in
  let in_quote = ref false in
  let words = ref [] in
  String.iter (fun c ->
    if c = '"' then in_quote := not !in_quote
    else if c = ' ' && not !in_quote then begin
      if Buffer.length buf > 0 then begin
        words := Buffer.contents buf :: !words;
        Buffer.clear buf
      end
    end
    else Buffer.add_char buf c
  ) s;
  if Buffer.length buf > 0 then words := Buffer.contents buf :: !words;
  List.rev !words

let print_help () =
  Printf.printf "\n";
  Printf.printf "  ╔══════════════════════════════════════════════════╗\n";
  Printf.printf "  ║         Reactive Stream Processor REPL          ║\n";
  Printf.printf "  ╠══════════════════════════════════════════════════╣\n";
  Printf.printf "  ║  SOURCES                                        ║\n";
  Printf.printf "  ║    source counter <start> <stop>                ║\n";
  Printf.printf "  ║    source random <bound> <count>                ║\n";
  Printf.printf "  ║    source sine <step> <count>                   ║\n";
  Printf.printf "  ║    source fib <count>                           ║\n";
  Printf.printf "  ║    source words \"hello world\"                   ║\n";
  Printf.printf "  ║    source range <start> <stop> <step>           ║\n";
  Printf.printf "  ║                                                  ║\n";
  Printf.printf "  ║  OPERATORS                                       ║\n";
  Printf.printf "  ║    pipe map (<expr>)      -- *2, +1, abs, sqrt  ║\n";
  Printf.printf "  ║    pipe filter (<expr>)   -- >5, even, positive ║\n";
  Printf.printf "  ║    pipe scan (<op>) <init>-- (+) 0, (*) 1       ║\n";
  Printf.printf "  ║    pipe take <n>                                 ║\n";
  Printf.printf "  ║    pipe drop <n>                                 ║\n";
  Printf.printf "  ║    pipe distinct                                 ║\n";
  Printf.printf "  ║    pipe buffer <n>                               ║\n";
  Printf.printf "  ║    pipe window tumbling <size>                   ║\n";
  Printf.printf "  ║    pipe window sliding <size> <step>             ║\n";
  Printf.printf "  ║    pipe throttle <n>                             ║\n";
  Printf.printf "  ║    pipe groupby mod<n>                           ║\n";
  Printf.printf "  ║    pipe sample <n>                               ║\n";
  Printf.printf "  ║                                                  ║\n";
  Printf.printf "  ║  SINKS                                           ║\n";
  Printf.printf "  ║    sink print | count | sum | avg | stats       ║\n";
  Printf.printf "  ║    sink histogram <bins> | collect               ║\n";
  Printf.printf "  ║                                                  ║\n";
  Printf.printf "  ║  CONTROL                                         ║\n";
  Printf.printf "  ║    run     -- execute pipeline                   ║\n";
  Printf.printf "  ║    show    -- show topology                      ║\n";
  Printf.printf "  ║    reset   -- clear pipeline                     ║\n";
  Printf.printf "  ║    bp drop <n> | buffer <n> | latest             ║\n";
  Printf.printf "  ║    demo <name>  -- run built-in demo             ║\n";
  Printf.printf "  ║    help | quit                                   ║\n";
  Printf.printf "  ╚══════════════════════════════════════════════════╝\n\n"

let repl () =
  Printf.printf "\n  ╔══════════════════════════════════════════════════╗\n";
  Printf.printf "  ║    🌊 Reactive Stream Processor v1.0             ║\n";
  Printf.printf "  ║    FRP with combinators, backpressure & more     ║\n";
  Printf.printf "  ║    Type 'help' for commands, 'demo <name>' to    ║\n";
  Printf.printf "  ║    see examples, or build your own pipeline!     ║\n";
  Printf.printf "  ╚══════════════════════════════════════════════════╝\n\n";
  let pipeline = ref empty_pipeline in
  let running = ref true in
  while !running do
    Printf.printf "reactive> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let words = split_words (String.trim line) in
      match words with
      | [] -> ()
      | ["quit"] | ["exit"] | ["q"] -> running := false
      | ["help"] | ["h"] | ["?"] -> print_help ()
      | ["reset"] ->
        pipeline := empty_pipeline;
        Printf.printf "Pipeline reset.\n"
      | ["run"] | ["go"] ->
        let n = run_pipeline !pipeline in
        Printf.printf "--- %d events processed ---\n" n
      | ["show"] | ["topology"] -> show_topology !pipeline
      | "source" :: "counter" :: a :: [b] ->
        (try
          let p = !pipeline in
          pipeline := { p with sources = p.sources @ [SCounter (int_of_string a, int_of_string b)] };
          Printf.printf "Added source: counter(%s..%s)\n" a b
        with _ -> Printf.printf "Usage: source counter <start> <stop>\n")
      | "source" :: "random" :: b :: [c] ->
        (try
          let p = !pipeline in
          pipeline := { p with sources = p.sources @ [SRandom (int_of_string b, int_of_string c)] };
          Printf.printf "Added source: random(0..%s, n=%s)\n" b c
        with _ -> Printf.printf "Usage: source random <bound> <count>\n")
      | "source" :: "sine" :: s :: [c] ->
        (try
          let p = !pipeline in
          pipeline := { p with sources = p.sources @ [SSine (float_of_string s, int_of_string c)] };
          Printf.printf "Added source: sine(step=%s, n=%s)\n" s c
        with _ -> Printf.printf "Usage: source sine <step> <count>\n")
      | "source" :: "fib" :: [n] ->
        (try
          let p = !pipeline in
          pipeline := { p with sources = p.sources @ [SFib (int_of_string n)] };
          Printf.printf "Added source: fib(n=%s)\n" n
        with _ -> Printf.printf "Usage: source fib <count>\n")
      | "source" :: "words" :: rest ->
        let text = String.concat " " rest in
        let p = !pipeline in
        pipeline := { p with sources = p.sources @ [SWords text] };
        Printf.printf "Added source: words(\"%s\")\n" text
      | "source" :: "range" :: a :: b :: [s] ->
        (try
          let p = !pipeline in
          pipeline := { p with sources = p.sources @ [SRange (float_of_string a, float_of_string b, float_of_string s)] };
          Printf.printf "Added source: range(%s..%s, step=%s)\n" a b s
        with _ -> Printf.printf "Usage: source range <start> <stop> <step>\n")
      | "pipe" :: "map" :: rest ->
        let expr = String.concat " " rest in
        (match parse_map_expr expr with
        | Some (name, f) ->
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpMap (name, f)] };
          Printf.printf "Added operator: map(%s)\n" name
        | None -> Printf.printf "Unknown map expression. Try: (*2), (+1), (abs), (sqrt), (neg)\n")
      | "pipe" :: "filter" :: rest ->
        let expr = String.concat " " rest in
        (match parse_filter_expr expr with
        | Some (name, f) ->
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpFilter (name, f)] };
          Printf.printf "Added operator: filter(%s)\n" name
        | None -> Printf.printf "Unknown filter expression. Try: (>5), (even), (positive)\n")
      | "pipe" :: "scan" :: rest ->
        let expr = String.concat " " rest in
        (* Parse "(<op>) <init>" *)
        let parts = String.split_on_char ' ' (String.trim expr) in
        (match parts with
        | [op_expr; init_str] ->
          (match parse_scan_expr op_expr with
          | Some (name, f) ->
            (try
              let init = VFloat (float_of_string init_str) in
              let p = !pipeline in
              pipeline := { p with operators = p.operators @ [OpScan (name, f, init)] };
              Printf.printf "Added operator: scan(%s, init=%s)\n" name init_str
            with _ -> Printf.printf "Invalid init value: %s\n" init_str)
          | None -> Printf.printf "Unknown scan op. Try: (+), (*), (max), (min)\n")
        | _ -> Printf.printf "Usage: pipe scan (<op>) <init>\n")
      | ["pipe"; "take"; n] ->
        (try
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpTake (int_of_string n)] };
          Printf.printf "Added operator: take(%s)\n" n
        with _ -> Printf.printf "Usage: pipe take <n>\n")
      | ["pipe"; "drop"; n] ->
        (try
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpDrop (int_of_string n)] };
          Printf.printf "Added operator: drop(%s)\n" n
        with _ -> Printf.printf "Usage: pipe drop <n>\n")
      | ["pipe"; "distinct"] ->
        let p = !pipeline in
        pipeline := { p with operators = p.operators @ [OpDistinct] };
        Printf.printf "Added operator: distinct\n"
      | ["pipe"; "buffer"; n] ->
        (try
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpBuffer (int_of_string n)] };
          Printf.printf "Added operator: buffer(%s)\n" n
        with _ -> Printf.printf "Usage: pipe buffer <n>\n")
      | ["pipe"; "window"; "tumbling"; n] ->
        (try
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpWindowTumbling (int_of_string n)] };
          Printf.printf "Added operator: window_tumbling(%s)\n" n
        with _ -> Printf.printf "Usage: pipe window tumbling <size>\n")
      | ["pipe"; "window"; "sliding"; s; st] ->
        (try
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpWindowSliding (int_of_string s, int_of_string st)] };
          Printf.printf "Added operator: window_sliding(%s, %s)\n" s st
        with _ -> Printf.printf "Usage: pipe window sliding <size> <step>\n")
      | ["pipe"; "throttle"; n] ->
        (try
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpThrottle (int_of_string n)] };
          Printf.printf "Added operator: throttle(%s)\n" n
        with _ -> Printf.printf "Usage: pipe throttle <n>\n")
      | "pipe" :: "groupby" :: [name] ->
        let p = !pipeline in
        let key_fn = if String.length name > 3 && String.sub name 0 3 = "mod" then
          let n = try int_of_string (String.sub name 3 (String.length name - 3)) with _ -> 3 in
          fun v -> string_of_int (value_to_int v mod n)
        else fun v -> value_to_string v
        in
        pipeline := { p with operators = p.operators @ [OpGroupBy (name, key_fn)] };
        Printf.printf "Added operator: groupby(%s)\n" name
      | ["pipe"; "sample"; n] ->
        (try
          let p = !pipeline in
          pipeline := { p with operators = p.operators @ [OpSample (int_of_string n)] };
          Printf.printf "Added operator: sample(%s)\n" n
        with _ -> Printf.printf "Usage: pipe sample <n>\n")
      | ["sink"; "print"] -> pipeline := { !pipeline with sink = SinkPrint }; Printf.printf "Sink: print\n"
      | ["sink"; "count"] -> pipeline := { !pipeline with sink = SinkCount }; Printf.printf "Sink: count\n"
      | ["sink"; "sum"] -> pipeline := { !pipeline with sink = SinkSum }; Printf.printf "Sink: sum\n"
      | ["sink"; "avg"] -> pipeline := { !pipeline with sink = SinkAvg }; Printf.printf "Sink: avg\n"
      | ["sink"; "stats"] -> pipeline := { !pipeline with sink = SinkStats }; Printf.printf "Sink: stats\n"
      | ["sink"; "collect"] -> pipeline := { !pipeline with sink = SinkCollect }; Printf.printf "Sink: collect\n"
      | ["sink"; "histogram"; n] ->
        (try pipeline := { !pipeline with sink = SinkHistogram (int_of_string n) };
          Printf.printf "Sink: histogram(%s)\n" n
        with _ -> Printf.printf "Usage: sink histogram <bins>\n")
      | ["bp"; "drop"; n] ->
        (try pipeline := { !pipeline with backpressure = Some (Drop (int_of_string n)) };
          Printf.printf "Backpressure: drop(limit=%s)\n" n
        with _ -> Printf.printf "Usage: bp drop <n>\n")
      | ["bp"; "buffer"; n] ->
        (try pipeline := { !pipeline with backpressure = Some (Buffer (int_of_string n)) };
          Printf.printf "Backpressure: buffer(limit=%s)\n" n
        with _ -> Printf.printf "Usage: bp buffer <n>\n")
      | ["bp"; "latest"] ->
        pipeline := { !pipeline with backpressure = Some LatestOnly };
        Printf.printf "Backpressure: latest_only\n"
      | "demo" :: [name] -> run_demo name
      | "demo" :: [] ->
        Printf.printf "Available demos: fibonacci-stats, sine-analysis, random-pipeline, windowed-avg, merge-streams, backpressure, groupby\n"
      | _ -> Printf.printf "Unknown command. Type 'help' for usage.\n"
  done;
  Printf.printf "\nGoodbye! 🌊\n"

(* ===== Main ===== *)
let () =
  if Array.length Sys.argv > 1 then begin
    match Sys.argv.(1) with
    | "--demo" ->
      let name = if Array.length Sys.argv > 2 then Sys.argv.(2) else "random-pipeline" in
      run_demo name
    | "--all-demos" ->
      List.iter run_demo ["fibonacci-stats"; "sine-analysis"; "random-pipeline"; "windowed-avg"; "merge-streams"; "backpressure"; "groupby"]
    | "--help" | "-h" -> print_help ()
    | _ -> Printf.printf "Unknown option: %s\nUse --demo <name>, --all-demos, or no args for REPL\n" Sys.argv.(1)
  end
  else repl ()
