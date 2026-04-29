(* code_mentor.ml — Autonomous Code Mentor Engine
   Analyzes OCaml source files to assess learner proficiency across 8
   skill dimensions, identifies gaps, generates personalized exercises,
   and tracks mastery progression over time.

   Features:
   - Scans all .ml files (excludes test_ prefixed and self)
   - Assesses 8 competency dimensions (0-100 each)
   - Detects skill gaps with severity classification
   - Generates contextual exercises at adaptive difficulty
   - Tracks progression in .mentor_progress.json
   - ASCII skill radar visualization
   - Motivational coaching based on improvement patterns
   - Interactive REPL for exploration

   Usage: ocaml code_mentor.ml
*)

(* ── Types ──────────────────────────────────────────────────────── *)

type severity = Critical | Moderate | Minor

type dimension =
  | PatternMatching
  | HigherOrder
  | TypeSystem
  | Recursion
  | ModulesAndFunctors
  | Concurrency
  | ErrorHandling
  | Abstraction

type skill_score = {
  dimension : dimension;
  score : int;
  evidence_count : int;
  complexity_depth : int;
}

type skill_gap = {
  gap_dimension : dimension;
  gap_score : int;
  gap_severity : severity;
  gap_suggestion : string;
}

type exercise = {
  title : string;
  description : string;
  starter_code : string;
  concepts : string list;
  difficulty : int;
  hints : string list;
}

type progress_entry = {
  timestamp : string;
  scores : (string * int) list;
}

type mastery_level = Novice | Apprentice | Journeyman | Expert | Master

type mentor_state = {
  current_scores : skill_score list;
  gaps : skill_gap list;
  exercises : exercise list;
  mastery : mastery_level;
  history : progress_entry list;
  streak_days : int;
}

(* ── Utilities ──────────────────────────────────────────────────── *)

let dim_to_string = function
  | PatternMatching -> "Pattern Matching"
  | HigherOrder -> "Higher-Order Functions"
  | TypeSystem -> "Type System"
  | Recursion -> "Recursion"
  | ModulesAndFunctors -> "Modules & Functors"
  | Concurrency -> "Concurrency"
  | ErrorHandling -> "Error Handling"
  | Abstraction -> "Abstraction"

let dim_to_key = function
  | PatternMatching -> "pattern_matching"
  | HigherOrder -> "higher_order"
  | TypeSystem -> "type_system"
  | Recursion -> "recursion"
  | ModulesAndFunctors -> "modules_functors"
  | Concurrency -> "concurrency"
  | ErrorHandling -> "error_handling"
  | Abstraction -> "abstraction"

let all_dimensions = [
  PatternMatching; HigherOrder; TypeSystem; Recursion;
  ModulesAndFunctors; Concurrency; ErrorHandling; Abstraction
]

let severity_to_string = function
  | Critical -> "CRITICAL"
  | Moderate -> "MODERATE"
  | Minor -> "MINOR"

let mastery_to_string = function
  | Novice -> "Novice"
  | Apprentice -> "Apprentice"
  | Journeyman -> "Journeyman"
  | Expert -> "Expert"
  | Master -> "Master"

let color_red s = "\027[31m" ^ s ^ "\027[0m"
let color_green s = "\027[32m" ^ s ^ "\027[0m"
let color_yellow s = "\027[33m" ^ s ^ "\027[0m"
let color_cyan s = "\027[36m" ^ s ^ "\027[0m"
let color_magenta s = "\027[35m" ^ s ^ "\027[0m"
let color_bold s = "\027[1m" ^ s ^ "\027[0m"

let read_file path =
  try
    let ic = open_in path in
    let buf = Buffer.create 4096 in
    (try while true do
       let line = input_line ic in
       Buffer.add_string buf line;
       Buffer.add_char buf '\n'
     done with End_of_file -> ());
    close_in ic;
    Some (Buffer.contents buf)
  with _ -> None

let write_file path content =
  try
    let oc = open_out path in
    output_string oc content;
    close_out oc;
    true
  with _ -> false

let lines_of_string s =
  let len = String.length s in
  if len = 0 then []
  else
    let lines = ref [] in
    let start = ref 0 in
    for i = 0 to len - 1 do
      if s.[i] = '\n' then begin
        lines := String.sub s !start (i - !start) :: !lines;
        start := i + 1
      end
    done;
    if !start < len then
      lines := String.sub s !start (len - !start) :: !lines;
    List.rev !lines

let string_contains haystack needle =
  let hlen = String.length haystack in
  let nlen = String.length needle in
  if nlen > hlen then false
  else
    let found = ref false in
    for i = 0 to hlen - nlen do
      if not !found then begin
        let ok = ref true in
        for j = 0 to nlen - 1 do
          if haystack.[i + j] <> needle.[j] then ok := false
        done;
        if !ok then found := true
      end
    done;
    !found

let count_occurrences content pattern =
  let plen = String.length pattern in
  let clen = String.length content in
  if plen = 0 || plen > clen then 0
  else
    let count = ref 0 in
    for i = 0 to clen - plen do
      let ok = ref true in
      for j = 0 to plen - 1 do
        if content.[i + j] <> pattern.[j] then ok := false
      done;
      if !ok then incr count
    done;
    !count

let current_timestamp () =
  let t = Unix.localtime (Unix.time ()) in
  Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02d"
    (t.Unix.tm_year + 1900) (t.Unix.tm_mon + 1) t.Unix.tm_mday
    t.Unix.tm_hour t.Unix.tm_min t.Unix.tm_sec

let clamp v lo hi = max lo (min hi v)

(* ── File Discovery ─────────────────────────────────────────────── *)

let discover_ml_files () =
  let files = ref [] in
  let dir = Sys.getcwd () in
  let entries = Sys.readdir dir in
  Array.iter (fun name ->
    if Filename.check_suffix name ".ml"
       && not (String.length name >= 5 && String.sub name 0 5 = "test_")
       && name <> "code_mentor.ml" then
      files := name :: !files
  ) entries;
  List.sort compare !files

(* ── Skill Analysis Engines ─────────────────────────────────────── *)

let analyze_pattern_matching content =
  let match_count = count_occurrences content "match " in
  let with_count = count_occurrences content " with" in
  let guard_count = count_occurrences content " when " in
  let nested = count_occurrences content "| " in
  let wildcard = count_occurrences content "| _ ->" in
  let tuple_pat = count_occurrences content ", _)" + count_occurrences content "(_," in
  let evidence = match_count + guard_count + tuple_pat in
  let depth = (min match_count 20) + (min guard_count 10) + (min nested 30)
              + (min wildcard 5) + (min with_count 20) + (min tuple_pat 10) in
  let raw_score = (float_of_int depth) /. 0.95 in
  (clamp (int_of_float raw_score) 0 100, evidence, depth)

let analyze_higher_order content =
  let map_count = count_occurrences content "List.map" + count_occurrences content "Array.map" in
  let fold_count = count_occurrences content "List.fold" + count_occurrences content "Array.fold" in
  let filter_count = count_occurrences content "List.filter" + count_occurrences content "Array.filter" in
  let iter_count = count_occurrences content "List.iter" + count_occurrences content "Array.iter" in
  let fun_count = count_occurrences content "(fun " + count_occurrences content "fun " in
  let pipe_count = count_occurrences content "|>" in
  let compose_count = count_occurrences content " @@ " in
  let evidence = map_count + fold_count + filter_count + fun_count in
  let depth = (min map_count 15) * 2 + (min fold_count 10) * 3
              + (min filter_count 10) * 2 + (min iter_count 10)
              + (min fun_count 20) + (min pipe_count 15) * 2
              + (min compose_count 10) * 2 in
  let raw_score = (float_of_int depth) /. 1.3 in
  (clamp (int_of_float raw_score) 0 100, evidence, depth)

let analyze_type_system content =
  let type_count = count_occurrences content "type " in
  let gadt_count = count_occurrences content ": " in
  let phantom = count_occurrences content "'phantom" + count_occurrences content "'a t" in
  let poly_var = count_occurrences content "`" in
  let functor_sig = count_occurrences content "module type" in
  let constraint_count = count_occurrences content "constraint " in
  let record_count = count_occurrences content "mutable " + count_occurrences content "{ " in
  let evidence = type_count + functor_sig + poly_var in
  let depth = (min type_count 30) * 2 + (min gadt_count 10)
              + (min phantom 5) * 3 + (min poly_var 10) * 2
              + (min functor_sig 5) * 4 + (min constraint_count 5) * 3
              + (min record_count 15) in
  let raw_score = (float_of_int depth) /. 1.5 in
  (clamp (int_of_float raw_score) 0 100, evidence, depth)

let analyze_recursion content =
  let rec_count = count_occurrences content "let rec " in
  let tail_count = count_occurrences content "aux " + count_occurrences content "loop " in
  let mutual_count = count_occurrences content " and " in
  let acc_count = count_occurrences content "acc" + count_occurrences content "accum" in
  let cps_count = count_occurrences content " k " + count_occurrences content "cont " in
  let evidence = rec_count + tail_count in
  let depth = (min rec_count 20) * 3 + (min tail_count 10) * 3
              + (min mutual_count 5) * 4 + (min acc_count 10) * 2
              + (min cps_count 5) * 5 in
  let raw_score = (float_of_int depth) /. 1.4 in
  (clamp (int_of_float raw_score) 0 100, evidence, depth)

let analyze_modules content =
  let module_count = count_occurrences content "module " in
  let sig_count = count_occurrences content " sig" + count_occurrences content ": sig" in
  let struct_count = count_occurrences content " struct" in
  let functor_count = count_occurrences content "functor" in
  let include_count = count_occurrences content "include " in
  let open_count = count_occurrences content "open " in
  let first_class = count_occurrences content "(module " in
  let evidence = module_count + functor_count + sig_count in
  let depth = (min module_count 15) * 2 + (min sig_count 10) * 3
              + (min struct_count 10) * 2 + (min functor_count 5) * 5
              + (min include_count 5) * 2 + (min open_count 10)
              + (min first_class 3) * 5 in
  let raw_score = (float_of_int depth) /. 1.2 in
  (clamp (int_of_float raw_score) 0 100, evidence, depth)

let analyze_concurrency content =
  let lwt_count = count_occurrences content "Lwt" + count_occurrences content "lwt" in
  let async_count = count_occurrences content "Async" + count_occurrences content "async" in
  let mutex_count = count_occurrences content "Mutex" + count_occurrences content "mutex" in
  let thread_count = count_occurrences content "Thread" + count_occurrences content "thread" in
  let channel_count = count_occurrences content "Event." + count_occurrences content "channel" in
  let domain_count = count_occurrences content "Domain" in
  let evidence = lwt_count + async_count + mutex_count + thread_count in
  let depth = (min lwt_count 10) * 3 + (min async_count 10) * 3
              + (min mutex_count 5) * 4 + (min thread_count 10) * 2
              + (min channel_count 5) * 4 + (min domain_count 5) * 4 in
  let raw_score = (float_of_int depth) /. 1.0 in
  (clamp (int_of_float raw_score) 0 100, evidence, depth)

let analyze_error_handling content =
  let option_count = count_occurrences content "Some " + count_occurrences content "None" in
  let result_count = count_occurrences content "Ok " + count_occurrences content "Error " in
  let try_count = count_occurrences content "try " in
  let raise_count = count_occurrences content "raise " in
  let with_exn = count_occurrences content "with exn" + count_occurrences content "with _" in
  let bind_count = count_occurrences content ">>=" + count_occurrences content "let* " in
  let evidence = option_count + result_count + try_count in
  let depth = (min option_count 20) * 2 + (min result_count 10) * 3
              + (min try_count 10) * 2 + (min raise_count 5)
              + (min with_exn 5) * 2 + (min bind_count 5) * 4 in
  let raw_score = (float_of_int depth) /. 1.2 in
  (clamp (int_of_float raw_score) 0 100, evidence, depth)

let analyze_abstraction content =
  let sig_count = count_occurrences content ": sig" + count_occurrences content "module type" in
  let private_count = count_occurrences content "private " in
  let abstract_type = count_occurrences content "type t" in
  let interface_count = count_occurrences content ".mli" in
  let encap = count_occurrences content "val " in
  let let_in = count_occurrences content "let " in
  let local_open = count_occurrences content "let open" in
  let evidence = sig_count + private_count + abstract_type in
  let depth = (min sig_count 10) * 4 + (min private_count 5) * 3
              + (min abstract_type 10) * 3 + (min interface_count 5) * 2
              + (min encap 15) * 2 + (min let_in 50)
              + (min local_open 5) * 2 in
  let raw_score = (float_of_int depth) /. 1.5 in
  (clamp (int_of_float raw_score) 0 100, evidence, depth)

(* ── Full Assessment ────────────────────────────────────────────── *)

let assess_all_files files =
  let totals = Array.make 8 (0, 0, 0) in
  let n = List.length files in
  List.iter (fun file ->
    match read_file file with
    | None -> ()
    | Some content ->
      let analyzers = [|
        analyze_pattern_matching; analyze_higher_order;
        analyze_type_system; analyze_recursion;
        analyze_modules; analyze_concurrency;
        analyze_error_handling; analyze_abstraction;
      |] in
      for i = 0 to 7 do
        let (s, e, d) = analyzers.(i) content in
        let (ts, te, td) = totals.(i) in
        totals.(i) <- (ts + s, te + e, td + d)
      done
  ) files;
  let dims = all_dimensions in
  List.mapi (fun i dim ->
    let (total_score, total_ev, total_depth) = totals.(i) in
    let avg_score = if n > 0 then total_score / n else 0 in
    { dimension = dim;
      score = clamp avg_score 0 100;
      evidence_count = total_ev;
      complexity_depth = total_depth; }
  ) dims

(* ── Gap Detection ──────────────────────────────────────────────── *)

let proficient_baseline = 70

let detect_gaps scores =
  let below = List.filter (fun s -> s.score < proficient_baseline) scores in
  let sorted = List.sort (fun a b -> compare a.score b.score) below in
  let top_gaps = match sorted with
    | a :: b :: c :: _ -> [a; b; c]
    | lst -> lst in
  List.map (fun s ->
    let sev = if s.score < 30 then Critical
              else if s.score < 50 then Moderate
              else Minor in
    let suggestion = match s.dimension with
      | PatternMatching -> "Practice nested pattern matching with guards and tuple destructuring"
      | HigherOrder -> "Implement common operations using map/fold instead of explicit recursion"
      | TypeSystem -> "Explore GADTs, phantom types, and polymorphic variants in small examples"
      | Recursion -> "Convert iterative algorithms to tail-recursive form with accumulators"
      | ModulesAndFunctors -> "Design module signatures and implement functors for generic containers"
      | Concurrency -> "Build simple producer-consumer patterns with threads and channels"
      | ErrorHandling -> "Replace exceptions with Result types and build monadic error pipelines"
      | Abstraction -> "Create abstract module types that hide implementation details"
    in
    { gap_dimension = s.dimension;
      gap_score = s.score;
      gap_severity = sev;
      gap_suggestion = suggestion; }
  ) top_gaps

(* ── Exercise Generation ────────────────────────────────────────── *)

let generate_exercises_for_gap gap =
  let diff = if gap.gap_score < 30 then 1
             else if gap.gap_score < 50 then 3
             else 4 in
  match gap.gap_dimension with
  | PatternMatching -> [
    { title = "Shape Area Calculator";
      description = "Define a shape type (Circle, Rectangle, Triangle) and compute areas using pattern matching with nested cases.";
      starter_code = "type shape = Circle of float | Rectangle of float * float | Triangle of float * float * float\n\nlet area shape =\n  (* your code here *)\n  failwith \"TODO\"";
      concepts = ["variant types"; "pattern matching"; "float arithmetic"];
      difficulty = diff;
      hints = ["Use match shape with | Circle r -> ..."; "Triangle: use Heron's formula"] };
    { title = "Expression Simplifier";
      description = "Write a function that simplifies arithmetic expressions (e.g., x+0 -> x, x*1 -> x) using deep pattern matching.";
      starter_code = "type expr = Num of int | Add of expr * expr | Mul of expr * expr | Var of string\n\nlet rec simplify expr =\n  (* your code here *)\n  failwith \"TODO\"";
      concepts = ["recursive patterns"; "nested matching"; "algebraic simplification"];
      difficulty = diff + 1;
      hints = ["Match on Add(e, Num 0) and Add(Num 0, e)"; "Don't forget to recurse into sub-expressions"] };
    { title = "JSON Path Extractor";
      description = "Given a nested JSON-like type, extract values at a dotted path using pattern matching with guards.";
      starter_code = "type json = Null | Bool of bool | Int of int | Str of string\n         | Arr of json list | Obj of (string * json) list\n\nlet rec extract path json =\n  (* your code here *)\n  failwith \"TODO\"";
      concepts = ["guards"; "list patterns"; "option types"];
      difficulty = diff + 1;
      hints = ["Split path on '.' to get segments"; "Use List.assoc_opt for object lookup"] };
    ]
  | HigherOrder -> [
    { title = "Pipeline Builder";
      description = "Implement a compose function and use it to build a data transformation pipeline from a list of functions.";
      starter_code = "let compose f g x = (* your code *) failwith \"TODO\"\n\nlet pipeline fns x =\n  (* Apply all functions left-to-right *)\n  failwith \"TODO\"";
      concepts = ["function composition"; "List.fold_left"; "higher-order functions"];
      difficulty = diff;
      hints = ["compose f g x = f (g x)"; "pipeline = List.fold_left (fun acc f -> f acc) x fns"] };
    { title = "Custom Map-Reduce";
      description = "Implement map_reduce: apply a mapper to each element, then reduce results with a combiner.";
      starter_code = "let map_reduce ~mapper ~reducer ~init lst =\n  (* your code here *)\n  failwith \"TODO\"";
      concepts = ["labeled arguments"; "fold"; "map"];
      difficulty = diff;
      hints = ["First map, then fold"; "Or do it in a single fold for efficiency"] };
    { title = "Memoized Function Wrapper";
      description = "Create a higher-order function that wraps any function with memoization using a hash table.";
      starter_code = "let memoize f =\n  (* Return a new function that caches results *)\n  failwith \"TODO\"";
      concepts = ["closures"; "Hashtbl"; "higher-order functions"];
      difficulty = diff + 1;
      hints = ["Create a Hashtbl inside the closure"; "Return a fun that checks cache first"] };
    ]
  | TypeSystem -> [
    { title = "Typed Expression Evaluator";
      description = "Use GADTs to create a type-safe expression evaluator that prevents adding ints to bools at compile time.";
      starter_code = "type _ expr =\n  | Int : int -> int expr\n  | Bool : bool -> bool expr\n  | Add : int expr * int expr -> int expr\n  | If : bool expr * 'a expr * 'a expr -> 'a expr\n\nlet rec eval : type a. a expr -> a = function\n  (* your code here *)\n  | _ -> failwith \"TODO\"";
      concepts = ["GADTs"; "existential types"; "type-safe evaluation"];
      difficulty = diff + 1;
      hints = ["Pattern match on each constructor"; "The return type is inferred by the GADT"] };
    { title = "Phantom Type State Machine";
      description = "Model a door (Locked/Unlocked/Open) using phantom types so invalid transitions are compile-time errors.";
      starter_code = "type locked\ntype unlocked\ntype opened\n\ntype _ door = Door : string -> _ door\n\nlet lock : unlocked door -> locked door = fun (Door s) ->\n  (* your code *) failwith \"TODO\"";
      concepts = ["phantom types"; "state machines"; "type-level programming"];
      difficulty = diff + 2;
      hints = ["Each function restricts input/output phantom types"; "Door constructor erases the state"] };
    { title = "Polymorphic Variant Protocol";
      description = "Define a protocol using polymorphic variants where each handler only accepts specific message types.";
      starter_code = "let handle_auth = function\n  | `Login (user, pass) -> (* ... *) failwith \"TODO\"\n  | `Logout -> failwith \"TODO\"\n\nlet handle_data = function\n  | `Query q -> failwith \"TODO\"\n  | `Update (k, v) -> failwith \"TODO\"";
      concepts = ["polymorphic variants"; "open types"; "row polymorphism"];
      difficulty = diff;
      hints = ["Polymorphic variants start with backtick"; "Types are inferred from usage"] };
    ]
  | Recursion -> [
    { title = "Tail-Recursive List Operations";
      description = "Implement reverse, flatten, and zip using only tail recursion with accumulators.";
      starter_code = "let reverse lst =\n  let rec aux acc = function\n    | [] -> acc\n    | x :: xs -> (* your code *) failwith \"TODO\"\n  in aux [] lst";
      concepts = ["tail recursion"; "accumulators"; "list operations"];
      difficulty = diff;
      hints = ["Build result in acc, reverse at end if order matters"; "aux carries the accumulated result"] };
    { title = "CPS Tree Traversal";
      description = "Implement tree traversal in continuation-passing style to avoid stack overflow on deep trees.";
      starter_code = "type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree\n\nlet fold_tree_cps f init tree =\n  let rec aux tree k =\n    (* your code here *)\n    failwith \"TODO\"\n  in aux tree (fun x -> x)";
      concepts = ["CPS"; "continuations"; "stack safety"];
      difficulty = diff + 2;
      hints = ["k is the continuation - call it with the result"; "For nodes: traverse left, then right in continuation"] };
    { title = "Mutual Recursion: Even/Odd Check";
      description = "Implement is_even and is_odd using mutual recursion on natural numbers (Peano style).";
      starter_code = "type nat = Zero | Succ of nat\n\nlet rec is_even = function\n  | Zero -> (* your code *) failwith \"TODO\"\n  | Succ n -> is_odd n\nand is_odd = function\n  | Zero -> failwith \"TODO\"\n  | Succ n -> failwith \"TODO\"";
      concepts = ["mutual recursion"; "Peano numbers"; "structural recursion"];
      difficulty = diff;
      hints = ["Zero is even"; "Succ n: delegate to the other function"] };
    ]
  | ModulesAndFunctors -> [
    { title = "Comparable Set Functor";
      description = "Write a functor that creates a Set module from any module satisfying an ORDERED signature.";
      starter_code = "module type ORDERED = sig\n  type t\n  val compare : t -> t -> int\nend\n\nmodule MakeSet (Ord : ORDERED) : sig\n  type t\n  val empty : t\n  val add : Ord.t -> t -> t\n  val mem : Ord.t -> t -> bool\nend = struct\n  (* your implementation *)\n  type t = unit\n  let empty = ()\n  let add _ _ = failwith \"TODO\"\n  let mem _ _ = failwith \"TODO\"\nend";
      concepts = ["functors"; "module signatures"; "abstract types"];
      difficulty = diff + 1;
      hints = ["Store elements as a sorted list"; "Use Ord.compare for ordering"] };
    { title = "Plugin System with First-Class Modules";
      description = "Design a plugin registry that accepts first-class modules implementing a PLUGIN interface.";
      starter_code = "module type PLUGIN = sig\n  val name : string\n  val run : string -> string\nend\n\nlet plugins : (module PLUGIN) list ref = ref []\n\nlet register (p : (module PLUGIN)) =\n  (* your code *) failwith \"TODO\"";
      concepts = ["first-class modules"; "dynamic dispatch"; "plugin architecture"];
      difficulty = diff + 2;
      hints = ["Store modules in a list"; "Unpack with (module P : PLUGIN) syntax"] };
    { title = "Layered Module Architecture";
      description = "Build a 3-layer system (Storage -> Service -> API) where each layer is a functor taking the layer below.";
      starter_code = "module type STORAGE = sig\n  type key\n  type value\n  val get : key -> value option\n  val put : key -> value -> unit\nend\n\nmodule MakeService (S : STORAGE) = struct\n  (* your code *) let _ = failwith \"TODO\"\nend";
      concepts = ["functor composition"; "layered architecture"; "dependency injection"];
      difficulty = diff + 1;
      hints = ["Each layer signature exposes its operations"; "Upper layers call lower layer functions via functor parameter"] };
    ]
  | Concurrency -> [
    { title = "Producer-Consumer with Channels";
      description = "Implement a bounded buffer using Thread and Mutex where producers wait when full and consumers wait when empty.";
      starter_code = "type 'a bounded_buffer = {\n  mutable data : 'a list;\n  capacity : int;\n  mutex : Mutex.t;\n  not_empty : Condition.t;\n  not_full : Condition.t;\n}\n\nlet produce buf item =\n  (* your code *) failwith \"TODO\"";
      concepts = ["threads"; "mutex"; "condition variables"; "bounded buffers"];
      difficulty = diff + 1;
      hints = ["Lock mutex, check capacity, wait on condition if full"; "Signal not_empty after producing"] };
    { title = "Parallel Map with Domains";
      description = "Implement parallel_map that splits work across multiple OCaml 5 domains and collects results.";
      starter_code = "let parallel_map ~num_domains f lst =\n  (* Split list into chunks, spawn domains, collect *)\n  failwith \"TODO\"";
      concepts = ["Domain"; "parallelism"; "work splitting"];
      difficulty = diff + 2;
      hints = ["Split list into num_domains chunks"; "Use Domain.spawn for each chunk, Domain.join to collect"] };
    { title = "Simple Future/Promise";
      description = "Implement a future type that represents a value computed asynchronously in another thread.";
      starter_code = "type 'a future\n\nval make : (unit -> 'a) -> 'a future\nval await : 'a future -> 'a";
      concepts = ["futures"; "synchronization"; "Thread"];
      difficulty = diff;
      hints = ["Store result in a ref protected by mutex"; "await blocks on a condition variable until result is set"] };
    ]
  | ErrorHandling -> [
    { title = "Result Monad Pipeline";
      description = "Build a pipeline that chains multiple fallible operations using Result and a bind operator.";
      starter_code = "let ( >>= ) r f = match r with Ok v -> f v | Error _ as e -> e\nlet ( >>| ) r f = match r with Ok v -> Ok (f v) | Error _ as e -> e\n\nlet parse_int s =\n  (* your code *) failwith \"TODO\"\n\nlet divide a b =\n  (* your code *) failwith \"TODO\"";
      concepts = ["Result type"; "monadic bind"; "error propagation"];
      difficulty = diff;
      hints = ["parse_int: use int_of_string_opt, convert None to Error"; "divide: check for zero divisor"] };
    { title = "Custom Error Hierarchy";
      description = "Design a typed error hierarchy using polymorphic variants for composable error handling.";
      starter_code = "type parse_error = [`Parse_failed of string | `Unexpected_token of string]\ntype io_error = [`File_not_found of string | `Permission_denied of string]\ntype app_error = [parse_error | io_error | `Unknown of string]\n\nlet handle_error : app_error -> string = function\n  | (* your code *) _ -> failwith \"TODO\"";
      concepts = ["polymorphic variants"; "error composition"; "exhaustive matching"];
      difficulty = diff + 1;
      hints = ["Each error variant starts with backtick"; "Pattern match on all variants for exhaustive handling"] };
    { title = "Retry with Exponential Backoff";
      description = "Implement a retry combinator that retries a fallible function with increasing delays.";
      starter_code = "let retry ~max_attempts ~base_delay_ms f =\n  (* Retry f up to max_attempts times with exponential backoff *)\n  failwith \"TODO\"";
      concepts = ["exception handling"; "retry logic"; "Unix.sleepf"];
      difficulty = diff;
      hints = ["Loop with a counter; catch exceptions"; "Delay doubles each attempt: base * 2^attempt"] };
    ]
  | Abstraction -> [
    { title = "Opaque Collection Module";
      description = "Design a module with an abstract type t where the internal representation is completely hidden from users.";
      starter_code = "module type COLLECTION = sig\n  type 'a t\n  val empty : 'a t\n  val add : 'a -> 'a t -> 'a t\n  val fold : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b\n  val size : 'a t -> int\nend\n\nmodule BagCollection : COLLECTION = struct\n  (* your implementation - hidden from users *)\n  type 'a t = unit\n  let empty = ()\n  let add _ _ = failwith \"TODO\"\n  let fold _ _ _ = failwith \"TODO\"\n  let size _ = failwith \"TODO\"\nend";
      concepts = ["abstract types"; "module signatures"; "information hiding"];
      difficulty = diff;
      hints = ["Use 'a list as internal representation"; "Signature hides the list type from users"] };
    { title = "Smart Constructor Pattern";
      description = "Implement validated types using smart constructors that enforce invariants at creation time.";
      starter_code = "module Email : sig\n  type t (* abstract *)\n  val create : string -> (t, string) result\n  val to_string : t -> string\nend = struct\n  type t = string\n  let create s =\n    (* validate and return *) failwith \"TODO\"\n  let to_string t = t\nend";
      concepts = ["smart constructors"; "invariant enforcement"; "abstract types"];
      difficulty = diff + 1;
      hints = ["Validate that string contains '@' and '.'"; "Only way to create Email.t is through the checked create function"] };
    { title = "Capability-Based Interface";
      description = "Design an API where different modules get different capability tokens limiting what operations they can perform.";
      starter_code = "type read_cap\ntype write_cap\ntype admin_cap\n\nmodule type STORE = sig\n  val read : read_cap -> string -> string option\n  val write : write_cap -> string -> string -> unit\n  val delete : admin_cap -> string -> unit\nend";
      concepts = ["phantom types"; "capability pattern"; "access control"];
      difficulty = diff + 2;
      hints = ["Capabilities are phantom types - empty types used for access control"; "Only authorized modules receive the capability tokens"] };
    ]

(* ── Mastery Level Computation ──────────────────────────────────── *)

let compute_mastery scores =
  let avg = List.fold_left (fun acc s -> acc + s.score) 0 scores
            / (max 1 (List.length scores)) in
  let min_score = List.fold_left (fun acc s -> min acc s.score) 100 scores in
  if avg >= 85 && min_score >= 70 then Master
  else if avg >= 70 && min_score >= 50 then Expert
  else if avg >= 55 && min_score >= 35 then Journeyman
  else if avg >= 35 then Apprentice
  else Novice

(* ── Progress Persistence ───────────────────────────────────────── *)

let progress_file = ".mentor_progress.json"

let scores_to_json scores =
  let pairs = List.map (fun s ->
    Printf.sprintf "    \"%s\": %d" (dim_to_key s.dimension) s.score
  ) scores in
  "{\n" ^ (String.concat ",\n" pairs) ^ "\n  }"

let entry_to_json entry =
  let pairs = List.map (fun (k, v) ->
    Printf.sprintf "    \"%s\": %d" k v
  ) entry.scores in
  Printf.sprintf "  { \"timestamp\": \"%s\", \"scores\": {\n%s\n  } }"
    entry.timestamp (String.concat ",\n" pairs)

let save_progress state =
  let history_json = List.map entry_to_json state.history in
  let content = Printf.sprintf "{\n  \"streak_days\": %d,\n  \"mastery\": \"%s\",\n  \"history\": [\n%s\n  ]\n}\n"
    state.streak_days
    (mastery_to_string state.mastery)
    (String.concat ",\n" history_json) in
  ignore (write_file progress_file content)

let load_progress () =
  match read_file progress_file with
  | None -> { current_scores = []; gaps = []; exercises = [];
              mastery = Novice; history = []; streak_days = 0 }
  | Some content ->
    (* Simple JSON parsing for streak_days *)
    let streak = ref 0 in
    let lines = lines_of_string content in
    List.iter (fun line ->
      if string_contains line "streak_days" then begin
        let parts = String.split_on_char ':' line in
        match parts with
        | _ :: rest ->
          let num_str = String.concat ":" rest in
          let cleaned = String.trim num_str in
          let cleaned = if String.length cleaned > 0 &&
                           cleaned.[String.length cleaned - 1] = ','
                        then String.sub cleaned 0 (String.length cleaned - 1)
                        else cleaned in
          (try streak := int_of_string (String.trim cleaned) with _ -> ())
        | _ -> ()
      end
    ) lines;
    { current_scores = []; gaps = []; exercises = [];
      mastery = Novice; history = []; streak_days = !streak }

(* ── ASCII Visualization ────────────────────────────────────────── *)

let draw_progress_bar width score =
  let filled = score * width / 100 in
  let empty = width - filled in
  let bar_char = if score >= 70 then color_green "█"
                 else if score >= 50 then color_yellow "█"
                 else color_red "█" in
  let result = Buffer.create (width * 4) in
  for _ = 1 to filled do Buffer.add_string result bar_char done;
  for _ = 1 to empty do Buffer.add_string result "░" done;
  Buffer.contents result

let draw_radar scores =
  Printf.printf "\n%s\n\n" (color_bold "╔══════════════════════════════════════════════════════╗");
  Printf.printf "%s\n" (color_bold "║           🎯 SKILL RADAR — Code Mentor              ║");
  Printf.printf "%s\n\n" (color_bold "╚══════════════════════════════════════════════════════╝");
  List.iter (fun s ->
    let label = Printf.sprintf "%-22s" (dim_to_string s.dimension) in
    let bar = draw_progress_bar 30 s.score in
    let score_str = if s.score >= 70 then color_green (string_of_int s.score)
                    else if s.score >= 50 then color_yellow (string_of_int s.score)
                    else color_red (string_of_int s.score) in
    Printf.printf "  %s %s %s/100  (%d evidence)\n" label bar score_str s.evidence_count
  ) scores;
  let avg = List.fold_left (fun acc s -> acc + s.score) 0 scores
            / (max 1 (List.length scores)) in
  Printf.printf "\n  %s Overall: %d/100\n" (color_bold "📊") avg

let print_gaps gaps =
  if gaps = [] then
    Printf.printf "\n  %s No significant gaps detected — well done!\n" (color_green "✅")
  else begin
    Printf.printf "\n%s\n\n" (color_bold "  🔍 SKILL GAPS (Priority Order)");
    List.iteri (fun i gap ->
      let sev_color = match gap.gap_severity with
        | Critical -> color_red | Moderate -> color_yellow | Minor -> color_cyan in
      Printf.printf "  %d. %s [%s] — Score: %d/100\n"
        (i + 1) (dim_to_string gap.gap_dimension)
        (sev_color (severity_to_string gap.gap_severity)) gap.gap_score;
      Printf.printf "     💡 %s\n\n" gap.gap_suggestion
    ) gaps
  end

let print_exercises exercises =
  Printf.printf "\n%s\n\n" (color_bold "  📝 PERSONALIZED EXERCISES");
  List.iteri (fun i ex ->
    let stars = String.make ex.difficulty '★' ^ String.make (5 - ex.difficulty) '☆' in
    Printf.printf "  %s %s\n" (color_cyan (Printf.sprintf "━━━ Exercise %d ━━━" (i + 1))) stars;
    Printf.printf "  %s %s\n" (color_bold "Title:") ex.title;
    Printf.printf "  %s\n" ex.description;
    Printf.printf "  %s %s\n" (color_magenta "Concepts:") (String.concat ", " ex.concepts);
    Printf.printf "\n  %s\n" (color_bold "Starter Code:");
    let code_lines = lines_of_string ex.starter_code in
    List.iter (fun l -> Printf.printf "    %s\n" (color_cyan l)) code_lines;
    Printf.printf "\n  %s\n" (color_bold "Hints:");
    List.iteri (fun j h -> Printf.printf "    %d. %s\n" (j + 1) h) ex.hints;
    Printf.printf "\n"
  ) exercises

(* ── Export ─────────────────────────────────────────────────────── *)

let export_json state =
  let scores_j = List.map (fun s ->
    Printf.sprintf "    { \"dimension\": \"%s\", \"score\": %d, \"evidence\": %d }"
      (dim_to_key s.dimension) s.score s.evidence_count
  ) state.current_scores in
  let gaps_j = List.map (fun g ->
    Printf.sprintf "    { \"dimension\": \"%s\", \"score\": %d, \"severity\": \"%s\" }"
      (dim_to_key g.gap_dimension) g.gap_score (severity_to_string g.gap_severity)
  ) state.gaps in
  Printf.sprintf "{\n  \"mastery\": \"%s\",\n  \"streak_days\": %d,\n  \"scores\": [\n%s\n  ],\n  \"gaps\": [\n%s\n  ]\n}"
    (mastery_to_string state.mastery) state.streak_days
    (String.concat ",\n" scores_j) (String.concat ",\n" gaps_j)

(* ── Motivational Messages ──────────────────────────────────────── *)

let motivate mastery streak =
  let msg = match mastery with
    | Master -> "🏆 You've achieved mastery! Keep exploring the edges of OCaml."
    | Expert -> "🌟 Expert level! You command OCaml with confidence."
    | Journeyman -> "⚡ Solid progress! You're building real fluency."
    | Apprentice -> "🌱 Growing steadily! Each exercise strengthens your foundation."
    | Novice -> "🚀 Every master was once a beginner. Let's build those skills!" in
  Printf.printf "\n  %s\n" msg;
  if streak > 0 then
    Printf.printf "  🔥 Practice streak: %d day%s!\n" streak (if streak > 1 then "s" else "");
  Printf.printf "\n"

(* ── REPL ───────────────────────────────────────────────────────── *)

let print_help () =
  Printf.printf "\n%s\n\n" (color_bold "  📚 Code Mentor — Available Commands");
  Printf.printf "  %-14s  Run full skill assessment on all .ml files\n" "assess";
  Printf.printf "  %-14s  Show prioritized skill gaps\n" "gaps";
  Printf.printf "  %-14s  Generate personalized exercises for top gaps\n" "exercises";
  Printf.printf "  %-14s  Show mastery progression over time\n" "progress";
  Printf.printf "  %-14s  Deep-dive into a specific dimension\n" "focus <dim>";
  Printf.printf "  %-14s  Show practice streak and motivation\n" "streak";
  Printf.printf "  %-14s  Export assessment as JSON\n" "export";
  Printf.printf "  %-14s  Show this help\n" "help";
  Printf.printf "  %-14s  Exit\n\n" "quit";
  Printf.printf "  Dimensions: pattern_matching, higher_order, type_system, recursion,\n";
  Printf.printf "              modules_functors, concurrency, error_handling, abstraction\n\n"

let find_dimension_by_key key =
  List.find_opt (fun d -> dim_to_key d = key) all_dimensions

let run_repl () =
  Printf.printf "\n%s\n" (color_bold "  🧠 Code Mentor Engine — Autonomous Skill Development");
  Printf.printf "  Type 'help' for commands, 'quit' to exit.\n\n";
  let state = ref (load_progress ()) in
  let running = ref true in
  while !running do
    Printf.printf "%s " (color_cyan "mentor>");
    let input = try String.trim (read_line ()) with End_of_file -> "quit" in
    let parts = String.split_on_char ' ' input in
    match parts with
    | ["quit"] | ["exit"] | ["q"] ->
      Printf.printf "  👋 Keep practicing! See you next time.\n";
      running := false
    | ["help"] | ["h"] | ["?"] -> print_help ()
    | ["assess"] ->
      let files = discover_ml_files () in
      Printf.printf "  Scanning %d .ml files...\n" (List.length files);
      let scores = assess_all_files files in
      let gaps = detect_gaps scores in
      let mastery = compute_mastery scores in
      state := { !state with current_scores = scores; gaps; mastery;
                             streak_days = !state.streak_days + 1 };
      let entry = { timestamp = current_timestamp ();
                    scores = List.map (fun s -> (dim_to_key s.dimension, s.score)) scores } in
      state := { !state with history = entry :: !state.history };
      save_progress !state;
      draw_radar scores;
      motivate mastery !state.streak_days
    | ["gaps"] ->
      if !state.current_scores = [] then
        Printf.printf "  ⚠️  Run 'assess' first to analyze your code.\n"
      else
        print_gaps !state.gaps
    | ["exercises"] ->
      if !state.gaps = [] then
        Printf.printf "  ⚠️  Run 'assess' first, then check 'gaps'.\n"
      else begin
        let all_ex = List.concat_map generate_exercises_for_gap !state.gaps in
        state := { !state with exercises = all_ex };
        print_exercises all_ex
      end
    | ["progress"] ->
      Printf.printf "\n  %s Mastery Level: %s\n" (color_bold "📈")
        (color_bold (mastery_to_string !state.mastery));
      Printf.printf "  Sessions recorded: %d\n" (List.length !state.history);
      Printf.printf "  Practice streak: %d days\n\n" !state.streak_days;
      (match !state.history with
       | [] -> Printf.printf "  No history yet. Run 'assess' to start tracking.\n"
       | entries ->
         let recent = match entries with
           | a :: b :: c :: _ -> [a; b; c]
           | lst -> lst in
         Printf.printf "  Recent assessments:\n";
         List.iter (fun e ->
           Printf.printf "    %s — " e.timestamp;
           let avg = List.fold_left (fun acc (_, v) -> acc + v) 0 e.scores
                     / (max 1 (List.length e.scores)) in
           Printf.printf "avg: %d/100\n" avg
         ) recent)
    | "focus" :: dim_key :: _ ->
      let key = String.trim dim_key in
      (match find_dimension_by_key key with
       | None -> Printf.printf "  ❌ Unknown dimension '%s'. See 'help' for list.\n" key
       | Some dim ->
         let gap = { gap_dimension = dim; gap_score = 40;
                     gap_severity = Moderate;
                     gap_suggestion = "Focused practice session" } in
         let exs = generate_exercises_for_gap gap in
         Printf.printf "\n  %s Deep-dive: %s\n" (color_bold "🔬") (dim_to_string dim);
         print_exercises exs)
    | ["streak"] ->
      Printf.printf "\n  🔥 Practice streak: %d day%s\n"
        !state.streak_days (if !state.streak_days <> 1 then "s" else "");
      motivate !state.mastery !state.streak_days
    | ["export"] ->
      let json = export_json !state in
      Printf.printf "\n%s\n\n" json;
      if write_file "mentor_export.json" json then
        Printf.printf "  💾 Exported to mentor_export.json\n"
      else
        Printf.printf "  ❌ Failed to write export file.\n"
    | [""] -> ()
    | _ -> Printf.printf "  ❓ Unknown command. Type 'help' for options.\n"
  done

(* ── Main Entry Point ───────────────────────────────────────────── *)

let () =
  Printf.printf "\n%s\n" (color_bold "  ╔═══════════════════════════════════════════════════╗");
  Printf.printf "%s\n" (color_bold "  ║     🧠 Autonomous Code Mentor Engine v1.0        ║");
  Printf.printf "%s\n\n" (color_bold "  ╚═══════════════════════════════════════════════════╝");
  Printf.printf "  Analyzes your OCaml code to identify strengths, gaps,\n";
  Printf.printf "  and generates personalized exercises for improvement.\n";
  run_repl ()
