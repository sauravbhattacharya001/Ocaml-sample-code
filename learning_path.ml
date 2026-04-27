(* learning_path.ml — Learning Path Advisor
   Autonomous knowledge assessment and personalized learning path
   generator for OCaml learners.

   Features:
   - Catalog of 30+ concept categories with dependency graph
   - Knowledge assessment quiz (15 adaptive questions)
   - Skill-level inference from quiz results
   - Personalized learning path generation with optimal ordering
   - Topological sort respecting prerequisites
   - Difficulty-adaptive recommendations
   - Estimated time per topic
   - Progress tracking with mastery scores
   - Gap analysis: identifies weakest prerequisite chains
   - Interactive REPL for exploration and assessment

   Usage: ocaml learning_path.ml
*)

(* ── Concept Categories ──────────────────────────────────────────── *)

type difficulty = Beginner | Intermediate | Advanced | Expert

type concept = {
  id : string;
  name : string;
  difficulty : difficulty;
  prereqs : string list;
  files : string list;
  description : string;
  est_hours : float;
}

let difficulty_to_string = function
  | Beginner -> "Beginner"
  | Intermediate -> "Intermediate"
  | Advanced -> "Advanced"
  | Expert -> "Expert"

let difficulty_to_int = function
  | Beginner -> 1 | Intermediate -> 2 | Advanced -> 3 | Expert -> 4

(* ── Concept Catalog ─────────────────────────────────────────────── *)

let catalog : concept list = [
  { id = "basics"; name = "OCaml Basics";
    difficulty = Beginner; prereqs = [];
    files = ["hello.ml"; "fibonacci.ml"; "factor.ml"; "list_last_elem.ml"];
    description = "Let bindings, type inference, pattern matching, pipes, basic recursion";
    est_hours = 3.0 };

  { id = "adt"; name = "Algebraic Data Types";
    difficulty = Beginner; prereqs = ["basics"];
    files = ["bst.ml"; "heap.ml"];
    description = "Variant types, records, polymorphic types, tree structures";
    est_hours = 4.0 };

  { id = "higher_order"; name = "Higher-Order Functions";
    difficulty = Beginner; prereqs = ["basics"];
    files = ["mergesort.ml"; "quickcheck.ml"];
    description = "Functions as values, map, fold, filter, closures, currying";
    est_hours = 3.0 };

  { id = "pattern_matching"; name = "Pattern Matching & Options";
    difficulty = Beginner; prereqs = ["basics"; "adt"];
    files = ["list_last_elem.ml"; "json.ml"];
    description = "Deep matching, guard clauses, option types, exhaustiveness";
    est_hours = 2.0 };

  { id = "modules"; name = "Modules & Signatures";
    difficulty = Intermediate; prereqs = ["adt"; "higher_order"];
    files = ["matrix.ml"; "hashmap.ml"; "graph.ml"];
    description = "Module signatures, structures, abstract types, encapsulation";
    est_hours = 4.0 };

  { id = "functors"; name = "Functors";
    difficulty = Intermediate; prereqs = ["modules"];
    files = ["matrix.ml"; "fenwick_tree.ml"; "game_ai.ml"];
    description = "Parameterized modules, functor signatures, module composition";
    est_hours = 5.0 };

  { id = "tail_recursion"; name = "Tail Recursion & Accumulators";
    difficulty = Intermediate; prereqs = ["basics"; "higher_order"];
    files = ["mergesort.ml"; "fibonacci.ml"];
    description = "Stack-safe recursion, continuation passing, accumulator patterns";
    est_hours = 2.0 };

  { id = "persistent_ds"; name = "Persistent Data Structures";
    difficulty = Intermediate; prereqs = ["adt"; "modules"];
    files = ["queue.ml"; "deque.ml"; "finger_tree.ml"; "persistent_vector.ml"; "hamt.ml"];
    description = "Structural sharing, amortized analysis, Okasaki-style collections";
    est_hours = 6.0 };

  { id = "hash_tables"; name = "Hash Tables & Memoization";
    difficulty = Intermediate; prereqs = ["modules"; "higher_order"];
    files = ["fibonacci.ml"; "hashmap.ml"; "lru_cache.ml"; "bloom_filter.ml"];
    description = "Imperative hash tables, memoization, probabilistic structures";
    est_hours = 4.0 };

  { id = "graph_algos"; name = "Graph Algorithms";
    difficulty = Intermediate; prereqs = ["modules"; "adt"];
    files = ["graph.ml"; "dijkstra.ml"; "network_flow.ml"];
    description = "BFS, DFS, shortest paths, MST, max flow, topological sort";
    est_hours = 6.0 };

  { id = "parsing"; name = "Parser Combinators";
    difficulty = Intermediate; prereqs = ["higher_order"; "adt"];
    files = ["parser.ml"; "json.ml"; "csv.ml"; "peg.ml"; "earley.ml"];
    description = "Recursive descent, monadic parsing, PEG, Earley";
    est_hours = 6.0 };

  { id = "monads"; name = "Monads & Composition";
    difficulty = Advanced; prereqs = ["higher_order"; "modules"];
    files = ["probability.ml"; "free_monad.ml"; "monad_transformers.ml"];
    description = "Monadic bind, return, transformers, free monads";
    est_hours = 6.0 };

  { id = "gadts_type"; name = "GADTs & Type-Level Programming";
    difficulty = Advanced; prereqs = ["adt"; "functors"];
    files = ["gadts.ml"];
    description = "Generalized ADTs, type witnesses, length-indexed vectors";
    est_hours = 5.0 };

  { id = "effects"; name = "Algebraic Effects & Handlers";
    difficulty = Advanced; prereqs = ["monads"];
    files = ["effects.ml"; "delimited_cont.ml"];
    description = "Effect handlers, delimited continuations, composable effects";
    est_hours = 5.0 };

  { id = "comonads"; name = "Comonads";
    difficulty = Expert; prereqs = ["monads"; "functors"];
    files = ["comonad.ml"];
    description = "Extract/extend, zippers, cellular automata, context-dependent computation";
    est_hours = 4.0 };

  { id = "optics"; name = "Optics (Lenses & Prisms)";
    difficulty = Advanced; prereqs = ["modules"; "higher_order"];
    files = ["optics.ml"];
    description = "Composable getters/setters, lenses, prisms, traversals";
    est_hours = 4.0 };

  { id = "lambda_calc"; name = "Lambda Calculus";
    difficulty = Advanced; prereqs = ["adt"; "pattern_matching"];
    files = ["lambda.ml"];
    description = "Untyped lambda calculus, substitution, reduction strategies";
    est_hours = 4.0 };

  { id = "type_inference"; name = "Type Inference (HM)";
    difficulty = Expert; prereqs = ["lambda_calc"; "monads"];
    files = ["type_inference.ml"];
    description = "Hindley-Milner, unification, constraint solving, let-polymorphism";
    est_hours = 6.0 };

  { id = "logic_prog"; name = "Logic Programming";
    difficulty = Advanced; prereqs = ["adt"; "parsing"];
    files = ["minikanren.ml"; "datalog.ml"];
    description = "Unification, relational programming, Datalog, miniKanren";
    est_hours = 5.0 };

  { id = "automata"; name = "Automata & Formal Languages";
    difficulty = Intermediate; prereqs = ["adt"; "modules"];
    files = ["automata.ml"; "fsm.ml"; "regex.ml"];
    description = "DFA/NFA, subset construction, minimization, regex matching";
    est_hours = 5.0 };

  { id = "concurrency"; name = "Concurrency Models";
    difficulty = Advanced; prereqs = ["modules"; "effects"];
    files = ["actor.ml"; "dining_philosophers.ml"; "gossip.ml"; "crdt.ml"];
    description = "Actors, CSP, CRDTs, gossip protocols, distributed systems";
    est_hours = 6.0 };

  { id = "symbolic"; name = "Symbolic Computation";
    difficulty = Advanced; prereqs = ["adt"; "pattern_matching"];
    files = ["calculus.ml"; "integration.ml"];
    description = "Symbolic differentiation/integration, algebraic simplification";
    est_hours = 5.0 };

  { id = "neural_ml"; name = "Neural Networks & ML";
    difficulty = Advanced; prereqs = ["higher_order"; "modules"];
    files = ["neural_network.ml"; "autodiff.ml"; "genetic.ml"; "bandit.ml"];
    description = "Backpropagation, autodiff, genetic algorithms, multi-armed bandits";
    est_hours = 6.0 };

  { id = "verification"; name = "Verification & Model Checking";
    difficulty = Expert; prereqs = ["logic_prog"; "automata"];
    files = ["model_checker.ml"; "sat.ml"; "theorem_prover.ml"];
    description = "CTL model checking, SAT solving, theorem proving";
    est_hours = 7.0 };

  { id = "vm_compiler"; name = "VMs & Compilers";
    difficulty = Advanced; prereqs = ["parsing"; "modules"];
    files = ["bytecode_vm.ml"; "rewrite.ml"];
    description = "Bytecode VMs, term rewriting, compilation";
    est_hours = 6.0 };

  { id = "geometry"; name = "Computational Geometry";
    difficulty = Intermediate; prereqs = ["basics"; "adt"];
    files = ["geometry.ml"; "interval_tree.ml"];
    description = "Convex hull, closest pair, sweep line, interval trees";
    est_hours = 4.0 };

  { id = "crypto_class"; name = "Classical Cryptography";
    difficulty = Intermediate; prereqs = ["basics"];
    files = ["crypto.ml"; "merkle_tree.ml"];
    description = "Caesar, Vigenere, XOR, Merkle trees, hash-based structures";
    est_hours = 3.0 };

  { id = "graphics"; name = "Graphics & Visualization";
    difficulty = Intermediate; prereqs = ["basics"; "higher_order"];
    files = ["lsystem.ml"; "ray_tracer.ml"; "signal.ml"];
    description = "L-systems, turtle graphics, SVG, ray tracing, signal processing";
    est_hours = 5.0 };

  { id = "frp"; name = "Functional Reactive Programming";
    difficulty = Expert; prereqs = ["monads"; "effects"];
    files = ["frp.ml"];
    description = "Signals, behaviors, events, push-based reactivity, animation";
    est_hours = 5.0 };

  { id = "agent_ai"; name = "Agent AI & Planning";
    difficulty = Advanced; prereqs = ["adt"; "graph_algos"];
    files = ["behavior_tree.ml"; "bdi_agent.ml"; "game_ai.ml"];
    description = "Behavior trees, BDI agents, minimax, game AI";
    est_hours = 5.0 };
]

(* ── Knowledge Graph Operations ──────────────────────────────────── *)

let find_concept id =
  List.find_opt (fun c -> c.id = id) catalog

let all_prereqs_deep id =
  let visited = Hashtbl.create 16 in
  let rec walk cid =
    if Hashtbl.mem visited cid then ()
    else begin
      Hashtbl.replace visited cid true;
      match find_concept cid with
      | None -> ()
      | Some c -> List.iter walk c.prereqs
    end
  in
  walk id;
  Hashtbl.fold (fun k _ acc -> if k <> id then k :: acc else acc) visited []

(* topological sort via Kahn's algorithm *)
let topological_sort (concepts : concept list) =
  let n = List.length concepts in
  let id_to_idx = Hashtbl.create n in
  let idx_to_c = Array.make n (List.hd concepts) in
  List.iteri (fun i c ->
    Hashtbl.replace id_to_idx c.id i;
    idx_to_c.(i) <- c
  ) concepts;
  let in_deg = Array.make n 0 in
  let adj = Array.make n [] in
  List.iter (fun c ->
    let ci = Hashtbl.find id_to_idx c.id in
    List.iter (fun pid ->
      match Hashtbl.find_opt id_to_idx pid with
      | Some pi ->
        adj.(pi) <- ci :: adj.(pi);
        in_deg.(ci) <- in_deg.(ci) + 1
      | None -> ()
    ) c.prereqs
  ) concepts;
  let queue = Queue.create () in
  Array.iteri (fun i d -> if d = 0 then Queue.push i queue) in_deg;
  let result = ref [] in
  while not (Queue.is_empty queue) do
    let u = Queue.pop queue in
    result := u :: !result;
    List.iter (fun v ->
      in_deg.(v) <- in_deg.(v) - 1;
      if in_deg.(v) = 0 then Queue.push v queue
    ) adj.(u)
  done;
  List.rev_map (fun i -> idx_to_c.(i)) (List.rev !result)

(* ── Quiz Engine ─────────────────────────────────────────────────── *)

type question = {
  q_text : string;
  q_options : string list;
  q_answer : int;  (* 0-indexed *)
  q_concept : string;
  q_diff : difficulty;
}

let questions : question list = [
  { q_text = "What does 'let x = 5 in x + 1' evaluate to?";
    q_options = ["5"; "6"; "Error"; "x + 1"];
    q_answer = 1; q_concept = "basics"; q_diff = Beginner };

  { q_text = "What is the type of 'fun x -> x'?";
    q_options = ["int -> int"; "'a -> 'a"; "string -> string"; "unit -> unit"];
    q_answer = 1; q_concept = "basics"; q_diff = Beginner };

  { q_text = "Which keyword introduces a variant type?";
    q_options = ["struct"; "type"; "let"; "module"];
    q_answer = 1; q_concept = "adt"; q_diff = Beginner };

  { q_text = "What does List.fold_left f init [a;b;c] compute?";
    q_options = ["f a (f b (f c init))"; "f (f (f init a) b) c";
                 "f init [a;b;c]"; "[f a; f b; f c]"];
    q_answer = 1; q_concept = "higher_order"; q_diff = Beginner };

  { q_text = "How do you make a recursive function tail-recursive?";
    q_options = ["Use 'rec' keyword"; "Add an accumulator parameter";
                 "Use a for loop"; "Wrap in lazy"];
    q_answer = 1; q_concept = "tail_recursion"; q_diff = Intermediate };

  { q_text = "What does 'module type S = sig val x : int end' define?";
    q_options = ["A functor"; "A module signature"; "A type alias"; "A class"];
    q_answer = 1; q_concept = "modules"; q_diff = Intermediate };

  { q_text = "What is a functor in OCaml?";
    q_options = ["A function that maps types"; "A module parameterized by another module";
                 "A type constructor"; "A monad"];
    q_answer = 1; q_concept = "functors"; q_diff = Intermediate };

  { q_text = "Which data structure provides amortized O(1) enqueue and dequeue?";
    q_options = ["Array"; "Banker's Queue (two-list queue)"; "Linked list"; "Hash table"];
    q_answer = 1; q_concept = "persistent_ds"; q_diff = Intermediate };

  { q_text = "What is the purpose of 'Option.bind'?";
    q_options = ["Create an option"; "Chain computations that may fail";
                 "Convert to string"; "Pattern match"];
    q_answer = 1; q_concept = "monads"; q_diff = Advanced };

  { q_text = "In a GADT, what does the return type annotation enable?";
    q_options = ["Faster compilation"; "Type refinement in pattern match branches";
                 "Polymorphic recursion"; "Tail call optimization"];
    q_answer = 1; q_concept = "gadts_type"; q_diff = Advanced };

  { q_text = "What distinguishes algebraic effects from monads for effect handling?";
    q_options = ["Effects are faster"; "Effects compose without transformers";
                 "Monads can't handle state"; "Effects require GADTs"];
    q_answer = 1; q_concept = "effects"; q_diff = Advanced };

  { q_text = "What is 'extract' in a comonad?";
    q_options = ["Unwrap the focused value from context";
                 "Remove an element from a list";
                 "Extract a module from a signature"; "Dereference a ref"];
    q_answer = 0; q_concept = "comonads"; q_diff = Expert };

  { q_text = "In Hindley-Milner type inference, what does unification do?";
    q_options = ["Merge two modules"; "Find substitution making two types equal";
                 "Optimize tail calls"; "Resolve ambiguous names"];
    q_answer = 1; q_concept = "type_inference"; q_diff = Expert };

  { q_text = "What is a lens in functional programming?";
    q_options = ["A debugging tool"; "A composable getter/setter pair";
                 "A type of monad"; "A compiler optimization"];
    q_answer = 1; q_concept = "optics"; q_diff = Advanced };

  { q_text = "In miniKanren, what does 'fresh' introduce?";
    q_options = ["A new function"; "A new logic variable";
                 "A fresh module"; "A new type"];
    q_answer = 1; q_concept = "logic_prog"; q_diff = Advanced };
]

(* ── Skill Assessment ────────────────────────────────────────────── *)

type assessment = {
  concept_scores : (string * float) list;  (* concept_id -> 0.0..1.0 *)
  overall_level : difficulty;
  strengths : string list;
  weaknesses : string list;
}

let assess_quiz (answers : (string * bool) list) : assessment =
  (* group by concept *)
  let concept_tbl = Hashtbl.create 16 in
  List.iter (fun (cid, correct) ->
    let (total, right) =
      match Hashtbl.find_opt concept_tbl cid with
      | Some (t, r) -> (t, r)
      | None -> (0, 0)
    in
    Hashtbl.replace concept_tbl cid
      (total + 1, if correct then right + 1 else right)
  ) answers;
  let scores = Hashtbl.fold (fun cid (t, r) acc ->
    (cid, float_of_int r /. float_of_int t) :: acc
  ) concept_tbl [] in
  let avg = if scores = [] then 0.0
    else List.fold_left (fun a (_, s) -> a +. s) 0.0 scores
         /. float_of_int (List.length scores) in
  let level =
    if avg >= 0.85 then Expert
    else if avg >= 0.65 then Advanced
    else if avg >= 0.4 then Intermediate
    else Beginner in
  let strengths = List.filter_map (fun (cid, s) ->
    if s >= 0.7 then Some cid else None) scores in
  let weaknesses = List.filter_map (fun (cid, s) ->
    if s < 0.5 then Some cid else None) scores in
  { concept_scores = scores; overall_level = level;
    strengths; weaknesses }

(* ── Learning Path Generator ─────────────────────────────────────── *)

type path_entry = {
  concept : concept;
  reason : string;
  priority : int;  (* 1=critical, 2=recommended, 3=enrichment *)
  mastery : float;  (* 0.0=unknown, from assessment *)
}

let generate_path (assess : assessment option) : path_entry list =
  let mastery_of cid = match assess with
    | None -> 0.0
    | Some a ->
      match List.assoc_opt cid a.concept_scores with
      | Some s -> s | None -> 0.0
  in
  let level = match assess with
    | None -> Beginner
    | Some a -> a.overall_level in
  let max_diff = match level with
    | Beginner -> 2 | Intermediate -> 3 | Advanced -> 4 | Expert -> 4 in
  (* filter concepts within reach *)
  let reachable = List.filter (fun c ->
    difficulty_to_int c.difficulty <= max_diff
  ) catalog in
  (* exclude already-mastered concepts *)
  let needed = List.filter (fun c ->
    mastery_of c.id < 0.85
  ) reachable in
  (* topological sort *)
  let sorted = topological_sort needed in
  (* assign priorities *)
  List.map (fun c ->
    let m = mastery_of c.id in
    let is_weak = match assess with
      | None -> false
      | Some a -> List.mem c.id a.weaknesses in
    let is_prereq_of_weak = match assess with
      | None -> false
      | Some a -> List.exists (fun wid ->
          match find_concept wid with
          | Some wc -> List.mem c.id wc.prereqs
          | None -> false
        ) a.weaknesses in
    let priority =
      if is_weak || is_prereq_of_weak then 1
      else if m < 0.5 then 2
      else 3 in
    let reason =
      if is_weak then "Weak area — needs focused practice"
      else if is_prereq_of_weak then
        "Prerequisite for a weak area — strengthen foundation"
      else if m < 0.3 then "New topic to explore"
      else if m < 0.5 then "Partially familiar — deepen understanding"
      else "Enrichment — expand breadth" in
    { concept = c; reason; priority; mastery = m }
  ) sorted

(* ── Gap Analysis ────────────────────────────────────────────────── *)

type gap = {
  gap_concept : string;
  gap_chain : string list;  (* prerequisite chain leading to gap *)
  severity : float;  (* 0.0 = fine, 1.0 = critical *)
}

let analyze_gaps (assess : assessment) : gap list =
  let mastery_of cid =
    match List.assoc_opt cid assess.concept_scores with
    | Some s -> s | None -> 0.0
  in
  List.filter_map (fun c ->
    let prereq_scores = List.filter_map (fun pid ->
      let s = mastery_of pid in
      if s < 0.5 then Some (pid, s) else None
    ) c.prereqs in
    if prereq_scores = [] then None
    else
      let chain = List.map fst prereq_scores in
      let severity = 1.0 -. (List.fold_left (fun a (_, s) -> a +. s) 0.0
        prereq_scores /. float_of_int (List.length prereq_scores)) in
      Some { gap_concept = c.id; gap_chain = chain; severity }
  ) catalog
  |> List.sort (fun a b -> compare b.severity a.severity)

(* ── Progress Tracker ────────────────────────────────────────────── *)

type progress = {
  completed : (string, float) Hashtbl.t;  (* concept_id -> mastery 0-1 *)
  total_hours : float;
  current_streak : int;
}

let create_progress () = {
  completed = Hashtbl.create 16;
  total_hours = 0.0;
  current_streak = 0;
}

let mark_complete prog cid mastery =
  let hours = match find_concept cid with
    | Some c -> c.est_hours | None -> 0.0 in
  Hashtbl.replace prog.completed cid mastery;
  { prog with total_hours = prog.total_hours +. hours;
              current_streak = prog.current_streak + 1 }

let progress_summary prog =
  let n = Hashtbl.length prog.completed in
  let total = List.length catalog in
  let avg_mastery = if n = 0 then 0.0
    else Hashtbl.fold (fun _ m acc -> acc +. m) prog.completed 0.0
         /. float_of_int n in
  Printf.sprintf "%d/%d topics (%.0f%%) | %.1f hours | avg mastery %.0f%% | streak %d"
    n total (100.0 *. float_of_int n /. float_of_int total)
    prog.total_hours (100.0 *. avg_mastery) prog.current_streak

(* ── Autonomous Recommendations ──────────────────────────────────── *)

type recommendation = {
  rec_concept : concept;
  rec_reason : string;
  rec_confidence : float;
  rec_next_steps : string list;
}

let recommend_next (assess : assessment option) (prog : progress) : recommendation list =
  let mastery_of cid =
    match Hashtbl.find_opt prog.completed cid with
    | Some m -> m
    | None -> match assess with
      | Some a -> (match List.assoc_opt cid a.concept_scores with
                   | Some s -> s | None -> 0.0)
      | None -> 0.0
  in
  (* find concepts whose prereqs are all >= 0.5 but concept itself < 0.7 *)
  let ready = List.filter (fun c ->
    let self_m = mastery_of c.id in
    let prereqs_ok = List.for_all (fun pid -> mastery_of pid >= 0.5) c.prereqs in
    prereqs_ok && self_m < 0.7
  ) catalog in
  (* score by: lower mastery = higher priority, lower difficulty first for ties *)
  let scored = List.map (fun c ->
    let m = mastery_of c.id in
    let score = (1.0 -. m) *. 0.7
      +. (1.0 -. float_of_int (difficulty_to_int c.difficulty) /. 4.0) *. 0.3 in
    (c, score)
  ) ready in
  let sorted = List.sort (fun (_, a) (_, b) -> compare b a) scored in
  let top = List.filteri (fun i _ -> i < 5) sorted in
  List.map (fun (c, conf) ->
    let next_steps = List.filter_map (fun other ->
      if List.mem c.id other.prereqs && mastery_of other.id < 0.5
      then Some (Printf.sprintf "Unlocks: %s" other.name)
      else None
    ) catalog in
    { rec_concept = c;
      rec_reason = Printf.sprintf "Ready to learn (prereqs met, current mastery %.0f%%)"
        (100.0 *. mastery_of c.id);
      rec_confidence = conf;
      rec_next_steps = if next_steps = [] then ["Deepens your overall OCaml expertise"]
                       else next_steps }
  ) top

(* ── Display Helpers ─────────────────────────────────────────────── *)

let bar width frac =
  let filled = int_of_float (frac *. float_of_int width) in
  let empty = width - filled in
  String.make filled '#' ^ String.make empty '-'

let print_header title =
  let line = String.make 60 '=' in
  Printf.printf "\n%s\n  %s\n%s\n\n" line title line

let print_concept c =
  Printf.printf "  %-25s [%s] ~%.1fh\n" c.name
    (difficulty_to_string c.difficulty) c.est_hours;
  Printf.printf "    %s\n" c.description;
  Printf.printf "    Files: %s\n" (String.concat ", " c.files);
  if c.prereqs <> [] then
    Printf.printf "    Prereqs: %s\n"
      (String.concat ", " (List.filter_map (fun pid ->
        match find_concept pid with
        | Some p -> Some p.name | None -> Some pid
      ) c.prereqs))

(* ── Interactive REPL ────────────────────────────────────────────── *)

let () =
  Random.self_init ();
  let assessment = ref None in
  let progress = ref (create_progress ()) in

  let show_help () =
    print_header "Learning Path Advisor — Commands";
    Printf.printf "  catalog       Show all %d concept categories\n" (List.length catalog);
    Printf.printf "  quiz          Take the knowledge assessment quiz\n";
    Printf.printf "  path          Generate your personalized learning path\n";
    Printf.printf "  recommend     Get top 5 next-step recommendations\n";
    Printf.printf "  gaps          Analyze knowledge gaps (requires quiz)\n";
    Printf.printf "  progress      Show your progress summary\n";
    Printf.printf "  complete <id> Mark a concept as completed\n";
    Printf.printf "  info <id>     Show details for a concept\n";
    Printf.printf "  deps <id>     Show full dependency chain\n";
    Printf.printf "  stats         Show catalog statistics\n";
    Printf.printf "  help          Show this help\n";
    Printf.printf "  quit          Exit\n\n"
  in

  let run_quiz () =
    print_header "Knowledge Assessment Quiz";
    Printf.printf "Answer %d questions to assess your OCaml knowledge.\n"
      (List.length questions);
    Printf.printf "Enter the number of your answer (1-%d).\n\n"
      (List.length (List.hd questions).q_options);
    let results = ref [] in
    List.iteri (fun qi q ->
      Printf.printf "Q%d [%s] %s\n" (qi + 1)
        (difficulty_to_string q.q_diff) q.q_text;
      List.iteri (fun oi opt ->
        Printf.printf "  %d) %s\n" (oi + 1) opt
      ) q.q_options;
      Printf.printf "> %!";
      let line = try input_line stdin with End_of_file -> "0" in
      let choice = (try int_of_string (String.trim line) with _ -> 0) - 1 in
      let correct = choice = q.q_answer in
      if correct then Printf.printf "  ✓ Correct!\n\n"
      else Printf.printf "  ✗ The answer was: %s\n\n"
        (List.nth q.q_options q.q_answer);
      results := (q.q_concept, correct) :: !results
    ) questions;
    let a = assess_quiz (List.rev !results) in
    assessment := Some a;
    print_header "Assessment Results";
    Printf.printf "  Overall Level: %s\n\n" (difficulty_to_string a.overall_level);
    Printf.printf "  Concept Scores:\n";
    List.iter (fun (cid, score) ->
      let name = match find_concept cid with
        | Some c -> c.name | None -> cid in
      Printf.printf "    %-25s [%s] %.0f%%\n" name (bar 20 score)
        (100.0 *. score)
    ) (List.sort (fun (_, a) (_, b) -> compare b a) a.concept_scores);
    Printf.printf "\n  Strengths: %s\n"
      (if a.strengths = [] then "(none identified)"
       else String.concat ", " (List.filter_map (fun cid ->
         match find_concept cid with Some c -> Some c.name | None -> None
       ) a.strengths));
    Printf.printf "  Weaknesses: %s\n"
      (if a.weaknesses = [] then "(none identified)"
       else String.concat ", " (List.filter_map (fun cid ->
         match find_concept cid with Some c -> Some c.name | None -> None
       ) a.weaknesses));
    Printf.printf "\n  Tip: Run 'path' to get a personalized learning plan!\n"
  in

  let show_path () =
    let path = generate_path !assessment in
    print_header "Your Personalized Learning Path";
    let total_hours = List.fold_left (fun a e -> a +. e.concept.est_hours) 0.0 path in
    Printf.printf "  %d topics | ~%.0f hours total\n\n" (List.length path) total_hours;
    let priorities = [1, "CRITICAL"; 2, "RECOMMENDED"; 3, "ENRICHMENT"] in
    List.iter (fun (p, label) ->
      let entries = List.filter (fun e -> e.priority = p) path in
      if entries <> [] then begin
        Printf.printf "  ── %s ──\n" label;
        List.iteri (fun i e ->
          Printf.printf "  %d. %-25s [%s] ~%.1fh\n" (i + 1)
            e.concept.name (bar 10 e.mastery) e.concept.est_hours;
          Printf.printf "     %s\n" e.reason;
          Printf.printf "     Files: %s\n" (String.concat ", " e.concept.files)
        ) entries;
        Printf.printf "\n"
      end
    ) priorities
  in

  let show_recommendations () =
    let recs = recommend_next !assessment !progress in
    print_header "Top Recommendations";
    if recs = [] then
      Printf.printf "  No recommendations — you've mastered everything! 🎉\n"
    else
      List.iteri (fun i r ->
        Printf.printf "  %d. %s (confidence: %.0f%%)\n" (i + 1)
          r.rec_concept.name (100.0 *. r.rec_confidence);
        Printf.printf "     %s\n" r.rec_reason;
        List.iter (fun s -> Printf.printf "     → %s\n" s) r.rec_next_steps;
        Printf.printf "\n"
      ) recs
  in

  let show_gaps () =
    match !assessment with
    | None -> Printf.printf "  Take the quiz first to identify gaps.\n"
    | Some a ->
      let gaps = analyze_gaps a in
      print_header "Knowledge Gap Analysis";
      if gaps = [] then
        Printf.printf "  No significant gaps detected! 🎯\n"
      else begin
        List.iteri (fun i g ->
          let name = match find_concept g.gap_concept with
            | Some c -> c.name | None -> g.gap_concept in
          Printf.printf "  %d. %s (severity: %.0f%%)\n" (i + 1)
            name (100.0 *. g.severity);
          Printf.printf "     Missing prereqs: %s\n"
            (String.concat ", " (List.filter_map (fun pid ->
              match find_concept pid with
              | Some c -> Some c.name | None -> Some pid
            ) g.gap_chain));
          Printf.printf "\n"
        ) (List.filteri (fun i _ -> i < 10) gaps)
      end
  in

  let show_stats () =
    print_header "Catalog Statistics";
    let by_diff d = List.length (List.filter (fun c -> c.difficulty = d) catalog) in
    Printf.printf "  Total concepts: %d\n" (List.length catalog);
    Printf.printf "  Beginner:       %d\n" (by_diff Beginner);
    Printf.printf "  Intermediate:   %d\n" (by_diff Intermediate);
    Printf.printf "  Advanced:       %d\n" (by_diff Advanced);
    Printf.printf "  Expert:         %d\n" (by_diff Expert);
    let total_hours = List.fold_left (fun a c -> a +. c.est_hours) 0.0 catalog in
    Printf.printf "  Total est. hours: %.0f\n" total_hours;
    let total_files = List.fold_left (fun a c ->
      a + List.length c.files) 0 catalog in
    Printf.printf "  Total files referenced: %d\n" total_files;
    let dep_count = List.fold_left (fun a c ->
      a + List.length c.prereqs) 0 catalog in
    Printf.printf "  Dependency edges: %d\n" dep_count
  in

  (* ── Main loop ── *)
  print_header "🐫 OCaml Learning Path Advisor";
  Printf.printf "  Autonomous knowledge assessment and personalized learning paths\n";
  Printf.printf "  for the OCaml Sample Code collection (%d concepts, %d files).\n\n"
    (List.length catalog)
    (List.fold_left (fun a c -> a + List.length c.files) 0 catalog);
  Printf.printf "  Type 'help' for commands, 'quiz' to start assessment.\n\n";

  let running = ref true in
  while !running do
    Printf.printf "advisor> %!";
    let line = try input_line stdin with End_of_file -> "quit" in
    let parts = String.split_on_char ' ' (String.trim line) in
    match parts with
    | ["quit"] | ["exit"] | ["q"] ->
      Printf.printf "Happy learning! 🐫\n"; running := false
    | ["help"] | ["h"] | ["?"] -> show_help ()
    | ["catalog"] | ["cat"] | ["list"] ->
      print_header "Concept Catalog";
      List.iter (fun c ->
        Printf.printf "  %-15s %-25s [%s]\n"
          c.id c.name (difficulty_to_string c.difficulty)
      ) catalog
    | ["quiz"] | ["assess"] -> run_quiz ()
    | ["path"] | ["plan"] -> show_path ()
    | ["recommend"] | ["rec"] | ["next"] -> show_recommendations ()
    | ["gaps"] | ["gap"] -> show_gaps ()
    | ["progress"] | ["prog"] ->
      Printf.printf "  %s\n" (progress_summary !progress)
    | ["complete"; cid] | ["done"; cid] ->
      (match find_concept cid with
       | None -> Printf.printf "  Unknown concept: %s\n" cid
       | Some c ->
         progress := mark_complete !progress cid 0.8;
         Printf.printf "  ✓ Marked '%s' complete! %s\n"
           c.name (progress_summary !progress))
    | ["info"; cid] ->
      (match find_concept cid with
       | None -> Printf.printf "  Unknown concept: %s\n" cid
       | Some c ->
         Printf.printf "\n"; print_concept c;
         let deep = all_prereqs_deep cid in
         if deep <> [] then
           Printf.printf "    Full prereq chain: %s\n"
             (String.concat " → " (List.filter_map (fun pid ->
               match find_concept pid with
               | Some p -> Some p.name | None -> None
             ) deep));
         Printf.printf "\n")
    | ["deps"; cid] ->
      (match find_concept cid with
       | None -> Printf.printf "  Unknown concept: %s\n" cid
       | Some c ->
         let deep = all_prereqs_deep cid in
         Printf.printf "  %s depends on:\n" c.name;
         if deep = [] then Printf.printf "    (no prerequisites)\n"
         else List.iter (fun pid ->
           match find_concept pid with
           | Some p -> Printf.printf "    → %s [%s]\n" p.name
             (difficulty_to_string p.difficulty)
           | None -> Printf.printf "    → %s\n" pid
         ) deep)
    | ["stats"] -> show_stats ()
    | [""] -> ()
    | _ -> Printf.printf "  Unknown command. Type 'help' for options.\n"
  done
