(* code_archaeology.ml — Autonomous Code Archaeology Engine
   Discovers hidden conceptual relationships between all .ml files
   by extracting "DNA signatures" from source code and building
   a knowledge graph of connections.

   Features:
   - Scans all .ml files and extracts conceptual DNA (patterns, techniques,
     data structures, algorithm families)
   - Builds a weighted relationship graph between files based on shared DNA
   - Discovers concept clusters (families of related implementations)
   - Identifies "missing links" — concepts that would bridge existing files
   - Traces evolution chains (how concepts build on each other)
   - Generates a "dig site report" with findings and recommendations
   - Suggests what files should be created to fill conceptual gaps
   - Interactive REPL for exploring the concept space

   Usage: ocaml code_archaeology.ml
*)

(* ── Types ──────────────────────────────────────────────────────── *)

type dna_marker =
  | Pattern of string       (* e.g., "recursion", "pattern_matching" *)
  | DataStructure of string (* e.g., "tree", "graph", "hash_table" *)
  | Algorithm of string     (* e.g., "sorting", "searching", "optimization" *)
  | Paradigm of string      (* e.g., "functional", "imperative", "concurrent" *)
  | Domain of string        (* e.g., "crypto", "graphics", "ai", "parsing" *)

type file_dna = {
  filename : string;
  markers : dna_marker list;
  marker_strengths : (string * float) list; (* marker_id -> strength 0.0-1.0 *)
  line_count : int;
  complexity_tier : string; (* "simple", "moderate", "complex", "expert" *)
}

type relationship = {
  file_a : string;
  file_b : string;
  shared_markers : string list;
  strength : float; (* 0.0-1.0, based on Jaccard similarity *)
}

type cluster = {
  cluster_id : int;
  name : string;
  members : string list;
  core_markers : string list;
}

type missing_link = {
  concept : string;
  description : string;
  bridges : string * string; (* would connect these two clusters *)
  difficulty : string;
  suggested_filename : string;
}

type evolution_chain = {
  chain_name : string;
  steps : (string * string) list; (* (filename, what it adds) *)
}

(* ── DNA Marker Extraction Rules ───────────────────────────────── *)

(* Each rule: (pattern_in_code, marker) *)
type extraction_rule = {
  keywords : string list;
  marker_id : string;
  marker_type : string; (* "pattern", "datastructure", "algorithm", "paradigm", "domain" *)
}

let extraction_rules : extraction_rule list = [
  (* Patterns *)
  { keywords = ["let rec"; "recursive"]; marker_id = "recursion"; marker_type = "pattern" };
  { keywords = ["match"; "with"; "->"; "| "]; marker_id = "pattern_matching"; marker_type = "pattern" };
  { keywords = ["fun "; "function "; "(fun "]; marker_id = "higher_order"; marker_type = "pattern" };
  { keywords = ["|>"; "@@"]; marker_id = "pipe_composition"; marker_type = "pattern" };
  { keywords = ["ref "; ":= "; "! "]; marker_id = "mutation"; marker_type = "pattern" };
  { keywords = ["Hashtbl"; "Hash"]; marker_id = "hashing"; marker_type = "pattern" };
  { keywords = ["module"; "sig"; "struct"; "functor"]; marker_id = "modules"; marker_type = "pattern" };
  { keywords = ["lazy"; "Lazy"]; marker_id = "laziness"; marker_type = "pattern" };
  { keywords = ["type.*=.*|"; "variant"]; marker_id = "algebraic_types"; marker_type = "pattern" };
  { keywords = ["bind"; "return"; ">>="]; marker_id = "monadic"; marker_type = "pattern" };
  { keywords = ["fold"; "reduce"; "aggregate"]; marker_id = "fold_reduce"; marker_type = "pattern" };
  { keywords = ["memoize"; "memo"; "cache"]; marker_id = "memoization"; marker_type = "pattern" };
  { keywords = ["tail_rec"; "acc "; "accumulator"]; marker_id = "tail_recursion"; marker_type = "pattern" };

  (* Data Structures *)
  { keywords = ["tree"; "Node"; "Leaf"; "left"; "right"; "height"]; marker_id = "tree"; marker_type = "datastructure" };
  { keywords = ["graph"; "vertex"; "edge"; "neighbor"; "adjacen"]; marker_id = "graph"; marker_type = "datastructure" };
  { keywords = ["queue"; "enqueue"; "dequeue"]; marker_id = "queue"; marker_type = "datastructure" };
  { keywords = ["stack"; "push"; "pop"]; marker_id = "stack"; marker_type = "datastructure" };
  { keywords = ["heap"; "priority"; "sift"]; marker_id = "heap"; marker_type = "datastructure" };
  { keywords = ["hash"; "bucket"; "collision"]; marker_id = "hash_table"; marker_type = "datastructure" };
  { keywords = ["trie"; "prefix"]; marker_id = "trie"; marker_type = "datastructure" };
  { keywords = ["array"; "Array"]; marker_id = "array"; marker_type = "datastructure" };
  { keywords = ["list"; "List"; "hd"; "tl"; "cons"]; marker_id = "list"; marker_type = "datastructure" };
  { keywords = ["map"; "Map"; "key"; "value"]; marker_id = "map"; marker_type = "datastructure" };
  { keywords = ["set"; "Set"; "member"; "union"; "inter"]; marker_id = "set"; marker_type = "datastructure" };
  { keywords = ["matrix"; "row"; "col"; "dim"]; marker_id = "matrix"; marker_type = "datastructure" };

  (* Algorithms *)
  { keywords = ["sort"; "compare"; "swap"; "partition"]; marker_id = "sorting"; marker_type = "algorithm" };
  { keywords = ["search"; "find"; "lookup"; "binary_search"]; marker_id = "searching"; marker_type = "algorithm" };
  { keywords = ["bfs"; "dfs"; "breadth"; "depth"; "traverse"]; marker_id = "graph_traversal"; marker_type = "algorithm" };
  { keywords = ["shortest"; "dijkstra"; "bellman"; "path"]; marker_id = "shortest_path"; marker_type = "algorithm" };
  { keywords = ["balance"; "rotate"; "rebalance"]; marker_id = "balancing"; marker_type = "algorithm" };
  { keywords = ["compress"; "encode"; "decode"; "huffman"]; marker_id = "compression"; marker_type = "algorithm" };
  { keywords = ["parse"; "token"; "lexer"; "grammar"]; marker_id = "parsing"; marker_type = "algorithm" };
  { keywords = ["unif"; "substitut"; "occur"]; marker_id = "unification"; marker_type = "algorithm" };
  { keywords = ["backtrack"; "solve"; "constraint"]; marker_id = "backtracking"; marker_type = "algorithm" };
  { keywords = ["fixpoint"; "fixed.point"; "converge"]; marker_id = "fixpoint"; marker_type = "algorithm" };
  { keywords = ["random"; "Random"; "probability"]; marker_id = "randomized"; marker_type = "algorithm" };
  { keywords = ["optim"; "fitness"; "evolve"; "mutate"]; marker_id = "optimization"; marker_type = "algorithm" };

  (* Paradigms *)
  { keywords = ["concurrent"; "thread"; "lock"; "mutex"; "atomic"]; marker_id = "concurrency"; marker_type = "paradigm" };
  { keywords = ["distributed"; "replica"; "consensus"; "vote"]; marker_id = "distributed"; marker_type = "paradigm" };
  { keywords = ["persistent"; "immutable"; "functional"]; marker_id = "persistence"; marker_type = "paradigm" };
  { keywords = ["reactive"; "signal"; "event"; "stream"]; marker_id = "reactive"; marker_type = "paradigm" };
  { keywords = ["effect"; "handler"; "perform"]; marker_id = "effects"; marker_type = "paradigm" };
  { keywords = ["continuation"; "shift"; "reset"; "cps"]; marker_id = "continuations"; marker_type = "paradigm" };
  { keywords = ["logic"; "clause"; "predicate"; "fact"; "rule"]; marker_id = "logic_programming"; marker_type = "paradigm" };

  (* Domains *)
  { keywords = ["cipher"; "encrypt"; "decrypt"; "hash"]; marker_id = "cryptography"; marker_type = "domain" };
  { keywords = ["neural"; "neuron"; "layer"; "train"; "gradient"]; marker_id = "machine_learning"; marker_type = "domain" };
  { keywords = ["ray"; "intersect"; "reflect"; "shade"; "render"]; marker_id = "graphics"; marker_type = "domain" };
  { keywords = ["automaton"; "nfa"; "dfa"; "state"; "transition"]; marker_id = "automata_theory"; marker_type = "domain" };
  { keywords = ["proof"; "theorem"; "infer"; "judgement"]; marker_id = "formal_methods"; marker_type = "domain" };
  { keywords = ["game"; "player"; "move"; "win"; "score"]; marker_id = "game_theory"; marker_type = "domain" };
  { keywords = ["network"; "flow"; "capacity"; "source"; "sink"]; marker_id = "network_theory"; marker_type = "domain" };
  { keywords = ["geometry"; "point"; "polygon"; "convex"]; marker_id = "geometry"; marker_type = "domain" };
  { keywords = ["symbolic"; "simplif"; "differentiat"; "integrat"]; marker_id = "symbolic_math"; marker_type = "domain" };
  { keywords = ["probabili"; "sample"; "distribut"; "bayes"]; marker_id = "probability_stats"; marker_type = "domain" };
]

(* ── File Scanning ─────────────────────────────────────────────── *)

let is_source_file name =
  let n = String.length name in
  n > 3
  && String.sub name (n - 3) 3 = ".ml"
  && (String.length name < 5 || String.sub name 0 5 <> "test_")
  && name <> "code_profiler.ml"
  && name <> "learning_path.ml"
  && name <> "code_archaeology.ml"
  && name <> "test_all.ml"
  && name <> "test_framework.ml"

let list_ml_files () =
  let dir = Sys.getcwd () in
  let entries = Sys.readdir dir in
  Array.to_list entries
  |> List.filter is_source_file
  |> List.sort String.compare

let read_file filename =
  try
    let ic = open_in filename in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Bytes.to_string s
  with _ -> ""

let count_lines s =
  let count = ref 1 in
  String.iter (fun c -> if c = '\n' then incr count) s;
  !count

(* ── DNA Extraction ────────────────────────────────────────────── *)

let string_contains_insensitive haystack needle =
  let h = String.lowercase_ascii haystack in
  let n = String.lowercase_ascii needle in
  let hn = String.length h in
  let nn = String.length n in
  if nn > hn then false
  else begin
    let found = ref false in
    for i = 0 to hn - nn do
      if not !found && String.sub h i nn = n then found := true
    done;
    !found
  end

let extract_marker_strength content rule =
  let total_chars = max 1 (String.length content) in
  let hits = List.fold_left (fun acc kw ->
    if string_contains_insensitive content kw then acc + 1 else acc
  ) 0 rule.keywords in
  let keyword_ratio = float_of_int hits /. float_of_int (List.length rule.keywords) in
  (* Also count occurrences for strength *)
  let lines = String.split_on_char '\n' content in
  let line_hits = List.fold_left (fun acc line ->
    let has_any = List.exists (fun kw ->
      string_contains_insensitive line kw) rule.keywords in
    if has_any then acc + 1 else acc
  ) 0 lines in
  let density = float_of_int line_hits /. float_of_int (max 1 (List.length lines)) in
  let strength = (keyword_ratio *. 0.6) +. (min 1.0 (density *. 5.0) *. 0.4) in
  if hits > 0 then Some (rule.marker_id, strength) else None

let make_marker marker_type marker_id =
  match marker_type with
  | "pattern" -> Pattern marker_id
  | "datastructure" -> DataStructure marker_id
  | "algorithm" -> Algorithm marker_id
  | "paradigm" -> Paradigm marker_id
  | "domain" -> Domain marker_id
  | _ -> Pattern marker_id

let extract_dna filename =
  let content = read_file filename in
  let lines = count_lines content in
  let results = List.filter_map (fun rule ->
    extract_marker_strength content rule
  ) extraction_rules in
  (* Filter by minimum strength threshold *)
  let threshold = 0.15 in
  let strong_results = List.filter (fun (_, s) -> s >= threshold) results in
  let markers = List.map (fun (mid, _) ->
    let rule = List.find (fun r -> r.marker_id = mid) extraction_rules in
    make_marker rule.marker_type mid
  ) strong_results in
  let complexity =
    if lines < 50 then "simple"
    else if lines < 150 then "moderate"
    else if lines < 400 then "complex"
    else "expert"
  in
  {
    filename;
    markers;
    marker_strengths = strong_results;
    line_count = lines;
    complexity_tier = complexity;
  }

(* ── Relationship Discovery ────────────────────────────────────── *)

let marker_id_of = function
  | Pattern s | DataStructure s | Algorithm s | Paradigm s | Domain s -> s

let jaccard_similarity set_a set_b =
  let module SS = Set.Make(String) in
  let sa = SS.of_list set_a in
  let sb = SS.of_list set_b in
  let inter = SS.cardinal (SS.inter sa sb) in
  let union = SS.cardinal (SS.union sa sb) in
  if union = 0 then 0.0
  else float_of_int inter /. float_of_int union

let discover_relationships dna_list =
  let rels = ref [] in
  let n = List.length dna_list in
  let arr = Array.of_list dna_list in
  for i = 0 to n - 2 do
    for j = i + 1 to n - 1 do
      let a = arr.(i) in
      let b = arr.(j) in
      let ids_a = List.map marker_id_of a.markers in
      let ids_b = List.map marker_id_of b.markers in
      let shared = List.filter (fun m -> List.mem m ids_b) ids_a in
      let sim = jaccard_similarity ids_a ids_b in
      if sim >= 0.15 && List.length shared >= 2 then
        rels := {
          file_a = a.filename;
          file_b = b.filename;
          shared_markers = shared;
          strength = sim;
        } :: !rels
    done
  done;
  List.sort (fun a b -> compare b.strength a.strength) !rels

(* ── Cluster Discovery (simple connected-components) ───────────── *)

let find_clusters dna_list relationships =
  let files = List.map (fun d -> d.filename) dna_list in
  let n = List.length files in
  let idx_of f =
    let rec aux i = function
      | [] -> -1
      | x :: _ when x = f -> i
      | _ :: rest -> aux (i + 1) rest
    in aux 0 files
  in
  let parent = Array.init n (fun i -> i) in
  let rec find i =
    if parent.(i) = i then i
    else begin parent.(i) <- find parent.(i); parent.(i) end
  in
  let union a b =
    let ra = find a and rb = find b in
    if ra <> rb then parent.(ra) <- rb
  in
  (* Use high-strength relationships for clustering *)
  List.iter (fun rel ->
    if rel.strength >= 0.25 then begin
      let ia = idx_of rel.file_a in
      let ib = idx_of rel.file_b in
      if ia >= 0 && ib >= 0 then union ia ib
    end
  ) relationships;
  (* Group by root *)
  let tbl = Hashtbl.create 16 in
  List.iteri (fun i f ->
    let root = find i in
    let existing = try Hashtbl.find tbl root with Not_found -> [] in
    Hashtbl.replace tbl root (f :: existing)
  ) files;
  (* Build clusters, skip singletons *)
  let cluster_id = ref 0 in
  Hashtbl.fold (fun _ members acc ->
    if List.length members < 2 then acc
    else begin
      incr cluster_id;
      (* Find common markers *)
      let member_dnas = List.filter_map (fun f ->
        List.find_opt (fun d -> d.filename = f) dna_list
      ) members in
      let all_markers = List.concat_map (fun d ->
        List.map marker_id_of d.markers
      ) member_dnas in
      (* Count frequencies *)
      let freq = Hashtbl.create 16 in
      List.iter (fun m ->
        let c = try Hashtbl.find freq m with Not_found -> 0 in
        Hashtbl.replace freq m (c + 1)
      ) all_markers;
      let nm = List.length members in
      let core = Hashtbl.fold (fun m c acc ->
        if c >= nm / 2 then m :: acc else acc
      ) freq [] in
      let name = match List.sort String.compare core with
        | [] -> "Cluster " ^ string_of_int !cluster_id
        | [x] -> String.capitalize_ascii x ^ " family"
        | x :: y :: _ -> String.capitalize_ascii x ^ " + " ^ y ^ " family"
      in
      { cluster_id = !cluster_id; name; members = List.sort String.compare members; core_markers = List.sort String.compare core } :: acc
    end
  ) tbl []
  |> List.sort (fun a b -> compare (List.length b.members) (List.length a.members))

(* ── Missing Link Detection ────────────────────────────────────── *)

let find_missing_links clusters dna_list =
  let known_markers = Hashtbl.create 32 in
  List.iter (fun d ->
    List.iter (fun m ->
      let mid = marker_id_of m in
      let existing = try Hashtbl.find known_markers mid with Not_found -> [] in
      Hashtbl.replace known_markers mid (d.filename :: existing)
    ) d.markers
  ) dna_list;
  (* Predefined interesting combinations that could bridge concepts *)
  let potential_bridges = [
    ("graph", "machine_learning", "graph_neural_network.ml",
     "Graph Neural Network — apply ML to graph-structured data",
     "Advanced");
    ("parsing", "machine_learning", "learned_parser.ml",
     "Learned Parser — neural parser that improves from examples",
     "Expert");
    ("concurrency", "graph", "parallel_graph.ml",
     "Parallel Graph Algorithms — concurrent BFS, parallel PageRank",
     "Advanced");
    ("cryptography", "distributed", "secure_multiparty.ml",
     "Secure Multi-Party Computation — privacy-preserving distributed computation",
     "Expert");
    ("reactive", "machine_learning", "reactive_ml.ml",
     "Reactive ML Pipeline — streaming data processing with online learning",
     "Advanced");
    ("geometry", "optimization", "spatial_optimizer.ml",
     "Spatial Optimizer — geometric optimization (facility location, Steiner trees)",
     "Advanced");
    ("automata_theory", "game_theory", "game_automaton.ml",
     "Game Automaton — automata-based game strategy learning",
     "Advanced");
    ("persistence", "concurrency", "persistent_concurrent.ml",
     "Persistent Concurrent Data Structures — lock-free persistent collections",
     "Expert");
    ("symbolic_math", "machine_learning", "symbolic_regression.ml",
     "Symbolic Regression — discover mathematical formulas via evolution",
     "Advanced");
    ("probability_stats", "graph", "probabilistic_graph.ml",
     "Probabilistic Graphical Models — Bayesian networks on graph structures",
     "Advanced");
    ("formal_methods", "concurrency", "concurrent_verifier.ml",
     "Concurrent System Verifier — model checking for concurrent programs",
     "Expert");
    ("tree", "graphics", "fractal_tree.ml",
     "Fractal Tree Renderer — recursive tree-based fractal generation",
     "Intermediate");
    ("sorting", "distributed", "distributed_sort.ml",
     "Distributed Sort — MapReduce-style distributed sorting",
     "Advanced");
    ("compression", "cryptography", "secure_compression.ml",
     "Secure Compression — encrypt-then-compress pipeline with integrity",
     "Advanced");
    ("monadic", "concurrency", "async_monad.ml",
     "Async Monad — monadic asynchronous computation framework",
     "Advanced");
  ] in
  List.filter_map (fun (marker_a, marker_b, suggested_file, desc, diff) ->
    let has_a = Hashtbl.mem known_markers marker_a in
    let has_b = Hashtbl.mem known_markers marker_b in
    (* Only suggest if both source domains exist but combination is novel *)
    let file_exists = List.exists (fun d -> d.filename = suggested_file) dna_list in
    if has_a && has_b && not file_exists then
      (* Find which clusters they belong to *)
      let cluster_a = List.find_opt (fun c ->
        List.mem marker_a c.core_markers) clusters in
      let cluster_b = List.find_opt (fun c ->
        List.mem marker_b c.core_markers) clusters in
      let bridge_names = (
        (match cluster_a with Some c -> c.name | None -> marker_a),
        (match cluster_b with Some c -> c.name | None -> marker_b)
      ) in
      Some {
        concept = desc;
        description = desc;
        bridges = bridge_names;
        difficulty = diff;
        suggested_filename = suggested_file;
      }
    else None
  ) potential_bridges

(* ── Evolution Chain Discovery ─────────────────────────────────── *)

let discover_evolution_chains dna_list relationships =
  (* Predefined evolution chains based on conceptual progression *)
  let chains = [
    ("Data Structure Evolution", [
      ("list_last_elem.ml", "Basic list operations");
      ("queue.ml", "FIFO ordering with amortized O(1)");
      ("deque.ml", "Double-ended access");
      ("finger_tree.ml", "Monoid-parameterized versatile structure");
      ("persistent_vector.ml", "Random access with structural sharing");
      ("rope.ml", "Balanced trees for text editing");
    ]);
    ("Tree Mastery", [
      ("bst.ml", "Basic binary search tree");
      ("rbtree.ml", "Self-balancing with color invariants");
      ("btree.ml", "Multi-way branching for disk storage");
      ("splay_tree.ml", "Self-adjusting for temporal locality");
      ("interval_tree.ml", "Augmented for range queries");
      ("finger_tree.ml", "Monoid-parameterized general tree");
    ]);
    ("Parsing Journey", [
      ("json.ml", "Recursive descent JSON parser");
      ("parser.ml", "Parser combinators");
      ("peg.ml", "PEG with packrat memoization");
      ("earley.ml", "Earley for ambiguous grammars");
      ("regex.ml", "NFA-based pattern matching");
    ]);
    ("Type Theory Path", [
      ("lambda.ml", "Untyped lambda calculus");
      ("type_infer.ml", "Hindley-Milner type inference");
      ("gadts.ml", "Generalized algebraic data types");
      ("theorem_prover.ml", "Proof search and natural deduction");
      ("proof_assistant.ml", "Interactive theorem proving");
    ]);
    ("Distributed Systems", [
      ("gossip.ml", "Epidemic information dissemination");
      ("crdt.ml", "Conflict-free replicated types");
      ("raft.ml", "Consensus algorithm");
      ("leader_election.ml", "Leader election protocols");
      ("stm.ml", "Software transactional memory");
    ]);
    ("AI & Learning", [
      ("genetic.ml", "Evolutionary optimization");
      ("neural_network.ml", "Feedforward networks with backprop");
      ("bandit.ml", "Multi-armed bandit strategies");
      ("mdp.ml", "Markov decision processes");
      ("hmm.ml", "Hidden Markov models");
      ("bayesian_net.ml", "Bayesian networks");
      ("game_ai.ml", "Minimax with alpha-beta pruning");
    ]);
    ("Formal Methods Ladder", [
      ("fsm.ml", "Finite state machines");
      ("automata.ml", "DFA/NFA construction & minimization");
      ("model_checker.ml", "CTL model checking");
      ("sat_solver.ml", "Boolean satisfiability");
      ("theorem_prover.ml", "Natural deduction proofs");
      ("term_rewriting.ml", "Knuth-Bendix completion");
    ]);
    ("Effects & Control Flow", [
      ("stream.ml", "Lazy evaluation and infinite sequences");
      ("free_monad.ml", "Program description vs interpretation");
      ("monad_transformers.ml", "Composable monad stacks");
      ("effects.ml", "Algebraic effects and handlers");
      ("delimited_cont.ml", "Shift/reset continuations");
      ("frp.ml", "Functional reactive programming");
    ]);
  ] in
  (* Filter to only include files that exist *)
  List.filter_map (fun (name, steps) ->
    let filtered = List.filter (fun (f, _) ->
      List.exists (fun d -> d.filename = f) dna_list
    ) steps in
    if List.length filtered >= 3 then
      Some { chain_name = name; steps = filtered }
    else None
  ) chains

(* ── Marker Frequency Analysis ─────────────────────────────────── *)

type marker_stats = {
  marker_name : string;
  occurrence_count : int;
  avg_strength : float;
  files_with : string list;
}

let analyze_marker_frequency dna_list =
  let tbl = Hashtbl.create 32 in
  List.iter (fun d ->
    List.iter (fun (mid, str) ->
      let (count, total_str, files) =
        try Hashtbl.find tbl mid
        with Not_found -> (0, 0.0, []) in
      Hashtbl.replace tbl mid (count + 1, total_str +. str, d.filename :: files)
    ) d.marker_strengths
  ) dna_list;
  Hashtbl.fold (fun mid (count, total_str, files) acc ->
    { marker_name = mid;
      occurrence_count = count;
      avg_strength = total_str /. float_of_int count;
      files_with = List.sort String.compare files;
    } :: acc
  ) tbl []
  |> List.sort (fun a b -> compare b.occurrence_count a.occurrence_count)

(* ── Anomaly Detection: Unique Files ───────────────────────────── *)

let find_unique_specimens dna_list relationships =
  (* Files with few/no strong relationships — they're conceptual outliers *)
  let rel_counts = Hashtbl.create 32 in
  List.iter (fun d -> Hashtbl.replace rel_counts d.filename 0) dna_list;
  List.iter (fun r ->
    if r.strength >= 0.2 then begin
      (try let c = Hashtbl.find rel_counts r.file_a in
           Hashtbl.replace rel_counts r.file_a (c + 1)
       with Not_found -> ());
      (try let c = Hashtbl.find rel_counts r.file_b in
           Hashtbl.replace rel_counts r.file_b (c + 1)
       with Not_found -> ())
    end
  ) relationships;
  Hashtbl.fold (fun file count acc ->
    if count <= 1 then (file, count) :: acc else acc
  ) rel_counts []
  |> List.sort (fun (_, a) (_, b) -> compare a b)

(* ── Report Generation ─────────────────────────────────────────── *)

let repeat_char c n =
  String.init n (fun _ -> c)

let print_header title =
  let bar = repeat_char '=' (String.length title + 4) in
  Printf.printf "\n%s\n  %s\n%s\n" bar title bar

let print_subheader title =
  Printf.printf "\n── %s %s\n" title (repeat_char '─' (max 0 (60 - String.length title)))

let truncate_string s max_len =
  if String.length s <= max_len then s
  else String.sub s 0 (max_len - 3) ^ "..."

let generate_report dna_list relationships clusters missing_links chains marker_stats unique_specimens =
  print_header "🏛️  CODE ARCHAEOLOGY ENGINE — DIG SITE REPORT";

  (* Overview *)
  print_subheader "Overview";
  Printf.printf "  Files analyzed:     %d\n" (List.length dna_list);
  Printf.printf "  Relationships found: %d\n" (List.length relationships);
  Printf.printf "  Concept clusters:   %d\n" (List.length clusters);
  Printf.printf "  Missing links:      %d\n" (List.length missing_links);
  Printf.printf "  Evolution chains:   %d\n" (List.length chains);
  Printf.printf "  Unique specimens:   %d\n" (List.length unique_specimens);

  let total_lines = List.fold_left (fun acc d -> acc + d.line_count) 0 dna_list in
  Printf.printf "  Total lines of code: %d\n" total_lines;

  (* Complexity Distribution *)
  print_subheader "Complexity Distribution";
  let count_tier t = List.length (List.filter (fun d -> d.complexity_tier = t) dna_list) in
  let tiers = ["simple"; "moderate"; "complex"; "expert"] in
  List.iter (fun t ->
    let c = count_tier t in
    let pct = 100.0 *. float_of_int c /. float_of_int (max 1 (List.length dna_list)) in
    let bar_len = int_of_float (pct /. 2.0) in
    Printf.printf "  %-10s %3d (%4.1f%%) %s\n" t c pct (repeat_char '#' bar_len)
  ) tiers;

  (* Top Markers *)
  print_subheader "Most Common DNA Markers (top 15)";
  let top_markers = if List.length marker_stats > 15 then
    List.filteri (fun i _ -> i < 15) marker_stats
  else marker_stats in
  List.iter (fun ms ->
    Printf.printf "  %-22s  %3d files  (avg strength: %.2f)\n"
      ms.marker_name ms.occurrence_count ms.avg_strength
  ) top_markers;

  (* Strongest Relationships *)
  print_subheader "Strongest Relationships (top 20)";
  let top_rels = if List.length relationships > 20 then
    List.filteri (fun i _ -> i < 20) relationships
  else relationships in
  List.iter (fun r ->
    Printf.printf "  %.2f  %-28s <-> %-28s  [%s]\n"
      r.strength
      (truncate_string r.file_a 28)
      (truncate_string r.file_b 28)
      (String.concat ", " (List.filteri (fun i _ -> i < 3) r.shared_markers))
  ) top_rels;

  (* Concept Clusters *)
  print_subheader "Concept Clusters";
  List.iter (fun c ->
    Printf.printf "\n  📦 %s (%d members)\n" c.name (List.length c.members);
    Printf.printf "     Core DNA: %s\n" (String.concat ", " c.core_markers);
    Printf.printf "     Members:  %s\n"
      (String.concat ", " (List.map (fun f ->
        String.sub f 0 (String.length f - 3)) c.members))
  ) clusters;

  (* Evolution Chains *)
  print_subheader "Evolution Chains";
  List.iter (fun chain ->
    Printf.printf "\n  🧬 %s\n" chain.chain_name;
    List.iteri (fun i (file, desc) ->
      let arrow = if i = 0 then "  " else "→ " in
      Printf.printf "     %s%-30s  %s\n" arrow file desc
    ) chain.steps
  ) chains;

  (* Missing Links *)
  print_subheader "Missing Links — Suggested New Files";
  List.iter (fun ml ->
    Printf.printf "\n  💡 %s\n" ml.suggested_filename;
    Printf.printf "     %s\n" ml.description;
    Printf.printf "     Bridges: %s ↔ %s\n" (fst ml.bridges) (snd ml.bridges);
    Printf.printf "     Difficulty: %s\n" ml.difficulty
  ) missing_links;

  (* Unique Specimens *)
  print_subheader "Unique Specimens (conceptual outliers)";
  Printf.printf "  These files have few connections — they explore unique territory:\n";
  List.iter (fun (file, count) ->
    Printf.printf "  🦕 %-30s  (%d strong connections)\n" file count
  ) (List.filteri (fun i _ -> i < 15) unique_specimens);

  (* Repository Health *)
  print_subheader "Repository Concept Health";
  let avg_markers = float_of_int (List.fold_left (fun acc d ->
    acc + List.length d.markers) 0 dna_list) /.
    float_of_int (max 1 (List.length dna_list)) in
  let avg_rel_strength = if relationships = [] then 0.0 else
    List.fold_left (fun acc r -> acc +. r.strength) 0.0 relationships /.
    float_of_int (List.length relationships) in
  let cluster_coverage = float_of_int (List.fold_left (fun acc c ->
    acc + List.length c.members) 0 clusters) /.
    float_of_int (max 1 (List.length dna_list)) *. 100.0 in

  Printf.printf "  Avg markers per file:    %.1f\n" avg_markers;
  Printf.printf "  Avg relationship strength: %.3f\n" avg_rel_strength;
  Printf.printf "  Cluster coverage:        %.1f%% of files in clusters\n" cluster_coverage;
  Printf.printf "  Concept diversity:       %d unique markers detected\n" (List.length marker_stats);

  let health_score =
    (min 30.0 (avg_markers *. 3.0)) +.
    (min 20.0 (avg_rel_strength *. 80.0)) +.
    (min 25.0 (cluster_coverage *. 0.25)) +.
    (min 25.0 (float_of_int (List.length marker_stats) *. 0.5)) in
  Printf.printf "\n  🏥 Overall Concept Health Score: %.0f / 100\n" (min 100.0 health_score);

  print_string "\n"

(* ── Interactive REPL ──────────────────────────────────────────── *)

let print_help () =
  Printf.printf "\nCode Archaeology Engine — Commands:\n";
  Printf.printf "  report        — Full dig site report\n";
  Printf.printf "  dna <file>    — Show DNA profile for a file\n";
  Printf.printf "  related <file> — Show files related to a given file\n";
  Printf.printf "  cluster <n>   — Show cluster details (by number)\n";
  Printf.printf "  chains        — List evolution chains\n";
  Printf.printf "  gaps          — Show missing links\n";
  Printf.printf "  unique        — Show conceptual outliers\n";
  Printf.printf "  markers       — Show all detected markers\n";
  Printf.printf "  search <term> — Find files by marker keyword\n";
  Printf.printf "  stats         — Quick stats summary\n";
  Printf.printf "  help          — This help message\n";
  Printf.printf "  quit          — Exit\n\n"

let repl_dna dna_list filename =
  let needle = if String.length filename > 3 &&
    String.sub filename (String.length filename - 3) 3 = ".ml"
    then filename else filename ^ ".ml" in
  match List.find_opt (fun d -> d.filename = needle) dna_list with
  | None -> Printf.printf "  File not found: %s\n" needle
  | Some d ->
    Printf.printf "\n  📋 DNA Profile: %s\n" d.filename;
    Printf.printf "     Lines: %d  |  Tier: %s\n" d.line_count d.complexity_tier;
    Printf.printf "     Markers (%d):\n" (List.length d.marker_strengths);
    let sorted = List.sort (fun (_, a) (_, b) -> compare b a) d.marker_strengths in
    List.iter (fun (mid, str) ->
      let bar_len = int_of_float (str *. 30.0) in
      Printf.printf "       %-22s %.2f %s\n" mid str (repeat_char '█' bar_len)
    ) sorted

let repl_related dna_list relationships filename =
  let needle = if String.length filename > 3 &&
    String.sub filename (String.length filename - 3) 3 = ".ml"
    then filename else filename ^ ".ml" in
  let rels = List.filter (fun r ->
    r.file_a = needle || r.file_b = needle) relationships in
  if rels = [] then Printf.printf "  No strong relationships found for %s\n" needle
  else begin
    Printf.printf "\n  🔗 Files related to %s:\n" needle;
    List.iter (fun r ->
      let other = if r.file_a = needle then r.file_b else r.file_a in
      Printf.printf "    %.2f  %-30s  [%s]\n" r.strength other
        (String.concat ", " r.shared_markers)
    ) (List.sort (fun a b -> compare b.strength a.strength) rels)
  end

let repl_search dna_list term =
  let t = String.lowercase_ascii term in
  let matches = List.filter (fun d ->
    List.exists (fun (mid, _) ->
      string_contains_insensitive mid t) d.marker_strengths
  ) dna_list in
  if matches = [] then Printf.printf "  No files match '%s'\n" term
  else begin
    Printf.printf "\n  🔍 Files matching '%s':\n" term;
    List.iter (fun d ->
      let matching_markers = List.filter (fun (mid, _) ->
        string_contains_insensitive mid t) d.marker_strengths in
      Printf.printf "    %-30s  %s\n" d.filename
        (String.concat ", " (List.map (fun (m, s) ->
          Printf.sprintf "%s(%.2f)" m s) matching_markers))
    ) matches
  end

let run_repl dna_list relationships clusters missing_links chains marker_stats unique_specimens =
  Printf.printf "\n🏛️  Code Archaeology Engine — Interactive Mode\n";
  Printf.printf "Type 'help' for commands, 'quit' to exit.\n\n";
  let running = ref true in
  while !running do
    Printf.printf "archaeology> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some cmd ->
      let parts = String.split_on_char ' ' (String.trim cmd) in
      match parts with
      | ["quit"] | ["exit"] | ["q"] -> running := false
      | ["help"] | ["h"] -> print_help ()
      | ["report"] ->
        generate_report dna_list relationships clusters missing_links
          chains marker_stats unique_specimens
      | ["dna"; file] -> repl_dna dna_list file
      | ["related"; file] -> repl_related dna_list relationships file
      | ["chains"] ->
        List.iter (fun chain ->
          Printf.printf "  🧬 %s (%d steps)\n" chain.chain_name
            (List.length chain.steps)
        ) chains
      | ["gaps"] ->
        List.iter (fun ml ->
          Printf.printf "  💡 %-30s  %s\n" ml.suggested_filename ml.difficulty
        ) missing_links
      | ["unique"] ->
        List.iter (fun (f, c) ->
          Printf.printf "  🦕 %-30s  %d connections\n" f c
        ) (List.filteri (fun i _ -> i < 15) unique_specimens)
      | ["markers"] ->
        List.iter (fun ms ->
          Printf.printf "  %-22s  %3d files\n" ms.marker_name ms.occurrence_count
        ) marker_stats
      | "search" :: terms ->
        repl_search dna_list (String.concat " " terms)
      | "cluster" :: [n] ->
        (try
          let idx = int_of_string n in
          match List.find_opt (fun c -> c.cluster_id = idx) clusters with
          | None -> Printf.printf "  Cluster %d not found\n" idx
          | Some c ->
            Printf.printf "\n  📦 %s\n" c.name;
            Printf.printf "     Core: %s\n" (String.concat ", " c.core_markers);
            List.iter (fun m -> Printf.printf "     • %s\n" m) c.members
        with Failure _ -> Printf.printf "  Usage: cluster <number>\n")
      | ["stats"] ->
        Printf.printf "  Files: %d | Relations: %d | Clusters: %d | Chains: %d | Gaps: %d\n"
          (List.length dna_list) (List.length relationships)
          (List.length clusters) (List.length chains)
          (List.length missing_links)
      | [""] -> ()
      | _ -> Printf.printf "  Unknown command. Type 'help' for options.\n"
  done;
  Printf.printf "\n🏛️  Dig complete. Happy exploring!\n"

(* ── Main ──────────────────────────────────────────────────────── *)

let () =
  Printf.printf "🏛️  Code Archaeology Engine — Scanning repository...\n%!";

  let files = list_ml_files () in
  Printf.printf "   Found %d source files to analyze.\n%!" (List.length files);

  (* Extract DNA from all files *)
  Printf.printf "   Extracting conceptual DNA...%!";
  let dna_list = List.map extract_dna files in
  Printf.printf " done.\n%!";

  (* Discover relationships *)
  Printf.printf "   Discovering relationships...%!";
  let relationships = discover_relationships dna_list in
  Printf.printf " found %d connections.\n%!" (List.length relationships);

  (* Find clusters *)
  Printf.printf "   Identifying concept clusters...%!";
  let clusters = find_clusters dna_list relationships in
  Printf.printf " found %d clusters.\n%!" (List.length clusters);

  (* Find missing links *)
  Printf.printf "   Detecting missing links...%!";
  let missing_links = find_missing_links clusters dna_list in
  Printf.printf " found %d gaps.\n%!" (List.length missing_links);

  (* Discover evolution chains *)
  Printf.printf "   Tracing evolution chains...%!";
  let chains = discover_evolution_chains dna_list relationships in
  Printf.printf " found %d chains.\n%!" (List.length chains);

  (* Marker frequency analysis *)
  let marker_stats = analyze_marker_frequency dna_list in

  (* Unique specimens *)
  let unique_specimens = find_unique_specimens dna_list relationships in

  (* Generate report *)
  generate_report dna_list relationships clusters missing_links
    chains marker_stats unique_specimens;

  (* Interactive REPL *)
  let is_interactive = Unix.isatty Unix.stdin in
  if is_interactive then
    run_repl dna_list relationships clusters missing_links
      chains marker_stats unique_specimens
  else
    Printf.printf "Run interactively for REPL mode.\n"
