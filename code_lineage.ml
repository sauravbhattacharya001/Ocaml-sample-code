(* ============================================================================
   code_lineage.ml - Autonomous Code Lineage Tracker
   ============================================================================

   An autonomous implementation genealogy engine that traces shared algorithmic
   DNA across OCaml modules, computes evolutionary distances, detects convergent
   evolution, builds phylogenetic family trees, and generates an interactive
   HTML dashboard.

   Demonstrates:
   - Genetic signature extraction from source code (60+ trait markers)
   - Jaccard-distance evolutionary distance computation
   - UPGMA hierarchical clustering for phylogenetic tree construction
   - Convergent evolution detection (unrelated files with similar traits)
   - Common ancestor inference from shared trait profiles
   - Lineage chain tracing (prerequisite → advanced progression)
   - Speciation event detection (where lineages diverge)
   - Extinction risk analysis (isolated modules with no relatives)
   - Health scoring 0-100 with autonomous insights
   - Self-contained interactive HTML dashboard with tree visualization

   Usage:
     ocamlopt code_lineage.ml -o code_lineage
     ./code_lineage

   Or interpreted:
     ocaml code_lineage.ml
   ============================================================================ *)

(* ── Random Infrastructure ──────────────────────────────────────────────── *)

let global_seed = ref 31415926

let next_random () =
  global_seed := (!global_seed * 1103515245 + 12345) land 0x3FFFFFFF;
  !global_seed

let random_int bound =
  if bound <= 0 then 0
  else (next_random ()) mod bound

let random_float () =
  float_of_int (random_int 10000) /. 10000.0

(* ── Core Types ─────────────────────────────────────────────────────────── *)

type trait_category =
  | Structural    (* data structure patterns *)
  | Algorithmic   (* algorithm families *)
  | Paradigmatic  (* programming paradigm markers *)
  | DomainSpecific (* application domain *)
  | Mechanical    (* low-level code patterns *)

type trait = {
  trait_id : string;
  trait_name : string;
  category : trait_category;
  keywords : string list;
}

type genome = {
  filename : string;
  traits : string list;        (* trait_ids present *)
  trait_strengths : (string * float) list; (* trait_id -> strength 0-1 *)
  line_count : int;
  complexity : float;          (* 0-1 *)
}

type distance_entry = {
  file_a : string;
  file_b : string;
  jaccard_dist : float;        (* 0=identical, 1=no overlap *)
  shared_traits : string list;
  unique_a : string list;
  unique_b : string list;
}

type phylo_node =
  | Leaf of string
  | Branch of phylo_node * phylo_node * float (* left, right, merge distance *)

type convergent_pair = {
  conv_a : string;
  conv_b : string;
  conv_shared : string list;
  conv_distance : float;       (* high = unrelated yet converged *)
  conv_explanation : string;
}

type lineage_chain = {
  chain_name : string;
  chain_steps : (string * string) list; (* (filename, trait_gained) *)
  chain_length : int;
}

type speciation_event = {
  ancestor_traits : string list;
  divergent_a : string;
  divergent_b : string;
  split_traits_a : string list;
  split_traits_b : string list;
}

type extinction_risk = {
  ext_file : string;
  ext_nearest_distance : float;
  ext_shared_count : int;
  ext_risk_level : string;     (* "Critical" / "High" / "Moderate" / "Low" *)
}

type lineage_report = {
  genomes : genome list;
  distances : distance_entry list;
  tree : phylo_node;
  convergences : convergent_pair list;
  lineages : lineage_chain list;
  speciations : speciation_event list;
  extinctions : extinction_risk list;
  health_score : float;
  insights : string list;
}

(* ── Trait Library (60+ traits) ─────────────────────────────────────────── *)

let trait_library : trait list = [
  (* Structural *)
  { trait_id = "tree"; trait_name = "Tree structures"; category = Structural;
    keywords = ["Node"; "Leaf"; "left"; "right"; "height"; "tree"] };
  { trait_id = "graph"; trait_name = "Graph structures"; category = Structural;
    keywords = ["vertex"; "edge"; "neighbor"; "adjacen"; "graph"] };
  { trait_id = "heap"; trait_name = "Heap/Priority queue"; category = Structural;
    keywords = ["heap"; "priority"; "sift"; "extract_min"; "merge"] };
  { trait_id = "hash_tbl"; trait_name = "Hash tables"; category = Structural;
    keywords = ["Hashtbl"; "bucket"; "collision"; "hash"] };
  { trait_id = "trie_ds"; trait_name = "Trie/Prefix tree"; category = Structural;
    keywords = ["trie"; "prefix"; "children"] };
  { trait_id = "linked_list"; trait_name = "Linked list operations"; category = Structural;
    keywords = ["hd"; "tl"; "cons"; "List.rev"; "List.map"] };
  { trait_id = "array_ds"; trait_name = "Array-based structures"; category = Structural;
    keywords = ["Array."; "array"; "index"; "length"] };
  { trait_id = "matrix_ds"; trait_name = "Matrix/2D structures"; category = Structural;
    keywords = ["matrix"; "row"; "col"; "dim"; "grid"] };
  { trait_id = "queue_ds"; trait_name = "Queue structures"; category = Structural;
    keywords = ["queue"; "enqueue"; "dequeue"; "front"; "rear"] };
  { trait_id = "stack_ds"; trait_name = "Stack structures"; category = Structural;
    keywords = ["stack"; "push"; "pop"; "top"] };
  { trait_id = "rope_ds"; trait_name = "Rope/String structure"; category = Structural;
    keywords = ["rope"; "concat"; "substring"; "Rope"] };
  { trait_id = "ring_buf"; trait_name = "Ring/Circular buffer"; category = Structural;
    keywords = ["ring"; "circular"; "wrap"; "capacity"] };
  { trait_id = "bloom_ds"; trait_name = "Probabilistic structures"; category = Structural;
    keywords = ["bloom"; "filter"; "false_positive"; "sketch"; "hyperlog"] };

  (* Algorithmic *)
  { trait_id = "sorting"; trait_name = "Sorting algorithms"; category = Algorithmic;
    keywords = ["sort"; "compare"; "swap"; "partition"; "pivot"] };
  { trait_id = "searching"; trait_name = "Search algorithms"; category = Algorithmic;
    keywords = ["search"; "find"; "lookup"; "binary_search"] };
  { trait_id = "graph_trav"; trait_name = "Graph traversal"; category = Algorithmic;
    keywords = ["bfs"; "dfs"; "breadth"; "depth"; "traverse"; "visit"] };
  { trait_id = "shortest_p"; trait_name = "Shortest path"; category = Algorithmic;
    keywords = ["shortest"; "dijkstra"; "bellman"; "distance"; "relax"] };
  { trait_id = "balancing"; trait_name = "Balancing/Rotation"; category = Algorithmic;
    keywords = ["balance"; "rotate"; "rebalance"; "splay"; "zig"; "zag"] };
  { trait_id = "compression"; trait_name = "Compression/Encoding"; category = Algorithmic;
    keywords = ["compress"; "encode"; "decode"; "huffman"; "lz"] };
  { trait_id = "parsing"; trait_name = "Parsing/Lexing"; category = Algorithmic;
    keywords = ["parse"; "token"; "lexer"; "grammar"; "lex"; "ast"] };
  { trait_id = "unification"; trait_name = "Unification"; category = Algorithmic;
    keywords = ["unif"; "substitut"; "occur"; "mgu"] };
  { trait_id = "backtrack"; trait_name = "Backtracking/CSP"; category = Algorithmic;
    keywords = ["backtrack"; "constraint"; "propagat"; "domain"] };
  { trait_id = "fixpoint"; trait_name = "Fixpoint iteration"; category = Algorithmic;
    keywords = ["fixpoint"; "fixed.point"; "converge"; "iterate"] };
  { trait_id = "randomized"; trait_name = "Randomized algorithms"; category = Algorithmic;
    keywords = ["random"; "Random"; "probability"; "sample"] };
  { trait_id = "optimize"; trait_name = "Optimization"; category = Algorithmic;
    keywords = ["optim"; "fitness"; "evolve"; "mutate"; "crossover"] };
  { trait_id = "dynamic_p"; trait_name = "Dynamic programming"; category = Algorithmic;
    keywords = ["memo"; "dp"; "tabul"; "subproblem"; "optimal"] };
  { trait_id = "divide_conq"; trait_name = "Divide and conquer"; category = Algorithmic;
    keywords = ["divide"; "conquer"; "merge"; "split"; "half"] };
  { trait_id = "greedy"; trait_name = "Greedy algorithms"; category = Algorithmic;
    keywords = ["greedy"; "best"; "local"; "heuristic"] };
  { trait_id = "flow_alg"; trait_name = "Network flow"; category = Algorithmic;
    keywords = ["flow"; "capacity"; "augment"; "residual"; "ford"] };
  { trait_id = "sim_anneal"; trait_name = "Simulated annealing"; category = Algorithmic;
    keywords = ["anneal"; "temperature"; "cool"; "accept"; "metropolis"] };

  (* Paradigmatic *)
  { trait_id = "recursion"; trait_name = "Recursion"; category = Paradigmatic;
    keywords = ["let rec"; "recursive"] };
  { trait_id = "pattern_match"; trait_name = "Pattern matching"; category = Paradigmatic;
    keywords = ["match"; "with"; "| _"] };
  { trait_id = "higher_ord"; trait_name = "Higher-order functions"; category = Paradigmatic;
    keywords = ["fun "; "function "; "List.map"; "List.fold"; "List.filter"] };
  { trait_id = "monadic"; trait_name = "Monadic style"; category = Paradigmatic;
    keywords = ["bind"; "return"; ">>="; ">>"; "monad"] };
  { trait_id = "mutation"; trait_name = "Mutable state"; category = Paradigmatic;
    keywords = ["ref "; ":="; "incr"; "decr"; "mutable"] };
  { trait_id = "modules"; trait_name = "Module system"; category = Paradigmatic;
    keywords = ["module"; "sig"; "struct"; "functor"; "include"] };
  { trait_id = "laziness"; trait_name = "Lazy evaluation"; category = Paradigmatic;
    keywords = ["lazy"; "Lazy"; "force"] };
  { trait_id = "continuations"; trait_name = "Continuations/CPS"; category = Paradigmatic;
    keywords = ["continuation"; "shift"; "reset"; "cps"; "callcc"] };
  { trait_id = "effects"; trait_name = "Algebraic effects"; category = Paradigmatic;
    keywords = ["effect"; "handler"; "perform"; "Effect"] };
  { trait_id = "concurrency"; trait_name = "Concurrency"; category = Paradigmatic;
    keywords = ["concurrent"; "thread"; "lock"; "mutex"; "atomic"; "Mutex"] };
  { trait_id = "fold_red"; trait_name = "Fold/Reduce patterns"; category = Paradigmatic;
    keywords = ["fold"; "reduce"; "aggregate"; "accumul"] };
  { trait_id = "tail_rec"; trait_name = "Tail recursion"; category = Paradigmatic;
    keywords = ["acc "; "accumulator"; "@tail_mod_cons"; "loop"] };
  { trait_id = "gadt"; trait_name = "GADTs"; category = Paradigmatic;
    keywords = ["type.*:.*->"; "GADT"; ": type"] };
  { trait_id = "phantom"; trait_name = "Phantom types"; category = Paradigmatic;
    keywords = ["phantom"; "witness"; "'phantom"; "type _ "] };

  (* Domain-specific *)
  { trait_id = "crypto"; trait_name = "Cryptography"; category = DomainSpecific;
    keywords = ["cipher"; "encrypt"; "decrypt"; "xor"; "key"] };
  { trait_id = "ml_ai"; trait_name = "Machine learning/AI"; category = DomainSpecific;
    keywords = ["neural"; "neuron"; "layer"; "train"; "gradient"; "weight"] };
  { trait_id = "graphics"; trait_name = "Graphics/Rendering"; category = DomainSpecific;
    keywords = ["ray"; "intersect"; "reflect"; "shade"; "render"; "pixel"] };
  { trait_id = "automata"; trait_name = "Automata theory"; category = DomainSpecific;
    keywords = ["automaton"; "nfa"; "dfa"; "state"; "transition"; "accept"] };
  { trait_id = "formal"; trait_name = "Formal methods"; category = DomainSpecific;
    keywords = ["proof"; "theorem"; "infer"; "judgement"; "derivation"] };
  { trait_id = "game_th"; trait_name = "Game theory"; category = DomainSpecific;
    keywords = ["game"; "player"; "move"; "win"; "score"; "minimax"] };
  { trait_id = "network"; trait_name = "Networking"; category = DomainSpecific;
    keywords = ["network"; "socket"; "connect"; "listen"; "packet"] };
  { trait_id = "geometry_d"; trait_name = "Computational geometry"; category = DomainSpecific;
    keywords = ["geometry"; "point"; "polygon"; "convex"; "hull"] };
  { trait_id = "symbolic"; trait_name = "Symbolic computation"; category = DomainSpecific;
    keywords = ["symbolic"; "simplif"; "differentiat"; "integrat"; "symbol"] };
  { trait_id = "prob_stat"; trait_name = "Probability/Statistics"; category = DomainSpecific;
    keywords = ["probabili"; "distribut"; "bayes"; "sample"; "variance"] };
  { trait_id = "type_sys"; trait_name = "Type systems"; category = DomainSpecific;
    keywords = ["type_check"; "type_infer"; "hindley"; "milner"; "polymorphi"] };
  { trait_id = "vm_interp"; trait_name = "VM/Interpreter"; category = DomainSpecific;
    keywords = ["bytecode"; "opcode"; "interpret"; "eval"; "execute"; "vm"] };
  { trait_id = "planning_d"; trait_name = "Planning/Scheduling"; category = DomainSpecific;
    keywords = ["plan"; "schedule"; "goal"; "action"; "precondition"] };
  { trait_id = "consensus_d"; trait_name = "Consensus/Distributed"; category = DomainSpecific;
    keywords = ["consensus"; "vote"; "leader"; "replicate"; "raft"; "paxos"] };

  (* Mechanical *)
  { trait_id = "io_file"; trait_name = "File I/O"; category = Mechanical;
    keywords = ["open_in"; "open_out"; "read"; "write"; "channel"] };
  { trait_id = "string_op"; trait_name = "String processing"; category = Mechanical;
    keywords = ["String."; "sprintf"; "Buffer."; "Bytes."; "substring"] };
  { trait_id = "exn_handle"; trait_name = "Exception handling"; category = Mechanical;
    keywords = ["try"; "with"; "raise"; "exception"; "failwith"] };
  { trait_id = "pp_output"; trait_name = "Pretty printing"; category = Mechanical;
    keywords = ["Printf"; "printf"; "fprintf"; "Format."; "pp_"] };
  { trait_id = "html_gen"; trait_name = "HTML generation"; category = Mechanical;
    keywords = ["<html"; "<div"; "<table"; "html"; "dashboard"] };
  { trait_id = "testing"; trait_name = "Testing/Assertions"; category = Mechanical;
    keywords = ["assert"; "test"; "expect"; "passed"; "failed"] };
]

(* ── File Scanning ──────────────────────────────────────────────────────── *)

let is_source_file name =
  let n = String.length name in
  n > 3
  && String.sub name (n - 3) 3 = ".ml"
  && (String.length name < 5 || String.sub name 0 5 <> "test_")
  && name <> "code_lineage.ml"

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

(* ── Trait Extraction ───────────────────────────────────────────────────── *)

let string_contains haystack needle =
  let hn = String.length haystack and nn = String.length needle in
  if nn > hn then false
  else
    let found = ref false in
    let i = ref 0 in
    while !i <= hn - nn && not !found do
      if String.sub haystack !i nn = needle then found := true
      else incr i
    done;
    !found

let count_occurrences haystack needle =
  let hn = String.length haystack and nn = String.length needle in
  if nn = 0 || nn > hn then 0
  else
    let count = ref 0 in
    for i = 0 to hn - nn do
      if String.sub haystack i nn = needle then incr count
    done;
    !count

let extract_genome filename : genome =
  let content = read_file filename in
  let lc = count_lines content in
  let lower = String.lowercase_ascii content in
  let traits = ref [] in
  let strengths = ref [] in
  List.iter (fun (t : trait) ->
    let total_hits = List.fold_left (fun acc kw ->
      acc + count_occurrences lower (String.lowercase_ascii kw)
    ) 0 t.keywords in
    if total_hits > 0 then begin
      traits := t.trait_id :: !traits;
      (* Strength based on hit density per 100 lines *)
      let density = float_of_int total_hits /. (float_of_int (max 1 lc) /. 100.0) in
      let strength = min 1.0 (density /. 10.0) in
      strengths := (t.trait_id, strength) :: !strengths
    end
  ) trait_library;
  let complexity =
    let tc = List.length !traits in
    min 1.0 (float_of_int tc /. 20.0)
  in
  { filename; traits = List.rev !traits;
    trait_strengths = List.rev !strengths;
    line_count = lc; complexity }

(* ── Distance Computation ───────────────────────────────────────────────── *)

let jaccard_distance set_a set_b =
  let intersection = List.filter (fun x -> List.mem x set_b) set_a in
  let union_size =
    let combined = set_a @ List.filter (fun x -> not (List.mem x set_a)) set_b in
    List.length combined
  in
  if union_size = 0 then 1.0
  else 1.0 -. (float_of_int (List.length intersection) /. float_of_int union_size)

let compute_distances genomes : distance_entry list =
  let pairs = ref [] in
  let n = List.length genomes in
  let arr = Array.of_list genomes in
  for i = 0 to n - 2 do
    for j = i + 1 to n - 1 do
      let a = arr.(i) and b = arr.(j) in
      let shared = List.filter (fun t -> List.mem t b.traits) a.traits in
      let unique_a = List.filter (fun t -> not (List.mem t b.traits)) a.traits in
      let unique_b = List.filter (fun t -> not (List.mem t a.traits)) b.traits in
      let jd = jaccard_distance a.traits b.traits in
      pairs := { file_a = a.filename; file_b = b.filename;
                 jaccard_dist = jd; shared_traits = shared;
                 unique_a; unique_b } :: !pairs
    done
  done;
  List.sort (fun a b -> compare a.jaccard_dist b.jaccard_dist) !pairs

(* ── UPGMA Phylogenetic Tree Construction ───────────────────────────────── *)

type cluster_node = {
  cnode : phylo_node;
  csize : int;
}

let build_phylo_tree genomes : phylo_node =
  if genomes = [] then Leaf "(empty)"
  else
  let n = List.length genomes in
  if n = 1 then Leaf (List.hd genomes).filename
  else begin
    (* Initialize clusters *)
    let clusters = Array.init n (fun i ->
      Some { cnode = Leaf (List.nth genomes i).filename; csize = 1 }
    ) in
    (* Distance matrix *)
    let dist = Array.init n (fun i ->
      Array.init n (fun j ->
        if i = j then 0.0
        else jaccard_distance (List.nth genomes i).traits (List.nth genomes j).traits
      )
    ) in
    for _step = 0 to n - 2 do
      (* Find closest pair *)
      let best_i = ref 0 and best_j = ref 1 and best_d = ref infinity in
      for i = 0 to n - 1 do
        for j = i + 1 to n - 1 do
          match clusters.(i), clusters.(j) with
          | Some _, Some _ when dist.(i).(j) < !best_d ->
            best_i := i; best_j := j; best_d := dist.(i).(j)
          | _ -> ()
        done
      done;
      let ci = !best_i and cj = !best_j in
      match clusters.(ci), clusters.(cj) with
      | Some a, Some b ->
        let merged = {
          cnode = Branch (a.cnode, b.cnode, !best_d);
          csize = a.csize + b.csize;
        } in
        clusters.(ci) <- Some merged;
        clusters.(cj) <- None;
        (* Update distances using UPGMA averaging *)
        for k = 0 to n - 1 do
          if k <> ci && k <> cj then
            match clusters.(k) with
            | Some _ ->
              let new_d =
                (dist.(ci).(k) *. float_of_int a.csize +.
                 dist.(cj).(k) *. float_of_int b.csize) /.
                float_of_int (a.csize + b.csize)
              in
              dist.(ci).(k) <- new_d;
              dist.(k).(ci) <- new_d
            | None -> ()
        done
      | _ -> ()
    done;
    (* Find remaining cluster *)
    let result = ref (Leaf "(error)") in
    Array.iter (fun c -> match c with Some x -> result := x.cnode | None -> ()) clusters;
    !result
  end

(* ── Convergent Evolution Detection ─────────────────────────────────────── *)

let detect_convergences genomes distances : convergent_pair list =
  (* Files that share specific traits despite being in different "families"
     (high overall distance but sharing unexpected domain traits) *)
  let domain_traits = List.filter (fun (t : trait) ->
    t.category = DomainSpecific || t.category = Algorithmic
  ) trait_library |> List.map (fun t -> t.trait_id) in
  let results = ref [] in
  List.iter (fun d ->
    if d.jaccard_dist > 0.65 then begin
      let domain_shared = List.filter (fun t -> List.mem t domain_traits) d.shared_traits in
      if List.length domain_shared >= 2 then begin
        let explanation = Printf.sprintf
          "%s and %s are evolutionarily distant (%.0f%% divergent) yet independently evolved %s"
          d.file_a d.file_b (d.jaccard_dist *. 100.0)
          (String.concat ", " domain_shared)
        in
        results := {
          conv_a = d.file_a; conv_b = d.file_b;
          conv_shared = domain_shared;
          conv_distance = d.jaccard_dist;
          conv_explanation = explanation;
        } :: !results
      end
    end
  ) distances;
  (* Top 15 most interesting convergences *)
  let sorted = List.sort (fun a b ->
    compare (List.length b.conv_shared, b.conv_distance)
            (List.length a.conv_shared, a.conv_distance)
  ) !results in
  let rec take n lst = match n, lst with
    | 0, _ | _, [] -> []
    | n, x :: xs -> x :: take (n-1) xs
  in
  take 15 sorted

(* ── Lineage Chain Discovery ────────────────────────────────────────────── *)

let discover_lineages genomes : lineage_chain list =
  (* Find progressive complexity chains: A has subset of B's traits,
     B has subset of C's traits, forming a learning/evolution path *)
  let sorted_by_traits = List.sort (fun a b ->
    compare (List.length a.traits) (List.length b.traits)
  ) genomes in
  let is_subset small big =
    List.for_all (fun t -> List.mem t big.traits) small.traits
  in
  let chains = ref [] in
  let used = Hashtbl.create 16 in
  List.iter (fun start ->
    if not (Hashtbl.mem used start.filename) && List.length start.traits <= 5 then begin
      let chain = ref [(start.filename, "origin")] in
      let current = ref start in
      let growing = ref true in
      while !growing do
        growing := false;
        let best = ref None in
        let best_new = ref 0 in
        List.iter (fun cand ->
          if cand.filename <> (!current).filename
             && not (Hashtbl.mem used cand.filename)
             && not (List.exists (fun (f,_) -> f = cand.filename) !chain)
             && is_subset !current cand
             && List.length cand.traits > List.length (!current).traits then begin
            let new_traits = List.length cand.traits - List.length (!current).traits in
            if new_traits > !best_new || !best = None then begin
              best := Some cand;
              best_new := new_traits
            end
          end
        ) sorted_by_traits;
        match !best with
        | Some next ->
          let gained = List.filter (fun t ->
            not (List.mem t (!current).traits)
          ) next.traits in
          let gained_str = String.concat "+" gained in
          chain := !chain @ [(next.filename, gained_str)];
          current := next;
          growing := true
        | None -> ()
      done;
      if List.length !chain >= 3 then begin
        let name = Printf.sprintf "%s lineage" (fst (List.hd !chain)) in
        chains := { chain_name = name; chain_steps = !chain;
                    chain_length = List.length !chain } :: !chains;
        List.iter (fun (f,_) -> Hashtbl.replace used f true) !chain
      end
    end
  ) sorted_by_traits;
  List.sort (fun a b -> compare b.chain_length a.chain_length) !chains

(* ── Speciation Event Detection ─────────────────────────────────────────── *)

let detect_speciations genomes distances : speciation_event list =
  (* Find cases where two files share a strong common ancestor trait set
     but then diverge into different domains *)
  let results = ref [] in
  List.iter (fun d ->
    if List.length d.shared_traits >= 3
       && List.length d.unique_a >= 2
       && List.length d.unique_b >= 2
       && d.jaccard_dist > 0.3 && d.jaccard_dist < 0.7 then begin
      results := {
        ancestor_traits = d.shared_traits;
        divergent_a = d.file_a;
        divergent_b = d.file_b;
        split_traits_a = d.unique_a;
        split_traits_b = d.unique_b;
      } :: !results
    end
  ) distances;
  let sorted = List.sort (fun a b ->
    compare (List.length b.ancestor_traits) (List.length a.ancestor_traits)
  ) !results in
  let rec take n lst = match n, lst with
    | 0, _ | _, [] -> []
    | n, x :: xs -> x :: take (n-1) xs
  in
  take 12 sorted

(* ── Extinction Risk Analysis ───────────────────────────────────────────── *)

let analyze_extinction genomes distances : extinction_risk list =
  List.map (fun g ->
    let relevant = List.filter (fun d ->
      d.file_a = g.filename || d.file_b = g.filename
    ) distances in
    let nearest = List.fold_left (fun best d ->
      min best d.jaccard_dist
    ) 1.0 relevant in
    let shared_count = List.fold_left (fun best d ->
      max best (List.length d.shared_traits)
    ) 0 relevant in
    let risk_level =
      if nearest > 0.85 then "Critical"
      else if nearest > 0.70 then "High"
      else if nearest > 0.50 then "Moderate"
      else "Low"
    in
    { ext_file = g.filename; ext_nearest_distance = nearest;
      ext_shared_count = shared_count; ext_risk_level = risk_level }
  ) genomes
  |> List.filter (fun e -> e.ext_risk_level <> "Low")
  |> List.sort (fun a b -> compare b.ext_nearest_distance a.ext_nearest_distance)

(* ── Health Scoring ─────────────────────────────────────────────────────── *)

let compute_health genomes distances convergences lineages speciations extinctions =
  let n = List.length genomes in
  if n = 0 then 50.0
  else
    (* 1. Diversity: how many distinct traits across the codebase *)
    let all_traits = List.concat_map (fun g -> g.traits) genomes in
    let unique_traits = List.sort_uniq String.compare all_traits in
    let diversity_score = min 1.0 (float_of_int (List.length unique_traits) /. 40.0) in

    (* 2. Connectivity: avg shared traits between pairs *)
    let avg_shared = if distances = [] then 0.0
      else
        let total = List.fold_left (fun acc d ->
          acc +. float_of_int (List.length d.shared_traits)
        ) 0.0 distances in
        total /. float_of_int (List.length distances)
    in
    let connectivity_score = min 1.0 (avg_shared /. 5.0) in

    (* 3. Lineage depth *)
    let max_chain = List.fold_left (fun acc l -> max acc l.chain_length) 0 lineages in
    let lineage_score = min 1.0 (float_of_int max_chain /. 6.0) in

    (* 4. Low extinction risk *)
    let critical = List.length (List.filter (fun e -> e.ext_risk_level = "Critical") extinctions) in
    let extinction_penalty = min 1.0 (float_of_int critical /. float_of_int (max 1 n)) in

    (* 5. Evolution activity (convergences + speciations = rich ecosystem) *)
    let evo_activity = min 1.0
      (float_of_int (List.length convergences + List.length speciations) /. 20.0) in

    let raw = diversity_score *. 25.0
            +. connectivity_score *. 25.0
            +. lineage_score *. 15.0
            +. (1.0 -. extinction_penalty) *. 15.0
            +. evo_activity *. 20.0 in
    max 0.0 (min 100.0 raw)

(* ── Insight Generation ─────────────────────────────────────────────────── *)

let generate_insights genomes distances convergences lineages speciations extinctions health =
  let insights = ref [] in
  let add s = insights := s :: !insights in
  let n = List.length genomes in

  (* Genome stats *)
  let all_traits = List.concat_map (fun g -> g.traits) genomes in
  let unique_traits = List.sort_uniq String.compare all_traits in
  add (Printf.sprintf "Scanned %d modules, identified %d unique genetic traits across the codebase"
    n (List.length unique_traits));

  (* Most common trait *)
  let trait_counts = List.map (fun tid ->
    (tid, List.length (List.filter (fun t -> t = tid) all_traits))
  ) unique_traits in
  let sorted_tc = List.sort (fun (_,a) (_,b) -> compare b a) trait_counts in
  (match sorted_tc with
   | (t,c) :: _ -> add (Printf.sprintf "Most prevalent trait: '%s' (found in %d modules)" t c)
   | [] -> ());

  (* Richest genome *)
  let richest = List.sort (fun a b -> compare (List.length b.traits) (List.length a.traits)) genomes in
  (match richest with
   | g :: _ -> add (Printf.sprintf "Most complex module: %s with %d traits"
       g.filename (List.length g.traits))
   | [] -> ());

  (* Closest pair *)
  (match distances with
   | d :: _ -> add (Printf.sprintf "Closest relatives: %s and %s (%.1f%% similar, sharing %s)"
       d.file_a d.file_b ((1.0 -. d.jaccard_dist) *. 100.0)
       (String.concat ", " d.shared_traits))
   | [] -> ());

  (* Convergences *)
  if convergences <> [] then
    add (Printf.sprintf "Detected %d convergent evolution events — unrelated modules independently evolved similar capabilities"
      (List.length convergences));

  (* Lineages *)
  if lineages <> [] then begin
    let longest = List.hd lineages in
    add (Printf.sprintf "Longest lineage chain: %s (%d steps) — shows progressive trait accumulation"
      longest.chain_name longest.chain_length)
  end;

  (* Speciations *)
  if speciations <> [] then
    add (Printf.sprintf "Identified %d speciation events where shared ancestry diverged into distinct specializations"
      (List.length speciations));

  (* Extinction risks *)
  let critical = List.filter (fun e -> e.ext_risk_level = "Critical") extinctions in
  if critical <> [] then
    add (Printf.sprintf "⚠ %d modules at critical extinction risk — highly isolated with no close relatives: %s"
      (List.length critical)
      (String.concat ", " (List.map (fun e -> e.ext_file) critical)));

  (* Health interpretation *)
  let grade =
    if health >= 80.0 then "thriving ecosystem with rich interconnections"
    else if health >= 60.0 then "healthy ecosystem with room for more cross-pollination"
    else if health >= 40.0 then "developing ecosystem — consider adding bridging implementations"
    else "sparse ecosystem — many isolated modules need connecting themes"
  in
  add (Printf.sprintf "Ecosystem health: %.0f/100 — %s" health grade);

  List.rev !insights

(* ── Full Analysis ──────────────────────────────────────────────────────── *)

let analyze () : lineage_report =
  let files = list_ml_files () in
  let genomes = List.map extract_genome files in
  let genomes = List.filter (fun g -> g.traits <> []) genomes in
  let distances = compute_distances genomes in
  let tree = build_phylo_tree genomes in
  let convergences = detect_convergences genomes distances in
  let lineages = discover_lineages genomes in
  let speciations = detect_speciations genomes distances in
  let extinctions = analyze_extinction genomes distances in
  let health = compute_health genomes distances convergences lineages speciations extinctions in
  let insights = generate_insights genomes distances convergences lineages speciations extinctions health in
  { genomes; distances; tree; convergences; lineages;
    speciations; extinctions; health_score = health; insights }

(* ── Console Output ─────────────────────────────────────────────────────── *)

let category_name = function
  | Structural -> "Structural"
  | Algorithmic -> "Algorithmic"
  | Paradigmatic -> "Paradigmatic"
  | DomainSpecific -> "Domain"
  | Mechanical -> "Mechanical"

let trait_name_of_id tid =
  match List.find_opt (fun t -> t.trait_id = tid) trait_library with
  | Some t -> t.trait_name
  | None -> tid

let rec tree_to_string indent = function
  | Leaf name -> indent ^ "└─ " ^ name
  | Branch (left, right, dist) ->
    let prefix = indent ^ "├─ [d=" ^ Printf.sprintf "%.2f" dist ^ "]" in
    prefix ^ "\n" ^
    tree_to_string (indent ^ "│  ") left ^ "\n" ^
    tree_to_string (indent ^ "│  ") right

let print_report report =
  Printf.printf "\n╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║       CODE LINEAGE TRACKER — Implementation Genealogy       ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n\n";

  (* Genome summary *)
  Printf.printf "── Genomes (%d modules) ──────────────────────────────────────\n\n"
    (List.length report.genomes);
  List.iter (fun g ->
    Printf.printf "  %-30s  %3d lines  %2d traits  complexity=%.2f\n"
      g.filename g.line_count (List.length g.traits) g.complexity;
    Printf.printf "    traits: %s\n" (String.concat ", " g.traits)
  ) (let rec take n = function [] -> [] | x :: xs -> if n <= 0 then [] else x :: take (n-1) xs in
     take 20 report.genomes);
  if List.length report.genomes > 20 then
    Printf.printf "  ... and %d more modules\n" (List.length report.genomes - 20);

  (* Phylogenetic tree *)
  Printf.printf "\n── Phylogenetic Tree (UPGMA) ────────────────────────────────\n\n";
  Printf.printf "%s\n" (tree_to_string "  " report.tree);

  (* Closest relatives *)
  Printf.printf "\n── Closest Relatives (Top 10) ───────────────────────────────\n\n";
  let rec take n = function [] -> [] | x :: xs -> if n <= 0 then [] else x :: take (n-1) xs in
  List.iter (fun d ->
    Printf.printf "  %.0f%% similar: %s ↔ %s\n"
      ((1.0 -. d.jaccard_dist) *. 100.0) d.file_a d.file_b;
    Printf.printf "    shared: %s\n" (String.concat ", " d.shared_traits)
  ) (take 10 report.distances);

  (* Convergent evolution *)
  if report.convergences <> [] then begin
    Printf.printf "\n── Convergent Evolution (%d events) ─────────────────────────\n\n"
      (List.length report.convergences);
    List.iter (fun c ->
      Printf.printf "  🔀 %s\n" c.conv_explanation
    ) report.convergences
  end;

  (* Lineage chains *)
  if report.lineages <> [] then begin
    Printf.printf "\n── Lineage Chains (%d discovered) ──────────────────────────\n\n"
      (List.length report.lineages);
    List.iter (fun l ->
      Printf.printf "  📜 %s (%d steps):\n" l.chain_name l.chain_length;
      List.iter (fun (f, gained) ->
        Printf.printf "    → %s [+%s]\n" f gained
      ) l.chain_steps
    ) report.lineages
  end;

  (* Speciation events *)
  if report.speciations <> [] then begin
    Printf.printf "\n── Speciation Events (%d detected) ─────────────────────────\n\n"
      (List.length report.speciations);
    List.iter (fun s ->
      Printf.printf "  🧬 Common ancestor traits: %s\n" (String.concat ", " s.ancestor_traits);
      Printf.printf "     → %s evolved: %s\n" s.divergent_a (String.concat ", " s.split_traits_a);
      Printf.printf "     → %s evolved: %s\n" s.divergent_b (String.concat ", " s.split_traits_b)
    ) report.speciations
  end;

  (* Extinction risk *)
  if report.extinctions <> [] then begin
    Printf.printf "\n── Extinction Risk (%d at risk) ─────────────────────────────\n\n"
      (List.length report.extinctions);
    List.iter (fun e ->
      let icon = match e.ext_risk_level with
        | "Critical" -> "🔴" | "High" -> "🟠" | _ -> "🟡" in
      Printf.printf "  %s %-6s %s (nearest relative: %.0f%% distant, max shared: %d)\n"
        icon e.ext_risk_level e.ext_file
        (e.ext_nearest_distance *. 100.0) e.ext_shared_count
    ) report.extinctions
  end;

  (* Health *)
  let bar_len = int_of_float (report.health_score /. 2.0) in
  let bar = String.make bar_len '#' ^ String.make (50 - bar_len) '-' in
  Printf.printf "\n── Ecosystem Health ─────────────────────────────────────────\n\n";
  Printf.printf "  [%s] %.0f/100\n" bar report.health_score;

  (* Insights *)
  Printf.printf "\n── Autonomous Insights ──────────────────────────────────────\n\n";
  List.iter (fun i -> Printf.printf "  💡 %s\n" i) report.insights;
  Printf.printf "\n"

(* ── HTML Dashboard ─────────────────────────────────────────────────────── *)

let esc s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c -> match c with
    | '<' -> Buffer.add_string b "&lt;"
    | '>' -> Buffer.add_string b "&gt;"
    | '&' -> Buffer.add_string b "&amp;"
    | '"' -> Buffer.add_string b "&quot;"
    | '\'' -> Buffer.add_string b "&#39;"
    | c -> Buffer.add_char b c
  ) s;
  Buffer.contents b

let generate_dashboard report =
  let b = Buffer.create 65536 in
  let add s = Buffer.add_string b s in

  add "<!DOCTYPE html><html lang='en'><head><meta charset='UTF-8'>\n";
  add "<meta name='viewport' content='width=device-width,initial-scale=1'>\n";
  add "<title>Code Lineage Tracker — Implementation Genealogy</title>\n";
  add "<style>\n";
  add ":root{--bg:#0a0e17;--card:#111827;--border:#1e293b;--text:#e2e8f0;";
  add "--dim:#64748b;--accent:#818cf8;--green:#34d399;--red:#f87171;";
  add "--orange:#fbbf24;--cyan:#22d3ee;--purple:#a78bfa;--pink:#f472b6}\n";
  add "*{margin:0;padding:0;box-sizing:border-box}\n";
  add "body{background:var(--bg);color:var(--text);font:14px/1.6 'SF Mono',monospace;padding:24px}\n";
  add ".header{text-align:center;padding:32px 0;border-bottom:1px solid var(--border);margin-bottom:24px}\n";
  add ".header h1{font-size:28px;color:var(--accent);margin-bottom:8px}\n";
  add ".header .sub{color:var(--dim);font-size:13px}\n";
  add ".health-gauge{display:flex;align-items:center;justify-content:center;gap:16px;margin:16px 0}\n";
  add ".health-bar{width:300px;height:24px;background:#1e293b;border-radius:12px;overflow:hidden}\n";
  add ".health-fill{height:100%;border-radius:12px;transition:width .5s}\n";
  add ".health-score{font-size:32px;font-weight:bold}\n";
  add ".tabs{display:flex;gap:4px;border-bottom:2px solid var(--border);margin-bottom:20px}\n";
  add ".tab{padding:10px 20px;cursor:pointer;border:none;background:none;color:var(--dim);";
  add "font:13px/1 'SF Mono',monospace;border-bottom:2px solid transparent;margin-bottom:-2px}\n";
  add ".tab:hover{color:var(--text)}.tab.active{color:var(--accent);border-bottom-color:var(--accent)}\n";
  add ".panel{display:none}.panel.active{display:block}\n";
  add ".card{background:var(--card);border:1px solid var(--border);border-radius:8px;padding:16px;margin-bottom:16px}\n";
  add ".card h3{color:var(--accent);margin-bottom:12px;font-size:15px}\n";
  add ".grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(350px,1fr));gap:16px}\n";
  add "table{width:100%;border-collapse:collapse}\n";
  add "th{text-align:left;padding:8px 12px;border-bottom:1px solid var(--border);color:var(--dim);font-size:12px}\n";
  add "td{padding:8px 12px;border-bottom:1px solid #1a2236;font-size:13px}\n";
  add "tr:hover{background:#ffffff08}\n";
  add ".badge{display:inline-block;padding:2px 8px;border-radius:4px;font-size:11px;font-weight:600}\n";
  add ".badge-critical{background:#7f1d1d;color:#fca5a5}\n";
  add ".badge-high{background:#78350f;color:#fbbf24}\n";
  add ".badge-moderate{background:#1e3a5f;color:#93c5fd}\n";
  add ".badge-low{background:#064e3b;color:#6ee7b7}\n";
  add ".tree-node{margin-left:20px;border-left:2px solid var(--border);padding-left:12px}\n";
  add ".tree-leaf{color:var(--green);font-weight:600}\n";
  add ".tree-dist{color:var(--dim);font-size:12px}\n";
  add ".trait-chip{display:inline-block;padding:2px 8px;margin:2px;border-radius:12px;font-size:11px;";
  add "background:#1e293b;color:var(--cyan)}\n";
  add ".insight{padding:12px;border-left:3px solid var(--accent);margin-bottom:8px;background:#111827}\n";
  add ".chain-step{display:flex;align-items:center;gap:8px;padding:4px 0}\n";
  add ".chain-arrow{color:var(--accent);font-weight:bold}\n";
  add ".chain-gained{color:var(--green);font-size:12px}\n";
  add ".conv-card{border-left:3px solid var(--purple)}\n";
  add ".spec-card{border-left:3px solid var(--pink)}\n";
  add ".search-box{width:100%;padding:8px 12px;background:var(--card);border:1px solid var(--border);";
  add "border-radius:6px;color:var(--text);font:13px 'SF Mono',monospace;margin-bottom:16px}\n";
  add "</style></head><body>\n";

  (* Header *)
  add "<div class='header'>\n";
  add "<h1>🧬 Code Lineage Tracker</h1>\n";
  add "<div class='sub'>Autonomous Implementation Genealogy Engine</div>\n";
  add "<div class='health-gauge'>\n";
  let color = if report.health_score >= 70.0 then "var(--green)"
    else if report.health_score >= 40.0 then "var(--orange)" else "var(--red)" in
  Printf.ksprintf add "<div class='health-bar'><div class='health-fill' style='width:%.0f%%;background:%s'></div></div>\n"
    report.health_score color;
  Printf.ksprintf add "<div class='health-score' style='color:%s'>%.0f</div>\n" color report.health_score;
  add "</div>\n";
  Printf.ksprintf add "<div class='sub'>%d modules · %d trait markers · %d lineage chains · %d convergences</div>\n"
    (List.length report.genomes) (List.length trait_library)
    (List.length report.lineages) (List.length report.convergences);
  add "</div>\n";

  (* Tabs *)
  add "<div class='tabs'>\n";
  List.iteri (fun i (label, _) ->
    Printf.ksprintf add "<button class='tab%s' onclick='showTab(%d)'>%s</button>\n"
      (if i = 0 then " active" else "") i label
  ) [("Insights", 0); ("Genomes", 1); ("Phylogeny", 2);
     ("Convergence", 3); ("Lineages", 4); ("Speciation", 5); ("Extinction", 6)];
  add "</div>\n";

  (* Panel 0: Insights *)
  add "<div class='panel active' id='panel-0'>\n";
  add "<div class='card'><h3>Autonomous Insights</h3>\n";
  List.iter (fun i ->
    Printf.ksprintf add "<div class='insight'>💡 %s</div>\n" (esc i)
  ) report.insights;
  add "</div></div>\n";

  (* Panel 1: Genomes *)
  add "<div class='panel' id='panel-1'>\n";
  add "<input class='search-box' placeholder='Filter modules...' oninput='filterGenomes(this.value)'>\n";
  add "<div id='genome-list'>\n";
  add "<table><thead><tr><th>Module</th><th>Lines</th><th>Traits</th><th>Complexity</th><th>Genetic Profile</th></tr></thead><tbody>\n";
  List.iter (fun g ->
    Printf.ksprintf add "<tr class='genome-row' data-name='%s'>" (String.lowercase_ascii g.filename);
    Printf.ksprintf add "<td class='tree-leaf'>%s</td>" (esc g.filename);
    Printf.ksprintf add "<td>%d</td><td>%d</td>" g.line_count (List.length g.traits);
    Printf.ksprintf add "<td>%.0f%%</td><td>" (g.complexity *. 100.0);
    List.iter (fun tid ->
      Printf.ksprintf add "<span class='trait-chip'>%s</span>" (esc tid)
    ) g.traits;
    add "</td></tr>\n"
  ) report.genomes;
  add "</tbody></table></div></div>\n";

  (* Panel 2: Phylogeny *)
  add "<div class='panel' id='panel-2'>\n";
  add "<div class='card'><h3>Phylogenetic Tree (UPGMA Hierarchical Clustering)</h3>\n";
  let rec render_tree = function
    | Leaf name ->
      Printf.ksprintf add "<div class='tree-leaf'>🍃 %s</div>\n" (esc name)
    | Branch (left, right, dist) ->
      Printf.ksprintf add "<div><span class='tree-dist'>merge distance: %.3f</span></div>\n" dist;
      add "<div class='tree-node'>\n";
      render_tree left;
      render_tree right;
      add "</div>\n"
  in
  render_tree report.tree;
  add "</div>\n";

  (* Closest relatives table *)
  add "<div class='card'><h3>Closest Relatives</h3>\n";
  add "<table><thead><tr><th>Similarity</th><th>Module A</th><th>Module B</th><th>Shared Traits</th></tr></thead><tbody>\n";
  let rec take n = function [] -> [] | x :: xs -> if n <= 0 then [] else x :: take (n-1) xs in
  List.iter (fun d ->
    Printf.ksprintf add "<tr><td>%.0f%%</td><td>%s</td><td>%s</td><td>"
      ((1.0 -. d.jaccard_dist) *. 100.0) (esc d.file_a) (esc d.file_b);
    List.iter (fun t -> Printf.ksprintf add "<span class='trait-chip'>%s</span>" (esc t)) d.shared_traits;
    add "</td></tr>\n"
  ) (take 20 report.distances);
  add "</tbody></table></div></div>\n";

  (* Panel 3: Convergent evolution *)
  add "<div class='panel' id='panel-3'>\n";
  if report.convergences = [] then
    add "<div class='card'><h3>No convergent evolution detected</h3></div>\n"
  else begin
    Printf.ksprintf add "<div class='card'><h3>Convergent Evolution (%d events)</h3>\n"
      (List.length report.convergences);
    add "<div class='grid'>\n";
    List.iter (fun c ->
      add "<div class='card conv-card'>\n";
      Printf.ksprintf add "<div style='color:var(--purple);font-weight:600'>%s ↔ %s</div>\n"
        (esc c.conv_a) (esc c.conv_b);
      Printf.ksprintf add "<div style='color:var(--dim);font-size:12px;margin:4px 0'>%.0f%% divergent</div>\n"
        (c.conv_distance *. 100.0);
      List.iter (fun t -> Printf.ksprintf add "<span class='trait-chip'>%s</span>" (esc t)) c.conv_shared;
      Printf.ksprintf add "<div style='margin-top:8px;font-size:12px'>%s</div>\n" (esc c.conv_explanation);
      add "</div>\n"
    ) report.convergences;
    add "</div></div>\n"
  end;
  add "</div>\n";

  (* Panel 4: Lineages *)
  add "<div class='panel' id='panel-4'>\n";
  if report.lineages = [] then
    add "<div class='card'><h3>No lineage chains discovered</h3></div>\n"
  else begin
    List.iter (fun l ->
      Printf.ksprintf add "<div class='card'><h3>📜 %s (%d steps)</h3>\n"
        (esc l.chain_name) l.chain_length;
      List.iter (fun (f, gained) ->
        add "<div class='chain-step'>\n";
        Printf.ksprintf add "<span class='chain-arrow'>→</span> <span class='tree-leaf'>%s</span>" (esc f);
        Printf.ksprintf add " <span class='chain-gained'>[+%s]</span>\n" (esc gained);
        add "</div>\n"
      ) l.chain_steps;
      add "</div>\n"
    ) report.lineages
  end;
  add "</div>\n";

  (* Panel 5: Speciation *)
  add "<div class='panel' id='panel-5'>\n";
  if report.speciations = [] then
    add "<div class='card'><h3>No speciation events detected</h3></div>\n"
  else begin
    add "<div class='grid'>\n";
    List.iter (fun s ->
      add "<div class='card spec-card'>\n";
      add "<div style='color:var(--pink);font-weight:600;margin-bottom:8px'>Common ancestor:</div>\n";
      List.iter (fun t -> Printf.ksprintf add "<span class='trait-chip'>%s</span>" (esc t)) s.ancestor_traits;
      Printf.ksprintf add "<div style='margin-top:12px'>→ <span class='tree-leaf'>%s</span> evolved: " (esc s.divergent_a);
      List.iter (fun t -> Printf.ksprintf add "<span class='trait-chip' style='background:#1e3a5f'>%s</span>" (esc t)) s.split_traits_a;
      add "</div>\n";
      Printf.ksprintf add "<div style='margin-top:4px'>→ <span class='tree-leaf'>%s</span> evolved: " (esc s.divergent_b);
      List.iter (fun t -> Printf.ksprintf add "<span class='trait-chip' style='background:#3b1e5f'>%s</span>" (esc t)) s.split_traits_b;
      add "</div></div>\n"
    ) report.speciations;
    add "</div>\n"
  end;
  add "</div>\n";

  (* Panel 6: Extinction *)
  add "<div class='panel' id='panel-6'>\n";
  if report.extinctions = [] then
    add "<div class='card'><h3>No modules at extinction risk — healthy ecosystem!</h3></div>\n"
  else begin
    add "<table><thead><tr><th>Risk</th><th>Module</th><th>Nearest Relative Distance</th><th>Max Shared Traits</th></tr></thead><tbody>\n";
    List.iter (fun e ->
      let badge_class = match e.ext_risk_level with
        | "Critical" -> "badge-critical" | "High" -> "badge-high"
        | "Moderate" -> "badge-moderate" | _ -> "badge-low" in
      Printf.ksprintf add "<tr><td><span class='badge %s'>%s</span></td>" badge_class e.ext_risk_level;
      Printf.ksprintf add "<td>%s</td><td>%.0f%%</td><td>%d</td></tr>\n"
        (esc e.ext_file) (e.ext_nearest_distance *. 100.0) e.ext_shared_count
    ) report.extinctions;
    add "</tbody></table>\n"
  end;
  add "</div>\n";

  (* JavaScript *)
  add "<script>\n";
  add "function showTab(n){document.querySelectorAll('.tab').forEach((t,i)=>{";
  add "t.classList.toggle('active',i===n)});";
  add "document.querySelectorAll('.panel').forEach((p,i)=>{";
  add "p.classList.toggle('active',i===n)})}\n";
  add "function filterGenomes(q){q=q.toLowerCase();";
  add "document.querySelectorAll('.genome-row').forEach(r=>{";
  add "r.style.display=r.dataset.name.includes(q)?'':'none'})}\n";
  add "</script>\n";
  add "</body></html>";

  Buffer.contents b

(* ── Test Suite ─────────────────────────────────────────────────────────── *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_test name condition =
  if condition then begin
    incr tests_passed;
    Printf.printf "  ✅ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ❌ %s\n" name
  end

let run_tests () =
  Printf.printf "\n── Running Tests ───────────────────────────────────────────\n\n";

  (* Trait extraction *)
  assert_test "trait_library has 60+ traits"
    (List.length trait_library >= 60);

  assert_test "all traits have unique IDs"
    (let ids = List.map (fun t -> t.trait_id) trait_library in
     List.length ids = List.length (List.sort_uniq String.compare ids));

  assert_test "all traits have keywords"
    (List.for_all (fun t -> t.keywords <> []) trait_library);

  (* String operations *)
  assert_test "string_contains finds match"
    (string_contains "hello world" "world");

  assert_test "string_contains rejects no match"
    (not (string_contains "hello" "xyz"));

  assert_test "count_occurrences counts correctly"
    (count_occurrences "abcabcabc" "abc" = 3);

  assert_test "count_occurrences empty"
    (count_occurrences "abc" "xyz" = 0);

  (* Jaccard distance *)
  assert_test "jaccard_distance identical = 0"
    (jaccard_distance ["a";"b";"c"] ["a";"b";"c"] = 0.0);

  assert_test "jaccard_distance disjoint = 1"
    (jaccard_distance ["a";"b"] ["c";"d"] = 1.0);

  assert_test "jaccard_distance empty = 1"
    (jaccard_distance [] [] = 1.0);

  assert_test "jaccard_distance partial"
    (let d = jaccard_distance ["a";"b";"c"] ["b";"c";"d"] in
     d > 0.4 && d < 0.6);

  assert_test "jaccard_distance symmetry"
    (jaccard_distance ["a";"b"] ["b";"c"] =
     jaccard_distance ["b";"c"] ["a";"b"]);

  (* Genome extraction *)
  assert_test "extract_genome handles missing file"
    (let g = extract_genome "nonexistent_xyz.ml" in
     g.line_count = 1 && g.traits = []);

  assert_test "extract_genome returns filename"
    (let g = extract_genome "nonexistent_xyz.ml" in
     g.filename = "nonexistent_xyz.ml");

  (* Phylo tree *)
  assert_test "build_phylo_tree empty"
    (match build_phylo_tree [] with Leaf "(empty)" -> true | _ -> false);

  assert_test "build_phylo_tree single"
    (let g = { filename = "a.ml"; traits = ["x"]; trait_strengths = [("x",0.5)];
               line_count = 10; complexity = 0.1 } in
     match build_phylo_tree [g] with Leaf "a.ml" -> true | _ -> false);

  assert_test "build_phylo_tree two produces branch"
    (let g1 = { filename = "a.ml"; traits = ["x";"y"]; trait_strengths = [];
                line_count = 10; complexity = 0.1 } in
     let g2 = { filename = "b.ml"; traits = ["y";"z"]; trait_strengths = [];
                line_count = 10; complexity = 0.1 } in
     match build_phylo_tree [g1; g2] with Branch _ -> true | _ -> false);

  assert_test "build_phylo_tree three"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x";"y"]; mk "b.ml" ["x";"y";"z"]; mk "c.ml" ["w"]] in
     match build_phylo_tree gs with Branch _ -> true | _ -> false);

  (* Distance computation *)
  assert_test "compute_distances returns sorted"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x"]; mk "b.ml" ["x";"y"]; mk "c.ml" ["z"]] in
     let ds = compute_distances gs in
     List.length ds = 3 &&
     (List.hd ds).jaccard_dist <= (List.nth ds 1).jaccard_dist);

  assert_test "compute_distances shared_traits correct"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x";"y"]; mk "b.ml" ["y";"z"]] in
     let ds = compute_distances gs in
     (List.hd ds).shared_traits = ["y"]);

  (* Convergence detection *)
  assert_test "detect_convergences empty for close files"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x";"y"]; mk "b.ml" ["x";"y"]] in
     let ds = compute_distances gs in
     detect_convergences gs ds = []);

  assert_test "detect_convergences finds distant shared domain traits"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["sorting";"searching";"x1";"x2";"x3";"x4";"x5";"x6";"x7"];
               mk "b.ml" ["sorting";"searching";"y1";"y2";"y3";"y4";"y5";"y6";"y7"]] in
     let ds = compute_distances gs in
     List.length (detect_convergences gs ds) >= 1);

  (* Lineage chains *)
  assert_test "discover_lineages finds subset chains"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x"];
               mk "b.ml" ["x";"y"];
               mk "c.ml" ["x";"y";"z"]] in
     let chains = discover_lineages gs in
     List.length chains >= 1);

  assert_test "discover_lineages chain has correct length"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x"];
               mk "b.ml" ["x";"y"];
               mk "c.ml" ["x";"y";"z"]] in
     let chains = discover_lineages gs in
     (List.hd chains).chain_length = 3);

  assert_test "discover_lineages rejects non-subset"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x"]; mk "b.ml" ["y"]] in
     let chains = discover_lineages gs in
     chains = []);

  (* Speciation *)
  assert_test "detect_speciations finds divergence"
    (let d = { file_a = "a.ml"; file_b = "b.ml"; jaccard_dist = 0.5;
               shared_traits = ["x";"y";"z"];
               unique_a = ["p";"q"]; unique_b = ["r";"s"] } in
     let specs = detect_speciations [] [d] in
     List.length specs = 1);

  assert_test "detect_speciations rejects too similar"
    (let d = { file_a = "a.ml"; file_b = "b.ml"; jaccard_dist = 0.1;
               shared_traits = ["x";"y";"z"];
               unique_a = ["p";"q"]; unique_b = ["r";"s"] } in
     detect_speciations [] [d] = []);

  assert_test "detect_speciations rejects too distant"
    (let d = { file_a = "a.ml"; file_b = "b.ml"; jaccard_dist = 0.9;
               shared_traits = ["x";"y";"z"];
               unique_a = ["p";"q"]; unique_b = ["r";"s"] } in
     detect_speciations [] [d] = []);

  (* Extinction risk *)
  assert_test "analyze_extinction flags isolated modules"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "lone.ml" ["z99"]; mk "a.ml" ["x";"y"]; mk "b.ml" ["x";"y"]] in
     let ds = compute_distances gs in
     let exts = analyze_extinction gs ds in
     List.exists (fun e -> e.ext_file = "lone.ml") exts);

  assert_test "analyze_extinction does not flag connected modules"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x";"y";"z"]; mk "b.ml" ["x";"y";"z"]] in
     let ds = compute_distances gs in
     analyze_extinction gs ds = []);

  (* Health scoring *)
  assert_test "compute_health returns 0-100"
    (let h = compute_health [] [] [] [] [] [] in h >= 0.0 && h <= 100.0);

  assert_test "compute_health varies with inputs"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x"]; mk "b.ml" ["y"]] in
     let ds = compute_distances gs in
     let h1 = compute_health gs ds [] [] [] [] in
     let gs2 = [mk "a.ml" (List.init 20 (fun i -> "t" ^ string_of_int i));
                mk "b.ml" (List.init 20 (fun i -> "t" ^ string_of_int i))] in
     let ds2 = compute_distances gs2 in
     let h2 = compute_health gs2 ds2 [] [] [] [] in
     h1 <> h2);

  (* Insight generation *)
  assert_test "generate_insights non-empty for valid data"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x";"y"]; mk "b.ml" ["y";"z"]] in
     let ds = compute_distances gs in
     let ins = generate_insights gs ds [] [] [] [] 50.0 in
     List.length ins >= 3);

  assert_test "generate_insights mentions health"
    (let ins = generate_insights [] [] [] [] [] [] 50.0 in
     List.exists (fun s -> string_contains s "50") ins);

  (* File scanning *)
  assert_test "is_source_file accepts .ml"
    (is_source_file "hello.ml");

  assert_test "is_source_file rejects test files"
    (not (is_source_file "test_hello.ml"));

  assert_test "is_source_file rejects self"
    (not (is_source_file "code_lineage.ml"));

  assert_test "is_source_file rejects non-ml"
    (not (is_source_file "hello.py"));

  (* Category names *)
  assert_test "category_name covers all"
    (category_name Structural = "Structural" &&
     category_name Algorithmic = "Algorithmic" &&
     category_name DomainSpecific = "Domain");

  (* Trait lookup *)
  assert_test "trait_name_of_id found"
    (trait_name_of_id "tree" = "Tree structures");

  assert_test "trait_name_of_id not found returns id"
    (trait_name_of_id "nonexistent" = "nonexistent");

  (* Tree rendering *)
  assert_test "tree_to_string leaf"
    (let s = tree_to_string "" (Leaf "test.ml") in
     string_contains s "test.ml");

  assert_test "tree_to_string branch"
    (let s = tree_to_string "" (Branch (Leaf "a.ml", Leaf "b.ml", 0.5)) in
     string_contains s "a.ml" && string_contains s "b.ml");

  (* HTML generation *)
  assert_test "esc escapes HTML"
    (esc "<script>" = "&lt;script&gt;");

  assert_test "esc handles quotes"
    (esc "a\"b" = "a&quot;b");

  assert_test "generate_dashboard produces HTML"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x"]] in
     let r = { genomes = gs; distances = []; tree = Leaf "a.ml";
               convergences = []; lineages = []; speciations = [];
               extinctions = []; health_score = 50.0; insights = ["test"] } in
     let html = generate_dashboard r in
     string_contains html "<!DOCTYPE html>" && string_contains html "Code Lineage Tracker");

  assert_test "generate_dashboard includes all panels"
    (let r = { genomes = []; distances = []; tree = Leaf "x";
               convergences = []; lineages = []; speciations = [];
               extinctions = []; health_score = 0.0; insights = [] } in
     let html = generate_dashboard r in
     string_contains html "panel-0" && string_contains html "panel-6");

  (* Integration: count_lines *)
  assert_test "count_lines empty"
    (count_lines "" = 1);

  assert_test "count_lines multi"
    (count_lines "a\nb\nc\n" = 4);

  (* Distance entry fields *)
  assert_test "distance unique_a correct"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     let gs = [mk "a.ml" ["x";"y"]; mk "b.ml" ["y";"z"]] in
     let ds = compute_distances gs in
     let d = List.hd ds in
     d.unique_a = ["x"] && d.unique_b = ["z"]);

  (* Edge case: single genome *)
  assert_test "compute_distances single genome"
    (let mk n ts = { filename = n; traits = ts; trait_strengths = [];
                     line_count = 10; complexity = 0.1 } in
     compute_distances [mk "a.ml" ["x"]] = []);

  Printf.printf "\n── Results: %d passed, %d failed ──\n\n"
    !tests_passed !tests_failed

(* ── Main ───────────────────────────────────────────────────────────────── *)

let () =
  run_tests ();
  Printf.printf "Analyzing codebase lineage...\n\n";
  let report = analyze () in
  print_report report;
  let html = generate_dashboard report in
  let oc = open_out "lineage_dashboard.html" in
  output_string oc html;
  close_out oc;
  Printf.printf "Dashboard written to lineage_dashboard.html\n"
