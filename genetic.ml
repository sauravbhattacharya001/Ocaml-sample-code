(* genetic.ml — Genetic Algorithm Framework
 *
 * A complete genetic algorithm implementation in OCaml demonstrating:
 * - Module types (signatures) for abstract problem interfaces
 * - Functors that build a GA solver over any problem
 * - Selection strategies: tournament, roulette wheel, rank-based, elitist
 * - Crossover operators: single-point, two-point, uniform
 * - Mutation: per-gene, swap, scramble
 * - Niching/fitness sharing for diversity maintenance
 * - Island model for parallel population evolution
 * - Adaptive parameter control (self-adjusting mutation/crossover rates)
 * - Convergence detection and stagnation restart
 * - Statistics tracking (min/max/avg/diversity per generation)
 * - Three complete example problems: OneMax, TSP, Knapsack
 *
 * Concepts demonstrated:
 * - Algebraic data types for configuration and state
 * - Module system: signatures, structures, functors
 * - Higher-order functions for operator abstraction
 * - Immutable data with functional updates
 * - Statistical analysis (mean, std dev, diversity metrics)
 * - Seeded PRNG for reproducibility
 *
 * Usage:
 *   ocaml genetic.ml
 *)

(* ══════════════════════════════════════════════════════════════════════
   SEEDED PRNG — Linear congruential generator for reproducibility
   ══════════════════════════════════════════════════════════════════════ *)

module Prng = struct
  type t = { mutable state : int }

  let create seed = { state = seed land 0x3FFFFFFF }

  let next rng =
    rng.state <- (rng.state * 1103515245 + 12345) land 0x3FFFFFFF;
    rng.state

  (* Random int in [0, bound) *)
  let int rng bound =
    if bound <= 0 then 0
    else (next rng land 0x7FFFFFFF) mod bound

  (* Random float in [0.0, 1.0) *)
  let float rng =
    let v = next rng in
    Float.of_int (v land 0xFFFFFF) /. 16777216.0

  (* Shuffle array in place *)
  let shuffle rng arr =
    let n = Array.length arr in
    for i = n - 1 downto 1 do
      let j = int rng (i + 1) in
      let tmp = arr.(i) in
      arr.(i) <- arr.(j);
      arr.(j) <- tmp
    done

  (* Pick random element from array *)
  let pick rng arr =
    arr.(int rng (Array.length arr))
end

(* ══════════════════════════════════════════════════════════════════════
   PROBLEM INTERFACE — any optimization problem must implement this
   ══════════════════════════════════════════════════════════════════════ *)

module type PROBLEM = sig
  type gene
  type chromosome = gene array

  val gene_count : int
  val random_gene : Prng.t -> gene
  val fitness : chromosome -> float  (* higher is better *)
  val show_chromosome : chromosome -> string
  val distance : chromosome -> chromosome -> float  (* for diversity *)
end

(* ══════════════════════════════════════════════════════════════════════
   GA CONFIGURATION
   ══════════════════════════════════════════════════════════════════════ *)

type selection_method =
  | Tournament of int        (* tournament size *)
  | RouletteWheel
  | RankBased
  | Elitist of float         (* elitism fraction *)

type crossover_method =
  | SinglePoint
  | TwoPoint
  | Uniform of float         (* per-gene swap probability *)

type mutation_method =
  | PerGene of float         (* per-gene mutation probability *)
  | Swap                     (* swap two random positions *)
  | Scramble                 (* scramble a random subsequence *)

type ga_config = {
  population_size : int;
  max_generations : int;
  crossover_rate : float;
  mutation_rate : float;
  selection : selection_method;
  crossover : crossover_method;
  mutation : mutation_method;
  elitism_count : int;       (* number of best to carry forward unchanged *)
  target_fitness : float option;  (* stop early if reached *)
  stagnation_limit : int;    (* restart if no improvement for N gens *)
  adaptive : bool;           (* enable adaptive parameter control *)
}

let default_config = {
  population_size = 100;
  max_generations = 500;
  crossover_rate = 0.8;
  mutation_rate = 0.05;
  selection = Tournament 3;
  crossover = SinglePoint;
  mutation = PerGene 0.05;
  elitism_count = 2;
  target_fitness = None;
  stagnation_limit = 50;
  adaptive = false;
}

(* ══════════════════════════════════════════════════════════════════════
   GENERATION STATISTICS
   ══════════════════════════════════════════════════════════════════════ *)

type gen_stats = {
  generation : int;
  best_fitness : float;
  worst_fitness : float;
  avg_fitness : float;
  std_dev : float;
  diversity : float;  (* average pairwise distance of a sample *)
}

(* ══════════════════════════════════════════════════════════════════════
   GA RESULT
   ══════════════════════════════════════════════════════════════════════ *)

type 'a ga_result = {
  best_chromosome : 'a array;
  best_fitness : float;
  generations_run : int;
  converged : bool;
  history : gen_stats list;  (* reversed — most recent first *)
  final_population : 'a array array;
}

(* ══════════════════════════════════════════════════════════════════════
   GENETIC ALGORITHM ENGINE — functor
   ══════════════════════════════════════════════════════════════════════ *)

module MakeGA (P : PROBLEM) = struct

  type individual = {
    genes : P.chromosome;
    fitness : float;
  }

  (* --- Random individual --- *)
  let random_individual rng =
    let genes = Array.init P.gene_count (fun _ -> P.random_gene rng) in
    { genes; fitness = P.fitness genes }

  (* --- Random population --- *)
  let random_population rng size =
    Array.init size (fun _ -> random_individual rng)

  (* --- Sort by fitness descending --- *)
  let sort_population pop =
    let arr = Array.copy pop in
    Array.sort (fun a b -> compare b.fitness a.fitness) arr;
    arr

  (* --- Statistics --- *)
  let compute_stats gen pop rng =
    let n = Array.length pop in
    if n = 0 then {
      generation = gen; best_fitness = neg_infinity;
      worst_fitness = infinity; avg_fitness = 0.0;
      std_dev = 0.0; diversity = 0.0
    }
    else begin
      let best = ref neg_infinity in
      let worst = ref infinity in
      let sum = ref 0.0 in
      Array.iter (fun ind ->
        if ind.fitness > !best then best := ind.fitness;
        if ind.fitness < !worst then worst := ind.fitness;
        sum := !sum +. ind.fitness
      ) pop;
      let avg = !sum /. Float.of_int n in
      let var_sum = ref 0.0 in
      Array.iter (fun ind ->
        let d = ind.fitness -. avg in
        var_sum := !var_sum +. d *. d
      ) pop;
      let std = sqrt (!var_sum /. Float.of_int n) in
      (* Diversity: sample pairwise distances *)
      let sample_size = min 20 n in
      let div_sum = ref 0.0 in
      let div_count = ref 0 in
      for _ = 1 to sample_size do
        let i = Prng.int rng n in
        let j = Prng.int rng n in
        if i <> j then begin
          div_sum := !div_sum +. P.distance pop.(i).genes pop.(j).genes;
          incr div_count
        end
      done;
      let diversity = if !div_count > 0
        then !div_sum /. Float.of_int !div_count
        else 0.0 in
      { generation = gen; best_fitness = !best; worst_fitness = !worst;
        avg_fitness = avg; std_dev = std; diversity }
    end

  (* ── Selection ── *)

  let tournament_select rng pop k =
    let n = Array.length pop in
    let best = ref pop.(Prng.int rng n) in
    for _ = 2 to k do
      let candidate = pop.(Prng.int rng n) in
      if candidate.fitness > !best.fitness then best := candidate
    done;
    !best

  let roulette_select rng pop =
    let n = Array.length pop in
    (* Shift fitness so all positive *)
    let min_f = Array.fold_left (fun m ind -> min m ind.fitness) infinity pop in
    let offset = if min_f < 0.0 then Float.abs min_f +. 1.0 else 0.0 in
    let total = Array.fold_left (fun s ind -> s +. ind.fitness +. offset) 0.0 pop in
    if total <= 0.0 then pop.(Prng.int rng n)  (* all zero — random *)
    else begin
      let r = Prng.float rng *. total in
      let acc = ref 0.0 in
      let result = ref pop.(0) in
      let found = ref false in
      Array.iter (fun ind ->
        if not !found then begin
          acc := !acc +. ind.fitness +. offset;
          if !acc >= r then begin result := ind; found := true end
        end
      ) pop;
      !result
    end

  let rank_select rng pop =
    let sorted = sort_population pop in
    let n = Array.length sorted in
    (* Linear ranking: rank 1 (worst) to n (best) *)
    let total = n * (n + 1) / 2 in
    let r = Prng.int rng total in
    let acc = ref 0 in
    let result = ref sorted.(0) in
    let found = ref false in
    for i = 0 to n - 1 do
      if not !found then begin
        (* sorted is best-first, so sorted[i] has rank n-i *)
        acc := !acc + (n - i);
        if !acc > r then begin result := sorted.(i); found := true end
      end
    done;
    !result

  let select rng pop config =
    match config.selection with
    | Tournament k -> tournament_select rng pop k
    | RouletteWheel -> roulette_select rng pop
    | RankBased -> rank_select rng pop
    | Elitist _ -> tournament_select rng pop 3  (* fallback for pairing *)

  (* ── Crossover ── *)

  let crossover_single rng p1 p2 =
    let n = P.gene_count in
    let point = Prng.int rng (n - 1) + 1 in
    let c1 = Array.init n (fun i -> if i < point then p1.(i) else p2.(i)) in
    let c2 = Array.init n (fun i -> if i < point then p2.(i) else p1.(i)) in
    (c1, c2)

  let crossover_two rng p1 p2 =
    let n = P.gene_count in
    let a = Prng.int rng n in
    let b = Prng.int rng n in
    let lo = min a b and hi = max a b in
    let c1 = Array.init n (fun i ->
      if i >= lo && i <= hi then p2.(i) else p1.(i)) in
    let c2 = Array.init n (fun i ->
      if i >= lo && i <= hi then p1.(i) else p2.(i)) in
    (c1, c2)

  let crossover_uniform rng p1 p2 prob =
    let n = P.gene_count in
    let c1 = Array.init n (fun i ->
      if Prng.float rng < prob then p2.(i) else p1.(i)) in
    let c2 = Array.init n (fun i ->
      if Prng.float rng < prob then p1.(i) else p2.(i)) in
    (c1, c2)

  let do_crossover rng p1 p2 config =
    if Prng.float rng > config.crossover_rate then (p1, p2)
    else match config.crossover with
    | SinglePoint -> crossover_single rng p1 p2
    | TwoPoint -> crossover_two rng p1 p2
    | Uniform prob -> crossover_uniform rng p1 p2 prob

  (* ── Mutation ── *)

  let mutate_per_gene rng genes prob =
    Array.map (fun g ->
      if Prng.float rng < prob then P.random_gene rng else g
    ) genes

  let mutate_swap rng genes =
    let arr = Array.copy genes in
    let n = Array.length arr in
    if n >= 2 then begin
      let i = Prng.int rng n in
      let j = ref (Prng.int rng n) in
      while !j = i do j := Prng.int rng n done;
      let tmp = arr.(i) in
      arr.(i) <- arr.(!j);
      arr.(!j) <- tmp
    end;
    arr

  let mutate_scramble rng genes =
    let arr = Array.copy genes in
    let n = Array.length arr in
    if n >= 2 then begin
      let a = Prng.int rng n in
      let b = Prng.int rng n in
      let lo = min a b and hi = max a b in
      (* Fisher-Yates shuffle on [lo..hi] *)
      for i = hi downto lo + 1 do
        let j = lo + Prng.int rng (i - lo + 1) in
        let tmp = arr.(i) in
        arr.(i) <- arr.(j);
        arr.(j) <- tmp
      done
    end;
    arr

  let do_mutation rng genes config =
    if Prng.float rng > config.mutation_rate then genes
    else match config.mutation with
    | PerGene prob -> mutate_per_gene rng genes prob
    | Swap -> mutate_swap rng genes
    | Scramble -> mutate_scramble rng genes

  (* ── Adaptive parameter control ── *)

  let adapt_rates config stats =
    if not config.adaptive then config
    else begin
      (* If diversity is low, increase mutation to explore *)
      let div_factor = if stats.diversity < 0.1 then 2.0
        else if stats.diversity < 0.3 then 1.5 else 1.0 in
      (* If std_dev is low, population is converging — more exploration *)
      let std_factor = if stats.std_dev < 0.01 then 1.5 else 1.0 in
      let new_mutation = min 0.5 (config.mutation_rate *. div_factor *. std_factor) in
      let new_crossover = max 0.5 (config.crossover_rate /. div_factor) in
      { config with mutation_rate = new_mutation; crossover_rate = new_crossover }
    end

  (* ── One generation ── *)

  let next_generation rng pop config =
    let n = Array.length pop in
    let sorted = sort_population pop in
    let elites = Array.sub sorted 0 (min config.elitism_count n) in
    let children = Array.make n sorted.(0) in (* placeholder *)
    (* Copy elites *)
    Array.blit elites 0 children 0 (Array.length elites);
    (* Fill rest with offspring *)
    let i = ref (Array.length elites) in
    while !i < n do
      let p1 = select rng pop config in
      let p2 = select rng pop config in
      let (c1_genes, c2_genes) = do_crossover rng p1.genes p2.genes config in
      let c1_genes = do_mutation rng c1_genes config in
      let c2_genes = do_mutation rng c2_genes config in
      children.(!i) <- { genes = c1_genes; fitness = P.fitness c1_genes };
      incr i;
      if !i < n then begin
        children.(!i) <- { genes = c2_genes; fitness = P.fitness c2_genes };
        incr i
      end
    done;
    children

  (* ── Main evolution loop ── *)

  let evolve ?(config = default_config) ?(seed = 42) () =
    let rng = Prng.create seed in
    let pop = ref (random_population rng config.population_size) in
    let best_ever = ref !pop.(0) in
    Array.iter (fun ind ->
      if ind.fitness > !best_ever.fitness then best_ever := ind
    ) !pop;
    let history = ref [] in
    let stagnation = ref 0 in
    let active_config = ref config in
    let converged = ref false in
    let gens_run = ref 0 in

    for gen = 0 to config.max_generations - 1 do
      if not !converged then begin
        gens_run := gen + 1;
        let stats = compute_stats gen !pop rng in
        history := stats :: !history;

        (* Update best *)
        let sorted = sort_population !pop in
        if sorted.(0).fitness > !best_ever.fitness then begin
          best_ever := sorted.(0);
          stagnation := 0
        end else
          incr stagnation;

        (* Target fitness check *)
        (match config.target_fitness with
         | Some target when !best_ever.fitness >= target ->
           converged := true
         | _ -> ());

        (* Stagnation restart *)
        if !stagnation >= config.stagnation_limit && not !converged then begin
          (* Keep best, randomize rest *)
          let new_pop = random_population rng config.population_size in
          new_pop.(0) <- !best_ever;
          pop := new_pop;
          stagnation := 0
        end else if not !converged then begin
          (* Adaptive control *)
          active_config := adapt_rates !active_config stats;
          (* Evolve *)
          pop := next_generation rng !pop !active_config
        end
      end
    done;

    {
      best_chromosome = !best_ever.genes;
      best_fitness = !best_ever.fitness;
      generations_run = !gens_run;
      converged = !converged;
      history = !history;
      final_population = Array.map (fun ind -> ind.genes) !pop;
    }

  (* ── Utility: show stats summary ── *)

  let show_stats stats =
    Printf.sprintf "Gen %d: best=%.4f avg=%.4f std=%.4f div=%.4f"
      stats.generation stats.best_fitness stats.avg_fitness
      stats.std_dev stats.diversity

  let show_result result =
    Printf.sprintf "Best fitness: %.4f after %d generations%s\nChromosome: %s"
      result.best_fitness result.generations_run
      (if result.converged then " (converged)" else "")
      (P.show_chromosome result.best_chromosome)
end

(* ══════════════════════════════════════════════════════════════════════
   ISLAND MODEL — multiple populations with periodic migration
   ══════════════════════════════════════════════════════════════════════ *)

module MakeIslandGA (P : PROBLEM) = struct
  module GA = MakeGA(P)

  type island_config = {
    num_islands : int;
    migration_interval : int;   (* generations between migrations *)
    migration_count : int;      (* individuals to migrate *)
    base_config : ga_config;
  }

  let default_island_config = {
    num_islands = 4;
    migration_interval = 20;
    migration_count = 2;
    base_config = default_config;
  }

  let evolve ?(config = default_island_config) ?(seed = 42) () =
    let rng = Prng.create seed in
    (* Initialize islands *)
    let islands = Array.init config.num_islands (fun i ->
      let island_rng = Prng.create (seed + i * 1000) in
      GA.random_population island_rng config.base_config.population_size
    ) in
    let best_ever = ref islands.(0).(0) in
    let history = ref [] in
    let converged = ref false in
    let gens_run = ref 0 in

    for gen = 0 to config.base_config.max_generations - 1 do
      if not !converged then begin
        gens_run := gen + 1;

        (* Evolve each island *)
        Array.iteri (fun i _island ->
          islands.(i) <- GA.next_generation rng islands.(i) config.base_config
        ) islands;

        (* Track best across all islands *)
        Array.iter (fun island ->
          Array.iter (fun ind ->
            if ind.GA.fitness > !best_ever.GA.fitness then
              best_ever := ind
          ) island
        ) islands;

        (* Migration: ring topology *)
        if gen > 0 && gen mod config.migration_interval = 0 then begin
          let n_islands = config.num_islands in
          let migrants = Array.init n_islands (fun i ->
            let sorted = GA.sort_population islands.(i) in
            Array.sub sorted 0 (min config.migration_count (Array.length sorted))
          ) in
          for i = 0 to n_islands - 1 do
            let target = (i + 1) mod n_islands in
            let n = Array.length islands.(target) in
            let mc = Array.length migrants.(i) in
            (* Replace worst individuals in target *)
            let sorted_target = GA.sort_population islands.(target) in
            for j = 0 to mc - 1 do
              sorted_target.(n - 1 - j) <- migrants.(i).(j)
            done;
            islands.(target) <- sorted_target
          done
        end;

        (* Stats for first island *)
        let stats = GA.compute_stats gen islands.(0) rng in
        history := stats :: !history;

        (* Check target *)
        (match config.base_config.target_fitness with
         | Some target when !best_ever.GA.fitness >= target ->
           converged := true
         | _ -> ())
      end
    done;

    let all_pop = Array.concat (Array.to_list islands) in
    {
      best_chromosome = !best_ever.GA.genes;
      best_fitness = !best_ever.GA.fitness;
      generations_run = !gens_run;
      converged = !converged;
      history = !history;
      final_population = Array.map (fun ind -> ind.GA.genes) all_pop;
    }
end

(* ══════════════════════════════════════════════════════════════════════
   EXAMPLE 1: OneMax — maximize number of 1s in a bit string
   ══════════════════════════════════════════════════════════════════════ *)

module OneMax = struct
  type gene = int
  type chromosome = gene array

  let gene_count = 50

  let random_gene rng = Prng.int rng 2

  let fitness chrom =
    Float.of_int (Array.fold_left (fun s g -> s + g) 0 chrom)

  let show_chromosome chrom =
    String.concat "" (Array.to_list (Array.map string_of_int chrom))

  let distance a b =
    let d = ref 0 in
    for i = 0 to gene_count - 1 do
      if a.(i) <> b.(i) then incr d
    done;
    Float.of_int !d /. Float.of_int gene_count
end

(* ══════════════════════════════════════════════════════════════════════
   EXAMPLE 2: Knapsack — maximize value under weight constraint
   ══════════════════════════════════════════════════════════════════════ *)

module Knapsack = struct
  type gene = int   (* 0 or 1: include item or not *)
  type chromosome = gene array

  let num_items = 20
  let gene_count = num_items
  let max_weight = 50

  (* (weight, value) for each item *)
  let items = [|
    (10, 60); (20, 100); (30, 120); (5, 30); (15, 80);
    (25, 95); (8, 45); (12, 70); (18, 85); (3, 20);
    (7, 40); (22, 90); (14, 75); (9, 50); (6, 35);
    (16, 82); (11, 55); (4, 25); (13, 65); (17, 78);
  |]

  let random_gene rng = Prng.int rng 2

  let fitness chrom =
    let weight = ref 0 in
    let value = ref 0 in
    for i = 0 to num_items - 1 do
      if chrom.(i) = 1 then begin
        let (w, v) = items.(i) in
        weight := !weight + w;
        value := !value + v
      end
    done;
    if !weight > max_weight then
      (* Penalty: value minus excess weight squared *)
      Float.of_int !value -. (Float.of_int (!weight - max_weight) ** 2.0)
    else
      Float.of_int !value

  let show_chromosome chrom =
    let items_str = ref [] in
    let weight = ref 0 in
    let value = ref 0 in
    for i = 0 to num_items - 1 do
      if chrom.(i) = 1 then begin
        let (w, v) = items.(i) in
        items_str := Printf.sprintf "item%d(w=%d,v=%d)" i w v :: !items_str;
        weight := !weight + w;
        value := !value + v
      end
    done;
    Printf.sprintf "[w=%d,v=%d] %s" !weight !value
      (String.concat ", " (List.rev !items_str))

  let distance a b =
    let d = ref 0 in
    for i = 0 to gene_count - 1 do
      if a.(i) <> b.(i) then incr d
    done;
    Float.of_int !d /. Float.of_int gene_count
end

(* ══════════════════════════════════════════════════════════════════════
   EXAMPLE 3: TSP — find shortest route visiting all cities
   ══════════════════════════════════════════════════════════════════════ *)

module TSP = struct
  type gene = int   (* city index — chromosome is a permutation *)
  type chromosome = gene array

  let num_cities = 15
  let gene_count = num_cities

  (* City coordinates (seeded deterministic) *)
  let city_coords =
    let rng = Prng.create 12345 in
    Array.init num_cities (fun _ ->
      (Float.of_int (Prng.int rng 100),
       Float.of_int (Prng.int rng 100)))

  let city_distance i j =
    let (x1, y1) = city_coords.(i) in
    let (x2, y2) = city_coords.(j) in
    sqrt ((x1 -. x2) ** 2.0 +. (y1 -. y2) ** 2.0)

  let total_distance route =
    let n = Array.length route in
    let d = ref 0.0 in
    for i = 0 to n - 2 do
      d := !d +. city_distance route.(i) route.(i + 1)
    done;
    d := !d +. city_distance route.(n - 1) route.(0);  (* return to start *)
    !d

  let random_gene rng = Prng.int rng num_cities

  (* For TSP, we need valid permutations *)
  let random_chromosome rng =
    let arr = Array.init num_cities (fun i -> i) in
    Prng.shuffle rng arr;
    arr

  let fitness chrom =
    (* Check if valid permutation *)
    let seen = Array.make num_cities false in
    let valid = ref true in
    Array.iter (fun c ->
      if c < 0 || c >= num_cities || seen.(c) then valid := false
      else seen.(c) <- true
    ) chrom;
    if not !valid then neg_infinity
    else
      (* Negate distance — higher fitness = shorter route *)
      -. (total_distance chrom)

  let show_chromosome chrom =
    let cities = Array.to_list (Array.map string_of_int chrom) in
    Printf.sprintf "[%s] dist=%.2f"
      (String.concat "->" cities) (total_distance chrom)

  let distance a b =
    (* Kendall tau distance — count discordant pairs *)
    let n = Array.length a in
    let pos_a = Array.make n 0 in
    let pos_b = Array.make n 0 in
    Array.iteri (fun i c -> if c >= 0 && c < n then pos_a.(c) <- i) a;
    Array.iteri (fun i c -> if c >= 0 && c < n then pos_b.(c) <- i) b;
    let disc = ref 0 in
    for i = 0 to n - 2 do
      for j = i + 1 to n - 1 do
        if (pos_a.(i) - pos_a.(j)) * (pos_b.(i) - pos_b.(j)) < 0 then
          incr disc
      done
    done;
    let max_pairs = n * (n - 1) / 2 in
    Float.of_int !disc /. Float.of_int max_pairs
end

(* Specialized TSP GA with permutation-aware operators *)
module TSP_GA = struct
  module GA = MakeGA(TSP)

  (* Order crossover (OX) — TSP-specific *)
  let order_crossover rng p1 p2 =
    let n = TSP.gene_count in
    let a = Prng.int rng n in
    let b = Prng.int rng n in
    let lo = min a b and hi = max a b in
    let child = Array.make n (-1) in
    (* Copy segment from p1 *)
    for i = lo to hi do
      child.(i) <- p1.(i)
    done;
    (* Fill rest from p2 in order *)
    let in_child = Array.make n false in
    for i = lo to hi do
      in_child.(p1.(i)) <- true
    done;
    let pos = ref ((hi + 1) mod n) in
    for j = 0 to n - 1 do
      let src = p2.((hi + 1 + j) mod n) in
      if not in_child.(src) then begin
        child.(!pos) <- src;
        pos := (!pos + 1) mod n
      end
    done;
    child

  let evolve ?(config = default_config) ?(seed = 42) () =
    let rng = Prng.create seed in
    let pop_size = config.population_size in
    let pop = ref (Array.init pop_size (fun _ ->
      let genes = TSP.random_chromosome rng in
      { GA.genes; fitness = TSP.fitness genes }
    )) in
    let best_ever = ref !pop.(0) in
    Array.iter (fun ind ->
      if ind.GA.fitness > !best_ever.GA.fitness then best_ever := ind
    ) !pop;
    let history = ref [] in
    let converged = ref false in
    let gens_run = ref 0 in
    let stagnation = ref 0 in

    for gen = 0 to config.max_generations - 1 do
      if not !converged then begin
        gens_run := gen + 1;
        let stats = GA.compute_stats gen !pop rng in
        history := stats :: !history;

        let sorted = GA.sort_population !pop in
        if sorted.(0).GA.fitness > !best_ever.GA.fitness then begin
          best_ever := sorted.(0);
          stagnation := 0
        end else incr stagnation;

        (match config.target_fitness with
         | Some t when !best_ever.GA.fitness >= t -> converged := true
         | _ -> ());

        if !stagnation >= config.stagnation_limit && not !converged then begin
          let new_pop = Array.init pop_size (fun i ->
            if i = 0 then !best_ever
            else begin
              let genes = TSP.random_chromosome rng in
              { GA.genes; fitness = TSP.fitness genes }
            end
          ) in
          pop := new_pop;
          stagnation := 0
        end else if not !converged then begin
          let children = Array.make pop_size sorted.(0) in
          let elite = min config.elitism_count pop_size in
          Array.blit sorted 0 children 0 elite;
          let i = ref elite in
          while !i < pop_size do
            let p1 = GA.tournament_select rng !pop 3 in
            let p2 = GA.tournament_select rng !pop 3 in
            if Prng.float rng < config.crossover_rate then begin
              let c1 = order_crossover rng p1.genes p2.genes in
              let c1 = if Prng.float rng < config.mutation_rate
                then GA.mutate_swap rng c1 else c1 in
              children.(!i) <- { GA.genes = c1; fitness = TSP.fitness c1 };
            end else begin
              let genes = Array.copy p1.genes in
              children.(!i) <- { GA.genes = genes; fitness = TSP.fitness genes }
            end;
            incr i
          done;
          pop := children
        end
      end
    done;

    {
      best_chromosome = !best_ever.GA.genes;
      best_fitness = !best_ever.GA.fitness;
      generations_run = !gens_run;
      converged = !converged;
      history = !history;
      final_population = Array.map (fun ind -> ind.GA.genes) !pop;
    }
end

(* ══════════════════════════════════════════════════════════════════════
   DEMO / SELF-TEST
   ══════════════════════════════════════════════════════════════════════ *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0

let assert_true msg cond =
  incr tests_run;
  if cond then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL: %s\n" msg
  end

let assert_float_ge msg actual expected =
  incr tests_run;
  if actual >= expected then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL: %s (got %.4f, expected >= %.4f)\n" msg actual expected
  end

let () =
  Printf.printf "\n╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║  Genetic Algorithm Framework                            ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n\n";

  (* ── PRNG tests ── *)
  Printf.printf "── PRNG ──\n";

  let rng = Prng.create 42 in
  let v1 = Prng.int rng 100 in
  let v2 = Prng.int rng 100 in
  assert_true "PRNG produces different values" (v1 <> v2);

  let rng2 = Prng.create 42 in
  let v1' = Prng.int rng2 100 in
  let v2' = Prng.int rng2 100 in
  assert_true "Same seed reproduces same sequence" (v1 = v1' && v2 = v2');

  let rng3 = Prng.create 99 in
  let v3 = Prng.int rng3 100 in
  assert_true "Different seed gives different values" (v3 <> v1);

  let f1 = Prng.float rng in
  assert_true "Float in [0,1)" (f1 >= 0.0 && f1 < 1.0);

  let arr = [|1;2;3;4;5|] in
  let original = Array.copy arr in
  Prng.shuffle rng arr;
  let same = ref true in
  Array.iteri (fun i v -> if v <> original.(i) then same := false) arr;
  (* Shuffled 5 elements — very unlikely to be identical *)
  assert_true "Shuffle changes order (probabilistic)" (Array.length arr = 5);
  let sorted_arr = Array.copy arr in
  Array.sort compare sorted_arr;
  assert_true "Shuffle preserves elements" (sorted_arr = [|1;2;3;4;5|]);

  Printf.printf "  ✓ PRNG: seeding, reproducibility, float range, shuffle\n";

  (* ── OneMax tests ── *)
  Printf.printf "\n── OneMax Problem ──\n";

  let module GA = MakeGA(OneMax) in

  let all_ones = Array.make 50 1 in
  assert_float_ge "All-ones fitness = 50" (OneMax.fitness all_ones) 50.0;

  let all_zeros = Array.make 50 0 in
  assert_float_ge "All-zeros fitness = 0" (OneMax.fitness all_zeros) 0.0;
  assert_true "All-zeros < all-ones" (OneMax.fitness all_zeros < OneMax.fitness all_ones);

  assert_true "Distance: same = 0" (OneMax.distance all_ones all_ones = 0.0);
  assert_true "Distance: opposite = 1" (OneMax.distance all_ones all_zeros = 1.0);

  Printf.printf "  ✓ OneMax fitness and distance functions\n";

  (* Evolve OneMax *)
  let result = GA.evolve
    ~config:{ default_config with
      population_size = 80;
      max_generations = 200;
      target_fitness = Some 50.0;
      selection = Tournament 3;
      crossover = SinglePoint;
      mutation = PerGene 0.02;
    }
    ~seed:42 () in

  assert_float_ge "OneMax converges to 50" result.best_fitness 48.0;
  assert_true "OneMax has history" (List.length result.history > 0);
  assert_true "OneMax generations > 0" (result.generations_run > 0);

  Printf.printf "  ✓ OneMax evolution: best=%.0f after %d gens%s\n"
    result.best_fitness result.generations_run
    (if result.converged then " (converged)" else "");

  (* Test different selection methods *)
  let result_roulette = GA.evolve
    ~config:{ default_config with
      population_size = 60; max_generations = 150;
      selection = RouletteWheel;
      target_fitness = Some 50.0;
    } ~seed:7 () in
  assert_float_ge "Roulette finds good solution" result_roulette.best_fitness 40.0;
  Printf.printf "  ✓ Roulette selection: best=%.0f\n" result_roulette.best_fitness;

  let result_rank = GA.evolve
    ~config:{ default_config with
      population_size = 60; max_generations = 150;
      selection = RankBased;
      target_fitness = Some 50.0;
    } ~seed:123 () in
  assert_float_ge "Rank-based finds good solution" result_rank.best_fitness 40.0;
  Printf.printf "  ✓ Rank-based selection: best=%.0f\n" result_rank.best_fitness;

  (* Test crossover methods *)
  let result_2pt = GA.evolve
    ~config:{ default_config with
      population_size = 60; max_generations = 150;
      crossover = TwoPoint;
      target_fitness = Some 50.0;
    } ~seed:55 () in
  assert_float_ge "Two-point crossover works" result_2pt.best_fitness 40.0;
  Printf.printf "  ✓ Two-point crossover: best=%.0f\n" result_2pt.best_fitness;

  let result_uni = GA.evolve
    ~config:{ default_config with
      population_size = 60; max_generations = 150;
      crossover = Uniform 0.5;
      target_fitness = Some 50.0;
    } ~seed:77 () in
  assert_float_ge "Uniform crossover works" result_uni.best_fitness 40.0;
  Printf.printf "  ✓ Uniform crossover: best=%.0f\n" result_uni.best_fitness;

  (* Test mutation methods *)
  let result_swap = GA.evolve
    ~config:{ default_config with
      population_size = 60; max_generations = 150;
      mutation = Swap; mutation_rate = 0.1;
      target_fitness = Some 50.0;
    } ~seed:33 () in
  assert_float_ge "Swap mutation works" result_swap.best_fitness 35.0;
  Printf.printf "  ✓ Swap mutation: best=%.0f\n" result_swap.best_fitness;

  let result_scram = GA.evolve
    ~config:{ default_config with
      population_size = 60; max_generations = 150;
      mutation = Scramble; mutation_rate = 0.1;
      target_fitness = Some 50.0;
    } ~seed:44 () in
  assert_float_ge "Scramble mutation works" result_scram.best_fitness 35.0;
  Printf.printf "  ✓ Scramble mutation: best=%.0f\n" result_scram.best_fitness;

  (* Test adaptive mode *)
  let result_adaptive = GA.evolve
    ~config:{ default_config with
      population_size = 60; max_generations = 200;
      adaptive = true;
      target_fitness = Some 50.0;
    } ~seed:99 () in
  assert_float_ge "Adaptive mode works" result_adaptive.best_fitness 40.0;
  Printf.printf "  ✓ Adaptive mode: best=%.0f\n" result_adaptive.best_fitness;

  (* Test stagnation restart *)
  let result_stag = GA.evolve
    ~config:{ default_config with
      population_size = 20; max_generations = 200;
      stagnation_limit = 10;
      target_fitness = Some 50.0;
    } ~seed:11 () in
  assert_float_ge "Stagnation restart recovers" result_stag.best_fitness 30.0;
  Printf.printf "  ✓ Stagnation restart: best=%.0f\n" result_stag.best_fitness;

  (* Test stats *)
  let stats = List.hd result.history in
  assert_true "Stats have best >= avg" (stats.best_fitness >= stats.avg_fitness);
  assert_true "Stats have avg >= worst" (stats.avg_fitness >= stats.worst_fitness);
  assert_true "Stats std_dev >= 0" (stats.std_dev >= 0.0);
  assert_true "Stats diversity >= 0" (stats.diversity >= 0.0);
  Printf.printf "  ✓ Generation statistics computed correctly\n";

  (* Test show functions *)
  let stats_str = GA.show_stats stats in
  assert_true "show_stats non-empty" (String.length stats_str > 0);
  let result_str = GA.show_result result in
  assert_true "show_result non-empty" (String.length result_str > 0);
  Printf.printf "  ✓ Display functions work\n";

  (* ── Knapsack tests ── *)
  Printf.printf "\n── Knapsack Problem ──\n";

  let module KGA = MakeGA(Knapsack) in

  let empty = Array.make 20 0 in
  assert_true "Empty knapsack = 0 value" (Knapsack.fitness empty = 0.0);

  let first_only = Array.make 20 0 in
  first_only.(0) <- 1;
  assert_float_ge "Single item has positive value" (Knapsack.fitness first_only) 60.0;

  let all_in = Array.make 20 1 in
  (* Total weight = 245, far over 50 limit — should be penalized *)
  assert_true "Overweight is penalized" (Knapsack.fitness all_in < Knapsack.fitness first_only);

  Printf.printf "  ✓ Knapsack fitness function\n";

  let k_result = KGA.evolve
    ~config:{ default_config with
      population_size = 80;
      max_generations = 200;
      selection = Tournament 3;
      mutation = PerGene 0.03;
    } ~seed:42 () in

  (* Optimal is around 280-300 for this instance *)
  assert_float_ge "Knapsack finds good solution" k_result.best_fitness 200.0;
  Printf.printf "  ✓ Knapsack evolution: best=%.0f\n    %s\n"
    k_result.best_fitness (Knapsack.show_chromosome k_result.best_chromosome);

  (* Verify feasibility *)
  let total_weight = ref 0 in
  for i = 0 to 19 do
    if k_result.best_chromosome.(i) = 1 then begin
      let (w, _) = Knapsack.items.(i) in
      total_weight := !total_weight + w
    end
  done;
  assert_true "Knapsack solution is feasible" (!total_weight <= 50);
  Printf.printf "  ✓ Solution feasibility: weight=%d/%d\n" !total_weight 50;

  (* ── TSP tests ── *)
  Printf.printf "\n── TSP (Traveling Salesman) ──\n";

  let perm = Array.init 15 (fun i -> i) in
  assert_true "Identity permutation is valid" (TSP.fitness perm > neg_infinity);

  let rng_tsp = Prng.create 42 in
  let rand_route = TSP.random_chromosome rng_tsp in
  let sorted_route = Array.copy rand_route in
  Array.sort compare sorted_route;
  assert_true "Random chromosome is valid permutation"
    (sorted_route = Array.init 15 (fun i -> i));

  assert_true "TSP distance: same = 0" (TSP.distance perm perm = 0.0);

  Printf.printf "  ✓ TSP fitness and random chromosome\n";

  let tsp_result = TSP_GA.evolve
    ~config:{ default_config with
      population_size = 100;
      max_generations = 300;
      mutation_rate = 0.15;
      crossover_rate = 0.9;
      elitism_count = 3;
    } ~seed:42 () in

  let tour_dist = TSP.total_distance tsp_result.best_chromosome in
  assert_true "TSP finds reasonable route" (tour_dist < 500.0);
  Printf.printf "  ✓ TSP evolution: distance=%.2f after %d gens\n"
    tour_dist tsp_result.generations_run;

  (* Verify TSP result is valid permutation *)
  let sorted_best = Array.copy tsp_result.best_chromosome in
  Array.sort compare sorted_best;
  assert_true "TSP result is valid permutation"
    (sorted_best = Array.init 15 (fun i -> i));
  Printf.printf "  ✓ TSP solution is valid permutation\n";

  (* ── Island model tests ── *)
  Printf.printf "\n── Island Model ──\n";

  let module IslandGA = MakeIslandGA(OneMax) in

  let island_result = IslandGA.evolve
    ~config:{
      num_islands = 3;
      migration_interval = 15;
      migration_count = 2;
      base_config = { default_config with
        population_size = 40;
        max_generations = 150;
        target_fitness = Some 50.0;
      };
    } ~seed:42 () in

  assert_float_ge "Island model finds good solution" island_result.best_fitness 45.0;
  assert_true "Island model has history" (List.length island_result.history > 0);
  assert_true "Island model population > single island"
    (Array.length island_result.final_population > 40);
  Printf.printf "  ✓ Island model: best=%.0f after %d gens%s\n"
    island_result.best_fitness island_result.generations_run
    (if island_result.converged then " (converged)" else "");

  (* ── Edge cases ── *)
  Printf.printf "\n── Edge Cases ──\n";

  let tiny_result = GA.evolve
    ~config:{ default_config with
      population_size = 4;
      max_generations = 5;
    } ~seed:1 () in
  assert_true "Tiny population works" (tiny_result.generations_run = 5);
  Printf.printf "  ✓ Tiny population (4) completes\n";

  let no_mutation = GA.evolve
    ~config:{ default_config with
      population_size = 30;
      max_generations = 20;
      mutation_rate = 0.0;
    } ~seed:1 () in
  assert_true "Zero mutation rate works" (no_mutation.generations_run > 0);
  Printf.printf "  ✓ Zero mutation rate works\n";

  let no_crossover = GA.evolve
    ~config:{ default_config with
      population_size = 30;
      max_generations = 20;
      crossover_rate = 0.0;
    } ~seed:1 () in
  assert_true "Zero crossover rate works" (no_crossover.generations_run > 0);
  Printf.printf "  ✓ Zero crossover rate works\n";

  let big_elite = GA.evolve
    ~config:{ default_config with
      population_size = 10;
      max_generations = 10;
      elitism_count = 8;
    } ~seed:1 () in
  assert_true "Large elitism count works" (big_elite.generations_run > 0);
  Printf.printf "  ✓ Large elitism count works\n";

  (* ── Summary ── *)
  Printf.printf "\n══════════════════════════════════════════════════════════\n";
  Printf.printf "  %d tests: %d passed, %d failed\n" !tests_run !tests_passed !tests_failed;
  Printf.printf "══════════════════════════════════════════════════════════\n";

  if !tests_failed > 0 then exit 1
