<div align="center">

# 🐫 OCaml Sample Code

**A curated collection of idiomatic OCaml programs demonstrating core functional programming concepts**

[![OCaml](https://img.shields.io/badge/language-OCaml-EC6813?style=flat-square&logo=ocaml&logoColor=white)](https://ocaml.org/)
[![License: MIT](https://img.shields.io/github/license/sauravbhattacharya001/Ocaml-sample-code?style=flat-square&color=7aa2f7)](LICENSE)
[![GitHub Pages](https://img.shields.io/badge/docs-GitHub%20Pages-222?style=flat-square&logo=github)](https://sauravbhattacharya001.github.io/Ocaml-sample-code/)
[![GitHub stars](https://img.shields.io/github/stars/sauravbhattacharya001/Ocaml-sample-code?style=flat-square&color=e0af68)](https://github.com/sauravbhattacharya001/Ocaml-sample-code/stargazers)
[![Coverage](https://codecov.io/gh/sauravbhattacharya001/Ocaml-sample-code/graph/badge.svg)](https://codecov.io/gh/sauravbhattacharya001/Ocaml-sample-code)

[**Browse Examples**](#programs) · [**Documentation Site**](https://sauravbhattacharya001.github.io/Ocaml-sample-code/) · [**Concept Map**](https://sauravbhattacharya001.github.io/Ocaml-sample-code/concept-map.html) · [**Complexity Cheat Sheet**](https://sauravbhattacharya001.github.io/Ocaml-sample-code/complexity.html) · [**Getting Started**](#getting-started)

</div>

---

## About

This repository contains self-contained OCaml programs that each focus on a specific language feature or algorithm. Every file compiles and runs independently — perfect for learning OCaml by reading and modifying real code.

**91 programs** covering: recursion, pattern matching, algebraic data types, GADTs, option types, higher-order functions, polymorphism, tail recursion, accumulators, tuple destructuring, input validation, hash tables, memoization, closures, pipe operator, imperative features, modules (Map, Set, Queue), records, graph algorithms, persistent data structures, priority queues, parser combinators, monadic composition, operator precedence parsing, tries, prefix search, string manipulation, Thompson's NFA construction, epsilon closure, regular expression parsing, set-based simulation, lazy evaluation, infinite sequences, self-balancing BSTs, sorting algorithms, disjoint sets, union-find, functional hash maps, separate chaining, auto-resizing, probabilistic data structures, bloom filters, double hashing, skip lists, randomized algorithms, ropes, balanced binary trees, text editing data structures, linear algebra, matrix operations, functors, module signatures, Gaussian elimination, symbolic differentiation, algebraic simplification, chain rule, partial derivatives, symbolic integration, u-substitution, numerical methods, probability monads, Monte Carlo simulation, Bayesian inference, logic programming, unification, algebraic effects, free monads, automatic differentiation, backpropagation, functional reactive programming, network flow algorithms, bytecode virtual machines, term rewriting systems, zippers, property-based testing, finger trees, persistent vectors, abstract interpretation, finite automata, constraint satisfaction, Datalog engines, double-ended queues, diff algorithms, Earley parsing, GADTs, game AI, garbage collection simulation, computational geometry, property graph databases, Huffman coding, HyperLogLog cardinality estimation, interval trees, lambda calculus, model checking, optics (lenses/prisms), PEG parsers, relational algebra, SAT solvers, string matching, suffix arrays, theorem proving, type inference, comonads, random access lists, hash array mapped tries, monad transformers, ray tracing, delimited continuations, Lindenmayer systems, turtle graphics, neural networks, signal processing (FFT, convolution, spectral analysis), behavior trees, autonomous agent task planning.

## Programs

| File | Description | Concepts |
|------|-------------|----------|
| [`abstract_interp.ml`](abstract_interp.ml) | Abstract interpreter for interval domain analysis | Lattice theory, widening/narrowing, abstract transfer functions, fixed-point computation |
| [`actor.ml`](actor.ml) | Actor model — Erlang-style message passing concurrency | Mailboxes, selective receive, supervision trees, process isolation, message routing, fault tolerance |
| [`autodiff.ml`](autodiff.ml) | Automatic differentiation — forward & reverse mode | Dual numbers, computation graphs, tape-based backpropagation, gradient/Jacobian/Hessian, Adam/momentum optimizers, neural network building blocks |
| [`automata.ml`](automata.ml) | Finite automata toolkit — DFA/NFA construction and minimization | Subset construction, Hopcroft's minimization, product construction, NFA→DFA conversion |
| [`bdd.ml`](bdd.ml) | Binary Decision Diagrams — ROBDD construction, Apply algorithm, SAT/TAUT checking | Hash-consing, Shannon expansion, cofactoring, quantification, ITE, DOT export, interactive REPL |
| [`behavior_tree.ml`](behavior_tree.ml) | Behavior Tree engine — hierarchical task planning for autonomous agents | Sequence/Selector/Parallel nodes, decorators (Inverter, Repeat, Cooldown), blackboard memory, tick execution, trace visualization, 3 domains (robot patrol, NPC, thermostat), interactive REPL |
| [`bloom_filter.ml`](bloom_filter.ml) | Bloom filter — probabilistic set membership | Double hashing, tunable FP rate, union, optimal sizing, saturation stats |
| [`bst.ml`](bst.ml) | Binary search tree (insert, delete, traversal, min/max, size, depth) | Algebraic data types, polymorphism, accumulators |
| [`btree.ml`](btree.ml) | B-Tree — self-balancing search tree with configurable degree | Multi-way branching, node splitting, in-order traversal, search, bulk insertion |
| [`bytecode_vm.ml`](bytecode_vm.ml) | Stack-based bytecode virtual machine with compiler and disassembler | Opcodes, stack machines, call frames, closures, upvalues, expression compilation, native functions, execution tracing |
| [`calculus.ml`](calculus.ml) | Symbolic differentiation — derivatives, simplification, evaluation | Algebraic data types, pattern matching, recursive transforms, chain rule, gradient |
| [`cartesian_tree.ml`](cartesian_tree.ml) | Cartesian Tree — binary tree with heap + BST properties | O(n) stack-based construction, range minimum queries (naive & O(1) sparse table), Euler tour, validation, pretty-printing |
| [`crypto.ml`](crypto.ml) | Classical ciphers — ROT13, Caesar, Vigenère, XOR, Rail Fence, Atbash | String manipulation, modular arithmetic, frequency analysis, symmetric encryption |
| [`comonad.ml`](comonad.ml) | Comonads — dual of monads for context-dependent computation | Identity/Env/Traced/Store/Stream comonads, Zipper1D/Zipper2D, cellular automata (Wolfram rules), Game of Life, spreadsheet evaluation, moving average, comonad laws |
| [`constraint.ml`](constraint.ml) | Constraint satisfaction problem solver — Sudoku, N-Queens, graph coloring | Backtracking, arc consistency (AC-3), constraint propagation, MRV/LCV heuristics, forward checking |
| [`crdt.ml`](crdt.ml) | CRDTs — Conflict-free Replicated Data Types for eventual consistency | G-Counter, PN-Counter, G-Set, OR-Set, LWW-Register, MV-Register, vector clocks, merge semilattices |
| [`csp.ml`](csp.ml) | Constraint satisfaction problem solver — Sudoku, N-Queens, graph coloring | Backtracking, arc consistency (AC-3), constraint propagation, MRV/LCV heuristics, forward checking |
| [`csv.ml`](csv.ml) | CSV parser & data analyzer — RFC 4180 parsing with type inference | String parsing, type inference, fold-based aggregation, group-by, filtering, sorting, pretty-printing |
| [`datalog.ml`](datalog.ml) | Datalog query engine — bottom-up evaluation with stratified negation | Semi-naive evaluation, unification, fixed-point computation, stratified negation, aggregation |
| [`delimited_cont.ml`](delimited_cont.ml) | Delimited continuations — shift/reset for composable control flow | CPS transformation, shift/reset, amb operator, coroutines, cooperative threading, exception handling as continuations |
| [`deque.ml`](deque.ml) | Purely functional deque (Okasaki's Banker's Deque) | Amortised O(1) both ends, persistent data structures, sliding window algorithms |
| [`diff.ml`](diff.ml) | Myers diff algorithm — the same algorithm used by git diff | Edit graph, shortest edit script, LCS extraction, unified diff formatting |
| [`dijkstra.ml`](dijkstra.ml) | Weighted graphs — Dijkstra's, Floyd-Warshall, Prim's MST | Weighted adjacency lists, priority queues, shortest paths, minimum spanning trees |
| [`earley.ml`](earley.ml) | Earley parser for context-free grammars | Earley items, predict/scan/complete operations, parse forests, ambiguity handling |
| [`euler_tour_tree.ml`](euler_tour_tree.ml) | Euler Tour Tree — dynamic forest connectivity via Euler tour sequences | Treap-backed implicit sequences, link/cut, connectivity queries, subtree aggregates, rerooting |
| [`effects.ml`](effects.ml) | Algebraic effects and handlers | Free monads, delimited continuations, CPS transforms, effect composition via coproducts, State/Exception/Nondeterminism/Writer/Reader/Coroutine effects, N-Queens |
| [`factor.ml`](factor.ml) | Prime factorization via optimized trial division | Recursion, mutual recursion, input validation |
| [`fenwick_tree.ml`](fenwick_tree.ml) | Fenwick Tree (Binary Indexed Tree) — prefix sums and point updates | Imperative arrays, bit manipulation, functors, O(log n) queries, order statistics |
| [`fibonacci.ml`](fibonacci.ml) | Fibonacci: naive vs memoized vs iterative | Hash tables, closures, imperative features, benchmarking |
| [`finger_tree.ml`](finger_tree.ml) | Finger Trees — versatile functional data structure (Hinze & Paterson, 2006) | Monoid-parameterised measure, 2-3 nodes, O(1) amortised deque ops, O(log n) concat/split, sequences, priority queues, sorted sequences |
| [`frp.ml`](frp.ml) | Functional Reactive Programming — signals, behaviors, events, streams | Time-varying behaviors, event combinators, push-based signals, reactive cells, state machines, animation easing, keyframes, spring physics |
| [`free_monad.ml`](free_monad.ml) | Free monads — separating program description from interpretation | Free/Freer monads, natural transformations, effect interpretation, coproduct effects, composable DSLs |
| [`fsm.ml`](fsm.ml) | Finite state machines — DFA/NFA construction and string acceptance | Variant types, pattern matching, sets/maps, fixpoints, formal language theory |
| [`gadts.ml`](gadts.ml) | Generalized Algebraic Data Types (GADTs) | Type-safe expression evaluators, length-indexed vectors, typed heterogeneous lists, type-level programming |
| [`game_ai.ml`](game_ai.ml) | Minimax game AI with alpha-beta pruning — Tic-Tac-Toe and Connect Four | Module signatures, functors, iterative deepening, transposition tables, minimax |
| [`gc_simulator.ml`](gc_simulator.ml) | Garbage collector simulator — 4 classic GC algorithms | Mark-and-sweep, Cheney's copying, reference counting (cycle detection), generational GC |
| [`genetic.ml`](genetic.ml) | Genetic algorithm framework — evolutionary optimization | Tournament/roulette selection, single/two-point crossover, mutation, elitism, TSP/knapsack/function optimization |
| [`geometry.ml`](geometry.ml) | Computational geometry — convex hull, closest pair, intersections | Cross/dot product, Graham scan, ray casting, divide & conquer, polygon operations |
| [`gossip.ml`](gossip.ml) | Gossip protocol simulator — epidemic information dissemination | Push/pull/push-pull strategies, convergence tracking, network partitions, anti-entropy, autonomous protocol advisor, multiple topologies, interactive REPL |
| [`graph.ml`](graph.ml) | Graph algorithms (BFS, DFS, topological sort, cycle detection) | Modules (Map, Set, Queue), records, imperative queues, variants |
| [`graph_db.ml`](graph_db.ml) | Property graph query engine with Cypher-inspired pattern matching | Property graphs, labeled nodes, typed relationships, backtracking search, projections |
| [`hamt.ml`](hamt.ml) | Hash Array Mapped Trie — persistent hash map (Bagwell 2001) | 32-way bitmap-compressed branching, structural sharing, O(log32 n) ops, collision handling, set operations, transient builder, statistics |
| [`hashmap.ml`](hashmap.ml) | Functional hash map — persistent immutable hash table | Separate chaining, auto-resize, fold/map/filter, merge/union, partition |
| [`heap.ml`](heap.ml) | Priority queue — leftist min-heap (insert, merge, sort, top-k) | Persistent data structures, rank annotations, custom comparators |
| [`hello.ml`](hello.ml) | Variables, types, pipes, and pattern matching | Let bindings, type inference, `Printf`, pipe operator |
| [`huffman.ml`](huffman.ml) | Huffman coding — lossless data compression | Priority queues, recursive tree traversal, frequency analysis, variable-length prefix codes |
| [`hyperloglog.ml`](hyperloglog.ml) | HyperLogLog — probabilistic cardinality estimator | Register-based sketching, harmonic mean estimation, bias correction, merge/union, intersection via inclusion-exclusion, Jaccard similarity, serialization |
| [`integration.ml`](integration.ml) | Symbolic integration engine — antiderivatives, definite integrals, numerical methods | Pattern-based rules, linearity, u-substitution, integration by parts (LIATE), Simpson's rule, verification via differentiation |
| [`interval_tree.ml`](interval_tree.ml) | Interval tree — augmented AVL for efficient overlap queries | AVL balancing, subtree augmentation, O(log n) overlap/stabbing queries |
| [`order_statistics_tree.ml`](order_statistics_tree.ml) | Order Statistics Tree — augmented weight-balanced BST | O(log n) rank, select, count_range, range_query, median, percentile, auto-rebalancing |
| [`json.ml`](json.ml) | JSON parser — complete RFC 8259 parser with queries and transforms | Recursive descent, mutual recursion, Unicode escapes, pretty printing, dot-notation queries |
| [`lambda.ml`](lambda.ml) | Untyped lambda calculus interpreter | Alpha-equivalence, capture-avoiding substitution, De Bruijn indices, beta reduction strategies |
| [`list_last_elem.ml`](list_last_elem.ml) | Find the last element of a list safely | Option types, pattern matching |
| [`lru_cache.ml`](lru_cache.ml) | LRU Cache — bounded least-recently-used cache | Put/get with auto-eviction, hit/miss stats, peek, resize, filter, fold |
| [`lsystem.ml`](lsystem.ml) | L-Systems — Lindenmayer systems and turtle graphics | D0L/stochastic/parametric L-systems, turtle interpretation, SVG output, Koch snowflake, Sierpinski triangle, dragon curve, Hilbert curve, plant/fern, Penrose tiling |
| [`matrix.ml`](matrix.ml) | Matrix — linear algebra with functors and modules | Functors, module signatures, Gaussian elimination, determinant, inverse, matrix power, norms |
| [`mergesort.ml`](mergesort.ml) | Merge sort with custom comparators | Higher-order functions, tail recursion, tuple destructuring |
| [`merkle_tree.ml`](merkle_tree.ml) | Merkle Tree — cryptographic hash trees for data integrity | Binary hash trees, inclusion proofs, O(log n) verification, tamper detection, tree diff |
| [`minikanren.ml`](minikanren.ml) | miniKanren logic programming engine | Unification, substitution, logic variables, streams, relational programming, Peano arithmetic, constraint solving |
| [`monad_transformers.ml`](monad_transformers.ml) | Monad Transformers — composable monad stacks | OptionT, ExceptT, ReaderT, WriterT, StateT, ContT, ListT, RWST, lift, transformer stacking, monad laws, callcc |
| [`model_checker.ml`](model_checker.ml) | CTL model checker for finite-state transition systems | Temporal logic (CTL), labeling algorithm, fixpoint computation, state exploration |
| [`network_flow.ml`](network_flow.ml) | Network flow algorithms — Edmonds-Karp max flow, min-cut, bipartite matching, MCMF | Residual graphs, BFS augmenting paths, flow decomposition, Bellman-Ford SPFA, bipartite reduction, multi-source/sink |
| [`neural_network.ml`](neural_network.ml) | Feedforward neural network with backpropagation — MLP from scratch | Configurable layers, sigmoid/tanh/relu/leaky_relu/softmax, Xavier/He init, MSE/cross-entropy loss, momentum, gradient clipping, learning rate scheduling, batch/stochastic training |
| [`optics.ml`](optics.ml) | Optics — lenses, prisms, and traversals for composable data access | Lenses (get/set), prisms (preview/build), traversals (fold/over), composition |
| [`parser.ml`](parser.ml) | Parser combinators — build parsers from small pieces (arithmetic, lists, key-value) | Higher-order functions, closures, monadic bind/map, recursive descent, operator precedence |
| [`peg.ml`](peg.ml) | Parsing Expression Grammar engine with packrat memoization | PEGs (Ford, 2004), packrat parsing, linear-time guarantee, ordered choice |
| [`persistent_vector.ml`](persistent_vector.ml) | Persistent Vector — Clojure-style immutable array with structural sharing | 32-way branching trie, O(log32 n) get/set, amortized O(1) push_back, tail buffer optimization, transient batch builder, map/fold/filter/sub/append/rev |
| [`probability.ml`](probability.ml) | Probability monad & Monte Carlo simulation | Monadic composition, sampling distributions, statistics, Monte Carlo integration, Markov chains, Bayesian inference |
| [`queue.ml`](queue.ml) | Purely functional queue (Okasaki's Banker's Queue) | Amortised O(1) enqueue/dequeue, two-list technique, persistence |
| [`quickcheck.ml`](quickcheck.ml) | QuickCheck — property-based testing framework | Random generators, monadic combinators, shrinking, counterexample minimization, property specification |
| [`random_access_list.ml`](random_access_list.ml) | Random Access List — Okasaki's skew-binary random access list | O(1) cons/head/tail, O(log n) lookup/update, complete binary trees, skew-binary numbers, persistent data structures |
| [`radix_tree.ml`](radix_tree.ml) | Radix Tree (Patricia Trie) — compressed prefix tree for efficient string storage | Edge compression, prefix search, insert/remove/member, all_words enumeration, space-efficient string sets |
| [`raft.ml`](raft.ml) | Raft consensus algorithm — distributed consensus simulation | Leader election, log replication, commitment quorum, network partitioning, AppendEntries/RequestVote RPCs |
| [`raytracer.ml`](raytracer.ml) | Raytracer — functional ray tracing engine with Phong shading | Vec3/Ray/Camera, sphere & plane intersection, Blinn-Phong lighting, shadows, reflections, anti-aliasing, PPM output |
| [`rbtree.ml`](rbtree.ml) | Red-Black tree — Okasaki-style self-balancing BST | Persistent data structures, balance invariants, set operations, higher-order functions |
| [`regex.ml`](regex.ml) | Regular expression engine — NFA-based pattern matching | Algebraic data types, recursive descent parsing, Thompson's NFA, epsilon closure |
| [`relational.ml`](relational.ml) | Mini relational algebra engine — SQL-like operations on typed tables | Schema validation, select/project/join/union, aggregates, group-by, query composition |
| [`rope.ml`](rope.ml) | Rope — balanced binary tree for efficient string operations | O(log n) concat/split/insert/delete, text editing, balancing, line operations |
| [`sat_solver.ml`](sat_solver.ml) | SAT solver using DPLL algorithm | Backtracking, unit propagation, pure literal elimination, CNF satisfiability |
| [`segment_tree.ml`](segment_tree.ml) | Segment Tree — efficient range queries and point updates | Functors, monoid abstraction, sum/min/max queries, O(log n) update |
| [`signal_processing.ml`](signal_processing.ml) | Signal Processing — FFT, convolution, spectral analysis, windowing | Cooley-Tukey radix-2 FFT/IFFT, magnitude/power/phase spectrum, spectral centroid, peak detection, Hamming/Hann/Blackman/flat-top windows, linear/circular convolution, cross-correlation, autocorrelation, signal generators (sine/square/sawtooth/triangle/chirp/noise), zero-crossing rate, RMS, moving average, EMA |
| [`skip_list.ml`](skip_list.ml) | Skip List — probabilistic sorted data structure | Randomized levels, O(log n) search/insert/delete, range queries, floor/ceil |
| [`splay_tree.ml`](splay_tree.ml) | Splay Tree — self-adjusting binary search tree | Amortized O(log n), top-down splaying, split/merge, range queries, rank, temporal locality |
| [`sorting.ml`](sorting.ml) | Sorting algorithms — 6 sorts with benchmarking utilities | Insertion, selection, quicksort (median-of-three), heapsort, natural mergesort, counting sort |
| [`stream.ml`](stream.ml) | Lazy streams — infinite/lazy sequences with on-demand evaluation | Lazy evaluation, closures, unfold/iterate/cycle, infinite sequences, memoization |
| [`stm.ml`](stm.ml) | Software Transactional Memory — composable concurrent state management | TVars, optimistic concurrency, conflict detection, retry/orElse, monadic composition, bounded channels, atomic transfers |
| [`string_match.ml`](string_match.ml) | String matching algorithms — KMP, Boyer-Moore, Rabin-Karp, Aho-Corasick, Z-algorithm | Failure functions, rolling hash, multi-pattern matching, O(n+m) matching |
| [`suffix_array.ml`](suffix_array.ml) | Suffix array with LCP array — full-text search and substring queries | Suffix sorting, Kasai's LCP, O(m log n) search, longest repeated substrings |
| [`suffix_automaton.ml`](suffix_automaton.ml) | Suffix Automaton (SAM) — minimal DFA recognizing all suffixes of a string | O(n) construction, substring check, distinct substring count, longest common substring, occurrence counting, shortest absent string |
| [`term_rewriting.ml`](term_rewriting.ml) | Term Rewriting Systems — unification, pattern matching, reduction strategies, Knuth-Bendix completion | First-order terms, Robinson's unification, LPO ordering, critical pairs, confluence checking, Peano/Boolean/Group TRSs |
| [`theorem_prover.ml`](theorem_prover.ml) | Propositional theorem prover via natural deduction | Sequent-style proof search, backtracking, inference rules, immutable contexts |
| [`trie.ml`](trie.ml) | Trie (prefix tree) — string storage, prefix search, auto-complete | Map module functor, recursive records, persistence, string manipulation |
| [`type_infer.ml`](type_infer.ml) | Hindley-Milner type inference engine (Algorithm W) | Unification, type variables, let-polymorphism, constraint generation, substitution |
| [`union_find.ml`](union_find.ml) | Union-Find (disjoint sets) — persistent functional implementation | Union-by-rank, path compression, Kruskal's MST, component analysis |
| [`zipper.ml`](zipper.ml) | Zipper — functional cursor for navigating and editing immutable structures | One-hole contexts, list/tree/filesystem zippers, Huet's zipper, rose trees, purely functional editing |
| [`euler_tour_tree.ml`](euler_tour_tree.ml) | Euler Tour Tree — dynamic forest connectivity via Euler tour sequences | Treap-backed implicit sequences, link/cut operations, connectivity queries, subtree aggregates, rerooting |
| [`incremental.ml`](incremental.ml) | Incremental Computation — self-adjusting computation framework | Dependency graph, change propagation, Var/map/map2/bind/array_fold, observers, cutoff functions, freeze, spreadsheet example |
| [`hyperloglog.ml`](hyperloglog.ml) | HyperLogLog — probabilistic cardinality estimator | Register-based sketching, harmonic mean estimation, bias correction, merge/union, intersection via inclusion-exclusion, Jaccard similarity, serialization |
| [`bandit.ml`](bandit.ml) | Multi-Armed Bandit Solver — exploration vs exploitation strategies | Epsilon-Greedy, UCB1, Softmax, Thompson Sampling, EXP3, Gradient Bandit, regret analysis, strategy comparison, non-stationary detection, interactive REPL |

## Getting Started

### Prerequisites

- **OCaml** ≥ 4.08 — install via [opam](https://opam.ocaml.org/doc/Install.html) or your package manager
- **GNU Make** (optional, for batch builds)

```bash
# macOS
brew install ocaml opam

# Ubuntu/Debian
sudo apt install ocaml opam

# Windows (WSL recommended)
sudo apt install ocaml opam

# Verify installation
ocaml -version
```

### Build & Run

```bash
# Clone the repo
git clone https://github.com/sauravbhattacharya001/Ocaml-sample-code.git
cd Ocaml-sample-code

# Build all programs
make

# Build and run all programs
make run

# Clean build artifacts
make clean
```

### Docker

Run all examples in a container — no local OCaml installation needed:

```bash
docker build -t ocaml-samples .
docker run --rm ocaml-samples
```

Run a single example:

```bash
docker run --rm ocaml-samples mergesort
```

### Run Individual Files

```bash
# Compile and run a single file
ocamlopt -o factor factor.ml && ./factor

# Or use the interactive REPL
ocaml
#use "factor.ml";;
```

## Code Highlights

### Prime Factorization — `factor.ml`

Optimized trial division: extracts factors of 2 first, then only checks odd divisors. Early-exits at √n when the remaining value must be prime.

```ocaml
let factors n =
  if n < 2 then invalid_arg "factors: input must be >= 2"
  else
    let rec extract_twos n =
      if n mod 2 = 0 then 2 :: extract_twos (n / 2)
      else odd_factors 3 n
    and odd_factors d n =
      if n = 1 then []
      else if d * d > n then [n]
      else if n mod d = 0 then d :: odd_factors d (n / d)
      else odd_factors (d + 2) n
    in
    extract_twos n
```

```
factors 12  → [2; 2; 3]
factors 360 → [2; 2; 2; 3; 3; 5]
factors 97  → [97]
```

### Binary Search Tree — `bst.ml`

Full BST with algebraic data types. Demonstrates insert, delete (with in-order successor replacement), membership check, and O(n) in-order traversal using an accumulator.

```ocaml
type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

let rec insert x = function
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (left, v, right) ->
    if x < v then Node (insert x left, v, right)
    else if x > v then Node (left, v, insert x right)
    else Node (left, v, right)

(* O(n) traversal — accumulator avoids quadratic list concatenation *)
let inorder tree =
  let rec aux acc = function
    | Leaf -> acc
    | Node (left, v, right) -> aux (v :: aux acc right) left
  in
  aux [] tree
```

```
In-order: 1 3 4 5 6 7 8
Contains 4: true  |  Contains 9: false
Depth: 3  |  Size: 7
After deleting 3: 1 4 5 6 7 8
```

### Merge Sort — `mergesort.ml`

Parameterized by a comparison function for maximum flexibility. Both `split` and `merge` are tail-recursive to handle large inputs without stack overflow.

```ocaml
let rec mergesort cmp = function
  | ([] | [_]) as l -> l
  | lst ->
    let (left, right) = split lst in
    merge cmp (mergesort cmp left) (mergesort cmp right)
```

```
Original:    [38; 27; 43; 3; 9; 82; 10]
Sorted asc:  [3; 9; 10; 27; 38; 43; 82]
Sorted desc: [82; 43; 38; 27; 10; 9; 3]
Words sorted: [apple; banana; cherry; date]
```

### Graph Algorithms — `graph.ml`

Full graph library with adjacency list (Map-based), BFS/DFS traversal, shortest path, connected components, cycle detection (3-color DFS), and topological sort (Kahn's algorithm).

```ocaml
module IntMap = Map.Make(Int)

type graph = {
  adj: int list IntMap.t;
  directed: bool;
}

let bfs g start =
  let visited = Hashtbl.create 16 in
  let queue = Queue.create () in
  Queue.push start queue;
  Hashtbl.replace visited start true;
  (* ... imperative BFS with O(1) queue operations *)
```

```
BFS from 1: [1; 2; 3; 4; 5]
DFS from 1: [1; 2; 4; 3; 5]
Shortest path 1->5: [1; 2; 4; 5]
Connected components: 2
Topological order: [1; 3; 2; 4; 5]
Has cycle: true  (directed graph with back edge)
```

### Priority Queue — `heap.ml`

A purely functional leftist min-heap. Every operation returns a new heap — the original is preserved (persistence). The "leftist" property ensures merge runs in O(log n) by keeping the right spine short.

```ocaml
type 'a heap =
  | Empty
  | Node of int * 'a * 'a heap * 'a heap
  (* Node (rank, value, left_child, right_child) *)

(* Merge is the fundamental operation — O(log n) *)
let rec merge cmp h1 h2 =
  match h1, h2 with
  | Empty, h | h, Empty -> h
  | Node (_, x, a1, b1), Node (_, y, _, _) ->
    if cmp x y <= 0 then make_node x a1 (merge cmp b1 h2)
    else merge cmp h2 h1

(* Everything else is built on merge *)
let insert cmp x h = merge cmp (Node (1, x, Empty, Empty)) h
let delete_min cmp = function
  | Empty -> Empty
  | Node (_, _, left, right) -> merge cmp left right
```

```
Sorted: [1; 2; 3; 4; 5; 6; 7; 8]
Heap sort: [3; 5; 12; 17; 28; 42; 50; 61; 84; 93]
Top 3 smallest: [3; 7; 12]
Persistence: original heap unchanged after insert/delete
```

### Trie (Prefix Tree) — `trie.ml`

A purely functional trie for efficient string storage and prefix-based retrieval. Uses OCaml's `Map.Make` functor for character-indexed children. Every operation returns a new trie — the original is preserved (persistence). Deletion prunes nodes that are no longer needed.

```ocaml
module CharMap = Map.Make(Char)

type trie = {
  is_word: bool;               (* does a word end here? *)
  children: trie CharMap.t;    (* children keyed by char *)
}

(* Insert — walk down, create nodes as needed *)
let rec insert word trie =
  match chars with
  | [] -> { node with is_word = true }
  | c :: rest ->
    let child = match CharMap.find_opt c node.children with
      | Some t -> t | None -> empty in
    { node with children = CharMap.add c (aux rest child) node.children }

(* Prefix search — find subtrie then collect all words *)
let words_with_prefix prefix trie =
  match find_subtrie prefix trie with
  | None -> []
  | Some subtrie -> collect_all_words subtrie
```

```
member "apple":  true   |  member "ap":     false
has_prefix "app": true  |  has_prefix "xyz": false

Auto-complete "app" -> [app; apple; application; apply]
Auto-complete "car" -> [car; card; care; careful; cart]

LCP of [flower; flow; flight]: "fl"
All words sorted: [ball; bat; car; card; cat]
```

### Regular Expression Engine — `regex.ml`

A complete regex engine built from scratch using Thompson's NFA construction. Parses regex syntax into an AST, compiles it to a non-deterministic finite automaton, and simulates it using epsilon-closure — guaranteed linear-time matching with no pathological backtracking.

```ocaml
(* Regex AST — algebraic data types *)
type char_matcher = Lit of char | Dot | Class of (char * char) list * bool
type regex = Empty | Char of char_matcher | Seq of regex * regex
           | Alt of regex * regex | Star of regex | Plus of regex | Opt of regex
           | Anchor_start | Anchor_end

(* Thompson's NFA construction — fragments with epsilon transitions *)
let rec build r = match r with
  | Star r1 ->
    let f = build r1 in
    let s = new_state () in let a = new_state () in
    add_trans s (Epsilon f.frag_start);
    add_trans s (Epsilon a);
    add_trans f.frag_accept (Epsilon f.frag_start);
    add_trans f.frag_accept (Epsilon a);
    { frag_start = s; frag_accept = a }
  | (* ... other cases ... *)

(* NFA simulation — set-based, no backtracking *)
let simulate_at nfa input start_pos =
  let current = ref (epsilon_closure nfa [nfa.start] input start_pos) in
  (* Step through input, tracking longest match *)
```

```
matches "hello" "hello"   = true
matches "ab+c"  "abbc"    = true    (* quantifiers *)
matches "ab+c"  "ac"      = false
matches "colou?r" "color"  = true   (* optional *)
matches "colou?r" "colour" = true
matches "cat|dog" "cat"   = true    (* alternation *)

find "[0-9]+" "abc 123 def" = "123" at pos 4
find_all "[a-z]+" "hello world" = ["hello"; "world"]
replace "[0-9]+" "abc 123 def 456" "#" = "abc # def #"
split "[,;]\s*" "apple, banana; cherry" = ["apple"; "banana"; "cherry"]
```

### Last Element — `list_last_elem.ml`

Classic safe list traversal using `Option` — no exceptions, no crashes on empty lists.

```ocaml
let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t
```

### Parser Combinators — `parser.ml`

Build complex parsers from small, composable pieces. Each parser is a function that takes input and returns either a value or an error — they snap together like LEGO bricks using operators like `>>=` (bind), `<|>` (choice), and `many`.

```ocaml
(* A parser is just a function *)
type 'a parser = string -> int -> 'a result

(* Combine two parsers in sequence (monadic bind) *)
let bind p f = fun input pos ->
  match p input pos with
  | Error _ as e -> e
  | Ok (a, pos') -> (f a) input pos'

(* Parse an arithmetic expression with correct precedence *)
let expr = chainl1 term add_op   (* + - are left-associative *)
let term = chainl1 power mul_op  (* * / are left-associative *)
let power = chainr1 atom pow_op  (* ^ is right-associative *)
let atom = number <|> parens     (* number or (expr) *)
```

```
calc "2 + 3 * 4"       = 14     (* precedence: 2 + (3*4) *)
calc "(2 + 3) * 4"     = 20     (* parentheses override *)
calc "2 ^ 3 ^ 2"       = 512    (* right-assoc: 2^(3^2) = 2^9 *)
calc "((3+5)*2)-(10/2)" = 11

int_list "[1, 2, 3]"   = [1; 2; 3]
kv "name = \"Alice\""  = ("name", "Alice")
```

## Project Structure

```
Ocaml-sample-code/
├── hello.ml              # Variables, types, pipes, pattern matching
├── fibonacci.ml          # Fibonacci: naive vs memoized vs iterative
├── bst.ml                # Binary search tree
├── factor.ml             # Prime factorization
├── list_last_elem.ml     # Last element of a list
├── mergesort.ml          # Merge sort
├── merkle_tree.ml        # Merkle tree (cryptographic hash trees)
├── graph.ml              # Graph algorithms (BFS, DFS, topological sort)
├── dijkstra.ml           # Weighted graphs (Dijkstra, Floyd-Warshall, Prim)
├── heap.ml               # Priority queue (leftist min-heap)
├── parser.ml             # Parser combinators (arithmetic, lists, key-value)
├── trie.ml               # Trie (prefix tree) — string storage, prefix search
├── regex.ml              # Regular expression engine (Thompson's NFA)
├── stream.ml             # Lazy streams (infinite sequences)
├── stm.ml                # Software Transactional Memory (STM)
├── rbtree.ml             # Red-Black tree (Okasaki-style BST)
├── sorting.ml            # 6 sorting algorithms with benchmarks
├── union_find.ml         # Union-Find (disjoint sets, Kruskal's MST)
├── hashmap.ml            # Functional hash map (persistent)
├── bloom_filter.ml       # Bloom filter (probabilistic set)
├── lru_cache.ml          # LRU cache (bounded, persistent)
├── segment_tree.ml       # Segment tree (range queries)
├── signal_processing.ml  # Signal processing (FFT, convolution, spectral analysis)
├── skip_list.ml          # Skip list (probabilistic sorted structure)
├── splay_tree.ml         # Splay tree (self-adjusting BST)
├── rope.ml               # Rope (text editing data structure)
├── btree.ml              # B-Tree (multi-way search tree)
├── json.ml               # JSON parser (RFC 8259)
├── matrix.ml             # Matrix / linear algebra (functors)
├── csv.ml                # CSV parser & data analyzer
├── fenwick_tree.ml       # Fenwick tree (binary indexed tree)
├── crypto.ml             # Classical ciphers (Caesar, Vigenère, etc.)
├── crdt.ml               # CRDTs (Conflict-free Replicated Data Types)
├── calculus.ml           # Symbolic differentiation
├── cartesian_tree.ml     # Cartesian tree with RMQ support
├── integration.ml        # Symbolic integration engine
├── probability.ml        # Probability monad & Monte Carlo
├── minikanren.ml         # miniKanren logic programming
├── effects.ml            # Algebraic effects and handlers
├── autodiff.ml           # Automatic differentiation (forward & reverse)
├── free_monad.ml         # Free monads (effect interpretation)
├── frp.ml                # Functional reactive programming
├── network_flow.ml       # Network flow (max flow, min-cut, MCMF)
├── neural_network.ml     # Feedforward neural network (MLP, backpropagation)
├── bytecode_vm.ml        # Bytecode VM with compiler
├── term_rewriting.ml     # Term rewriting (Knuth-Bendix completion)
├── zipper.ml             # Zippers for immutable structures
├── quickcheck.ml         # Property-based testing framework
├── random_access_list.ml # Random access list (skew-binary)
├── finger_tree.ml        # Finger trees (Hinze & Paterson)
├── persistent_vector.ml  # Persistent vector (Clojure-style)
├── abstract_interp.ml    # Abstract interpretation (interval domain)
├── actor.ml              # Actor model (Erlang-style concurrency)
├── automata.ml           # Finite automata toolkit (DFA/NFA)
├── comonad.ml            # Comonads (context-dependent computation)
├── constraint.ml         # Constraint solver (CSP with AC-3)
├── csp.ml                # Constraint satisfaction (Sudoku, N-Queens)
├── datalog.ml            # Datalog query engine
├── deque.ml              # Purely functional deque (Banker's Deque)
├── delimited_cont.ml     # Delimited continuations (shift/reset)
├── diff.ml               # Myers diff algorithm (git diff)
├── earley.ml             # Earley parser (any CFG)
├── fsm.ml                # Finite state machines
├── gadts.ml              # GADTs (type-safe evaluators)
├── game_ai.ml            # Minimax game AI (Tic-Tac-Toe, Connect Four)
├── gc_simulator.ml       # Garbage collector simulator (4 algorithms)
├── genetic.ml            # Genetic algorithm (evolutionary optimization)
├── geometry.ml           # Computational geometry (convex hull, etc.)
├── gossip.ml             # Gossip protocol simulator (push/pull/push-pull)
├── graph_db.ml           # Property graph query engine
├── hamt.ml               # Hash Array Mapped Trie (persistent hash map)
├── huffman.ml            # Huffman coding (lossless compression)
├── hyperloglog.ml        # HyperLogLog (probabilistic cardinality estimation)
├── interval_tree.ml      # Interval tree (augmented AVL)
├── lambda.ml             # Untyped lambda calculus interpreter
├── lsystem.ml            # L-Systems (Lindenmayer systems, turtle graphics)
├── model_checker.ml      # CTL model checker
├── monad_transformers.ml # Monad transformers (composable stacks)
├── order_statistics_tree.ml # Order Statistics Tree (rank, select, range)
├── optics.ml             # Optics (lenses, prisms, traversals)
├── peg.ml                # PEG parser (packrat memoization)
├── queue.ml              # Purely functional queue
├── radix_tree.ml         # Radix Tree (Patricia Trie) — compressed prefix tree
├── raft.ml               # Raft consensus algorithm (Banker's Queue)
├── raytracer.ml          # Ray tracing engine (functional)
├── relational.ml         # Relational algebra engine
├── sat_solver.ml         # SAT solver (DPLL algorithm)
├── string_match.ml       # String matching (KMP, Boyer-Moore, etc.)
├── suffix_array.ml       # Suffix array with LCP
├── suffix_automaton.ml   # Suffix Automaton (SAM)
├── theorem_prover.ml     # Propositional theorem prover
├── type_infer.ml         # Hindley-Milner type inference
├── incremental.ml        # Incremental computation (self-adjusting)
├── test_*.ml             # Test suites
├── LEARNING_PATH.md      # Progressive learning guide
├── Dockerfile            # Multi-stage Docker build
├── .dockerignore         # Docker build context exclusions
├── Makefile              # Build automation
├── docs/
│   └── index.html        # GitHub Pages documentation site
├── .github/
│   └── workflows/
│       ├── coverage.yml  # Code coverage workflow
│       └── pages.yml     # Pages deployment workflow
├── .editorconfig         # Editor formatting rules
├── .gitignore            # Build artifact exclusions
├── CONTRIBUTING.md       # Contribution guidelines & style guide
└── LICENSE               # MIT License
```

## Documentation

📖 **Interactive documentation site:** [sauravbhattacharya001.github.io/Ocaml-sample-code](https://sauravbhattacharya001.github.io/Ocaml-sample-code/)

The docs site features syntax-highlighted code samples with expected output for each program.

## Learning Resources

📚 **[Learning Path](LEARNING_PATH.md)** — A guided order for studying the examples in this repo, from basics through advanced concepts.

New to OCaml? These resources complement the examples in this repo:

- [**OCaml.org Tutorials**](https://ocaml.org/docs) — official guides and language manual
- [**Real World OCaml**](https://dev.realworldocaml.org/) — comprehensive free book
- [**99 Problems in OCaml**](https://ocaml.org/exercises) — practice problems by difficulty
- [**OCaml Playground**](https://ocaml.org/play) — try OCaml in the browser

## Testing & Coverage

The repository includes a comprehensive test suite (`test_all.ml`) covering all core algorithms:

```bash
# Run tests
make test

# Run tests with coverage (requires bisect_ppx)
opam install bisect_ppx ocamlfind
make coverage

# Generate HTML coverage report
make coverage-html
# Open _coverage/index.html in your browser
```

**Tested algorithms:** BST operations, prime factorization, Fibonacci (naive/memoized/iterative), merge sort, min/max heaps, list operations, graph algorithms (BFS, DFS, shortest path, cycle detection, topological sort, connected components), trie operations (insert, delete, member, prefix search, auto-complete, longest common prefix, pruning, persistence), parser combinators (primitives, combinators, arithmetic expression evaluation), regex engine (parsing, matching, quantifiers, alternation, character classes, anchors, find/find_all/replace/split).

Coverage reports are generated automatically on every push via [GitHub Actions](https://github.com/sauravbhattacharya001/Ocaml-sample-code/actions/workflows/coverage.yml) using [bisect_ppx](https://github.com/aantron/bisect_ppx).

## Contributing

Contributions are welcome! See **[CONTRIBUTING.md](CONTRIBUTING.md)** for detailed guidelines, style conventions, and how to add tests.

**Quick start:**

1. Fork the repository
2. Create a feature branch (`git checkout -b add-heap-example`)
3. Write a self-contained `.ml` file with comments explaining the concepts
4. Add tests to `test_all.ml` if applicable
5. Verify: `make all && make test`
6. Submit a pull request

## License

This project is licensed under the MIT License — see the [LICENSE](LICENSE) file for details.

---

<div align="center">

**Built by [Saurav Bhattacharya](https://github.com/sauravbhattacharya001)**

⭐ Star this repo if you found it useful!

</div>
