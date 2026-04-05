# 📚 Learning Path

A guided order for studying the examples in this repository. Each file builds on concepts from the previous ones.

## Stage 1: Foundations

### [`hello.ml`](hello.ml) — Start Here

**Concepts:** `let` bindings, type inference, `Printf`, string concatenation, pipe operator (`|>`)

OCaml infers types without annotations. The pipe operator chains transformations left-to-right, making data pipelines readable:

```ocaml
[1; 2; 3; 4; 5]
|> List.filter (fun x -> x mod 2 = 0)   (* keep evens *)
|> List.map (fun x -> x * x)             (* square them *)
|> List.fold_left (+) 0                   (* sum *)
(* Result: 20 *)
```

**Key takeaway:** OCaml code reads like math. No semicolons, no type declarations, no `return` keyword.

---

## Stage 2: Core Patterns

### [`list_last_elem.ml`](list_last_elem.ml) — Safe List Traversal

**Concepts:** `option` types, pattern matching, recursion

OCaml uses `Option` instead of null. This function never crashes — it returns `None` for empty lists and `Some x` for the last element:

```ocaml
let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t
```

**Key takeaway:** Pattern matching replaces `if/else` chains and is exhaustive — the compiler warns if you miss a case.

### [`factor.ml`](factor.ml) — Recursive Algorithms

**Concepts:** recursion, mutual recursion (`and`), input validation (`invalid_arg`)

Builds on recursion from `list_last_elem.ml`. Introduces mutually recursive functions (`extract_twos` and `odd_factors` defined with `and`) and shows how OCaml handles errors without exceptions in the happy path.

**Key takeaway:** Mutual recursion with `let rec ... and ...` is a natural way to express multi-phase algorithms.

---

## Stage 3: Data Structures

### [`bst.ml`](bst.ml) — Algebraic Data Types

**Concepts:** variant types, polymorphism (`'a`), structural recursion, accumulators

This is where OCaml shines. Algebraic data types let you model tree structures in 3 lines:

```ocaml
type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree
```

The `'a` means the tree works with any type — integers, strings, custom records. Pattern matching on trees feels natural.

**Key takeaway:** Algebraic data types + pattern matching = elegant data structure code. The accumulator pattern in `inorder` converts O(n²) to O(n).

---

## Stage 4: Higher-Order Functions

### [`mergesort.ml`](mergesort.ml) — Functions as Arguments

**Concepts:** higher-order functions, polymorphism, tail recursion, tuple destructuring

The sort function takes a comparison function as a parameter — sort ascending, descending, or by any custom criteria:

```ocaml
mergesort compare data           (* ascending *)
mergesort (fun a b -> compare b a) data  (* descending *)
mergesort String.compare words   (* strings! *)
```

Both `split` and `merge` are tail-recursive to handle large inputs without stack overflow.

**Key takeaway:** Passing functions as arguments makes code reusable. Tail recursion makes it production-ready.

---

## Stage 5: Imperative OCaml

### [`fibonacci.ml`](fibonacci.ml) — Mutable State When You Need It

**Concepts:** hash tables (`Hashtbl`), closures, memoization, `Sys.time` benchmarking

OCaml is primarily functional, but supports mutable state. The memoized Fibonacci uses a closure over a hash table — the cache persists between calls but is invisible to the outside world:

```ocaml
let fib_memo =
  let cache = Hashtbl.create 64 in
  let rec fib n = ...
  in fib  (* only the function escapes; cache is private *)
```

Compares three approaches: naive (exponential), memoized (linear), and iterative (constant space). Demonstrates that choosing the right approach matters more than micro-optimization.

**Key takeaway:** OCaml lets you use mutable state locally while keeping your public API pure. Closures are a powerful encapsulation mechanism.

---

## Stage 6: Modules & Graph Algorithms

### [`graph.ml`](graph.ml) — Modules, Records, and Classic Algorithms

**Concepts:** functor-generated modules (`Map.Make`, `Set.Make`), record types, imperative queues (`Queue`), BFS, DFS, topological sort, cycle detection

This example brings together everything from earlier stages. It uses OCaml's `Map.Make` functor to create a type-safe adjacency list, records for structured data, and both functional recursion and imperative queues:

```ocaml
module IntMap = Map.Make(Int)

type graph = {
  adj: int list IntMap.t;
  directed: bool;
}
```

BFS uses `Queue` for O(1) operations; DFS uses natural recursion. Cycle detection uses a 3-color scheme (White/Gray/Black) — a `Gray` back-edge means a cycle. Topological sort uses Kahn's in-degree algorithm.

**Key takeaway:** OCaml modules and functors let you build type-safe abstractions. Real-world OCaml combines functional and imperative styles — use whichever fits the algorithm.

---

## Stage 7: Persistent Data Structures

### [`heap.ml`](heap.ml) — Purely Functional Priority Queue

**Concepts:** rank-annotated algebraic data types, persistent (immutable) data structures, merge-based design, custom comparators, bottom-up construction

A leftist heap is a priority queue where every operation creates a new heap — the original is preserved. This is "persistence" — a hallmark of functional programming. The key insight is that **everything is built on `merge`**:

```ocaml
type 'a heap =
  | Empty
  | Node of int * 'a * 'a heap * 'a heap

let rec merge cmp h1 h2 =
  match h1, h2 with
  | Empty, h | h, Empty -> h
  | Node (_, x, a1, b1), Node (_, y, _, _) ->
    if cmp x y <= 0 then make_node x a1 (merge cmp b1 h2)
    else merge cmp h2 h1
```

Insert is `merge` with a singleton. Delete-min is `merge` of the two children. The "rank" annotation keeps the right spine short (O(log n)), guaranteeing efficient operations.

Also demonstrates bottom-up O(n) heap construction via pairwise merging, heap sort, and top-k extraction.

**Key takeaway:** Persistent data structures let you "undo" operations for free — the old version still exists. The merge-based design pattern shows how one well-designed operation can power an entire API.

---

## Stage 8: Tries & String Algorithms

### [`trie.ml`](trie.ml) — Prefix Tree for String Storage

**Concepts:** `Map.Make` functor (character-indexed children), recursive record types, persistence, string-to-char-list conversion, tree pruning, prefix-based retrieval

A trie stores strings as paths through a tree where each edge is a character. Words sharing prefixes share nodes — making prefix search and auto-complete natural O(m) operations (m = query length). Like the heap, every operation returns a new trie — the original is preserved.

```ocaml
module CharMap = Map.Make(Char)

type trie = {
  is_word: bool;               (* does a word end at this node? *)
  children: trie CharMap.t;    (* children keyed by character *)
}
```

The `CharMap` (created via `Map.Make(Char)`) gives us sorted character keys for free — `all_words` returns results in lexicographic order without explicit sorting. Deletion prunes dead-end nodes automatically.

Key operations: `insert`, `member`, `delete`, `has_prefix`, `words_with_prefix` (auto-complete), `longest_common_prefix`, ASCII visualization.

**Key takeaway:** Choosing the right data structure turns hard problems into simple ones. Prefix search in a trie is trivial — just navigate to the prefix node and collect descendants. The `Map.Make` functor pattern for character-indexed children is reusable for any alphabet.

---

## Stage 9: Parser Combinators

### [`parser.ml`](parser.ml) — Building Parsers from Small Pieces

**Concepts:** higher-order functions (functions returning functions), closures, monadic bind (`>>=`), function composition, recursive descent, operator precedence, algebraic data types for ASTs

Parser combinators are *the* quintessential functional programming pattern. Each parser is a function; you build complex parsers by combining simple ones with operators:

```ocaml
type 'a parser = string -> int -> 'a result

(* Monadic bind: sequence two parsers *)
let bind p f = fun input pos ->
  match p input pos with
  | Error _ as e -> e
  | Ok (a, pos') -> (f a) input pos'
```

The library includes 15+ combinators (`bind`, `map`, `choice`, `many`, `sep_by`, `between`, `chainl1`, `chainr1`, etc.) and three complete parsers:

- **Arithmetic expressions** with correct operator precedence (`+`, `-`, `*`, `/`, `^`, parentheses)
- **Integer lists** (`[1, 2, 3]`)
- **Key-value pairs** (`name = "Alice", age = "30"`)

The expression parser demonstrates how layered grammar rules naturally encode precedence:

```ocaml
let expr  = chainl1 term  add_op   (* lowest: + - *)
let term  = chainl1 power mul_op   (* middle: * / *)
let power = chainr1 atom  pow_op   (* highest: ^  *)
let atom  = integer <|> parens     (* base cases *)
```

**Key takeaway:** Monadic composition (`>>=`) is the most powerful functional pattern — it lets you thread state (parse position) through a chain of operations while keeping each step independent and composable. The same pattern appears in I/O, error handling, async programming, and more.

---

## Stage 10: Regular Expressions

### [`regex.ml`](regex.ml) — Building a Regex Engine from Scratch

**Concepts:** recursive descent parsing (regex syntax → AST), Thompson's NFA construction (AST → state machine), epsilon closure (set-based state tracking), NFA simulation (linear-time matching), character classes, escapes, anchors

This example ties together parsing (Stage 9) with automata theory. A regex pattern is parsed into an AST, compiled to a non-deterministic finite automaton (NFA) using Thompson's construction, then simulated using epsilon-closure — tracking all possible states simultaneously:

```ocaml
(* The regex AST *)
type regex = Empty | Char of char_matcher | Seq of regex * regex
           | Alt of regex * regex | Star of regex | Plus of regex | Opt of regex
           | Anchor_start | Anchor_end

(* Thompson's NFA: Star creates a split state with back-edge *)
| Star r1 ->
  let f = build r1 in
  let s = new_state () in let a = new_state () in
  add_trans s (Epsilon f.frag_start);  (* enter body *)
  add_trans s (Epsilon a);             (* skip body *)
  add_trans f.frag_accept (Epsilon f.frag_start);  (* loop *)
  add_trans f.frag_accept (Epsilon a);             (* exit *)
```

The key insight is the NFA simulation: instead of backtracking (which can be exponential), we track **all possible states** at once using epsilon closure. This guarantees O(n×m) time where n is the input length and m is the pattern length — no pathological cases.

Features: `.` (any char), `*+?` (quantifiers), `|` (alternation), `()` (grouping), `[a-z]` (character classes), `[^...]` (negation), `\d\w\s` (shorthands), `^$` (anchors). Full API: `matches`, `find`, `find_all`, `replace`, `split`.

**Key takeaway:** Thompson's construction elegantly converts a declarative pattern into an executable state machine. The NFA simulation with epsilon closure demonstrates that tracking multiple states simultaneously (a set-based approach) avoids the exponential blowup of naive backtracking.

---

## Stage 11: Linear Algebra & Functors

### [`matrix.ml`](matrix.ml) — Matrix Operations via Functors

**Concepts:** Module signatures (`NUM`), functors (`Make`), abstract types, imperative arrays, Gaussian elimination, numerical algorithms

This is the capstone example for OCaml's module system. A `NUM` signature defines what it means to be a numeric type, then a `Make` functor produces a complete matrix library for any type implementing `NUM`:

```ocaml
module type NUM = sig
  type t
  val zero : t
  val one : t
  val add : t -> t -> t
  val mul : t -> t -> t
  (* ... *)
end

module Make (N : NUM) = struct
  type t = { rows: int; cols: int; data: N.t array array }
  let mul a b = (* matrix multiplication using N.mul and N.add *)
  let det m = (* Gaussian elimination with partial pivoting *)
  let inverse m = (* Gauss-Jordan elimination *)
  (* ... *)
end

module FloatMatrix = Make(Float_Num)
module IntMatrix   = Make(Int_Num)
```

Features: create/identity/diagonal, add/sub/mul/scale/hadamard, transpose, determinant (Gaussian elimination with partial pivoting), inverse (Gauss-Jordan), trace, matrix power (fast exponentiation), Frobenius/max norms, predicates (symmetric, diagonal, triangular), fold/map/iter, pretty printing.

**Key takeaway:** Functors let you write algorithms once and reuse them across types. The `Make(Float_Num)` and `Make(Int_Num)` instantiations produce completely separate, type-safe matrix implementations from the same code. This is OCaml's answer to generics/templates — more powerful because functors can express complex constraints.

---

## Stage 12: Control Flow & Continuations

### [`delimited_cont.ml`](delimited_cont.ml) — Shift/Reset for Composable Control Flow

**Concepts:** CPS (Continuation-Passing Style), delimited continuations via shift/reset, amb operator, coroutines, cooperative threading, exception handling as continuations

Delimited continuations capture only part of a computation (up to the nearest `reset`), unlike `call/cc` which captures everything. This makes them composable and practical for non-deterministic search, coroutines, and effect systems:

```ocaml
(* shift captures the current continuation up to reset *)
let result = reset (fun () ->
  let x = shift (fun k -> k 10 + k 20) in
  x * 2)
(* Result: 10*2 + 20*2 = 60 *)
```

Features: shift/reset primitives, CPS transformation, `amb` operator for backtracking search, cooperative coroutines, yield/resume threading, exception handling via continuations.

**Key takeaway:** Delimited continuations unify many seemingly different control flow patterns — exceptions, generators, backtracking, coroutines — under a single abstraction. Once you understand shift/reset, algebraic effects (Stage 13's `effects.ml`) become much clearer.

---

## Stage 13: Generative Art & Rewriting

### [`lsystem.ml`](lsystem.ml) — Lindenmayer Systems and Turtle Graphics

**Concepts:** string rewriting, deterministic/stochastic/parametric L-systems, turtle graphics interpretation, SVG generation, fractal geometry

L-systems generate complex structures by repeatedly rewriting strings according to rules, then interpreting the result geometrically. Each symbol becomes a turtle command (move, turn, push/pop):

```ocaml
(* Koch snowflake: start with a triangle, replace each line with a bump *)
let koch = { axiom = "F--F--F";
             rules = [('F', "F+F--F+F")];
             angle = 60.0 }

(* After n iterations, interpret as turtle graphics → SVG *)
let svg = lsystem_to_svg koch 4
```

Features: D0L systems (deterministic, context-free), stochastic L-systems (random rule selection), parametric L-systems (symbols with numeric parameters), turtle graphics interpretation, SVG output. Classic fractals: Koch snowflake, Sierpinski triangle, dragon curve, Hilbert curve, plant/fern, Penrose tiling.

**Key takeaway:** L-systems show how simple recursive rewriting rules produce stunning visual complexity — the same principle underlying fractal geometry, plant morphology, and procedural generation.

---

## Stage 14: Machine Learning from Scratch

### [`neural_network.ml`](neural_network.ml) — Feedforward Neural Network with Backpropagation

**Concepts:** multilayer perceptrons, activation functions, weight initialization, gradient descent, backpropagation, loss functions, learning rate scheduling, momentum

A complete MLP implementation using only OCaml's standard library — no frameworks, no external dependencies. Forward pass, loss computation, backward pass with gradient flow, and weight updates:

```ocaml
(* Create a 2-layer network: 2 inputs → 4 hidden → 1 output *)
let net = create_network [2; 4; 1]
    ~activation:Relu ~output_activation:Sigmoid
    ~init:He ~loss:BinaryCrossEntropy

(* Train on XOR for 1000 epochs *)
let trained = train net xor_data
    ~epochs:1000 ~lr:0.01 ~momentum:0.9
```

Features: configurable layer sizes, activation functions (sigmoid, tanh, relu, leaky_relu, softmax), Xavier/He weight initialization, MSE and cross-entropy loss, batch and stochastic training, momentum, gradient clipping, learning rate scheduling (constant, decay, step), training history tracking.

**Key takeaway:** Implementing backpropagation from scratch reveals the core mechanics behind deep learning — it's just the chain rule applied systematically through a computation graph, with gradient descent updating weights to minimize loss.

---

## Stage 15: Search, Optimization & Constraint Solving

### [`astar.ml`](astar.ml) — A* Pathfinding

**Concepts:** priority queues, heuristic search, graph traversal, grid-based pathfinding

A generic A* implementation with pluggable heuristics (Manhattan, Euclidean, Chebyshev) and ASCII visualization. Demonstrates how informed search dramatically reduces exploration compared to BFS/Dijkstra by combining actual cost with estimated remaining distance.

**Key takeaway:** A* is optimal when the heuristic is admissible (never overestimates). The implementation shows how OCaml's module system cleanly separates the search algorithm from domain-specific heuristics.

### [`simplex.ml`](simplex.ml) — Linear Programming

**Concepts:** two-phase simplex method, tableau operations, optimization, constraint systems

Solves linear programs (maximize c^Tx subject to Ax ≤ b, x ≥ 0) using the classic simplex algorithm. Covers pivot operations, artificial variables for Phase I, and degeneracy handling.

**Key takeaway:** The simplex method navigates vertices of a convex polytope — each pivot moves to an adjacent vertex with a better objective value.

### [`dancing_links.ml`](dancing_links.ml) — Exact Cover (Algorithm X)

**Concepts:** Knuth's Algorithm X, doubly-linked circular lists, backtracking, constraint satisfaction

Implements Donald Knuth's DLX technique for solving exact cover problems — the foundation for efficient Sudoku solvers, polyomino tilings, and N-Queens. The "dancing" refers to the elegant unlinking/relinking of nodes during backtracking.

**Key takeaway:** DLX shows how a clever data structure (doubly-linked circular lists with column headers) can make backtracking dramatically faster by enabling O(1) undo operations.

### [`bdd.ml`](bdd.ml) — Binary Decision Diagrams

**Concepts:** reduced ordered BDDs, memoization, canonical representations, Boolean algebra

BDDs provide compact canonical representations of Boolean functions. Used in hardware verification, model checking, and symbolic computation. Operations like AND, OR, and equivalence checking become polynomial on the BDD representation.

**Key takeaway:** Canonicity is powerful — two Boolean functions are equivalent if and only if their BDDs are identical, enabling O(1) equivalence checking after construction.

---

## Stage 16: Advanced Trees & Probabilistic Structures

### [`splay_tree.ml`](splay_tree.ml) — Self-Adjusting BST

**Concepts:** amortized analysis, tree rotations, self-adjusting data structures, working set property

Splay trees rotate accessed nodes to the root, providing O(log n) amortized time without storing balance information. Frequently accessed elements migrate toward the root, giving excellent cache locality.

### [`treap.ml`](treap.ml) — Randomized BST

**Concepts:** randomized data structures, heap-ordered priorities, expected O(log n) operations

A treap combines BST ordering on keys with heap ordering on random priorities. The random priorities ensure the tree is balanced in expectation — no rotations needed, just split and merge.

### [`aa_tree.ml`](aa_tree.ml) — Simplified Red-Black Tree

**Concepts:** level-based balancing, skew/split operations, simplified invariants

AA trees use a single "level" integer instead of red/black colors, reducing the number of cases in insert/delete from ~20 to ~2. Two operations — `skew` (right rotation) and `split` (left rotation + level increment) — handle all rebalancing.

### [`cuckoo_filter.ml`](cuckoo_filter.ml) — Space-Efficient Approximate Sets

**Concepts:** fingerprinting, cuckoo hashing, probabilistic membership testing, deletion support

Like Bloom filters but supports deletion and offers better space efficiency at low false-positive rates. Elements are stored as fingerprints in a cuckoo hash table with bucket-based relocation.

### [`hyperloglog.ml`](hyperloglog.ml) — Cardinality Estimation

**Concepts:** probabilistic counting, harmonic mean, register-based estimation

Estimates the number of distinct elements in a stream using only O(log log n) space. Used in databases and analytics to count unique visitors, distinct queries, etc.

**Key takeaway:** Probabilistic data structures trade exact answers for dramatic space savings — HyperLogLog can estimate billions of unique elements using just a few KB of memory.

---

## Stage 17: Systems, Languages & Computation Theory

### [`turing_machine.ml`](turing_machine.ml) — Universal Computation

**Concepts:** Turing machine model, transition tables, tape-based computation, halting

A classic single-tape Turing machine simulator with configurable alphabets and transition rules. The foundational model of computation — any algorithm can be expressed as a Turing machine.

### [`prolog.ml`](prolog.ml) — Logic Programming Interpreter

**Concepts:** unification, occurs check, backtracking search, Horn clauses, SLD resolution

A mini Prolog interpreter implementing unification with occurs check and depth-first search through the clause database. Demonstrates how logic programming inverts the usual control flow — you declare *what* to find, not *how* to find it.

### [`forth.ml`](forth.ml) — Stack-Based Language

**Concepts:** stack machines, concatenative programming, dictionary-based dispatch

A Forth interpreter with a data stack, return stack, and extensible word dictionary. Forth's minimalism makes it an excellent study in language implementation — the entire interpreter loop fits in a few dozen lines.

### [`consistent_hashing.ml`](consistent_hashing.ml) — Distributed Key Routing

**Concepts:** hash rings, virtual nodes, minimal remapping, distributed systems

A purely functional consistent hashing ring for distributing keys across nodes. When a node joins or leaves, only K/N keys need remapping (K = total keys, N = nodes) — essential for distributed caches, databases, and CDNs.

### [`dining_philosophers.ml`](dining_philosophers.ml) — Concurrency Patterns

**Concepts:** deadlock avoidance, resource ordering, mutual exclusion, classical concurrency problems

The classic dining philosophers problem demonstrating deadlock conditions and solutions. Shows how resource ordering or asymmetric strategies prevent circular wait.

**Key takeaway:** Concurrency bugs arise from the interaction of correct components. The dining philosophers problem illustrates why reasoning about concurrent systems requires thinking about *all possible interleavings*.

---

## What's Next?

After working through these examples, try:

1. **Modify an example** — Add `find` to the BST, or make merge sort stable
2. **Write a new one** — Implement a stack, queue, or graph traversal
3. **Read the manual** — [OCaml.org docs](https://ocaml.org/docs) cover modules, functors, and the standard library
4. **Try Real World OCaml** — [dev.realworldocaml.org](https://dev.realworldocaml.org/) for production patterns

## Concept Index

| Concept | Files |
|---------|-------|
| Abstract interpretation | `abstract_interp.ml` |
| Actor model | `actor.ml` |
| Algebraic data types | `bst.ml`, `btree.ml`, `calculus.ml`, `crdt.ml`, `csv.ml`, `free_monad.ml`, `fsm.ml`, `gadts.ml`, `game_ai.ml`, `genetic.ml`, `heap.ml`, `huffman.ml`, `lambda.ml`, `lsystem.ml`, `parser.ml`, `peg.ml`, `persistent_vector.ml`, `regex.ml`, `sat_solver.ml`, `stm.ml`, `theorem_prover.ml`, `type_infer.ml`, `zipper.ml` |
| Algebraic effects | `effects.ml` |
| Automata & finite state machines | `automata.ml`, `cellular_automata.ml`, `fsm.ml`, `regex.ml` |
| Caching & eviction | `lru_cache.ml` |
| Calculus & differentiation | `autodiff.ml`, `calculus.ml`, `integration.ml` |
| Closures & encapsulation | `bytecode_vm.ml`, `fibonacci.ml`, `memoize.ml`, `parser.ml`, `regex.ml` |
| Comonads | `comonad.ml` |
| Compilers & interpreters | `abstract_interp.ml`, `bytecode_vm.ml`, `forth.ml`, `gadts.ml`, `lambda.ml`, `prolog.ml`, `turing_machine.ml` |
| Compression algorithms | `compression.ml`, `huffman.ml` |
| Computational geometry | `geometry.ml`, `kd_tree.ml`, `quadtree.ml` |
| Concurrency & parallelism | `actor.ml`, `csp.ml`, `deque.ml`, `dining_philosophers.ml`, `petri_net.ml`, `stm.ml` |
| Constraint satisfaction | `constraint.ml`, `csp.ml`, `dancing_links.ml` |
| Continuations & CPS | `delimited_cont.ml`, `effects.ml`, `free_monad.ml`, `peg.ml` |
| CRDTs (Conflict-free Replicated Data Types) | `crdt.ml` |
| Cryptography | `crypto.ml` |
| Data formats & serialization | `csv.ml`, `json.ml` |
| Diff algorithms | `diff.ml` |
| Distributed systems & consensus | `consistent_hashing.ml`, `crdt.ml`, `merkle_tree.ml`, `raft.ml` |
| Dynamic programming & memoization | `fibonacci.ml`, `game_ai.ml`, `memoize.ml`, `peg.ml`, `stream.ml` |
| Evolutionary algorithms | `genetic.ml` |
| Formal verification & model checking | `bdd.ml`, `model_checker.ml`, `sat_solver.ml` |
| Free monads | `free_monad.ml` |
| Functional reactive programming | `frp.ml` |
| GADTs (Generalized ADTs) | `gadts.ml` |
| Game AI & minimax | `game_ai.ml` |
| Garbage collection simulation | `gc_simulator.ml` |
| Generative art & simulation | `cellular_automata.ml`, `lsystem.ml`, `music.ml` |
| Graph algorithms (BFS, DFS, shortest path) | `astar.ml`, `dijkstra.ml`, `graph.ml`, `graph_db.ml`, `maze.ml`, `network_flow.ml` |
| Hash-based data structures | `bloom_filter.ml`, `cuckoo_filter.ml`, `hamt.ml`, `hashmap.ml` |
| Higher-order functions | `autodiff.ml`, `calculus.ml`, `csv.ml`, `game_ai.ml`, `genetic.ml`, `lsystem.ml`, `matrix.ml`, `mergesort.ml`, `parser.ml`, `quickcheck.ml`, `signal_processing.ml`, `sorting.ml`, `stream.ml`, `trie.ml` |
| Incremental computation | `incremental.ml` |
| Lambda calculus | `lambda.ml` |
| Lazy evaluation & streams | `quickcheck.ml`, `stream.ml` |
| Linear algebra & tensors | `matrix.ml`, `tensor.ml` |
| Logic programming | `datalog.ml`, `minikanren.ml`, `prolog.ml`, `relational.ml` |
| Linear programming & optimization | `simplex.ml` |
| Logic circuits | `logic_circuit.ml` |
| Machine learning & neural networks | `autodiff.ml`, `neural_network.ml` |
| Modules & functors | `comonad.ml`, `constraint.ml`, `effects.ml`, `fenwick_tree.ml`, `finger_tree.ml`, `game_ai.ml`, `genetic.ml`, `heap.ml`, `matrix.ml`, `memoize.ml`, `monad_transformers.ml`, `segment_tree.ml`, `trie.ml` |
| Monads & monad transformers | `delimited_cont.ml`, `frp.ml`, `monad_transformers.ml`, `parser.ml`, `probability.ml`, `quickcheck.ml`, `stm.ml` |
| Network flow algorithms | `network_flow.ml` |
| Numerical integration | `integration.ml` |
| Optics & lenses | `optics.ml` |
| Parsing & grammars | `csv.ml`, `earley.ml`, `json.ml`, `parser.ml`, `peg.ml`, `regex.ml` |
| Pattern matching | `bst.ml`, `calculus.ml`, `csv.ml`, `factor.ml`, `fsm.ml`, `hello.ml`, `list_last_elem.ml`, `parser.ml`, `sat_solver.ml`, `sorting.ml`, `string_match.ml`, `term_rewriting.ml`, `theorem_prover.ml`, `zipper.ml` |
| Persistent (immutable) data structures | `deque.ml`, `finger_tree.ml`, `hamt.ml`, `hashmap.ml`, `heap.ml`, `optics.ml`, `persistent_array.ml`, `persistent_vector.ml`, `queue.ml`, `random_access_list.ml`, `rbtree.ml`, `trie.ml`, `union_find.ml`, `zipper.ml` |
| Polymorphism (`'a`) | `bst.ml`, `btree.ml`, `csv.ml`, `diff.ml`, `dijkstra.ml`, `finger_tree.ml`, `hamt.ml`, `heap.ml`, `json.ml`, `mergesort.ml`, `monad_transformers.ml`, `parser.ml`, `persistent_vector.ml`, `quickcheck.ml`, `random_access_list.ml`, `rbtree.ml`, `skip_list.ml`, `stream.ml`, `type_infer.ml` |
| Probabilistic data structures | `bloom_filter.ml`, `count_min_sketch.ml`, `cuckoo_filter.ml`, `hyperloglog.ml`, `skip_list.ml` |
| Probability & statistics | `probability.ml` |
| Property-based testing | `quickcheck.ml` |
| Queues, deques & heaps | `binomial_heap.ml`, `deque.ml`, `fibonacci_heap.ml`, `heap.ml`, `leftist_heap.ml`, `pairing_heap.ml`, `queue.ml` |
| Polynomials & algebra | `polynomial.ml` |
| Range query structures | `fenwick_tree.ml`, `interval_tree.ml`, `segment_tree.ml`, `sparse_table.ml` |
| Ray tracing & graphics | `raytracer.ml` |
| Recursion & structural induction | `bst.ml`, `btree.ml`, `csv.ml`, `factor.ml`, `fibonacci.ml`, `finger_tree.ml`, `game_ai.ml`, `huffman.ml`, `json.ml`, `kd_tree.ml`, `list_last_elem.ml`, `lsystem.ml`, `mergesort.ml`, `parser.ml`, `peg.ml`, `regex.ml`, `sat_solver.ml`, `sorting.ml`, `tensor.ml`, `theorem_prover.ml`, `trie.ml`, `type_infer.ml`, `zipper.ml` |
| Signal processing & FFT | `signal_processing.ml` |
| Software transactional memory | `stm.ml` |
| Sorting algorithms | `mergesort.ml`, `sorting.ml` |
| String algorithms | `rope.ml`, `string_match.ml`, `succinct_bitvector.ml`, `suffix_array.ml`, `suffix_automaton.ml`, `suffix_tree.ml` |
| Tail recursion & accumulators | `csv.ml`, `fibonacci.ml`, `mergesort.ml`, `persistent_vector.ml`, `sorting.ml`, `trie.ml` |
| Term rewriting systems | `term_rewriting.ml` |
| Theorem proving & logic | `theorem_prover.ml` |
| Trees (BST, B-tree, red-black, etc.) | `aa_tree.ml`, `adaptive_radix_tree.ml`, `bplus_tree.ml`, `bst.ml`, `btree.ml`, `cartesian_tree.ml`, `euler_tour_tree.ml`, `fenwick_tree.ml`, `finger_tree.ml`, `huffman.ml`, `interval_tree.ml`, `kd_tree.ml`, `link_cut_tree.ml`, `order_statistics_tree.ml`, `radix_tree.ml`, `rbtree.ml`, `rope.ml`, `scapegoat_tree.ml`, `segment_tree.ml`, `splay_tree.ml`, `treap.ml`, `trie.ml`, `two_three_tree.ml`, `union_find.ml`, `van_emde_boas.ml`, `wavelet_tree.ml`, `weight_balanced_tree.ml`, `yfast_trie.ml`, `zip_tree.ml` |
| Type inference & type systems | `type_infer.ml` |
| Union-Find (disjoint sets) | `union_find.ml` |
| Zippers & cursor navigation | `zipper.ml` |
