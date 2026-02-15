<div align="center">

# 🐫 OCaml Sample Code

**A curated collection of idiomatic OCaml programs demonstrating core functional programming concepts**

[![OCaml](https://img.shields.io/badge/language-OCaml-EC6813?style=flat-square&logo=ocaml&logoColor=white)](https://ocaml.org/)
[![License: MIT](https://img.shields.io/github/license/sauravbhattacharya001/Ocaml-sample-code?style=flat-square&color=7aa2f7)](LICENSE)
[![GitHub Pages](https://img.shields.io/badge/docs-GitHub%20Pages-222?style=flat-square&logo=github)](https://sauravbhattacharya001.github.io/Ocaml-sample-code/)
[![GitHub stars](https://img.shields.io/github/stars/sauravbhattacharya001/Ocaml-sample-code?style=flat-square&color=e0af68)](https://github.com/sauravbhattacharya001/Ocaml-sample-code/stargazers)
[![Coverage](https://img.shields.io/badge/coverage-bisect__ppx-brightgreen?style=flat-square&logo=ocaml)](https://github.com/sauravbhattacharya001/Ocaml-sample-code/actions/workflows/coverage.yml)

[**Browse Examples**](#programs) · [**Documentation Site**](https://sauravbhattacharya001.github.io/Ocaml-sample-code/) · [**Getting Started**](#getting-started)

</div>

---

## About

This repository contains self-contained OCaml programs that each focus on a specific language feature or algorithm. Every file compiles and runs independently — perfect for learning OCaml by reading and modifying real code.

**Concepts covered:** recursion, pattern matching, algebraic data types, option types, higher-order functions, polymorphism, tail recursion, accumulators, tuple destructuring, input validation, hash tables, memoization, closures, pipe operator, imperative features, modules (Map, Set, Queue), records, graph algorithms, persistent data structures, priority queues.

## Programs

| File | Description | Concepts |
|------|-------------|----------|
| [`hello.ml`](hello.ml) | Variables, types, pipes, and pattern matching | Let bindings, type inference, `Printf`, pipe operator |
| [`fibonacci.ml`](fibonacci.ml) | Fibonacci: naive vs memoized vs iterative | Hash tables, closures, imperative features, benchmarking |
| [`factor.ml`](factor.ml) | Prime factorization via optimized trial division | Recursion, mutual recursion, input validation |
| [`list_last_elem.ml`](list_last_elem.ml) | Find the last element of a list safely | Option types, pattern matching |
| [`bst.ml`](bst.ml) | Binary search tree (insert, delete, traversal, min/max, size, depth) | Algebraic data types, polymorphism, accumulators |
| [`mergesort.ml`](mergesort.ml) | Merge sort with custom comparators | Higher-order functions, tail recursion, tuple destructuring |
| [`graph.ml`](graph.ml) | Graph algorithms (BFS, DFS, topological sort, cycle detection) | Modules (Map, Set, Queue), records, imperative queues, variants |
| [`heap.ml`](heap.ml) | Priority queue — leftist min-heap (insert, merge, sort, top-k) | Persistent data structures, rank annotations, custom comparators |

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

### Last Element — `list_last_elem.ml`

Classic safe list traversal using `Option` — no exceptions, no crashes on empty lists.

```ocaml
let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t
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
├── graph.ml              # Graph algorithms (BFS, DFS, topological sort)
├── heap.ml               # Priority queue (leftist min-heap)
├── LEARNING_PATH.md          # Progressive learning guide
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

**Tested algorithms:** BST operations, prime factorization, Fibonacci (naive/memoized/iterative), merge sort, min/max heaps, list operations, graph algorithms (BFS, DFS, shortest path, cycle detection, topological sort, connected components).

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
