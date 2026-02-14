<div align="center">

# 🐫 OCaml Sample Code

**A curated collection of idiomatic OCaml programs demonstrating core functional programming concepts**

[![OCaml](https://img.shields.io/badge/language-OCaml-EC6813?style=flat-square&logo=ocaml&logoColor=white)](https://ocaml.org/)
[![License: MIT](https://img.shields.io/github/license/sauravbhattacharya001/Ocaml-sample-code?style=flat-square&color=7aa2f7)](LICENSE)
[![GitHub Pages](https://img.shields.io/badge/docs-GitHub%20Pages-222?style=flat-square&logo=github)](https://sauravbhattacharya001.github.io/Ocaml-sample-code/)
[![GitHub stars](https://img.shields.io/github/stars/sauravbhattacharya001/Ocaml-sample-code?style=flat-square&color=e0af68)](https://github.com/sauravbhattacharya001/Ocaml-sample-code/stargazers)

[**Browse Examples**](#programs) · [**Documentation Site**](https://sauravbhattacharya001.github.io/Ocaml-sample-code/) · [**Getting Started**](#getting-started)

</div>

---

## About

This repository contains self-contained OCaml programs that each focus on a specific language feature or algorithm. Every file compiles and runs independently — perfect for learning OCaml by reading and modifying real code.

**Concepts covered:** recursion, pattern matching, algebraic data types, option types, higher-order functions, polymorphism, tail recursion, accumulators, tuple destructuring, input validation.

## Programs

| File | Description | Concepts |
|------|-------------|----------|
| [`a.ml`](a.ml) | Hello world — basic console output | `print_endline`, I/O |
| [`b.ml`](b.ml) | Second hello world example | Basic output |
| [`factor.ml`](factor.ml) | Prime factorization via optimized trial division | Recursion, mutual recursion, input validation |
| [`list_last_elem.ml`](list_last_elem.ml) | Find the last element of a list safely | Option types, pattern matching |
| [`bst.ml`](bst.ml) | Binary search tree (insert, delete, traversal, min/max, size, depth) | Algebraic data types, polymorphism, accumulators |
| [`mergesort.ml`](mergesort.ml) | Merge sort with custom comparators | Higher-order functions, tail recursion, tuple destructuring |

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
├── a.ml                  # Hello world
├── b.ml                  # Hello world (variation)
├── bst.ml                # Binary search tree
├── factor.ml             # Prime factorization
├── list_last_elem.ml     # Last element of a list
├── mergesort.ml          # Merge sort
├── Dockerfile            # Multi-stage Docker build
├── .dockerignore         # Docker build context exclusions
├── Makefile              # Build automation
├── docs/
│   └── index.html        # GitHub Pages documentation site
├── .github/
│   └── workflows/
│       └── pages.yml     # Pages deployment workflow
├── .editorconfig         # Editor formatting rules
├── .gitignore            # Build artifact exclusions
└── LICENSE               # MIT License
```

## Documentation

📖 **Interactive documentation site:** [sauravbhattacharya001.github.io/Ocaml-sample-code](https://sauravbhattacharya001.github.io/Ocaml-sample-code/)

The docs site features syntax-highlighted code samples with expected output for each program.

## Learning Resources

New to OCaml? These resources complement the examples in this repo:

- [**OCaml.org Tutorials**](https://ocaml.org/docs) — official guides and language manual
- [**Real World OCaml**](https://dev.realworldocaml.org/) — comprehensive free book
- [**99 Problems in OCaml**](https://ocaml.org/exercises) — practice problems by difficulty
- [**OCaml Playground**](https://ocaml.org/play) — try OCaml in the browser

## Contributing

Contributions are welcome! Ideas for new examples:

- **Data structures:** hash tables, heaps, graphs
- **Algorithms:** binary search, BFS/DFS, dynamic programming
- **Language features:** modules, functors, GADTs, monads
- **I/O:** file reading, command-line parsing

To contribute:

1. Fork the repository
2. Create a feature branch (`git checkout -b add-heap-example`)
3. Write a self-contained `.ml` file with comments explaining the concepts
4. Include example output in comments or a `let () = ...` block
5. Test it compiles: `ocamlopt -o yourfile yourfile.ml`
6. Submit a pull request

## License

This project is licensed under the MIT License — see the [LICENSE](LICENSE) file for details.

---

<div align="center">

**Built by [Saurav Bhattacharya](https://github.com/sauravbhattacharya001)**

⭐ Star this repo if you found it useful!

</div>
