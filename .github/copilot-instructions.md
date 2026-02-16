# Copilot Instructions for OCaml Sample Code

## Project Overview

This repository contains self-contained OCaml programs demonstrating core functional programming concepts. Each `.ml` file in the root directory is an independent program that compiles and runs on its own.

## Architecture

```
├── hello.ml           # Variables, types, pipes, pattern matching
├── fibonacci.ml       # Fibonacci: naive, memoized, iterative
├── factor.ml          # Prime factorization with memoization
├── list_last_elem.ml  # List operations and pattern matching
├── bst.ml             # Binary search tree (algebraic data types)
├── mergesort.ml       # Merge sort with polymorphic comparisons
├── graph.ml           # Graph algorithms (BFS, DFS, Dijkstra, topological sort)
├── heap.ml            # Min-heap / priority queue (persistent data structure)
├── test_all.ml        # Comprehensive test suite (assertion-based)
├── Makefile           # Build system
├── Dockerfile         # Multi-stage Docker build
└── docs/              # MkDocs documentation site
```

## Language & Toolchain

- **Language:** OCaml 5.x
- **Compiler:** `ocamlopt` (native-code compiler, preferred) or `ocamlc` (bytecode)
- **Build system:** GNU Make
- **Package manager:** opam
- **Test framework:** Custom assertion-based (no external dependencies for basic tests)
- **Coverage:** bisect_ppx + ocamlfind (optional, for coverage reporting)

## Building

```bash
# Build all programs
make all

# Build and run tests
make test

# Run all programs
make run

# Clean build artifacts
make clean
```

## Testing

Tests live in `test_all.ml`. The test framework is hand-rolled (no external deps needed):

```bash
# Build and run tests
make test
```

This compiles `test_all.ml` and runs it. Tests use simple assertions (`assert_equal`, `assert_true`, `assert_raises`) and print pass/fail results to stdout.

**Test coverage** (requires `bisect_ppx` and `ocamlfind`):
```bash
opam install bisect_ppx ocamlfind --yes
eval $(opam env)
make coverage
```

## Conventions

- **Each file is self-contained.** Every `.ml` file compiles independently with `ocamlopt -o name name.ml`.
- **Idiomatic OCaml.** Use pattern matching, algebraic data types, option types, tail recursion, and the pipe operator (`|>`) where appropriate.
- **No external dependencies** for the main programs. Only `test_all.ml` coverage needs `bisect_ppx`.
- **Functional style preferred.** Minimize mutation; use immutable data structures and recursion. Imperative features are acceptable for performance-critical sections (e.g., hash tables for memoization).
- **Consistent formatting.** 2-space indentation, descriptive variable names, comments explaining non-obvious logic.
- **Testing.** When adding a new program, add corresponding tests to `test_all.ml` and register the source file in the `Makefile`'s `SOURCES` variable.

## Adding a New Program

1. Create `your_program.ml` in the root directory.
2. Add it to `SOURCES` in the `Makefile`.
3. Add tests in `test_all.ml` (create a new `suite` block).
4. Update the README table with the program's description and concepts.
5. Verify: `make all && make test`

## Key OCaml Patterns Used

- **Algebraic data types:** `type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree`
- **Pattern matching:** Exhaustive matches with `match ... with`
- **Option types:** `None | Some x` for safe null handling
- **Tail recursion:** Use accumulators to avoid stack overflow
- **Higher-order functions:** `List.map`, `List.fold_left`, `List.filter`
- **Records:** `type point = { x: float; y: float }`
- **Modules:** `Map.Make`, `Set.Make`, `Queue`
- **Hash tables:** `Hashtbl.create`, `Hashtbl.find`, `Hashtbl.replace`

## CI/CD

- **Coverage workflow** (`.github/workflows/coverage.yml`): Builds with bisect_ppx instrumentation, runs tests, generates coverage reports.
- **Docker workflow** (`.github/workflows/docker.yml`): Builds multi-stage Docker image.
- **CodeQL** (`.github/workflows/codeql.yml`): Security scanning.
- **Pages** (`.github/workflows/pages.yml`): Deploys documentation site.
