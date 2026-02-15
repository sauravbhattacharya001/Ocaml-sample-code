# Contributing to OCaml Sample Code

Thanks for your interest in contributing! This repository is a curated collection of idiomatic OCaml programs — each self-contained, well-documented, and focused on specific language features or algorithms.

## What Makes a Good Contribution

### New Examples

Each `.ml` file should:

- **Be self-contained** — compile and run independently with `ocamlopt -o name name.ml`
- **Focus on specific concepts** — don't try to cover everything in one file
- **Include inline comments** — explain what's happening and why, especially for non-obvious OCaml idioms
- **Show output** — include expected output in comments or print it in `let () = ...`
- **Use idiomatic OCaml** — pattern matching over if/else, immutable data by default, proper use of `option` types

### Ideas for New Examples

- **Data structures:** red-black trees, tries, persistent arrays
- **Algorithms:** binary search, dynamic programming, Dijkstra's shortest path, A*
- **Language features:** modules & functors, GADTs, monads, phantom types, ppx
- **I/O:** file reading/writing, command-line parsing with `Arg`
- **Concurrency:** `Lwt` or `Eio` basics (these would need opam deps documented)

### Improvements to Existing Code

- Bug fixes (with tests)
- Performance improvements with benchmarks
- Better documentation or clearer explanations
- Additional edge case handling

## Getting Started

### Prerequisites

- **OCaml 4.14+** (5.x preferred) — install via [opam](https://opam.ocaml.org/doc/Install.html)
- **Make** — for building and testing

```bash
# Install OCaml via opam
opam init
opam switch create 5.2.1
eval $(opam env)

# Clone and build
git clone https://github.com/sauravbhattacharya001/Ocaml-sample-code.git
cd Ocaml-sample-code
make all
make test
```

### Running Coverage

```bash
opam install bisect_ppx ocamlfind
make coverage        # Summary
make coverage-html   # HTML report in _coverage/
```

## Workflow

1. **Fork** the repository
2. **Create a feature branch** from `master`:
   ```bash
   git checkout -b add-trie-example
   ```
3. **Write your code** following the style guide below
4. **Add tests** — if your example includes testable functions, add test cases to `test_all.ml`
5. **Verify** everything compiles and tests pass:
   ```bash
   make all
   make test
   ```
6. **Commit** with a clear message:
   ```bash
   git commit -m "Add trie data structure with insert/search/prefix operations"
   ```
7. **Push** and open a pull request

## Style Guide

### File Structure

```ocaml
(* program_name.ml — Brief description *)
(* Concepts: list the OCaml concepts demonstrated *)

(* === Type definitions === *)
type 'a my_type = ...

(* === Core functions === *)
let my_function x =
  (* Explain non-obvious logic *)
  ...

(* === Demo / Main === *)
let () =
  Printf.printf "=== Program Name ===\n";
  (* Show the functions in action *)
  ...
```

### Conventions

- **Naming:** `snake_case` for functions and variables (OCaml convention)
- **Types:** Use polymorphic types (`'a`) where it makes sense
- **Comments:** Explain the *why*, not just the *what*
- **Pattern matching:** Prefer `match`/`function` over nested `if`/`else`
- **Tail recursion:** Use accumulators for recursive functions that process large inputs
- **Error handling:** Use `option`/`result` types, not exceptions (unless demonstrating them)

### Don'ts

- No `open` at the top level (keeps examples self-contained and clear)
- No external dependencies unless the example specifically demonstrates a library
- No mutable state unless demonstrating imperative OCaml features
- No incomplete pattern matches (the compiler warns about these)

## Adding Tests

If your example has pure functions, add tests to `test_all.ml`:

```ocaml
(* Copy or reimplement your functions in test_all.ml *)
(* Then add a test function: *)

let test_my_feature () = suite "My Feature" (fun () ->
  assert_true ~msg:"basic case" (my_function 42 = expected);
  assert_equal ~msg:"edge case"
    (string_of_result expected_val)
    (string_of_result (my_function edge_input));
  assert_raises ~msg:"invalid input" (fun () -> my_function bad_input);
)

(* Register it in the main let () block *)
```

## Reporting Issues

Found a bug or have a suggestion? [Open an issue](https://github.com/sauravbhattacharya001/Ocaml-sample-code/issues/new/choose) with:

- **What** you found or want to change
- **Why** it matters (correctness, clarity, performance)
- **How** you'd fix it (if you have a suggestion)

## Code of Conduct

Be respectful and constructive. This is an educational project — questions and learning-oriented PRs are welcome.

## License

By contributing, you agree that your contributions will be licensed under the [MIT License](LICENSE).
