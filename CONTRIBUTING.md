# Contributing to OCaml Sample Code

Thanks for your interest in contributing! This repository is a curated collection of **128 self-contained OCaml programs** covering algorithms, data structures, compilers, concurrency, and more — plus **53 interactive learning tools** deployed on [GitHub Pages](https://sauravbhattacharya001.github.io/Ocaml-sample-code/).

## Table of Contents

- [Project Architecture](#project-architecture)
- [What Makes a Good Contribution](#what-makes-a-good-contribution)
- [Getting Started](#getting-started)
- [Development Workflow](#development-workflow)
- [Style Guide](#style-guide)
- [Adding Tests](#adding-tests)
- [Contributing Documentation](#contributing-documentation)
- [CI Pipeline](#ci-pipeline)
- [Reporting Issues](#reporting-issues)
- [Code of Conduct](#code-of-conduct)

## Project Architecture

```
Ocaml-sample-code/
├── *.ml                    # 128 self-contained OCaml programs
├── test_all.ml             # Unified test suite (unit tests for core modules)
├── test_*.ml               # Standalone test files for specific modules
├── Makefile                # Build system (all / test / coverage / clean)
├── ocaml-sample-code.opam  # Package metadata
├── package.json            # Jest tests for docs site JavaScript
├── docs/                   # 53 interactive HTML tools (GitHub Pages)
│   ├── index.html          # Landing page & program catalog
│   ├── explorer.html       # Algorithm visualizer
│   ├── quiz.html           # Interactive quiz system
│   ├── flashcards.html     # Concept flashcards
│   ├── cheat-sheet.html    # OCaml quick reference
│   ├── style.css           # Shared styles
│   └── ...                 # Per-topic interactive pages
├── tests/                  # Jest test suites for docs site
├── __tests__/              # Additional JS test files
├── .github/
│   ├── workflows/          # CI, CodeQL, coverage, Docker, Pages, releases
│   └── ISSUE_TEMPLATE/     # Bug report, example request, docs improvement
├── LEARNING_PATH.md        # Guided learning progression
└── Dockerfile              # Container build
```

### Two Codebases

This repo has two distinct contribution areas:

1. **OCaml programs** (`*.ml`) — compiled with `ocamlopt`, tested via `test_all.ml`, no external deps for most files
2. **Interactive docs** (`docs/`) — vanilla HTML/CSS/JS (zero framework dependencies), tested with Jest, deployed to GitHub Pages

## What Makes a Good Contribution

### New OCaml Examples

Each `.ml` file should:

- **Be self-contained** — compile and run independently with `ocamlopt -o name name.ml`
- **Focus on specific concepts** — don't try to cover everything in one file
- **Include inline comments** — explain what's happening and why, especially for non-obvious OCaml idioms
- **Show output** — include expected output in comments or print it in `let () = ...`
- **Use idiomatic OCaml** — pattern matching over if/else, immutable data by default, proper use of `option` types

### Ideas for New Examples

- **Data structures:** persistent arrays, amortized queues, Fibonacci heaps
- **Algorithms:** dynamic programming, topological sort, maximum bipartite matching
- **Language features:** modules & functors (advanced), first-class modules, extensible variants
- **Concurrency:** `Eio` basics, domain-level parallelism (OCaml 5.x multicore)
- **Compilers:** register allocation, SSA form, CPS transformation

### Improvements to Existing Code

- Bug fixes (with tests)
- Performance improvements with benchmarks
- Better documentation or clearer explanations
- Additional edge case handling
- Replacing imperative patterns with functional equivalents

### New Interactive Docs Pages

- Visualization of an algorithm not yet covered
- Interactive exercises for a concept
- Tool improvements (accessibility, mobile support, better explanations)

## Getting Started

### Prerequisites

- **OCaml 4.14+** (5.x preferred) — install via [opam](https://opam.ocaml.org/doc/Install.html)
- **Make** — for building and testing OCaml code
- **Node.js 18+** — only needed for docs site testing

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

### Running Docs Tests

```bash
npm install
npm test             # Jest test suite for docs site
```

### Previewing Docs Locally

Open any file in `docs/` directly in your browser — they're all static HTML with no build step:

```bash
# macOS
open docs/index.html

# Linux
xdg-open docs/index.html

# Or use any local server
python3 -m http.server 8000 --directory docs
```

## Development Workflow

1. **Fork** the repository
2. **Create a feature branch** from `master`:
   ```bash
   git checkout -b add-fibonacci-heap
   ```
3. **Write your code** following the style guide below
4. **Add tests** — unit tests for OCaml code in `test_all.ml`, Jest tests for docs pages
5. **Update the Makefile** — if your `.ml` file needs external packages, add it to `SOURCES_PKG` with the appropriate `ocamlfind` build rule
6. **Verify** everything works:
   ```bash
   make all          # All OCaml programs compile
   make test         # OCaml tests pass
   npm test          # Docs tests pass (if you touched docs/)
   ```
7. **Commit** with a clear, conventional message:
   ```bash
   git commit -m "feat: add Fibonacci heap with decrease-key and merge"
   ```
8. **Push** and open a pull request

### Commit Message Format

Use [conventional commits](https://www.conventionalcommits.org/):

- `feat: add trie data structure` — new example or feature
- `fix: correct off-by-one in segment tree query` — bug fix
- `docs: add interactive B-tree visualizer` — docs/learning tools
- `test: add edge cases for LRU cache eviction` — test additions
- `refactor: simplify parser combinator chain` — code improvement

## Style Guide

### OCaml File Structure

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

### OCaml Conventions

- **Naming:** `snake_case` for functions and variables
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

### Docs Site Conventions

- **Zero dependencies** — vanilla HTML/CSS/JS only, no frameworks or CDNs
- **Shared styles** — use `style.css` for consistent look
- **Self-contained pages** — each HTML file works independently
- **Accessible** — use semantic HTML, ARIA labels, keyboard navigation where possible
- **Responsive** — pages should work on mobile and desktop

## Adding Tests

### OCaml Tests

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

### Docs Site Tests

Add Jest tests in `tests/` or `__tests__/`:

```javascript
// tests/my-page.test.js
const fs = require('fs');
const path = require('path');

describe('My Page', () => {
  let html;
  beforeAll(() => {
    html = fs.readFileSync(path.join(__dirname, '../docs/my-page.html'), 'utf8');
  });

  test('has required elements', () => {
    expect(html).toContain('<title>');
    // ...
  });
});
```

## CI Pipeline

Every push and PR triggers these workflows:

| Workflow | File | What It Does |
|----------|------|-------------|
| **CI** | `ci.yml` | Builds all 128 programs, runs OCaml + Jest tests |
| **Coverage** | `coverage.yml` | Bisect_ppx instrumented test run, uploads to Codecov |
| **CodeQL** | `codeql.yml` | Security scanning |
| **Docker** | `docker.yml` | Builds and pushes container image |
| **Pages** | `pages.yml` | Deploys `docs/` to GitHub Pages on merge to master |
| **Release** | `release.yml` | Creates releases on version tags |
| **Labeling** | `label.yml`, `pr-labeler.yml`, `issue-labeler.yml` | Auto-labels issues and PRs |
| **Stale** | `stale.yml` | Marks inactive issues/PRs |

Your PR must pass **CI** before merge. Coverage and CodeQL results appear as PR checks.

## Contributing Documentation

### Adding a New Interactive Page

1. Create `docs/your-topic.html` following existing pages as templates
2. Include the shared stylesheet: `<link rel="stylesheet" href="style.css">`
3. Add a link from `docs/index.html`
4. Add Jest tests in `tests/`
5. The page deploys automatically on merge

### Improving the Learning Path

The `LEARNING_PATH.md` file provides a guided progression through the examples. If you add a new example that fits into the learning sequence, update the path accordingly.

## Reporting Issues

Found a bug or have a suggestion? [Open an issue](https://github.com/sauravbhattacharya001/Ocaml-sample-code/issues/new/choose) using one of the templates:

- **Bug Report** — something doesn't compile or produces wrong output
- **Example Request** — suggest a new OCaml program to add
- **Docs Improvement** — suggest improvements to interactive tools

Include:
- **What** you found or want to change
- **Why** it matters (correctness, clarity, performance)
- **How** you'd fix it (if you have a suggestion)

## Code of Conduct

Be respectful and constructive. This is an educational project — questions and learning-oriented PRs are welcome.

## License

By contributing, you agree that your contributions will be licensed under the [MIT License](LICENSE).
