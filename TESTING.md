# Testing Guide — OCaml Sample Code

This document is the single source of truth for *how* the test suites in this repository are organized, *how* to run them locally, and *how* CI exercises them. If you're adding a new module or fixing a bug, start here.

It complements [`CONTRIBUTING.md`](CONTRIBUTING.md), which covers contribution workflow and style. For an end-to-end walkthrough of the project structure, see [`README.md`](README.md). For the curated learning order, see [`LEARNING_PATH.md`](LEARNING_PATH.md).

---

## Table of Contents

- [Two Codebases, Two Test Stacks](#two-codebases-two-test-stacks)
- [Test File Layout](#test-file-layout)
- [Quick Start](#quick-start)
- [OCaml Tests](#ocaml-tests)
  - [The Unified Suite (`test_all.ml`)](#the-unified-suite-test_allml)
  - [Per-module Suites (`test_*.ml`)](#per-module-suites-test_ml)
  - [Script vs Compiled Tests](#script-vs-compiled-tests)
  - [Running a Single Test](#running-a-single-test)
- [Docs / JavaScript Tests](#docs--javascript-tests)
- [Coverage](#coverage)
- [What CI Runs](#what-ci-runs)
- [Adding a New Test](#adding-a-new-test)
- [Pre-Push Checklist](#pre-push-checklist)
- [Troubleshooting](#troubleshooting)

---

## Two Codebases, Two Test Stacks

This repository ships **two independent codebases** and each has its own test stack. Knowing which one your change touches tells you which tests must be green before pushing.

| Codebase | Where | Language | Test runner | Build entry point |
|---|---|---|---|---|
| OCaml programs | `*.ml` at repo root | OCaml (4.14 + 5.x) | `make test` / `make test-extended` | `Makefile` |
| Interactive docs site | `docs/` | HTML / CSS / vanilla JS | `npm test` (Jest, jsdom) | `package.json` |

The two stacks are completely decoupled — you can change an `.ml` file without touching the docs site, and vice versa. CI runs both lanes on every push.

---

## Test File Layout

```
.
├── test_all.ml                 # unified OCaml suite (fast lane)
├── test_framework.ml           # shared assertion helpers used by some test_*.ml
├── test_<module>.ml            # ~40 per-module OCaml suites (extended lane)
├── tests/                      # standalone Node smoke scripts (NOT jest)
│                               #   run individually with: node tests/<file>.js
└── __tests__/                  # jest test files for the docs site
```

The Jest config in `jest.config.js` explicitly ignores `tests/` so the standalone Node scripts (some of which call `process.exit` at the top level) don't get picked up by `npm test`.

---

## Quick Start

```bash
# OCaml — fast lane, runs on every CI build
make test

# OCaml — full lane, runs every test_*.ml (compiled + script)
make test-extended

# Docs / JS — Jest suites in __tests__/
npm install
npm test

# Coverage report (OCaml, bisect_ppx)
make coverage           # text summary
make coverage-html      # _coverage/index.html
```

If you're on Windows without an OCaml toolchain, see [Troubleshooting](#troubleshooting) — the recommended path is WSL2 + opam, not native Windows builds.

---

## OCaml Tests

### The Unified Suite (`test_all.ml`)

`test_all.ml` is the **fast lane**: a single binary that exercises the core data structures and algorithms (~hundreds of assertions, runs in seconds). It is what `make test` builds and runs, and what the `build-and-test` CI job gates on. Treat it as the canonical "did I break the basics?" check.

When you add a new core data-structure module, the lightweight assertion-style sanity tests for it usually belong in `test_all.ml` so they run on every push. Larger property-based or scenario suites belong in a per-module `test_<module>.ml` file (see below).

### Per-module Suites (`test_*.ml`)

The repository also ships ~40 dedicated `test_<module>.ml` files — one per non-trivial module — that cover deeper invariants, scenarios, edge cases, and property-style tests that would bloat `test_all.ml`.

Historically these files were not wired into the build and could rot silently (see issue #103). They are now discovered automatically by the `test-extended` Makefile target and run in their own CI job. The pattern, in pseudocode:

```
ALL_TEST_FILES   = test_*.ml \ {test_framework.ml, test_all.ml}
SCRIPT_TESTS     = files that start with `#use "..."` toplevel directives
COMPILED_TESTS   = everything else
test-extended    = test  +  build & run COMPILED_TESTS  +  ocaml SCRIPT_TESTS
```

### Script vs Compiled Tests

Two flavors of per-module test coexist; the distinction matters because they're run differently:

| Flavor | How you tell | How it's run |
|---|---|---|
| **Compiled** | Self-contained `.ml` (inlines the module under test, or pairs with it via an explicit Makefile rule). | `ocamlopt -o test_x test_x.ml` then `./test_x` |
| **Script** | Starts with `#use "module.ml";;` toplevel directives. | `ocaml test_x.ml` (loaded by the OCaml interpreter) |

A handful of compiled tests need a paired module file or external packages — those have explicit Makefile rules:

- `test_skip_list` ↔ `skip_list.ml`
- `test_csp` ↔ `csp.ml`
- `test_graph_db` ↔ `graph_db.ml`
- `test_sat_solver` (self-contained)
- `test_compression` ↔ `test_framework.ml + compression.ml`
- `test_huffman` ↔ `test_framework.ml + huffman.ml` (links `str` via `ocamlfind`)

Everything else is built by the generic static-pattern rule in the `Makefile`.

### Running a Single Test

```bash
# Compiled per-module suite
make test_skip_list && ./test_skip_list

# Script-style per-module suite
ocaml test_some_module.ml

# Just the fast lane
make test
```

To iterate on a single module without rebuilding the world:

```bash
ocamlopt -o test_x test_x.ml && ./test_x
```

After iterating, run `make test` once before pushing to make sure you didn't break a neighbor.

---

## Docs / JavaScript Tests

The docs site (`docs/`) is plain HTML/CSS/JS — zero framework dependencies — and is tested with [Jest](https://jestjs.io/) using `jest-environment-jsdom`. Test files live in `__tests__/`.

```bash
npm install         # one-time; pins jest@30 and jest-environment-jsdom@30
npm test            # runs all __tests__/*.test.js
npm test -- ds-chooser     # filter by name
```

Important guard-rails baked into `jest.config.js`:

- `tests/` is in `testPathIgnorePatterns`. Files in `tests/` are standalone Node smoke scripts, not Jest specs — several call `process.exit(...)` and would crash a Jest run.
- `--no-coverage` is the default in `npm test` so the suite stays fast for local iteration. The Coverage workflow re-enables it for CI reporting.

When you add or change a docs page that has interactive behavior (form validation, chooser logic, quiz scoring, etc.), add a jsdom-based test under `__tests__/` that asserts the behavior end-to-end against the page's DOM and inline JS.

---

## Coverage

OCaml coverage uses [`bisect_ppx`](https://github.com/aantron/bisect_ppx).

```bash
opam install bisect_ppx ocamlfind
make coverage         # text summary printed at the end of the run
make coverage-html    # writes _coverage/index.html
```

The Coverage CI workflow (`.github/workflows/coverage.yml`) builds the same artifacts and publishes the report, including for the extended per-binary suites (each binary is given its own timeout so a runaway test does not poison the report). See the badge in `README.md` for the current line-coverage number.

---

## What CI Runs

Three OCaml jobs and several auxiliary jobs run on every push and PR. The OCaml lanes:

| Job | Matrix | Gate | Notes |
|---|---|---|---|
| `build-and-test` | `ocaml-compiler: 5.x, 4.14.x` | **Required** | Builds everything (`make all`), runs `make test`, runs `make run` as a smoke pass. |
| `extended-tests` | `5.x` only | Advisory (`continue-on-error: true`) | Runs `make test-extended` — every per-module suite. Flip to required once all extended suites are reliably green. |
| `lint` | `5.x` | Required when `.ocamlformat` exists | Skipped automatically if there's no config, so contributors aren't blocked by formatter drift. |

Auxiliary lanes: CodeQL, Coverage (bisect_ppx), Pages (deploys `docs/`), Docker, Release, opam publish, stale-bot, issue/PR labelers, welcome. See `.github/workflows/`.

Both `push` and `pull_request` lanes skip when only `*.md`, `docs/**`, `LICENSE`, `.gitignore`, or `.editorconfig` change — pure documentation changes don't burn CI minutes on the build matrix.

---

## Adding a New Test

For a new OCaml module `foo.ml`:

1. **Sanity tests** that should run on every push → add to `test_all.ml` near similar modules.
2. **Deep / scenario / property tests** → create `test_foo.ml`. The generic Makefile rule will pick it up automatically the next time `make test-extended` runs.
3. If `test_foo` needs to *link* against `foo.ml` (rather than inline the helpers it needs), add an explicit Makefile rule modeled on `test_skip_list` or `test_csp`.
4. If `test_foo` needs an opam package, link it via `ocamlfind` and model the rule on `test_huffman` (which pulls in `str`).
5. Run it locally: `make test_foo && ./test_foo`.
6. Run `make test` to make sure you didn't regress the fast lane.

For a new docs-site interaction:

1. Create `__tests__/<feature>.test.js`.
2. Set up the DOM via `document.body.innerHTML = ...` or by loading the page's HTML fixture.
3. Exercise the same JS the page uses (factor it out into a small CommonJS-style module if needed so Jest can `require()` it).
4. `npm test -- <feature>` to iterate.

Tests should be **deterministic** — no `Random.self_init`, no wall-clock dependencies, no network. Property-style tests should seed the PRNG.

---

## Pre-Push Checklist

Before `git push`, in order of fastest-to-slowest:

```bash
make test           # fast lane, must be green
npm test            # docs-site lane, must be green if you touched docs/, __tests__/, jest.config.js
make test-extended  # full lane, should be green; if not, note which suite was pre-existing red
make coverage       # only if you intentionally moved coverage
```

If a test was already red on `master` before your change, say so in the commit body (`pre-existing: test_x asserts X but the fix is out of scope here`) instead of pretending you fixed it. Future-you will thank present-you.

---

## Troubleshooting

**`make: ocamlopt: Command not found`**
Install opam and an OCaml switch:
```bash
opam init -y
opam switch create 5.x
eval $(opam env)
opam install ocamlfind alcotest bisect_ppx
```

**Windows native OCaml build fails**
Use WSL2 with Ubuntu and run the opam steps above. Native Windows OCaml is not exercised by CI.

**`ocamlfind: Package 'alcotest' not found`**
Some per-module tests pull in `alcotest`, `str`, or `unix` via `ocamlfind`. Run `opam install ocamlfind alcotest --yes` and `eval $(opam env)` once per shell.

**Jest collects something from `tests/` and crashes**
That should not happen — `jest.config.js` ignores `tests/`. If you renamed `jest.config.js` or moved a script into `__tests__/`, restore the ignore pattern or move the script back to `tests/`.

**A `test_*.ml` script test fails with `Cannot find file ...`**
Script tests use `#use "..."` and resolve paths relative to the working directory. Run them from the repo root, not from a subdirectory.

**Coverage report says 0% for a module you definitely tested**
`bisect_ppx` instruments code at compile time. If you ran `make test` *before* `make coverage`, the cached binaries aren't instrumented. Run `make clean && make coverage`.

---

If something here is wrong, out of date, or missing, open a PR — this file should track reality, not the other way around.
