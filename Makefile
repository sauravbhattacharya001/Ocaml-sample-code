# OCaml Sample Code - Makefile
# Build and run all example programs

# Use the native-code compiler for best performance.
# Change to 'ocamlc' for bytecode if ocamlopt is unavailable.
OCAML = ocamlopt

# Sources that need no external packages
SOURCES_PLAIN = hello.ml fibonacci.ml factor.ml list_last_elem.ml bst.ml \
	mergesort.ml graph.ml dijkstra.ml heap.ml parser.ml trie.ml regex.ml \
	stream.ml rbtree.ml sorting.ml union_find.ml rope.ml btree.ml json.ml \
	matrix.ml huffman.ml queue.ml fenwick_tree.ml hashmap.ml \
	bloom_filter.ml interval_tree.ml lru_cache.ml segment_tree.ml \
	skip_list.ml suffix_array.ml calculus.ml type_infer.ml optics.ml \
	minikanren.ml effects.ml network_flow.ml peg.ml integration.ml \
	term_rewriting.ml abstract_interp.ml autodiff.ml automata.ml \
	bytecode_vm.ml crypto.ml csp.ml datalog.ml earley.ml frp.ml \
	fsm.ml gadts.ml game_ai.ml gc_simulator.ml geometry.ml lambda.ml \
	model_checker.ml probability.ml relational.ml sat_solver.ml \
	string_match.ml theorem_prover.ml diff.ml graph_db.ml zipper.ml \
	quickcheck.ml raft.ml incremental.ml hamt.ml \
	comonad.ml constraint.ml crdt.ml deque.ml finger_tree.ml \
	genetic.ml monad_transformers.ml persistent_vector.ml \
	random_access_list.ml raytracer.ml stm.ml delimited_cont.ml \
	neural_network.ml lsystem.ml cellular_automata.ml memoize.ml \
	signal_processing.ml spreadsheet.ml pairing_heap.ml \
	aa_tree.ml adaptive_radix_tree.ml astar.ml bdd.ml benchmark.ml \
	binomial_heap.ml bplus_tree.ml cartesian_tree.ml compression.ml \
	consistent_hashing.ml count_min_sketch.ml cuckoo_filter.ml \
	dancing_links.ml dining_philosophers.ml euler_tour_tree.ml \
	fibonacci_heap.ml forth.ml hyperloglog.ml \
	leftist_heap.ml link_cut_tree.ml logic_circuit.ml maze.ml \
	merkle_tree.ml mini_sql.ml music.ml order_statistics_tree.ml \
	persistent_array.ml petri_net.ml polynomial.ml prolog.ml \
	quadtree.ml radix_tree.ml ring_buffer.ml scapegoat_tree.ml \
	simplex.ml sparse_table.ml splay_tree.ml succinct_bitvector.ml \
	suffix_automaton.ml suffix_tree.ml treap.ml turing_machine.ml \
	two_three_tree.ml typeclass.ml van_emde_boas.ml wavelet_tree.ml \
	weight_balanced_tree.ml yfast_trie.ml zip_tree.ml process_calculus.ml \
	bandit.ml property_discovery.ml code_lineage.ml fuzzing_engine.ml \
	aho_corasick.ml z_algorithm.ml manacher.ml boyer_moore.ml kmp.ml rabin_karp.ml \
	bitap.ml sunday.ml gap_buffer.ml

# Sources that require ocamlfind + external packages
SOURCES_PKG = csv.ml free_monad.ml actor.ml kd_tree.ml tensor.ml http_server.ml
# csv.ml needs: ocamlfind ocamlopt -package str -linkpkg csv.ml -o csv
# free_monad.ml needs: ocamlfind ocamlopt -package str -linkpkg free_monad.ml -o free_monad
# actor.ml needs: ocamlfind ocamlopt -package unix -linkpkg actor.ml -o actor
# kd_tree.ml needs: ocamlfind ocamlopt -package alcotest -linkpkg kd_tree.ml -o kd_tree
# tensor.ml needs: ocamlfind ocamlopt -package alcotest -linkpkg tensor.ml -o tensor

SOURCES = $(SOURCES_PLAIN) $(SOURCES_PKG)
TARGETS_PLAIN = $(SOURCES_PLAIN:.ml=)
TARGETS_PKG = $(SOURCES_PKG:.ml=)
TARGETS = $(TARGETS_PLAIN) $(TARGETS_PKG)

.PHONY: all clean run test coverage coverage-html

all: $(TARGETS)

# Plain sources: no special flags
$(TARGETS_PLAIN): %: %.ml
	$(OCAML) -o $@ $<

# csv needs the str package via ocamlfind
csv: csv.ml
	ocamlfind $(OCAML) -package str -linkpkg $< -o $@

# free_monad needs the str package via ocamlfind
free_monad: free_monad.ml
	ocamlfind $(OCAML) -package str -linkpkg $< -o $@

# actor needs the unix package via ocamlfind
actor: actor.ml
	ocamlfind $(OCAML) -package unix -linkpkg $< -o $@

# http_server needs the unix package via ocamlfind
http_server: http_server.ml
	ocamlfind $(OCAML) -package unix -linkpkg $< -o $@

# kd_tree needs the alcotest package via ocamlfind
kd_tree: kd_tree.ml
	ocamlfind $(OCAML) -package alcotest -linkpkg $< -o $@

# tensor needs the alcotest package via ocamlfind
tensor: tensor.ml
	ocamlfind $(OCAML) -package alcotest -linkpkg $< -o $@

test: test_all
	@echo "=== Running tests ==="
	@./test_all

test_skip_list: skip_list.ml test_skip_list.ml
	$(OCAML) -o test_skip_list skip_list.ml test_skip_list.ml

test_graph_db: graph_db.ml test_graph_db.ml
	$(OCAML) -o test_graph_db graph_db.ml test_graph_db.ml

test_sat_solver: test_sat_solver.ml
	$(OCAML) -o test_sat_solver test_sat_solver.ml

# ----------------------------------------------------------------------
# Extended test discovery (resolves issue #103).
#
# `make test` above runs the unified `test_all` suite plus a few ad-hoc
# targets. The repo also ships ~40 dedicated `test_*.ml` files that were
# never wired into the build, so they could rot silently and never showed
# up in coverage.
#
# `make test-extended` discovers and runs ALL of them. Two flavors:
#
#   1. "Script" tests use `#use "...";;` toplevel directives, so they
#      must be loaded by the `ocaml` interpreter, not compiled. We detect
#      this with a simple grep at make time.
#
#   2. "Compiled" tests are self-contained `.ml` files (the test inlines
#      whatever module helpers it needs) and build with `ocamlopt`. A
#      couple of tests genuinely depend on the module under test
#      (e.g. `test_skip_list` opens `Skip_list.SkipList`); those keep
#      explicit, hand-wired rules above so they always link correctly.
#
# CI invokes `make test-extended` in a separate job so a regression in
# an extended suite does not block the fast `make test` lane.
# ----------------------------------------------------------------------

ALL_TEST_FILES := $(filter-out test_framework.ml test_all.ml, $(wildcard test_*.ml))
SCRIPT_TESTS   := $(shell grep -l -E '^[[:space:]]*#use[[:space:]]+"' $(ALL_TEST_FILES) 2>/dev/null)
COMPILED_TESTS := $(filter-out $(SCRIPT_TESTS), $(ALL_TEST_FILES))
COMPILED_TEST_BINS := $(COMPILED_TESTS:.ml=)

# Compiled tests share a generic build rule. `test_skip_list`, `test_csp`,
# `test_graph_db`, and `test_sat_solver` have explicit rules elsewhere
# (or above) because they need a paired module file or a custom name.
#
# Implementation note: we declare the rule with `%: %.ml` for compiled
# tests by listing them via static-pattern syntax so Make does not pick
# the broad rule for other targets.
$(filter-out test_skip_list test_csp test_graph_db test_sat_solver test_compression test_huffman, $(COMPILED_TEST_BINS)): %: %.ml
	$(OCAML) -o $@ $<

test_csp: csp.ml test_csp.ml
	$(OCAML) -o test_csp csp.ml test_csp.ml

test_compression: test_framework.ml compression.ml test_compression.ml
	$(OCAML) -o test_compression test_framework.ml compression.ml test_compression.ml

test_huffman: test_framework.ml huffman.ml test_huffman.ml
	ocamlfind $(OCAML) -package str -linkpkg test_framework.ml huffman.ml test_huffman.ml -o test_huffman

.PHONY: test-extended test-scripts test-compiled

test-extended: test test-compiled test-scripts
	@echo ""
	@echo "=== Extended test summary: $(words $(COMPILED_TEST_BINS)) compiled + $(words $(SCRIPT_TESTS)) script suites + test_all ==="

test-compiled: $(COMPILED_TEST_BINS)
	@echo ""
	@echo "=== Running compiled test binaries ($(words $(COMPILED_TEST_BINS)) suites) ==="
	@fail=0; for t in $(COMPILED_TEST_BINS); do \
		echo ""; echo "--- $$t ---"; \
		if ! ./$$t; then echo "FAIL: $$t"; fail=1; fi; \
	done; \
	exit $$fail

test-scripts:
	@echo ""
	@echo "=== Running script test suites ($(words $(SCRIPT_TESTS)) suites, via ocaml toplevel) ==="
	@fail=0; for t in $(SCRIPT_TESTS); do \
		echo ""; echo "--- $$t ---"; \
		if ! ocaml $$t; then echo "FAIL: $$t"; fail=1; fi; \
	done; \
	exit $$fail

run: all
	@for prog in $(TARGETS_PLAIN); do \
		echo "=== $$prog ===" ; \
		./$$prog ; \
		echo "" ; \
	done
	@echo "=== csv ==="
	@./csv
	@echo ""

# Coverage: build test suite with bisect_ppx instrumentation
# Requires: opam install bisect_ppx ocamlfind
coverage:
	@echo "=== Building with coverage instrumentation ==="
	ocamlfind ocamlopt -package bisect_ppx -linkpkg test_all.ml -o test_all_cov 2>/dev/null || \
	ocamlfind ocamlc -package bisect_ppx -linkpkg test_all.ml -o test_all_cov
	@echo "=== Running tests with coverage ==="
	BISECT_FILE=$$(pwd)/bisect ./test_all_cov
	@echo "=== Coverage summary ==="
	bisect-ppx-report summary

coverage-html: coverage
	bisect-ppx-report html -o _coverage
	@echo "Coverage report: _coverage/index.html"

clean:
	rm -f $(TARGETS) test_all test_all_cov test_skip_list test_graph_db test_sat_solver test_csp test_compression test_huffman $(COMPILED_TEST_BINS) *.cmi *.cmx *.cmo *.o bisect*.coverage
	rm -rf _coverage
