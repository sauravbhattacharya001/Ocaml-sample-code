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
	neural_network.ml

# Sources that require ocamlfind + external packages
SOURCES_PKG = csv.ml free_monad.ml actor.ml
# csv.ml needs: ocamlfind ocamlopt -package str -linkpkg csv.ml -o csv
# free_monad.ml needs: ocamlfind ocamlopt -package str -linkpkg free_monad.ml -o free_monad
# actor.ml needs: ocamlfind ocamlopt -package unix -linkpkg actor.ml -o actor

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

test: test_all
	@echo "=== Running tests ==="
	@./test_all

test_skip_list: skip_list.ml test_skip_list.ml
	$(OCAML) -o test_skip_list skip_list.ml test_skip_list.ml

test_graph_db: graph_db.ml test_graph_db.ml
	$(OCAML) -o test_graph_db graph_db.ml test_graph_db.ml

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
	rm -f $(TARGETS) test_all test_all_cov test_skip_list test_graph_db *.cmi *.cmx *.cmo *.o bisect*.coverage
	rm -rf _coverage
