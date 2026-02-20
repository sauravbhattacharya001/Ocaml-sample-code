# OCaml Sample Code - Makefile
# Build and run all example programs

# Use the native-code compiler for best performance.
# Change to 'ocamlc' for bytecode if ocamlopt is unavailable.
OCAML = ocamlopt
SOURCES = hello.ml fibonacci.ml factor.ml list_last_elem.ml bst.ml mergesort.ml graph.ml heap.ml parser.ml trie.ml
TARGETS = $(SOURCES:.ml=)

.PHONY: all clean run test coverage coverage-html

all: $(TARGETS)

%: %.ml
	$(OCAML) -o $@ $<

test: test_all
	@echo "=== Running tests ==="
	@./test_all

run: all
	@echo "=== hello ==="
	@./hello
	@echo ""
	@echo "=== fibonacci ==="
	@./fibonacci
	@echo ""
	@echo "=== factor ==="
	@./factor
	@echo ""
	@echo "=== list_last_elem ==="
	@./list_last_elem
	@echo ""
	@echo "=== bst ==="
	@./bst
	@echo ""
	@echo "=== mergesort ==="
	@./mergesort
	@echo ""
	@echo "=== graph ==="
	@./graph
	@echo ""
	@echo "=== heap ==="
	@./heap
	@echo ""
	@echo "=== parser ==="
	@./parser
	@echo ""
	@echo "=== trie ==="
	@./trie

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
	rm -f $(TARGETS) test_all test_all_cov *.cmi *.cmx *.cmo *.o bisect*.coverage
	rm -rf _coverage
