# OCaml Sample Code - Makefile
# Build and run all example programs

# Use the native-code compiler for best performance.
# Change to 'ocamlc' for bytecode if ocamlopt is unavailable.
OCAML = ocamlopt
SOURCES = hello.ml fibonacci.ml factor.ml list_last_elem.ml bst.ml mergesort.ml graph.ml heap.ml
TARGETS = $(SOURCES:.ml=)

.PHONY: all clean run test

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

clean:
	rm -f $(TARGETS) test_all *.cmi *.cmx *.cmo *.o
