# OCaml Sample Code - Makefile
# Build and run all example programs

# Use the native-code compiler for best performance.
# Change to 'ocamlc' for bytecode if ocamlopt is unavailable.
OCAML = ocamlopt
SOURCES = hello.ml fibonacci.ml factor.ml list_last_elem.ml bst.ml mergesort.ml graph.ml
TARGETS = $(SOURCES:.ml=)

.PHONY: all clean run

all: $(TARGETS)

%: %.ml
	$(OCAML) -o $@ $<

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

clean:
	rm -f $(TARGETS) *.cmi *.cmx *.cmo *.o
