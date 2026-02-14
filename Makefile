# OCaml Sample Code - Makefile
# Build and run all example programs

OCAMLC = ocamlopt
SOURCES = a.ml b.ml factor.ml list_last_elem.ml bst.ml mergesort.ml
TARGETS = $(SOURCES:.ml=)

.PHONY: all clean run

all: $(TARGETS)

%: %.ml
	$(OCAMLC) -o $@ $<

run: all
	@echo "=== a ==="
	@./a
	@echo ""
	@echo "=== b ==="
	@./b
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

clean:
	rm -f $(TARGETS) *.cmi *.cmx *.cmo *.o
