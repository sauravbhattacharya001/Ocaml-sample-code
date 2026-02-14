# OCaml Sample Code - Makefile
# Build and run all example programs

OCAMLFIND = ocamlfind
OCAMLC = ocamlopt
SOURCES = a.ml b.ml factor.ml list_last_elem.ml bst.ml
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

clean:
	rm -f $(TARGETS) *.cmi *.cmx *.cmo *.o
