# ---- Build stage ----
FROM ocaml/opam:ubuntu-24.04-ocaml-5.2 AS builder

# Switch to root to install system deps, then back to opam user
USER root
RUN apt-get update && apt-get install -y --no-install-recommends make && \
    rm -rf /var/lib/apt/lists/*
USER opam

WORKDIR /home/opam/app

# Copy source files
COPY --chown=opam:opam Makefile *.ml ./

# Build all programs with the native-code compiler
RUN make all

# ---- Runtime stage ----
FROM ubuntu:24.04 AS runtime

RUN apt-get update && \
    apt-get install -y --no-install-recommends ca-certificates && \
    rm -rf /var/lib/apt/lists/*

# Create a non-root user
RUN useradd --create-home --shell /bin/bash --no-log-init ocaml
USER ocaml
WORKDIR /home/ocaml

# Copy only the compiled native binaries (no source, no compiler)
# Binary names match the .ml source filenames defined in the Makefile
COPY --from=builder /home/opam/app/hello           ./bin/hello
COPY --from=builder /home/opam/app/fibonacci        ./bin/fibonacci
COPY --from=builder /home/opam/app/factor           ./bin/factor
COPY --from=builder /home/opam/app/list_last_elem   ./bin/list_last_elem
COPY --from=builder /home/opam/app/bst              ./bin/bst
COPY --from=builder /home/opam/app/mergesort        ./bin/mergesort

ENV PATH="/home/ocaml/bin:${PATH}"

# Health check — verify at least one binary is functional
HEALTHCHECK --interval=30s --timeout=5s --start-period=5s --retries=1 \
    CMD hello || exit 1

# Default: run all examples in sequence
CMD ["sh", "-c", "\
echo '=== hello ===' && hello && echo '' && \
echo '=== fibonacci ===' && fibonacci && echo '' && \
echo '=== factor ===' && factor && echo '' && \
echo '=== list_last_elem ===' && list_last_elem && echo '' && \
echo '=== bst ===' && bst && echo '' && \
echo '=== mergesort ===' && mergesort"]
