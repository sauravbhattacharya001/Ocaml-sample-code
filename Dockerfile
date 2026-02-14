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
RUN useradd --create-home --shell /bin/bash ocaml
USER ocaml
WORKDIR /home/ocaml

# Copy only the compiled native binaries (no source, no compiler)
COPY --from=builder /home/opam/app/a       ./bin/a
COPY --from=builder /home/opam/app/b       ./bin/b
COPY --from=builder /home/opam/app/factor  ./bin/factor
COPY --from=builder /home/opam/app/list_last_elem ./bin/list_last_elem
COPY --from=builder /home/opam/app/bst     ./bin/bst
COPY --from=builder /home/opam/app/mergesort ./bin/mergesort

ENV PATH="/home/ocaml/bin:${PATH}"

# Default: run all examples in sequence
CMD ["sh", "-c", "\
echo '=== a ===' && a && echo '' && \
echo '=== b ===' && b && echo '' && \
echo '=== factor ===' && factor && echo '' && \
echo '=== list_last_elem ===' && list_last_elem && echo '' && \
echo '=== bst ===' && bst && echo '' && \
echo '=== mergesort ===' && mergesort"]
