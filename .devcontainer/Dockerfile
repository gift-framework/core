FROM mcr.microsoft.com/devcontainers/base:ubuntu

# Lean 4
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.14.0
ENV PATH="/root/.elan/bin:${PATH}"

# Coq
RUN apt-get update && apt-get install -y opam \
    && opam init --disable-sandboxing -y \
    && eval $(opam env) \
    && opam pin add coq 8.18.0 -y

ENV PATH="/root/.opam/default/bin:${PATH}"
