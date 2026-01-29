FROM mcr.microsoft.com/devcontainers/base:ubuntu

# Lean 4
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.14.0
ENV PATH="/root/.elan/bin:${PATH}"
