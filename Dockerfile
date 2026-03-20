FROM ubuntu:24.04

# Prevent interactive prompts
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    python3 \
    python3-pip \
    build-essential \
    libgmp-dev \
    bc \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Install Node.js 22 LTS
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get install -y nodejs \
    && rm -rf /var/lib/apt/lists/*

# Install Rust and cargo tools (wasmtime, wasm-tools)
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"
RUN cargo install wasmtime-cli wasm-tools

# Install lean-lsp-mcp dependencies
RUN pip install leanclient --break-system-packages

# Set up workspace
WORKDIR /workspace

# Copy project files
COPY lean-toolchain .
RUN elan toolchain install $(cat lean-toolchain)

COPY lakefile.lean .
COPY VerifiedJS.lean .

# Fetch Lean dependencies (cache this layer)
RUN lake update 2>&1 | tail -5

# Copy everything else
COPY . .

# Build
RUN lake build 2>&1 | tail -10

# Install pre-push hook
RUN mkdir -p .git/hooks && \
    echo '#!/bin/bash' > .git/hooks/pre-push && \
    echo './tests/run_tests.sh --fast || { echo "ERROR: regression detected. Fix before pushing."; exit 1; }' >> .git/hooks/pre-push && \
    echo './scripts/sorry_report.sh || { echo "ERROR: sorry threshold exceeded."; exit 1; }' >> .git/hooks/pre-push && \
    chmod +x .git/hooks/pre-push

# Default: agent harness
CMD ["bash"]
