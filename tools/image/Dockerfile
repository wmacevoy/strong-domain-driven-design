# The prover's tools, as an image: Lean 4.36.0 (what the prover uses of it: tools/lean-slim.sh),
# a Python with libclang, a C++ compiler and git. A program's CI runs its proofs in it, so that
# nothing is fetched or installed for them on each run. Built from the repository's root:
#     docker build -f tools/image/Dockerfile .
# It is rebuilt only when the pins here or in tools/lean.sh change (.github/workflows/image.yml).
FROM ubuntu:24.04 AS lean
RUN apt-get update -q && apt-get install -y -q --no-install-recommends ca-certificates curl zstd \
    && rm -rf /var/lib/apt/lists/*
WORKDIR /src
COPY tools/lean.sh tools/lean-slim.sh tools/
# lean.sh fetches the release pinned and checks it against GitHub's digest for it
RUN tools/lean.sh && tools/lean-slim.sh .tools/lean-4.36.0-linux /opt/lean

FROM ubuntu:24.04
RUN apt-get update -q && apt-get install -y -q --no-install-recommends \
        ca-certificates git g++ make python3 python3-venv \
    && rm -rf /var/lib/apt/lists/*
# libclang, pinned: the version pixi.toml resolves to here (2026-11-21)
RUN python3 -m venv /opt/prover-python && /opt/prover-python/bin/pip install --no-cache-dir libclang==18.1.1
COPY --from=lean /opt/lean /opt/lean
ENV LEAN=/opt/lean/bin/lean PYTHON=/opt/prover-python/bin/python PATH=/opt/lean/bin:$PATH
RUN lean --version && "$PYTHON" -c 'import clang.cindex'
