#!/bin/sh
# course/prove.sh NAME: prove the course's class NAME, whose files stand together in one folder of
# course/: NAME.hpp (the class), NAME.claims.lean (the proof of what is owed), and, if there are,
# NAME.proof.cpp (what is claimed, as a test that cannot be run) and NAME.proof-claims.lean.
# It puts them where the prover looks (build/course/NAME) and runs prover/prove.sh. The tools are
# this project's: tools/lean.sh and pixi install make them (or set LEAN and PYTHON).
set -e
cd "$(dirname "$0")/.."
name=${1:?course/prove.sh NAME: which class}
at=$(dirname "$(find course -name "$name.hpp" | head -n 1)")
[ -f "$at/$name.hpp" ] || { echo "course: no $name.hpp under course/"; exit 2; }
: "${LEAN:=$PWD/.tools/lean-4.36.0-linux/bin/lean}" "${PYTHON:=$PWD/.pixi/envs/default/bin/python}"
export LEAN PYTHON
W=$PWD/build/course/$name
rm -rf "$W/model" "$W/claims" "$W/proofs" && mkdir -p "$W/model" "$W/claims" "$W/proofs"
cp "$at"/*.hpp "$W/model/"
[ ! -f "$at/$name.claims.lean" ] || cp "$at/$name.claims.lean" "$W/claims/${name}Claims.lean"
[ ! -f "$at/$name.proof.cpp" ] || cp "$at/$name.proof.cpp" "$W/proofs/$name.proof.cpp"
[ ! -f "$at/$name.proof-claims.lean" ] || cp "$at/$name.proof-claims.lean" "$W/claims/${name}ProofClaims.lean"
DOMAIN=$W prover/prove.sh "$name"
