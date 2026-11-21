#!/bin/sh
# The check: the prover's own tests (what it reads, refuses and proves of the classes written for
# them, and the audit refusing claims made to cheat); then gosh's proofs, run by this prover, where
# gosh is beside this project. Success prints "check: PASS". It refuses to start without what it
# needs (SE1/T2).
#
#     tools/check.sh          everything: what a merge is held to
#     tools/check.sh --lite   while working: the prover's own tests alone
#
# gosh's proofs stand in gosh, beside its classes, and gosh runs them by its tools/proofs.sh with
# its own copy of the prover (since 2026-11-21). Here the same proofs are run by this prover, so
# that a change to it is seen on gosh before gosh takes it. gosh is read, never changed: what the
# prover writes goes to build/gosh here.
set -e
cd "$(dirname "$0")/.."
MODE=heavy
for a in "$@"; do
    case "$a" in
        --lite) MODE=lite ;;
        *) echo "check: cannot start: $a is not --lite"; exit 2 ;;
    esac
done
LEAN_VERSION=4.36.0
: "${LEAN:=$PWD/.tools/lean-$LEAN_VERSION-linux/bin/lean}" "${PYTHON:=$PWD/.pixi/envs/default/bin/python}" "${GOSH:=$PWD/../gosh}"
export LEAN PYTHON
[ -x "$LEAN" ] || { echo "check: cannot start: no Lean at $LEAN (tools/lean.sh fetches it; or set LEAN)"; exit 2; }
case "$("$LEAN" --version)" in
    *"version $LEAN_VERSION,"*) ;;
    *) echo "check: cannot start: $LEAN is not Lean $LEAN_VERSION, the version pinned"; exit 2 ;;
esac
"$PYTHON" -c 'import clang.cindex' 2>/dev/null || { echo "check: cannot start: $PYTHON has no libclang (pixi install makes one; or set PYTHON)"; exit 2; }

# 1. The prover's own tests.
mkdir -p build
PATH="$(dirname "$LEAN"):$PATH" "$PYTHON" prover/test_prooc.py > build/prover-tests.log 2>&1 || { tail -n 20 build/prover-tests.log; echo "check: FAIL: the prover's own tests (log: build/prover-tests.log)"; exit 1; }
echo "prover: its own tests pass ($(grep -c . build/prover-tests.log) lines: build/prover-tests.log)"
if [ "$MODE" = lite ]; then
    echo "check: PASS (lite: the prover's own tests; NOT run: gosh's proofs by this prover. The whole check is tools/check.sh)"
    exit 0
fi

# 2. gosh's proofs, by this prover: every domain, the lint of all of gosh, and each broken.
[ -x "$GOSH/tools/proofs.sh" ] || { echo "check: cannot start: no gosh with tools/proofs.sh at $GOSH (set GOSH)"; exit 2; }
PROVER=$PWD/prover PROOFS_OUT=$PWD/build/gosh "$GOSH/tools/proofs.sh" || { echo "check: FAIL: gosh's proofs, by this prover"; exit 1; }
echo "check: PASS"
