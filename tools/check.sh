#!/bin/sh
# The check: every domain proved, and every proof seen to fail when its model is broken.
# Success prints "check: PASS". It refuses to start without what it needs (SE1/T2).
set -e
cd "$(dirname "$0")/.."
LEAN_VERSION=4.36.0
: "${LEAN:=$PWD/.tools/lean-$LEAN_VERSION-linux/bin/lean}" "${PYTHON:=python3}" "${GOSH:=$PWD/../gosh}" "${GOSH_REF:=strong/main}"
export LEAN PYTHON
[ -x "$LEAN" ] || { echo "check: cannot start: no Lean at $LEAN (CONTRIBUTING.md says how to get it; or set LEAN)"; exit 2; }
case "$("$LEAN" --version)" in
    *"version $LEAN_VERSION,"*) ;;
    *) echo "check: cannot start: $LEAN is not Lean $LEAN_VERSION, the version pinned"; exit 2 ;;
esac
"$PYTHON" -c 'import clang.cindex' 2>/dev/null || { echo "check: cannot start: $PYTHON has no libclang (set PYTHON to one that has: CONTRIBUTING.md)"; exit 2; }
[ -f oopc/cpp-proof-gen/prove.sh ] || { echo "check: cannot start: no oopc/ (git submodule update --init)"; exit 2; }

# gosh is read as it is committed at GOSH_REF, a branch of the repository at GOSH: its files are put
# in .subject/, and nothing is written to gosh. What gosh's working tree holds does not matter.
SUBJECT_COMMIT=$(git -C "$GOSH" rev-parse --verify --quiet "$GOSH_REF^{commit}") || { echo "check: cannot start: no gosh at $GOSH with a branch $GOSH_REF (set GOSH and GOSH_REF: gosh's own text is what is read)"; exit 2; }
rm -rf .subject && mkdir .subject
git -C "$GOSH" archive "$SUBJECT_COMMIT" src | tar -x -C .subject
SUBJECT=$PWD/.subject
export SUBJECT SUBJECT_COMMIT
echo "check: gosh is read at $GOSH_REF, commit $(git -C "$GOSH" rev-parse --short "$SUBJECT_COMMIT")"

# REQ1/DOM-1: each domain of gosh is proved, from gosh's own files.
DOMAIN="$PWD/domains/gosh" oopc/cpp-proof-gen/prove.sh StunAnswer MeetupCounter CounterWindow is_stun_request
# REQ1/RED-1: each proof fails when its model is broken.
"$PYTHON" tools/red-test.py
echo "check: PASS"
