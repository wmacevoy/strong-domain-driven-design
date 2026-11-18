#!/bin/sh
# The check: every domain proved, and every proof seen to fail when its model is broken.
# Success prints "check: PASS". It refuses to start without what it needs (SE1/T2).
set -e
cd "$(dirname "$0")/.."
LEAN_VERSION=4.36.0
: "${LEAN:=$PWD/.tools/lean-$LEAN_VERSION-linux/bin/lean}" "${PYTHON:=python3}" "${SUBJECT:=$PWD/../gosh}"
export LEAN PYTHON SUBJECT
[ -x "$LEAN" ] || { echo "check: cannot start: no Lean at $LEAN (CONTRIBUTING.md says how to get it; or set LEAN)"; exit 2; }
case "$("$LEAN" --version)" in
    *"version $LEAN_VERSION,"*) ;;
    *) echo "check: cannot start: $LEAN is not Lean $LEAN_VERSION, the version pinned"; exit 2 ;;
esac
"$PYTHON" -c 'import clang.cindex' 2>/dev/null || { echo "check: cannot start: $PYTHON has no libclang (set PYTHON to one that has: CONTRIBUTING.md)"; exit 2; }
[ -f oopc/cpp-proof-gen/prove.sh ] || { echo "check: cannot start: no oopc/ (git submodule update --init)"; exit 2; }

[ -f "$SUBJECT/src/meetup/registrations.h" ] || { echo "check: cannot start: gosh is not at $SUBJECT (set SUBJECT to its directory: its own text is what is read)"; exit 2; }
echo "check: gosh is read at $SUBJECT, commit $(git -C "$SUBJECT" rev-parse --short HEAD 2>/dev/null || echo unknown)$(git -C "$SUBJECT" diff --quiet 2>/dev/null || echo ', with changes not committed')"

# REQ1/DOM-1: each domain of gosh is proved. CounterWindow is read from gosh's own file; StunAnswer
# is still gosh's code written again (docs/QUEUE.md).
DOMAIN="$PWD/domains/gosh" oopc/cpp-proof-gen/prove.sh StunAnswer CounterWindow
# REQ1/RED-1: each proof fails when its model is broken.
"$PYTHON" tools/red-test.py
echo "check: PASS"
