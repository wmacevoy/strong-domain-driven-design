#!/bin/sh
# The check: what is proved compiled, the program around it linted, every domain proved, and each
# of these seen to fail when gosh is broken.
# Success prints "check: PASS". It refuses to start without what it needs (SE1/T2).
#
#     tools/check.sh                      everything (--heavy): what CI and a merge are held to
#     tools/check.sh --lite [DOMAIN...]   while working: only these domains are proved and broken
#                                         (all of them, proved and not broken, if none is named);
#                                         the lint, which reads all of gosh, is not run
# --lite ends "check: PASS (lite ...)" and says what it left out: it is never the whole check.
set -e
cd "$(dirname "$0")/.."
MODE=heavy; ONLY=
for a in "$@"; do
    case "$a" in
        --lite) MODE=lite ;;
        --heavy) MODE=heavy ;;
        -*) echo "check: cannot start: $a is not --lite or --heavy"; exit 2 ;;
        *) ONLY="$ONLY $a" ;;
    esac
done
[ "$MODE" = lite ] || [ -z "$ONLY" ] || { echo "check: cannot start: a domain is named ($ONLY ), and that is for --lite: the whole check is of every domain"; exit 2; }
LEAN_VERSION=4.36.0
: "${LEAN:=$PWD/.tools/lean-$LEAN_VERSION-linux/bin/lean}" "${PYTHON:=python3}" "${GOSH:=$PWD/../gosh}" "${GOSH_REF:=strong/main}"
export LEAN PYTHON
[ -x "$LEAN" ] || { echo "check: cannot start: no Lean at $LEAN (CONTRIBUTING.md says how to get it; or set LEAN)"; exit 2; }
case "$("$LEAN" --version)" in
    *"version $LEAN_VERSION,"*) ;;
    *) echo "check: cannot start: $LEAN is not Lean $LEAN_VERSION, the version pinned"; exit 2 ;;
esac
"$PYTHON" -c 'import clang.cindex' 2>/dev/null || { echo "check: cannot start: $PYTHON has no libclang (set PYTHON to one that has: CONTRIBUTING.md)"; exit 2; }
CORE=$GOSH/.build/core
[ -f "$CORE/src/include/config.h" ] || { echo "check: cannot start: gosh at $GOSH has not been built (tools/build.sh there): the lint reads every file, and they include mosh's core and its config.h"; exit 2; }
[ -f prover/prove.sh ] || { echo "check: cannot start: no prover/ (it is part of this repository)"; exit 2; }

# gosh is read as it is committed at GOSH_REF, a branch of the repository at GOSH: its files are put
# in .subject/, and nothing is written to gosh. What gosh's working tree holds does not matter.
SUBJECT_COMMIT=$(git -C "$GOSH" rev-parse --verify --quiet "$GOSH_REF^{commit}") || { echo "check: cannot start: no gosh at $GOSH with a branch $GOSH_REF (set GOSH and GOSH_REF: gosh's own text is what is read)"; exit 2; }
rm -rf .subject && mkdir .subject
git -C "$GOSH" archive "$SUBJECT_COMMIT" src | tar -x -C .subject
rm -rf .subject-include && mkdir .subject-include
git -C "$GOSH" archive "$SUBJECT_COMMIT" vendor | tar -x -C .subject-include
SUBJECT=$PWD/.subject
export SUBJECT SUBJECT_COMMIT
echo "check: gosh is read at $GOSH_REF, commit $(git -C "$GOSH" rev-parse --short "$SUBJECT_COMMIT")"

# The full compile of what is proved has three steps, in this order: the C++ compiler, the lint,
# the prover. Each refuses the program; the later ones rest on the earlier.
DOMAINS="StunAnswer bounded_of bounded_checked_of CounterWindow is_stun_request_checked MeetupHeader MeetupNonce MeetupRegister"
STRONG=src/strong

# 1. compile. What is proved compiles alone, with every warning an error: by the usual compiler,
# which reads pre(...) as nothing, and by g++ 16, which compiles it as a contract. (All of gosh is
# compiled by gosh's own check, not here.)
: "${CXX:=c++}"
GXX16=$GOSH/tools/gcc16/.pixi/envs/default/bin/x86_64-conda-linux-gnu-g++
for f in "$SUBJECT/$STRONG"/*.h; do
    "$CXX" -std=gnu++17 -fsyntax-only -Wall -Wextra -Werror -I"$SUBJECT" -x c++ "$f" || { echo "check: compile: FAIL: $f ($CXX)"; exit 1; }
    if [ -x "$GXX16" ]; then
        "$GXX16" --sysroot=/ -isystem "/usr/include/$(cc -print-multiarch)" -std=c++26 -fcontracts -fsyntax-only -Wall -Wextra -Werror -I"$SUBJECT" -x c++ "$f" || { echo "check: compile: FAIL: $f (g++ 16, with contracts)"; exit 1; }
    fi
done
if [ -x "$GXX16" ]; then echo "compile: ok: $(ls "$SUBJECT/$STRONG"/*.h | wc -l) files under $STRONG, by $CXX and by g++ 16 with contracts"
else echo "compile: ok: $(ls "$SUBJECT/$STRONG"/*.h | wc -l) files under $STRONG, by $CXX alone: NOT by g++ 16, so no pre(...) was compiled as a contract (none at $GXX16: in gosh, . tools/gcc16.sh fetches it)"; fi

# 2. lint. What a proof takes as given of the program around it, looked for in the program, so
# that a proof has only its own class to answer for. First each class is read by the generator,
# which refuses what it cannot give an exact meaning (a field that is not private, a pointer kept,
# a global): that writes gen/, where the rules find what each class is.
READ_ONLY=1 DOMAIN="$PWD/domains/gosh" prover/prove.sh $DOMAINS
# REQ1/SHAPE-4: code that is not proved comes in only by what expects nothing of its caller: it makes
# no bounded number itself and calls nothing that says pre(...). Everything of gosh's src that is
# not one of the classes above is such code. And what is proved stands under src/strong, in the
# namespace Strong, with nothing beside it there that is not proved.
STRONG=$STRONG DOMAIN="$PWD/domains/gosh" "$PYTHON" prover/ingress.py $DOMAINS
# REQ1/SHAPE-4: and at a call of what is proved no two arguments are one thing, nothing starts a
# thread, and nothing outside reaches a proved value's bytes. This reads every file of gosh's src
# as Clang does, so it needs what they include: gosh's vendored headers (as committed), and mosh's
# core with its config.h, which only a build of gosh makes (.build/core in gosh's working tree).
LINT_INCLUDE="$PWD/.subject-include:$CORE:$CORE/src/include"; export LINT_INCLUDE
if [ "$MODE" = lite ]; then
    # --lite: the domains named, and what each is written with (its `uses` lines), in the order DOMAINS has them
    PROVE=$DOMAINS
    if [ -n "$ONLY" ]; then
        want=$ONLY
        for d in $ONLY; do
            [ -f "domains/gosh/from/$d" ] || { echo "check: cannot start: no domain $d (domains/gosh/from/ has: $DOMAINS)"; exit 2; }
            want="$want $(sed -n 's/^uses //p' "domains/gosh/from/$d" | tr '\n' ' ')"
        done
        PROVE=
        for d in $DOMAINS; do case " $want " in *" $d "*) PROVE="$PROVE $d" ;; esac; done
    fi
    DOMAIN="$PWD/domains/gosh" prover/prove.sh $PROVE
    if [ -n "$ONLY" ]; then RED_ONLY="$ONLY" "$PYTHON" tools/red-test.py; fi
    echo "check: PASS (lite: proved:$PROVE; NOT run: the lint of all of gosh$([ -n "$ONLY" ] && echo ", the other domains' proofs, the rules' red cases" || echo ", any red case"). The whole check is tools/check.sh)"
    exit 0
fi
STRONG=$STRONG INCLUDE="$LINT_INCLUDE" "$PYTHON" prover/lint.py

# 3. prove. REQ1/DOM-1: each domain of gosh is proved, from gosh's own files.
DOMAIN="$PWD/domains/gosh" prover/prove.sh $DOMAINS
# REQ1/RED-1: each proof fails when its model is broken, and each rule refuses a gosh that breaks it.
"$PYTHON" tools/red-test.py
echo "check: PASS"
