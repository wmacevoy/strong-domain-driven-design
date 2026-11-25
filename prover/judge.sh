#!/bin/sh
# judge.sh: does the prover still write, byte for byte, what it wrote? And do its rules still say
# what they said? It proves every class of the prover's own (model/, sample/), and then nothing
# under gen/ may differ from what is committed. Quick (about two minutes); the full judgment of a
# change is this, then test_prooc.py, then the project's tools/check.sh.
#     LEAN=... PYTHON=... sh prover/judge.sh
set -e
cd "$(dirname "$0")"
: "${LEAN:?set LEAN}" "${PYTHON:?set PYTHON}"
export LEAN PYTHON SUBJECT="$PWD/sample"
# (each class after what it uses)
sh prove.sh Gauge Tally Bits Zeros Score Board Shelf Percent Dial Histogram Checksum frame_begins bounded_of bounded_checked_of Tank fits Jar Water Tray Station > build/judge.log 2>&1 \
    || { tail -n 5 build/judge.log; echo "judge: FAIL: a class of the prover's own is no longer proved"; exit 1; }
changed=$(git status --porcelain -- gen)
[ -z "$changed" ] || { echo "$changed" | head -n 10; echo "judge: FAIL: what is generated differs from what is committed (git diff -- prover/gen)"; exit 1; }
echo "judge: ok: $(grep -c '^PROVED' build/judge.log) proved, and gen/ is as committed"
