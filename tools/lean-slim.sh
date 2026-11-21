#!/bin/sh
# lean-slim.sh FROM TO: of the Lean release unpacked at FROM, what the prover uses, copied to TO:
# lean and leanchecker, the shared libraries they load, and the compiled libraries Init, Std and
# Lean (the audit imports Lean), without their editor indexes (.ilean). Left out: Lake, the static
# libraries, LLVM and clang, the sources. For the image (tools/image/Dockerfile), which then holds
# about two thirds of the release; that this is enough is shown by the check passing with it.
set -e
from=$1; to=$2
[ -x "$from/bin/lean" ] || { echo "lean-slim: no Lean at $from" >&2; exit 2; }
mkdir -p "$to/bin" "$to/lib/lean"
cp "$from/bin/lean" "$from/bin/leanchecker" "$to/bin/"
cp -P "$from"/lib/lean/*.so "$to/lib/lean/"
for m in Init Std Lean; do
    (cd "$from/lib/lean" && find "$m" "$m.olean"* "$m.ir"* -type f ! -name '*.ilean' 2>/dev/null) | while read -r f; do
        mkdir -p "$to/lib/lean/$(dirname "$f")"
        cp "$from/lib/lean/$f" "$to/lib/lean/$f"
    done
done
cp "$from/LICENSE" "$to/" 2>/dev/null || true
cp -r "$from/LICENSES" "$to/" 2>/dev/null || true
