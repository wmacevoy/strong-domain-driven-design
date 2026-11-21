#!/bin/sh
# Fetches the Lean this project's prover is pinned to, into .tools/lean-VERSION-linux, once: the
# release from GitHub (about 600 MB, 3 GB unpacked; no Lean packages are needed), checked against
# the digest GitHub gives for it. Prints the path to its bin/lean. Linux, x86_64 or aarch64.
# Nothing is built: it is the release as it stands.
set -e
cd "$(dirname "$0")/.."
VERSION=4.36.0
case "$(uname -s)-$(uname -m)" in
    Linux-x86_64) asset=lean-$VERSION-linux.tar.zst; dir=lean-$VERSION-linux
        sha=2b7ab1ed8b92d2e6abfaf41344823b510064dbc9c0260cac73eb496ab2dea6eb ;;
    Linux-aarch64) asset=lean-$VERSION-linux_aarch64.tar.zst; dir=lean-$VERSION-linux_aarch64
        sha=35471998152191ef809418ce5bf61f8fc5f209e5e3be05b48bdc4949fdb3e726 ;;
    *) echo "lean: cannot start: no release of Lean $VERSION is pinned here for $(uname -s) $(uname -m)" >&2; exit 2 ;;
esac
if [ ! -x ".tools/$dir/bin/lean" ]; then
    mkdir -p .tools
    curl -fsSL -o ".tools/$asset" "https://github.com/leanprover/lean4/releases/download/v$VERSION/$asset"
    echo "$sha  .tools/$asset" | sha256sum -c --quiet - || { rm -f ".tools/$asset"; echo "lean: FAIL: .tools/$asset is not the release pinned" >&2; exit 1; }
    tar --zstd -x -f ".tools/$asset" -C .tools
    rm -f ".tools/$asset"
fi
echo "$PWD/.tools/$dir/bin/lean"
