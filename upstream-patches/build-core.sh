#!/bin/sh
# Rebuild the mathematical core of upstream's compression section with the width
# (N+1)^6 replaced by (7N^2+8)N+1. Needs scripts/fetch-upstream.sh to have been run with
# lean/OAI/Computability added to the sparse checkout (git -C src sparse-checkout add
# lean/OAI/Computability). Downloads the Lean 4.34.1 toolchain and Mathlib with its cache
# (about 8 GB) into upstream-build/.
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/src/lean"
OUT="${1:-$ROOT/upstream-build}"
HERE="$ROOT/upstream-patches"
mkdir -p "$OUT"
while read -r m; do
  f="$(echo "$m" | tr . /).lean"
  mkdir -p "$OUT/$(dirname "$f")"
  cp "$SRC/$f" "$OUT/$f"
done < "$HERE/modules-core.txt"
cp "$SRC/lean-toolchain" "$OUT/"
cp "$HERE/lakefile.lean" "$OUT/"
cd "$OUT"
lake exe cache get
C=OAI.Optimization.LinearProgramming.Compression
TARGETS="$C.MinorAssignments $C.AdaptiveRequests $C.BitBudget $C.Offline"
lake build $TARGETS          # upstream, unchanged
patch -p1 < "$HERE/core-width.patch"
lake build $TARGETS          # with the smaller width
