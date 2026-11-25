#!/bin/sh
# Rebuild upstream's top-level theorems (strongly_polynomial_optimization and
# strongly_polynomial_feasibility, 1552 modules) with the width (N+1)^6 replaced by
# (7N^2+8)N+1. Needs scripts/fetch-upstream.sh to have been run and
#   git -C src sparse-checkout add lean/OAI/Computability
# Downloads the Lean 4.34.1 toolchain, Mathlib with its cache and the Hex lattice libraries
# (about 8 GB) into upstream-build/. The build takes on the order of half an hour.
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/src/lean"
OUT="${1:-$ROOT/upstream-build}"
HERE="$ROOT/upstream-patches"
mkdir -p "$OUT"
while read -r m; do
  [ -z "$m" ] && continue
  f="$(echo "$m" | tr . /).lean"
  mkdir -p "$OUT/$(dirname "$f")"
  cp "$SRC/$f" "$OUT/$f"
done < "$HERE/modules-top.txt"
cp "$SRC/lean-toolchain" "$OUT/"
cp "$HERE/lakefile-full.lean" "$OUT/lakefile.lean"
cd "$OUT"
lake update HexBareiss HexLLLMathlib
lake exe cache get
patch -p1 < "$HERE/full-width.patch"
# Optional second patch: lower the constants of upstream's price search
# (query bound x^1510 -> x^989). Applies on top of full-width.patch.
if [ "${CLOCK:-1}" = 1 ]; then patch -p1 < "$HERE/clock.patch"; fi
lake build OAI.Optimization.LinearProgramming.Optimization OAI.Optimization.LinearProgramming.Feasibility
