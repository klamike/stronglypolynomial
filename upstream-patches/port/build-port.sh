#!/bin/sh
# Build this repository's library (formal/SPLP) under upstream's toolchain (Lean 4.34.1) and
# Mathlib revision, together with upstream's own definition of the price-game query model
# (PriceGame/Model.lean, unchanged), and prove SPLPUpstream.exists_tree against it.
# Needs scripts/fetch-upstream.sh to have been run. Downloads the toolchain and Mathlib with
# its cache (about 8 GB) into upstream-build-port/ unless they are already there.
set -eu
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${1:-$ROOT/upstream-build-port}"
HERE="$ROOT/upstream-patches/port"
M=OAI/Optimization/LinearProgramming/PriceGame
mkdir -p "$OUT/$M" "$OUT/SPLPUpstream"
cp -R "$ROOT/formal/SPLP" "$ROOT/formal/SPLP.lean" "$OUT/"
cp "$ROOT/src/lean/$M/Model.lean" "$OUT/$M/"
cp "$HERE/SPLPUpstream/Tree.lean" "$OUT/SPLPUpstream/"
cp "$HERE/lakefile.lean" "$OUT/"
cp "$ROOT/src/lean/lean-toolchain" "$OUT/"
cd "$OUT"
lake exe cache get
lake build SPLP SPLPUpstream.Tree
