#!/bin/sh
# Fetch the upstream preprint and its Lean development (github.com/openai/math, Apache-2.0)
# into src/ for reference. src/ is not tracked by this repository and nothing in formal/
# depends on it. The checkout is shallow, blobless and sparse, pinned to the upstream commit
# this work started from.
set -eu

REV=3344da59991ed94f9ba711217b29c1d760badfa6
DEST="${1:-$(cd "$(dirname "$0")/.." && pwd)/src}"

if [ -e "$DEST" ]; then
  echo "$DEST already exists; remove it to fetch again" >&2
  exit 1
fi

git init -q "$DEST"
git -C "$DEST" remote add origin https://github.com/openai/math.git
git -C "$DEST" config remote.origin.promisor true
git -C "$DEST" config remote.origin.partialclonefilter blob:none
git -C "$DEST" sparse-checkout set \
  preprints/Strongly-polynomial-linear-programming-November-24-2026 \
  lean/OAI/Optimization \
  lean/ComparatorChallenges \
  lean/docs \
  lean/patches
git -C "$DEST" fetch -q --depth 1 --filter=blob:none origin "$REV"
git -C "$DEST" checkout -q --detach FETCH_HEAD
echo "upstream checked out at $REV in $DEST"
