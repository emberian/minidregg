#!/usr/bin/env bash
# The one gate. Every step must pass; there is no fallback and no skip flag.
#   1. proof hygiene: no bare `#print axioms`, no project `axiom`.
#   2. `lake build Minidregg`: the umbrella imports every library root
#      (Theory Kernel Pred Effects Compiler Selvage Assurance Host), so every
#      library module elaborates, every pinned axiom footprint is compared, and
#      every build-time `#eval` check runs.
#   3. emitted artifacts: the build re-writes descriptors, test vectors and
#      Rust glue from Lean (prover/testdata, prover/generated, ...). If the
#      build changed any tracked file, the committed copy had drifted from its
#      Lean source, and the gate fails. Compared against the tree as it stood
#      before the build, so local uncommitted edits do not trip it.
#   4. the build-closure census: every tracked library `.lean` module is
#      imported from Minidregg.
#   5. the journey (native/resource-client/journey.sh) when it exists on this
#      revision. It is required, not optional, once present.
set -euo pipefail
repo_root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo_root"
lake=${LAKE:-lake}

echo "== gate 1/5: proof hygiene"
bash scripts/check-proof-hygiene.sh

tree_before=$(git diff --binary | git hash-object --stdin)

echo "== gate 2/5: lake build Minidregg"
"$lake" build Minidregg

echo "== gate 3/5: the build changed no tracked file"
tree_after=$(git diff --binary | git hash-object --stdin)
if [[ "$tree_before" != "$tree_after" ]]; then
  git diff --stat
  echo "gate 3: the build rewrote tracked files; commit the Lean-emitted copies" >&2
  exit 1
fi

echo "== gate 4/5: every library module is rooted"
bash scripts/check-build-closure.sh

echo "== gate 5/5: journey"
if [[ -f native/resource-client/journey.sh ]]; then
  bash native/resource-client/journey.sh
else
  echo "journey: native/resource-client/journey.sh is not on this revision"
fi
echo "gates: PASS"
