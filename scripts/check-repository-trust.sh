#!/usr/bin/env bash
# Composite repository trust gate.  The caller must first build `Minidregg` so
# the carrier census can import its complete environment.
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

bash scripts/check-proof-hygiene.sh
bash scripts/check-import-boundary.sh
bash scripts/check-carrier-census.sh "$@"
git diff --check
echo 'repository-trust: PASS'
