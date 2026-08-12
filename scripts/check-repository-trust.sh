#!/usr/bin/env bash
# Composite repository trust gate.  The caller must first build `Minidregg` so
# the carrier census can import its complete environment.
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd -P)
if repo_root=$(git -C "$script_dir" rev-parse --show-toplevel 2>/dev/null); then
  in_git_worktree=true
else
  repo_root=$(cd "$script_dir/.." && pwd -P)
  in_git_worktree=false
fi
cd "$repo_root"

bash scripts/check-proof-hygiene.sh
bash scripts/check-import-boundary.sh
bash scripts/check-carrier-census.sh "$@"
if $in_git_worktree; then
  git diff --check
else
  echo 'repository-trust: archive source integrity is enforced by the evidence runner'
fi
echo 'repository-trust: PASS'
