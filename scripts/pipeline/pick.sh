#!/usr/bin/env bash
# pick.sh COMMIT... : cherry-pick onto HEAD (committer ember arlynx, unsigned). Conflicts only in
# GENERATED files (protocol/lean-build-surfaces.json, scripts/gates/host-closure.pin, ResearchWip.lean)
# take HEAD's copy (regenerate once at the end of the batch with regen-pins.sh); conflicts in umbrella
# import files (Kernel.lean Theory.lean Compiler.lean Host.lean Assurance.lean ObjectiveProofs.lean ...)
# go through union-imports.py. Anything else stops with the conflicted paths listed.
set -u
export GIT_COMMITTER_NAME="ember arlynx" GIT_COMMITTER_EMAIL=cmrx64@gmail.com
H=$(cd "$(dirname "$0")" && pwd)
gen='^(protocol/lean-build-surfaces\.json|scripts/gates/host-closure\.pin|ResearchWip\.lean)$'
for c in "$@"; do
  if git -c commit.gpgsign=false cherry-pick "$c" >/dev/null 2>&1; then echo "picked $c -> $(git rev-parse --short HEAD)"; continue; fi
  for f in $(git diff --name-only --diff-filter=U); do
    if [[ "$f" =~ $gen ]]; then git checkout --ours -- "$f" && git add "$f"
    elif [ "$f" = scripts/local-gates.sh ] && python3 "$H/gates-union.py" "$f" >/dev/null 2>&1; then git add "$f"
    elif [[ "$f" =~ ^[A-Za-z]+\.lean$ ]] && python3 "$H/union-imports.py" "$f" >/dev/null 2>&1; then git add "$f"
    fi
  done
  if [ -n "$(git diff --name-only --diff-filter=U)" ]; then echo "STOP at $c: $(git diff --name-only --diff-filter=U | tr '\n' ' ')"; exit 1; fi
  if git diff --cached --quiet; then git cherry-pick --skip >/dev/null 2>&1; echo "skipped $c (empty after resolution)"; continue; fi
  git -c commit.gpgsign=false -c core.editor=true cherry-pick --continue >/dev/null && echo "picked $c -> $(git rev-parse --short HEAD) (generated/import conflicts resolved)"
done
