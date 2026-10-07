#!/usr/bin/env bash
# regen-pins.sh "REASON" : after a batch, regenerate build surfaces and (if the closure moved) the Host
# closure pin with REASON, and commit them as one merge-keeper commit. No-op when nothing changed.
# Every step's exit code counts (pipefail): a red re-check after --update stops the commit.
set -euo pipefail
export GIT_COMMITTER_NAME="ember arlynx" GIT_COMMITTER_EMAIL=cmrx64@gmail.com
if ! bash scripts/check-host-closure.sh >/dev/null 2>&1; then
  out=$(bash scripts/check-host-closure.sh --update "$1"); printf '%s\n' "$out" | tail -1
fi
python3 scripts/lean-build-surfaces.py generate >/dev/null
python3 scripts/lean-build-surfaces.py check
out=$(bash scripts/check-host-closure.sh); printf '%s\n' "$out" | tail -1
git add protocol/lean-build-surfaces.json scripts/gates/host-closure.pin ResearchWip.lean
if git diff --cached --quiet; then echo "regen-pins: nothing to commit"; exit 0; fi
printf 'gates: re-pin the Host closure and build surfaces for the batch (merge-keeper)\n\n%s\n\n`check-host-closure.sh --update` and `lean-build-surfaces.py generate` output only; the\nlanes'"'"' own regenerations were made against other bases. Nothing else re-emitted.\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' "$1" > "$(git rev-parse --git-dir)/REGEN_MSG"
git -c commit.gpgsign=false commit -q -F "$(git rev-parse --git-dir)/REGEN_MSG" && git log --oneline -1
