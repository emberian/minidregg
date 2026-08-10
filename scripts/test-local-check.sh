#!/usr/bin/env bash
# End-to-end regression for the local evidence runner.  It checks one immutable
# source snapshot successfully, then verifies that an otherwise-successful
# command which mutates archived source is rejected with exit 86.  The live
# worktree's README is hashed before and after as a sentinel against leakage.
if (( BASH_VERSINFO[0] < 5 )); then
  for minidregg_bash in /opt/homebrew/bin/bash /usr/local/bin/bash; do
    if [[ -x "$minidregg_bash" ]]; then
      exec "$minidregg_bash" "$0" "$@"
    fi
  done
  echo "test-local-check: Bash >= 5 is required (running $BASH_VERSION)" >&2
  exit 2
fi
set -euo pipefail

if [[ ${1:-} == --bash-bootstrap-only ]]; then
  printf 'bash=%s\n' "$BASH_VERSION"
  exit 0
fi

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"
runner=$repo_root/scripts/local-check.sh
[[ -x "$runner" ]] || {
  echo "test-local-check: $runner is not executable" >&2
  exit 2
}
bash_path=$(command -v bash)
[[ "$bash_path" == /* && -x "$bash_path" ]] || {
  echo "test-local-check: bash does not resolve to an absolute executable" >&2
  exit 2
}

revision=${1:-HEAD}
test_root=${MINIDREGG_LOCAL_TEST_ROOT:-$(mktemp -d "${TMPDIR:-/tmp}/minidregg-local-check-test.XXXXXXXX")}
check_root=${MINIDREGG_LOCAL_TEST_CHECK_ROOT:-$test_root/checks}
mkdir -p "$check_root" "$test_root/evidence"
test_root=$(cd "$test_root" && pwd -P)
check_root=$(cd "$check_root" && pwd -P)
readme_before=$(shasum -a 256 README.md | awk '{print $1}')

echo "test_root=$test_root"
echo "clean check: lake build Theory.CanonicalTransition"
MINIDREGG_LOCAL_CHECK_ROOT="$check_root" \
MINIDREGG_EVIDENCE_DIR="$test_root/evidence" \
  "$runner" "$revision" -- lake build Theory.CanonicalTransition

echo "adversarial check: successful command mutates archived README.md"
set +e
MINIDREGG_LOCAL_CHECK_ROOT="$check_root" \
MINIDREGG_EVIDENCE_DIR="$test_root/evidence" \
  "$runner" "$revision" -- "$bash_path" -c \
    'printf "\nlocal-check mutation sentinel\n" >> README.md'
mutation_status=$?
set -e
[[ "$mutation_status" -eq 86 ]] || {
  echo "test-local-check: expected mutation rejection 86, got $mutation_status" >&2
  exit 1
}

readme_after=$(shasum -a 256 README.md | awk '{print $1}')
[[ "$readme_before" == "$readme_after" ]] || {
  echo "test-local-check: live worktree README.md changed" >&2
  exit 1
}

mapfile -t envelopes < <(find "$test_root/evidence" -maxdepth 1 -type f -name '*.json' -print | LC_ALL=C sort)
[[ ${#envelopes[@]} -eq 2 ]] || {
  echo "test-local-check: expected two evidence envelopes, got ${#envelopes[@]}" >&2
  exit 1
}
jq -s -e 'map(select(.result.runnerExit == 0 and .result.commandExit == 0 and
  .result.sourceIntegrityExit == 0 and .result.dependencyIntegrityExit == 0 and
  .dependencies.runLocalTree == true and .dependencies.sharedInodes == false)) | length == 1' \
  "${envelopes[@]}" >/dev/null
jq -s -e 'map(select(.result.runnerExit == 86 and .result.commandExit == 0 and
  .result.sourceIntegrityExit == 1 and .result.dependencyIntegrityExit == 0)) | length == 1' \
  "${envelopes[@]}" >/dev/null

echo "PASS: clean committed-source run accepted"
echo "PASS: archived-source mutation rejected; live worktree unchanged"
printf 'evidence_dir=%s\n' "$test_root/evidence"
