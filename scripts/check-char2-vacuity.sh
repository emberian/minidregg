#!/usr/bin/env bash
# Fails when any declaration outside Selvage/CharTwoWall.lean quantifies over a
# carrier that is EMPTY at characteristic two.  Such a declaration compiles,
# passes its axiom pin, and proves nothing.
#
# Unlike the carrier census (which reports a count and gates only on its own
# self-test), this one gates on the FINDING: the honest number is zero and the
# tree is at zero today.
#
# usage: scripts/check-char2-vacuity.sh
set -euo pipefail

cd "$(dirname "$0")/.."

if ! output=$(lake env lean scripts/CharTwoVacuityCensus.lean 2>&1); then
  echo "$output" >&2
  echo "char2-vacuity: FAILED (see above)" >&2
  exit 1
fi

echo "$output"

if ! grep -q "^self-test *: PASS" <<<"$output"; then
  echo "char2-vacuity: self-test did not pass" >&2
  exit 1
fi

if ! grep -q "^CHAR-2 VACUOUS declarations : 0$" <<<"$output"; then
  echo "char2-vacuity: expected zero vacuous declarations" >&2
  exit 1
fi
