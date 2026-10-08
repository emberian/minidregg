#!/usr/bin/env bash
# Restore each old m4 driver expectation independently in temporary source.
# Usage: plant-drift-m4.sh NEW_RESULTS_ROOT
set -euo pipefail
[[ $# == 1 ]] || { echo "usage: $0 NEW_RESULTS_ROOT" >&2; exit 64; }
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
. "$HERE/plant-drift-lib.sh"
drift_setup m4 "$1"

drift_copy fields native/resource-client/shell-journey.sh
drift_replace 'create shared declared {"type":"all","predicates":[]} 2' \
  'create shared declared {"type":"all","predicates":[]}'
grep -Fx 'step J2 0 sponsor '\''create shared declared {"type":"all","predicates":[]}'\''' "$COPY/$DRIVER"
drift_red
grep -F 'm4 J4 submit first-action expected=0 got=3:' "$EVIDENCE/row.err"
grep -F 'Minidregg.Kernel.DeclaredResourceScalar.Reject.undeclaredField 2' "$EVIDENCE/log/38-J4-newcomer.stderr"
echo 'RED fields: m4 J4 submit first-action expected=0 got=3: undeclaredField 2'

drift_copy consent native/resource-client/shell-journey.sh
drift_replace 'step J5 1 stranger "read stolen"' 'step J5 3 stranger "read stolen"'
drift_replace 'step J5 1 stranger "invoke stranger-write stolen create 3 1"' \
  'step J5 3 stranger "invoke stranger-write stolen create 3 1"'
grep -Fx 'step J5 3 stranger "read stolen"' "$COPY/$DRIVER"
grep -Fx 'step J5 3 stranger "invoke stranger-write stolen create 3 1"' "$COPY/$DRIVER"
drift_red
grep -F 'm4 J5 read stolen expected=3 got=1: error: local consent refused before signing:' "$EVIDENCE/row.err"
for command in 'read stolen' 'invoke stranger-write stolen create 3 1'; do
  awk -F '\t' -v command="$command" \
    '$3=="stranger" && $4==command && $5==3 && $6==1 && $8=="FAIL" {red=1} END {exit !red}' \
    "$EVIDENCE/log/steps.tsv"
done
echo 'RED consent: m4 J5 read/write expected=3 got=1: local consent refused before signing'

drift_copy completion native/resource-client/shell-journey.sh
drift_replace "tty_step J4 newcomer \$'read\\tsh\\t\\rhis\\t\\rexit\\r'" \
  "tty_step J4 newcomer \$'rea\\tsh\\t\\rhis\\t\\rexit\\r'"
grep -Fx "tty_step J4 newcomer \$'rea\\tsh\\t\\rhis\\t\\rexit\\r'" "$COPY/$DRIVER"
drift_red
grep -F "m4 J4 tty: Tab completed 'read shared' and the Host answered field 2 = 1 expected=- got=-: check failed" "$EVIDENCE/row.err"
grep -aF 'usage: unknown verb reash; type help' "$EVIDENCE/log/42-J4-newcomer-tty.stdout"
echo 'RED completion: m4 J4 tty check failed: usage: unknown verb reash; type help'
