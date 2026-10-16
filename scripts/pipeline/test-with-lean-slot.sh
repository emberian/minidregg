#!/usr/bin/env bash
# scripts/pipeline/test-with-lean-slot.sh -- with-lean-slot's queue on a scratch slot dir (Linux: flock, GNU touch).
# Seconds; builds nothing. Checks: grants follow enqueue order; at most N run at once; a waiter whose
# WITH_LEAN_SLOT_PIDFILE lives outside the queue is still served (the installed copy's starvation);
# a priority ticket passes ordinary ones; waits.tsv has one line per run.
set -uo pipefail
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
T=$(mktemp -d "${TMPDIR:-/tmp}/wls-test.XXXXXX"); trap 'rm -rf "$T"' EXIT
export PIPELINE_ROOT=$T PIPELINE_LEAN_SLOT_DIR=$T/slots PIPELINE_LEAN_SLOTS=2 LAKE_ARTIFACT_CACHE=false
mkdir -p "$T/slots"
job() { echo "start $1 $(date +%s.%N)" >> "$T/events"; sleep "$2"; echo "end $1 $(date +%s.%N)" >> "$T/events"; }
export -f job; export T
fail() { echo "test-with-lean-slot: FAIL: $*"; exit 1; }
# two holders, then five waiters enqueued one second apart (mtime resolution), one with an outside PID file
"$here/with-lean-slot" bash -c 'job h1 6' & "$here/with-lean-slot" bash -c 'job h2 6' &
sleep 1
for i in 1 2 3 4 5; do
  if [ "$i" = 3 ]; then WITH_LEAN_SLOT_PIDFILE=$T/outside.pid "$here/with-lean-slot" bash -c "job w$i 1" &
  else "$here/with-lean-slot" bash -c "job w$i 1" & fi
  sleep 1.1
done
WITH_LEAN_SLOT_PRIORITY=1 "$here/with-lean-slot" bash -c 'job p 1' &
wait
order=$(awk '$1=="start"{print $2}' "$T/events" | tr '\n' ' ')
case "$order" in "h1 h2 p w1 w2 w3 w4 w5 "|"h2 h1 p w1 w2 w3 w4 w5 ") ;; *) fail "grant order: $order" ;; esac
max=$(sort -k3 -n "$T/events" | awk '$1=="start"{n++; if(n>m)m=n} $1=="end"{n--} END{print m}')
[ "$max" -le 2 ] || fail "$max concurrent over 2 slots"
[ "$(wc -l < "$T/slots/waits.tsv")" = 8 ] || fail "waits.tsv has $(wc -l < "$T/slots/waits.tsv") lines, not 8"
echo "test-with-lean-slot: PASS (order: $order; max concurrent $max; waits.tsv 8 lines)"
