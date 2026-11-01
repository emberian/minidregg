#!/bin/sh
# Enrolment under a ticking clock: a retained plan is resumed while current, re-planned under the
# SAME request once the source has moved, and never planned twice for one name.
#
#   enrol-resume-acceptance.sh HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY
#
# On a fresh private Store (newparticipant-acceptance.sh) the sponsor plans the newcomer's
# enrollment; the clock ticks (`mini clock --action tick`, the real ticker) as the clock and
# certifier timers do on a box. Asserted:
#   1. `enroll plan` again, same --dir, no commit in between: the same custody (subject, keyId,
#      plan bytes), nothing planned (no new replanned/);
#   2. after a tick, `enroll plan` again, same --dir: the stale plan retires under replanned/NN and
#      the same request is planned again (same subject and keyId, new plan bytes);
#   3. `enroll plan` for the same name with ANOTHER --dir is refused naming the retained plan;
#   4. after a tick, `seal` of the retained plan is refused and points at `plan`; `plan` re-plans,
#      `seal` then signs; a tick before `submit` has the Host refuse with no record, on which
#      `plan` re-plans in place and seal + submit admit (or the Host admits at once: either way,
#      exactly one admission);
#   5. the admitted subject and keyId are the first plan's; the namespace holds one request record
#      and one binding for the name;
#   6. five members enrol back to back under a running ticker (the composed world's `enroll
#      member-1..5`, cut 4's red): plan, seal, submit each; a seal the consent provider refuses
#      because a tick landed points at `plan`, which re-plans the SAME request; five admissions, five
#      subjects, each the subject its first plan printed;
#   7. a pinned plan (`pin-enrollment-plan-height`) sealed after a tick and admitted after another: L1's
#      `pinHeaderAt` (92341df2) keeps the authored deadline and the consent provider re-derives the plan
#      at a later height within it. A Host without the pin, or older than 92341df2, fails this step.
# Steps 2 and 4 take the path the consent provider decides for a pinned plan after a tick (resumed and
# signed as it stands, or re-planned under the same request), each path with its own assertions.
# Every step leaves cmd/stdout/stderr/exit under ROOT/log (provisioning-acceptance.sh's shape).
set -eu
umask 077
[ "$#" -eq 5 ] || { echo "usage: $0 HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY" >&2; exit 2; }
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 ROOT=$5
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
command -v jq >/dev/null 2>&1 || { echo 'jq is required' >&2; exit 2; }
"$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$ROOT" >"$ROOT.bootstrap.stdout"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
mv "$ROOT.bootstrap.stdout" "$ROOT/bootstrap-handoff.stdout"
CONFIG="$ROOT/deployment/pinned-config.json"
SOCKET="$ROOT/public/mini.sock"
LOG="$ROOT/log"; mkdir -m 700 "$LOG"
printf 'step\texit\n' >"$ROOT/steps.tsv"
step() { # NAME EXPECT(ok|fail) COMMAND...
  name=$1 expect=$2; shift 2
  printf '%s\n' "$*" >"$LOG/$name.cmd"
  set +e; "$@" >"$LOG/$name.stdout" 2>"$LOG/$name.stderr"; code=$?; set -e
  printf '%s\n' "$code" >"$LOG/$name.exit"; printf '%s\t%s\n' "$name" "$code" >>"$ROOT/steps.tsv"
  if [ "$expect" = ok ] && [ "$code" -ne 0 ]; then echo "step $name failed ($code)" >&2; tail -20 "$LOG/$name.stderr" >&2; exit 1; fi
  if [ "$expect" = fail ] && [ "$code" -eq 0 ]; then echo "step $name unexpectedly succeeded" >&2; exit 1; fi
}
said() { grep -q "$2" "$LOG/$1.stderr" || { echo "step $1 did not say: $2" >&2; tail -3 "$LOG/$1.stderr" >&2; exit 1; }; }
# The fixture hands over its running server (ROOT/public/server.pid, the socket bound). This run uses
# that server and stops it by that PID file when it ends, however it ends. (Starting a second
# `mini serve` here overwrote the PID file and left the fixture's server running after every run.)
[ -s "$ROOT/public/server.pid" ] && kill -0 "$(cat "$ROOT/public/server.pid")" 2>/dev/null \
  || { echo 'the fixture handed over no running server (ROOT/public/server.pid)' >&2; exit 1; }
trap 'kill -TERM "$(cat "$ROOT/public/server.pid")" 2>/dev/null || true' EXIT
waited=0; until [ -S "$SOCKET" ]; do waited=$((waited + 1)); [ "$waited" -lt 1200 ] || { echo 'socket did not appear' >&2; exit 1; }; sleep 0.1; done
# A tick asserts the wall clock's second; the Host refuses one that does not advance past the last
# tick's (ClockTickReceiver.decideTick: clockNotAdvancing, no record). Every tick here, and step 6's
# ticker, therefore waits for a second later than the last tick's (`$ROOT/last-tick`), so two ticks
# never share a second and each is a commit.
next_second() {
  last=$(cat "$ROOT/last-tick" 2>/dev/null || echo 0)
  while [ "$(date +%s)" -le "$last" ]; do sleep 0.1; done
}
tick() {
  next_second
  step "$1" ok "$MINI" clock --action tick --workspace "$ROOT/clock"
  date +%s >"$ROOT/last-tick"
}
# A confirmed tick's commit: the clock's accepted count, the second it asserted, the world root after it.
tick_commit() { jq -er 'select(.type == "confirmed") | "\(.acceptedCount) \(.asserted.now) \(.worldRoot)"' "$LOG/$1.stdout"; }
NS=$(jq -r .namespaceRoot "$ROOT/sponsor/workspace.json")
A="$ROOT/attempts/newcomer"
plan() { step "$1" "$2" "$MINI" enroll --action plan --sponsor-workspace "$ROOT/sponsor" --factory-ref factory \
  --name newcomer --new-key "$ROOT/newcomer.key" --dir "$3"; }
plan_sha() { sha256sum "$A/plan.bin" | cut -d' ' -f1; }
same_identity() { [ "$(jq -er .subject "$LOG/$1.stdout")" = "$SUBJECT" ] && [ "$(jq -er .keyId "$LOG/$1.stdout")" = "$KEYID" ]; }

plan plan-1 ok "$A"
SUBJECT=$(jq -er .subject "$LOG/plan-1.stdout"); KEYID=$(jq -er .keyId "$LOG/plan-1.stdout")
P1=$(plan_sha)
PINNED=$(jq -r '.pinnedAtHeight // empty' "$A/pin.json")
# 1. resumption: nothing moved, nothing planned again
plan plan-resume ok "$A"
same_identity plan-resume; [ "$(plan_sha)" = "$P1" ]; [ ! -e "$A/replanned" ]
said plan-resume 'a validated plan is retained'
# 2. after a tick: an unpinned plan is stale and re-planned under the same request; a pinned one is
#    the Host's plan pinned at the same height again, so it is resumed
tick tick-1
plan plan-after-tick ok "$A"
same_identity plan-after-tick
if [ -n "$PINNED" ] && [ ! -e "$A/replanned" ]; then
  [ "$(plan_sha)" = "$P1" ]
  said plan-after-tick 'a validated plan is retained'
else
  [ "$(plan_sha)" != "$P1" ]; [ -s "$A/replanned/01/plan.bin" ]
  said plan-after-tick 'the retained plan is stale against the moved source'
  [ "$(ls "$NS" | grep -c '^released-')" = 1 ]
fi
# 3. another --dir for the same name is refused, naming the retained plan
plan plan-elsewhere fail "$ROOT/attempts/newcomer-again"
said plan-elsewhere "already planned at $A"
[ ! -e "$ROOT/attempts/newcomer-again/pin.json" ]
# 4. a tick before seal: an unpinned plan is refused by the consent provider, which points at plan; a
#    pinned one is signed as it stands (the consent provider re-derives it at the observation's height)
tick tick-2
set +e; "$MINI" enroll --action seal --dir "$A" >"$LOG/seal-1.stdout" 2>"$LOG/seal-1.stderr"; code=$?; set -e
printf 'seal-1\t%s\n' "$code" >>"$ROOT/steps.tsv"
if [ "$code" -ne 0 ]; then
  said seal-1 'plans the same request again'
  before=$(ls "$A/replanned" 2>/dev/null | wc -l | tr -d ' ')
  plan plan-2 ok "$A"
  same_identity plan-2; [ "$(ls "$A/replanned" | wc -l | tr -d ' ')" = $((before + 1)) ]
  step seal-2 ok "$MINI" enroll --action seal --dir "$A"
else
  [ -n "$PINNED" ] || { echo "an unpinned plan was sealed across a tick" >&2; exit 1; }
fi
tick tick-3
set +e; "$MINI" enroll --action submit --dir "$A" >"$LOG/submit-1.stdout" 2>"$LOG/submit-1.stderr"; code=$?; set -e
printf '%s\n' "$code" >"$LOG/submit-1.exit"; printf 'submit-1\t%s\n' "$code" >>"$ROOT/steps.tsv"
if [ "$code" -ne 0 ]; then
  [ -s "$A/submit-refused.json" ] || { echo "submit refused without the no-record marker:" >&2; tail -5 "$LOG/submit-1.stderr" >&2; exit 1; }
  said submit-1 'refused by the Host with no record'
  step seal-refused fail "$MINI" enroll --action seal --dir "$A"
  said seal-refused 'plan again'
  plan plan-3 ok "$A"
  same_identity plan-3; [ -s "$(ls -d "$A"/replanned/* | tail -1)/submit-refused.json" ]
  step seal-3 ok "$MINI" enroll --action seal --dir "$A"
  step submit-3 ok "$MINI" enroll --action submit --dir "$A"
  PATH_TAKEN=submit-refused-no-record-then-replanned
else
  PATH_TAKEN=submit-admitted-across-the-tick
fi
# 5. one identity, one record, one binding
[ "$(jq -er .subject "$A/enrollment.json")" = "$SUBJECT" ]
[ "$(jq -er .keyId "$A/enrollment.json")" = "$KEYID" ]
[ "$(jq -er .authority "$A/enrollment.json")" = admitted-key-only ]
records=$(for f in "$NS"/request-*.json; do jq -r 'select(.request=="newcomer") | .request' "$f"; done | wc -l | tr -d ' ')
[ "$records" = 1 ] || { echo "namespace holds $records request records for newcomer" >&2; exit 1; }
bindings=$(ls "$NS" | grep -c '^binding-' || true)
[ "$bindings" = 1 ] || { echo "namespace holds $bindings bindings" >&2; exit 1; }
step lookup ok "$MINI" enroll --action lookup --dir "$A"
# 6. Five members back to back under a running ticker (a tick every 15 s, a box's one-minute ticker
#    compressed, racing the composed world's enrolments): a seal or submit refused because a tick landed
#    after the plan re-plans the same request (bounded at six); five admissions.
( while :; do
    next_second
    date +%s >"$ROOT/last-tick"
    "$MINI" clock --action tick --workspace "$ROOT/clock" >/dev/null 2>&1 &
    printf '%s\n' "$!" >"$ROOT/tick-child.pid"
    wait "$!" 2>/dev/null || true
    date +%s >"$ROOT/last-tick"
    sleep 15 &
    printf '%s\n' "$!" >"$ROOT/tick-sleep.pid"
    wait "$!" 2>/dev/null || true
  done ) &
printf '%s\n' "$!" >"$ROOT/ticker.pid"
trap 'kill -TERM "$(cat "$ROOT/ticker.pid" 2>/dev/null)" "$(cat "$ROOT/tick-sleep.pid" 2>/dev/null)" 2>/dev/null || true; kill -TERM "$(cat "$ROOT/public/server.pid")" 2>/dev/null || true' EXIT
for i in 1 2 3 4 5; do
  "$MINI" keygen --secret "$ROOT/member-$i.key" --public "$ROOT/member-$i.pub" >"$ROOT/member-$i-keygen.json"
  M="$ROOT/attempts/member-$i"
  mplan() { step "$1" ok "$MINI" enroll --action plan --sponsor-workspace "$ROOT/sponsor" --factory-ref factory \
    --name "member-$i" --new-key "$ROOT/member-$i.key" --dir "$M"; }
  mplan "member-$i-plan"
  first=$(jq -er .subject "$LOG/member-$i-plan.stdout")
  admitted=""
  for try in 1 2 3 4 5 6; do
    set +e; "$MINI" enroll --action seal --dir "$M" >"$LOG/member-$i-seal-$try.stdout" 2>"$LOG/member-$i-seal-$try.stderr"; code=$?; set -e
    printf 'member-%s-seal-%s\t%s\n' "$i" "$try" "$code" >>"$ROOT/steps.tsv"
    if [ "$code" -ne 0 ]; then
      said "member-$i-seal-$try" 'plan'
      mplan "member-$i-replan-$try"; [ "$(jq -er .subject "$LOG/member-$i-replan-$try.stdout")" = "$first" ]
      continue
    fi
    set +e; "$MINI" enroll --action submit --dir "$M" >"$LOG/member-$i-submit-$try.stdout" 2>"$LOG/member-$i-submit-$try.stderr"; code=$?; set -e
    printf 'member-%s-submit-%s\t%s\n' "$i" "$try" "$code" >>"$ROOT/steps.tsv"
    if [ "$code" -eq 0 ]; then admitted=1; break; fi
    [ -s "$M/submit-refused.json" ] || { echo "member-$i submit refused without the no-record marker" >&2; tail -5 "$LOG/member-$i-submit-$try.stderr" >&2; exit 1; }
    mplan "member-$i-after-refusal-$try"; [ "$(jq -er .subject "$LOG/member-$i-after-refusal-$try.stdout")" = "$first" ]
  done
  [ -n "$admitted" ] || { echo "member-$i was not admitted in six seals under the ticker" >&2; exit 1; }
  [ "$(jq -er .authority "$M/enrollment.json")" = admitted-key-only ]
  [ "$(jq -er .subject "$M/enrollment.json")" = "$first" ]
done
kill -TERM "$(cat "$ROOT/ticker.pid" 2>/dev/null)" "$(cat "$ROOT/tick-sleep.pid" 2>/dev/null)" 2>/dev/null || true
if [ -s "$ROOT/tick-child.pid" ]; then
  while kill -0 "$(cat "$ROOT/tick-child.pid")" 2>/dev/null; do sleep 0.05; done
fi
wait "$(cat "$ROOT/ticker.pid")" 2>/dev/null || true
date +%s >"$ROOT/last-tick"
members=$(for i in 1 2 3 4 5; do jq -er .subject "$ROOT/attempts/member-$i/enrollment.json"; done | sort -u | wc -l | tr -d ' ')
[ "$members" = 5 ] || { echo "five members admitted $members distinct subjects" >&2; exit 1; }
seals=$(grep -c '^member-.-seal-' "$ROOT/steps.tsv")
# 7. A pinned plan survives ticks: planned, a tick, sealed as it stands, a tick, admitted.
[ -n "$PINNED" ] || { echo "enrol-resume: FAIL the Host has no pin-enrollment-plan-height; a plan cannot survive a tick" >&2; exit 1; }
"$MINI" keygen --secret "$ROOT/second.key" --public "$ROOT/second.pub" >"$ROOT/second-keygen.json"
B="$ROOT/attempts/second"
step pinned-plan ok "$MINI" enroll --action plan --sponsor-workspace "$ROOT/sponsor" --factory-ref factory \
  --name second --new-key "$ROOT/second.key" --dir "$B"
[ -s "$B/plan-pinned.bin" ]; [ "$(jq -er .pinnedAtHeight "$B/pin.json")" = "$(jq -er .height "$B/observation/challenge.json")" ]
tick tick-4
step pinned-seal ok "$MINI" enroll --action seal --dir "$B"
tick tick-5
# the plan crossed two commits: both ticks confirmed, the clock's count and asserted second strictly
# rising, and two different world roots (each tick moved the log the plan was pinned under)
set -- $(tick_commit tick-4) $(tick_commit tick-5)
[ "$#" -eq 6 ] && [ "$4" -gt "$1" ] && [ "$5" -gt "$2" ] && [ "$3" != "$6" ] \
  || { echo "step 7: the two ticks are not two distinct commits: $*" >&2; exit 1; }
step pinned-submit ok "$MINI" enroll --action submit --dir "$B"
[ "$(jq -er .authority "$B/enrollment.json")" = admitted-key-only ]
[ "$(jq -er .subject "$B/enrollment.json")" = "$(jq -er .subject "$LOG/pinned-plan.stdout")" ]
[ ! -e "$B/replanned" ]
echo "enrol-resume: PASS ($PATH_TAKEN; pinned=${PINNED:+yes}; five members back to back under a 15 s ticker in $seals seals; pinned plan admitted across two ticks) subject=$SUBJECT keyId=$KEYID"
