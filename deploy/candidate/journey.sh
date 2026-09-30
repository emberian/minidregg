#!/usr/bin/env bash
# The bake-off journey (J0-J8) against a serving candidate Store.
#
# usage: journey.sh --state STATE_DIR --out NEW_DIR [--restart-command 'CMD']
#
# STATE_DIR is a Store made by `run.sh init` and serving (`run.sh start`, or a
# supervisor running `run.sh serve`). J6 restarts it: by default through
# `run.sh stop` + `run.sh start`; under a supervisor pass --restart-command
# (for example 'systemctl --user restart mini-store'). The journey enrolls two
# new participants, creates one resource and finally locks that resource with a
# deny-all law. Its records are permanent: run it against a Store made for it.
#
# Every step leaves NAME.cmd/.stdout/.stderr/.exit/.wall under NEW_DIR/steps.
# The table printed at the end is NEW_DIR/journey.tsv.
set -euo pipefail
CANDIDATE_PROG=journey.sh
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
# shellcheck source=deploy/candidate/lib.sh
. "$here/lib.sh"
candidate_require jq od tr awk date

state="" out="" restart_command=""
while [ $# -gt 0 ]; do
  case "$1" in
    --state) state=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    --restart-command) restart_command=$2; shift 2 ;;
    -h|--help) sed -n '2,16p' "$0"; exit 0 ;;
    *) candidate_die "unknown argument: $1" ;;
  esac
done
[ -n "$state" ] && [ -n "$out" ] || candidate_die "--state and --out are required"
candidate_state "$state"
J=$(candidate_abs "$out")
[ ! -e "$J" ] || candidate_die "refusing existing journey directory: $J"
umask 077
mkdir -p "$J/steps" "$J/keys" "$J/requests" "$J/attempts"
export TMPDIR=$STATE/tmp
tag=$(od -An -N4 -tx4 /dev/urandom | tr -d ' \n')
P=$STATE/genesis-params.json
SP=$STATE/sponsor
TSV=$J/journey.tsv
printf 'journey\tstep\texpect\texit\twall_s\tresult\tnote\n' >"$TSV"
declare -A verdict wall
current=""

begin() { current=$1; verdict[$current]=PASS; wall[$current]=0; }
fail() { verdict[$current]=FAIL; }
row() { printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$current" "$1" "$2" "$3" "$4" "$5" "$6" >>"$TSV"; }

# step NAME EXPECT(0|refuse) CMD...  -- refuse means any nonzero exit is the expected outcome
step() {
  local name=$1 expect=$2 rc start end seconds result note
  shift 2
  { printf '%q ' "$@"; echo; } >"$J/steps/$name.cmd"
  start=$(date +%s.%N)
  set +e
  "$@" >"$J/steps/$name.stdout" 2>"$J/steps/$name.stderr"
  rc=$?
  set -e
  end=$(date +%s.%N)
  seconds=$(awk -v a="$start" -v b="$end" 'BEGIN { printf "%.3f", b - a }')
  echo "$rc" >"$J/steps/$name.exit"
  echo "$seconds" >"$J/steps/$name.wall"
  wall[$current]=$(awk -v a="${wall[$current]}" -v b="$seconds" 'BEGIN { printf "%.3f", a + b }')
  if { [ "$expect" = 0 ] && [ "$rc" = 0 ]; } || { [ "$expect" = refuse ] && [ "$rc" != 0 ]; }; then
    result=ok
  else
    result=UNEXPECTED
    fail
  fi
  note=""
  if [ "$rc" != 0 ]; then note=$(refusal "$J/steps/$name.stderr"); fi
  row "$name" "$expect" "$rc" "$seconds" "$result" "$note"
}

# check DESCRIPTION CMD...  -- a named assertion over retained artifacts
check() {
  local description=$1
  shift
  if "$@" >/dev/null 2>&1; then
    row "check" "-" "-" "-" ok "$description"
  else
    row "check" "-" "-" "-" FAILED "$description"
    fail
  fi
}

# The client prints the Host's encoded Outcome in hex; show its readable text.
refusal() {
  local line hex
  line=$(grep -m1 -o 'host refused [a-z-]*; encoded refusal: [0-9a-f]*' "$1" || true)
  if [ -z "$line" ]; then
    tr '\n' ' ' <"$1" | cut -c1-160
    return
  fi
  hex=${line##*: }
  printf '%s: ' "${line%%;*}"
  printf '%b' "$(printf '%s' "$hex" | sed 's/../\\x&/g')" | tr -c '[:print:]' ' ' | tr -s ' ' | cut -c1-160
}

mini() { "$MINI" "$@"; }
field_value() { jq -r --arg f "$2" '[.page.entries[] | select(.key.field == $f) | .value][0] // "absent"' "$1"; }
json_is() { jq -e "$2" "$1" >/dev/null; }

completed=0
finish() {
  local overall=PASS j
  [ "$completed" = 1 ] || { overall=FAIL; row ABORTED - - - FAILED "journey stopped early; see the last step's stderr"; }
  {
    printf '\nJourney against %s (tag %s)\n\n' "$STATE" "$tag"
    printf '%-4s  %-6s  %11s\n' J result step_wall_s
    for j in J0 J1 J2 J3 J4 J5 J6 J7 J8; do
      printf '%-4s  %-6s  %11s\n' "$j" "${verdict[$j]:-NOTRUN}" "${wall[$j]:--}"
      [ "${verdict[$j]:-NOTRUN}" = PASS ] || overall=FAIL
    done
    printf '\noverall: %s\n\nsteps (%s):\n' "$overall" "$TSV"
    column -t -s "$(printf '\t')" "$TSV" 2>/dev/null || cat "$TSV"
  } | tee "$J/summary.txt"
  [ "$overall" = PASS ] || exit 1
}
trap finish EXIT

# ---------------------------------------------------------------- J0
begin J0
check "Store socket exists" test -S "$SOCKET"
step J0-sponsor 0 "$here/run.sh" sponsor --state "$STATE"
step J0-factory-read 0 mini workspace --action read --dir "$SP" --name factory
check "sponsor's signed factory read answered" json_is "$J/steps/J0-factory-read.stdout" '.type == "resource"'

# ---------------------------------------------------------------- J1
begin J1
step J1-keygen 0 mini keygen --secret "$J/keys/newcomer.key" --public "$J/keys/newcomer.pub"
NA=$J/attempts/newcomer
step J1-plan 0 mini enroll --action plan --sponsor-workspace "$SP" --factory-ref factory \
  --name "newcomer-$tag" --new-key "$J/keys/newcomer.key" --dir "$NA"
step J1-seal 0 mini enroll --action seal --dir "$NA"
step J1-submit 0 mini enroll --action submit --dir "$NA"
step J1-lookup 0 mini enroll --action lookup --dir "$NA"
check "enrollment installed" json_is "$NA/submit.json" '.confirmation == "installed"'
check "lookup returns the same receipt" test \
  "$(jq -r .transactionId "$NA/submit.json")" = "$(jq -r .receipt.transactionId "$J/steps/J1-lookup.stdout")"
newcomer_public=$(od -An -tx1 -v "$J/keys/newcomer.pub" | tr -d ' \n')
check "newcomer key absent from genesis, operator and pinned config" \
  bash -c "! grep -q $newcomer_public '$STATE/genesis.json' '$STATE/operator.json' '$CONFIG'"
NEWCOMER=$(jq -r .subject "$NA/enrollment.json")

# ---------------------------------------------------------------- J2
begin J2
RES=shared-$tag
printf '{"type":"all","predicates":[]}\n' >"$J/requests/all.json"
step J2-create 0 mini workspace --action create --dir "$SP" --name "$RES" --storage declared \
  --predicate "$J/requests/all.json"
check "resource birth installed" json_is "$SP/attempts/create-$RES/outcome.json" '.confirmation == "installed"'
TARGET=$(jq -r .target "$SP/refs/$RES.json")
OWNER_CAP=$(jq -r .observeCapability "$SP/refs/$RES.json")

# ---------------------------------------------------------------- J3
begin J3
jq -n --arg name "$RES" --arg recipient "$NEWCOMER" \
  '{type: "minidregg-workspace-proposal-v1", action: "delegate", name: $name,
    recipient: $recipient, verbs: ["observe", "mutate"], maxCost: "50000"}' >"$J/requests/delegate.json"
GRANT=grant-$tag
step J3-propose 0 mini workspace --action propose --dir "$SP" --request "$J/requests/delegate.json" \
  --proposal-id "$GRANT"
step J3-submit 0 mini workspace --action submit --dir "$SP" --intent "$SP/proposals/$GRANT/intent.json" \
  --attempt "$SP/attempts/$GRANT"
step J3-publish 0 mini workspace --action publish-delegation --dir "$SP" --proposal-id "$GRANT" \
  --attempt "$SP/attempts/$GRANT"
REF=$SP/proposals/$GRANT/recipient-reference.json
check "delegation installed" json_is "$SP/attempts/$GRANT/outcome.json" '.confirmation == "installed"'
check "reference names the newcomer" json_is "$REF" ".recipient == \"$NEWCOMER\""
CHILD_CAP=$(jq -r .capability "$REF")

# ---------------------------------------------------------------- J4
begin J4
NW=$J/newcomer
step J4-init 0 mini workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --enrollment "$NA/enrollment.json" --dir "$NW"
step J4-import 0 mini workspace --action import --dir "$NW" --name shared --from-ref "$REF"
step J4-read0 0 mini workspace --action read --dir "$NW" --name shared
check "field 2 absent before the newcomer writes" test "$(field_value "$J/steps/J4-read0.stdout" 2)" = absent
invoke() {
  jq -n --arg name "$1" --argjson action "$2" \
    '{type: "minidregg-workspace-proposal-v1", action: "invoke",
      targets: [{name: $name, payload: {type: "scalar", actions: [$action]}}]}'
}
invoke shared '{"type":"create","key":{"type":"object","field":"2"},"value":"1"}' >"$J/requests/create-2.json"
step J4-propose 0 mini workspace --action propose --dir "$NW" --request "$J/requests/create-2.json" \
  --proposal-id first-action
step J4-submit 0 mini workspace --action submit --dir "$NW" --intent "$NW/proposals/first-action/intent.json" \
  --attempt "$NW/attempts/first-action"
step J4-read1 0 mini workspace --action read --dir "$NW" --name shared
check "newcomer write installed" json_is "$NW/attempts/first-action/outcome.json" '.confirmation == "installed"'
check "signed readback shows field 2 = 1" test "$(field_value "$J/steps/J4-read1.stdout" 2)" = 1

# ---------------------------------------------------------------- J5
begin J5
TA=$J/attempts/third
TW=$J/third
step J5-keygen 0 mini keygen --secret "$J/keys/third.key" --public "$J/keys/third.pub"
step J5-enroll-plan 0 mini enroll --action plan --sponsor-workspace "$SP" --factory-ref factory \
  --name "third-$tag" --new-key "$J/keys/third.key" --dir "$TA"
step J5-enroll-seal 0 mini enroll --action seal --dir "$TA"
step J5-enroll-submit 0 mini enroll --action submit --dir "$TA"
THIRD=$(jq -r .subject "$TA/enrollment.json")
step J5-init 0 mini workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --enrollment "$TA/enrollment.json" --dir "$TW"
step J5-import-child 0 mini workspace --action import --dir "$TW" --name stolen --kind object \
  --target "$TARGET" --observe-capability "$CHILD_CAP"
step J5-import-owner 0 mini workspace --action import --dir "$TW" --name owner --kind object \
  --target "$TARGET" --observe-capability "$OWNER_CAP"
step J5-read-child refuse mini workspace --action read --dir "$TW" --name stolen
step J5-read-owner refuse mini workspace --action read --dir "$TW" --name owner
invoke stolen '{"type":"create","key":{"type":"object","field":"3"},"value":"1"}' >"$J/requests/third-create-3.json"
step J5-propose-write refuse mini workspace --action propose --dir "$TW" \
  --request "$J/requests/third-create-3.json" --proposal-id third-write
# Adversary path: take an intent the newcomer could author against current
# roots and resubmit it under the third participant's subject and key.
invoke shared '{"type":"create","key":{"type":"object","field":"3"},"value":"1"}' >"$J/requests/create-3.json"
step J5-newcomer-authors-template 0 mini workspace --action propose --dir "$NW" \
  --request "$J/requests/create-3.json" --proposal-id template-for-third
jq --arg s "$THIRD" '.subject = $s | .purpose.draft.command.subject = $s' \
  "$NW/proposals/template-for-third/intent.json" >"$J/requests/third-crafted-intent.json"
step J5-submit-crafted refuse mini workspace --action submit --dir "$TW" \
  --intent "$J/requests/third-crafted-intent.json"
# An unenrolled key with a subject nobody was given.
STRANGER=$(( $(od -An -N4 -tu4 /dev/urandom | tr -d ' ') + 1000000000 ))
step J5u-keygen 0 mini keygen --secret "$J/keys/stranger.key" --public "$J/keys/stranger.pub"
step J5u-init 0 mini workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --key "$J/keys/stranger.key" --subject "$STRANGER" --dir "$J/stranger"
step J5u-import 0 mini workspace --action import --dir "$J/stranger" --name stolen --kind object \
  --target "$TARGET" --observe-capability "$CHILD_CAP"
step J5u-read refuse mini workspace --action read --dir "$J/stranger" --name stolen
jq --arg s "$STRANGER" '.subject = $s | .purpose.draft.command.subject = $s' \
  "$NW/proposals/template-for-third/intent.json" >"$J/requests/stranger-crafted-intent.json"
step J5u-submit-crafted refuse mini workspace --action submit --dir "$J/stranger" \
  --intent "$J/requests/stranger-crafted-intent.json"
step J5-control-newcomer-read 0 mini workspace --action read --dir "$NW" --name shared
check "control: newcomer still reads field 2 = 1" test "$(field_value "$J/steps/J5-control-newcomer-read.stdout" 2)" = 1
check "no call was produced for the third participant" bash -c "! find '$TW/attempts' -name call.bin | grep -q ."

# ---------------------------------------------------------------- J6
begin J6
restart_start=$(date +%s.%N)
if [ -n "$restart_command" ]; then
  step J6-restart 0 sh -c "$restart_command"
else
  step J6-stop 0 "$here/run.sh" stop --state "$STATE"
  step J6-start 0 "$here/run.sh" start --state "$STATE"
fi
first_read=""
for _ in $(seq 1 1200); do
  if [ -S "$SOCKET" ] && mini workspace --action read --dir "$NW" --name shared \
      >"$J/steps/J6-first-read.stdout" 2>"$J/steps/J6-first-read.stderr"; then
    first_read=$(date +%s.%N)
    break
  fi
  sleep 0.5
done
if [ -n "$first_read" ]; then
  reopen=$(awk -v a="$restart_start" -v b="$first_read" 'BEGIN { printf "%.3f", b - a }')
  row J6-reopen-to-first-signed-read - 0 "$reopen" ok "restart issued to first successful signed read"
else
  row J6-reopen-to-first-signed-read - 1 - UNEXPECTED "no signed read within 600 s"
  fail
fi
check "after restart field 2 = 1" test "$(field_value "$J/steps/J6-first-read.stdout" 2)" = 1
step J6-enroll-lookup 0 mini enroll --action lookup --dir "$NA"
check "enrollment receipt unchanged after restart" test \
  "$(jq -r .transactionId "$NA/submit.json")" = "$(jq -r .receipt.transactionId "$J/steps/J6-enroll-lookup.stdout")"
step J6-retry-submit 0 mini retry --attempt "$NW/attempts/first-action" --mode submit
check "exact resubmit is a replay of the same transaction" bash -c "
  jq -e '.confirmation == \"replayed\"' '$J/steps/J6-retry-submit.stdout' &&
  test \"\$(jq -r .transactionId '$J/steps/J6-retry-submit.stdout')\" = \"\$(jq -r .transactionId '$NW/attempts/first-action/outcome.json')\""
invoke shared '{"type":"write","key":{"type":"object","field":"2"},"value":"2","expected":"1"}' >"$J/requests/write-2.json"
step J6-next-propose 0 mini workspace --action propose --dir "$NW" --request "$J/requests/write-2.json" \
  --proposal-id after-restart
step J6-next-submit 0 mini workspace --action submit --dir "$NW" --intent "$NW/proposals/after-restart/intent.json" \
  --attempt "$NW/attempts/after-restart"
check "next write is exactly one record after the third enrollment (no second effect from the resubmit)" test \
  "$(jq -r .acceptedCount "$NW/attempts/after-restart/outcome.json")" = \
  "$(( $(jq -r .acceptedCount "$TA/submit.json") + 1 ))"

# ---------------------------------------------------------------- J7
begin J7
step J7-describe-before 0 mini workspace --action describe --dir "$SP" --name "$RES"
jq -n --arg name "$RES" '{type: "minidregg-workspace-proposal-v1", action: "install-policy", name: $name,
  predicate: {type: "not", predicate: {type: "any", predicates: []}}}' >"$J/requests/law-v2.json"
step J7-propose 0 mini workspace --action propose --dir "$SP" --request "$J/requests/law-v2.json" \
  --proposal-id "law-$tag"
step J7-submit 0 mini workspace --action submit --dir "$SP" --intent "$SP/proposals/law-$tag/intent.json" \
  --attempt "$SP/attempts/law-$tag"
step J7-describe-after 0 mini workspace --action describe --dir "$SP" --name "$RES"
check "law installed" json_is "$SP/attempts/law-$tag/outcome.json" '.confirmation == "installed"'
check "law version advanced to 1 with the new predicate" json_is "$J/steps/J7-describe-after.stdout" \
  '.version == "1" and .predicate.type == "not"'
invoke shared '{"type":"write","key":{"type":"object","field":"2"},"value":"7","expected":"2"}' >"$J/requests/write-7.json"
step J7-newcomer-propose 0 mini workspace --action propose --dir "$NW" --request "$J/requests/write-7.json" \
  --proposal-id after-law
step J7-newcomer-submit 0 mini workspace --action submit --dir "$NW" --intent "$NW/proposals/after-law/intent.json" \
  --attempt "$NW/attempts/after-law"
step J7-newcomer-readback 0 mini workspace --action read --dir "$NW" --name shared
check "newcomer write under the new law installed; readback 7" bash -c "
  jq -e '.confirmation == \"installed\"' '$NW/attempts/after-law/outcome.json' &&
  test \"\$(jq -r --arg f 2 '[.page.entries[] | select(.key.field == \$f) | .value][0]' '$J/steps/J7-newcomer-readback.stdout')\" = 7"

# ---------------------------------------------------------------- J8
begin J8
invoke shared '{"type":"write","key":{"type":"object","field":"2"},"value":"8","expected":"7"}' >"$J/requests/write-8.json"
step J8-newcomer-prelock-propose 0 mini workspace --action propose --dir "$NW" --request "$J/requests/write-8.json" \
  --proposal-id prelock
jq -n --arg name "$RES" '{type: "minidregg-workspace-proposal-v1", action: "install-policy", name: $name,
  predicate: {type: "any", predicates: []}}' >"$J/requests/deny-all.json"
step J8-propose-deny 0 mini workspace --action propose --dir "$SP" --request "$J/requests/deny-all.json" \
  --proposal-id "lockout-$tag"
step J8-submit-deny 0 mini workspace --action submit --dir "$SP" --intent "$SP/proposals/lockout-$tag/intent.json" \
  --attempt "$SP/attempts/lockout-$tag"
check "deny-all installed" json_is "$SP/attempts/lockout-$tag/outcome.json" '.confirmation == "installed"'
step J8-newcomer-read refuse mini workspace --action read --dir "$NW" --name shared
step J8-newcomer-propose-write refuse mini workspace --action propose --dir "$NW" \
  --request "$J/requests/write-8.json" --proposal-id after-lock
step J8-newcomer-submit-prelock refuse mini workspace --action submit --dir "$NW" \
  --intent "$NW/proposals/prelock/intent.json" --attempt "$NW/attempts/prelock"
step J8-sponsor-read refuse mini workspace --action read --dir "$SP" --name "$RES"
jq -n --arg name "$RES" '{type: "minidregg-workspace-proposal-v1", action: "install-policy", name: $name,
  predicate: {type: "all", predicates: []}}' >"$J/requests/repair.json"
step J8-sponsor-repair-propose refuse mini workspace --action propose --dir "$SP" --request "$J/requests/repair.json" \
  --proposal-id "repair-$tag"
step J8-prior-lookup 0 mini retry --attempt "$NW/attempts/after-law" --mode lookup
step J8-prior-retry-submit 0 mini retry --attempt "$NW/attempts/after-law" --mode submit
check "historical write recovers as the original receipt after the lock" bash -c "
  for f in '$J/steps/J8-prior-lookup.stdout' '$J/steps/J8-prior-retry-submit.stdout'; do
    jq -e '.confirmation == \"replayed\"' \"\$f\" >/dev/null &&
    test \"\$(jq -r .transactionId \"\$f\")\" = \"\$(jq -r .transactionId '$NW/attempts/after-law/outcome.json')\" || exit 1
  done"
check "no call was produced for the post-lock pre-authored write" test ! -e "$NW/attempts/prelock/call.bin"

# ---------------------------------------------------------------- table
completed=1
