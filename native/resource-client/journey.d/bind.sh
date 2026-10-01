#!/usr/bin/env bash
# journey.d/bind.sh — two agents, disjoint writes, both admitted in either order
# with no re-plan (lane BIND, Theory.PlanBinding).
#
# Agent S (the sponsor) writes its own resource `bind-solo`; agent N (the
# newcomer) writes `bind-n`, delegated to it. Each plan is prepared AND SIGNED before either is
# submitted (`workspace submit --prepare-only true`), then the two sealed calls
# are submitted with `mini retry --mode submit`, in one order and then, with
# fresh plans, in the other. Under whole-root binding the second submit of each
# pair was refused (the authority root, the revision counter and the height had
# all moved). The overlap pole: two plans on the SAME target cell; the second
# is refused, because a plan reads its target cell whole (expectedTargetRoot).
#
# Runs as a journey hook (exported: MINI SOCKET SPONSOR_WS NEWCOMER_WS
# JOURNEY_STEP_DIR). Exit 0 = both poles held. Last stdout line = the result.
set -euo pipefail
D=$JOURNEY_STEP_DIR
mkdir -p "$D/req"
res=$D/bind-result.tsv
: >"$res"

scalar() {  # NAME ACTION FIELD VALUE
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"%s","payload":{"type":"scalar","actions":[{"type":"%s","key":{"type":"object","field":"%s"},"value":"%s"}]}}]}\n' "$1" "$2" "$3" "$4"
}
installed() { jq -e '.type == "confirmed" and .confirmation == "installed"' "$1" >/dev/null 2>&1; }

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
"$MINI" workspace --action create --dir "$SPONSOR_WS" --name bind-solo --storage declared \
  --predicate "$D/req/permit-all.json" --fields 301-310 >"$D/create.out" 2>"$D/create.err" \
  || { echo "sponsor could not create bind-solo: $(tail -1 "$D/create.err")" >&2; exit 1; }
# The newcomer's own resource: created by the sponsor, delegated observe+mutate
# to the newcomer, imported into the newcomer's workspace (the J2-J4 path; the
# journey's `shared` is locked by J8 when this hook runs).
"$MINI" workspace --action create --dir "$SPONSOR_WS" --name bind-n --storage declared \
  --predicate "$D/req/permit-all.json" --fields 301-310 >"$D/create-n.out" 2>"$D/create-n.err" \
  || { echo "sponsor could not create bind-n: $(tail -1 "$D/create-n.err")" >&2; exit 1; }
jq -n --arg r "$NEWCOMER_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"bind-n",
  recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/delegate.json"
"$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/delegate.json" \
  --proposal-id bind-grant >"$D/grant.propose.out" 2>"$D/grant.propose.err" \
  || { echo "delegate propose failed: $(tail -1 "$D/grant.propose.err")" >&2; exit 1; }
"$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/bind-grant/intent.json" \
  --attempt "$SPONSOR_WS/attempts/bind-grant" >"$D/grant.submit.out" 2>"$D/grant.submit.err" \
  || { echo "delegate submit failed: $(tail -1 "$D/grant.submit.err")" >&2; exit 1; }
"$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id bind-grant \
  --attempt "$SPONSOR_WS/attempts/bind-grant" >"$D/grant.publish.out" 2>"$D/grant.publish.err" \
  || { echo "publish-delegation failed: $(tail -1 "$D/grant.publish.err")" >&2; exit 1; }
"$MINI" workspace --action import --dir "$NEWCOMER_WS" --name bind-n \
  --from-ref "$SPONSOR_WS/proposals/bind-grant/recipient-reference.json" >"$D/import.out" 2>"$D/import.err" \
  || { echo "newcomer import failed: $(tail -1 "$D/import.err")" >&2; exit 1; }

# plan WS NAME FIELD LABEL: propose + prepare-and-sign, no submit.
plan() {
  local ws=$1 name=$2 field=$3 label=$4
  scalar "$name" create "$field" 1 >"$D/req/$label.json"
  "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$label.json" \
    --proposal-id "$label" >"$D/$label.propose.out" 2>"$D/$label.propose.err" \
    || { echo "$label propose failed: $(tail -1 "$D/$label.propose.err")" >&2; return 1; }
  "$MINI" workspace --action submit --dir "$ws" --intent "$ws/proposals/$label/intent.json" \
    --attempt "$ws/attempts/$label" --prepare-only true >"$D/$label.prepare.out" 2>"$D/$label.prepare.err" \
    || { echo "$label prepare failed: $(tail -1 "$D/$label.prepare.err")" >&2; return 1; }
  [ -s "$ws/attempts/$label/call.bin" ] || { echo "$label has no sealed call" >&2; return 1; }
  [ ! -e "$ws/attempts/$label/outcome.json" ] || { echo "$label was submitted during prepare" >&2; return 1; }
  echo "$ws/attempts/$label" >"$D/$label.attempt"
}
# send LABEL: submit the sealed call exactly as signed.
send() {
  local label=$1
  local rc=0
  "$MINI" retry --attempt "$(cat "$D/$label.attempt")" --mode submit >"$D/$label.submit.out" 2>"$D/$label.submit.err" || rc=$?
  local verdict=refused
  installed "$D/$label.submit.out" && verdict=installed
  printf '%s\t%s\t%s\t%s\n' "$label" "$rc" "$verdict" "$(tail -1 "$D/$label.submit.err" | tr '\t' ' ')" >>"$res"
  [ "$verdict" = installed ]
}

# Pair 1: both signed, then S first, N second.
plan "$SPONSOR_WS" bind-solo 301 p1-sponsor
plan "$NEWCOMER_WS" bind-n 302 p1-newcomer
send p1-sponsor || { echo "p1: sponsor refused" >&2; cat "$res" >&2; exit 1; }
send p1-newcomer || { echo "p1: newcomer refused after sponsor's commit" >&2; tail -1 "$res" >&2; exit 1; }

# Pair 2: fresh plans, both signed, then N first, S second.
plan "$SPONSOR_WS" bind-solo 303 p2-sponsor
plan "$NEWCOMER_WS" bind-n 304 p2-newcomer
send p2-newcomer || { echo "p2: newcomer refused" >&2; exit 1; }
send p2-sponsor || { echo "p2: sponsor refused after newcomer's commit" >&2; tail -1 "$res" >&2; exit 1; }

# Overlap pole: two sponsor plans on the same cell, both signed before either
# commits; the second read the cell whole, so it must be refused.
plan "$SPONSOR_WS" bind-solo 305 p3-first
plan "$SPONSOR_WS" bind-solo 306 p3-second
send p3-first || { echo "p3: first overlapping write refused" >&2; exit 1; }
if send p3-second; then
  echo "p3: a plan whose target cell moved was admitted" >&2; exit 1
fi
grep -q . "$D/p3-second.submit.err" || { echo "p3: refusal carried no reason" >&2; exit 1; }

echo "pairs: S,N and N,S installed without re-plan; overlap refused: $(tail -1 "$D/p3-second.submit.err")" >&2
echo "$res"
