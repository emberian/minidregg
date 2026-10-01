#!/usr/bin/env bash
# journey.d/jjoint.sh — K-JOINT-INDEX: a law names another participant of a
# joint command by POSITION (`joint/index/{i}/…`, 0-based target order), not by
# cell id, and a position the command does not have is refused, not vacuous.
#
# `jj-a` carries the law
#   any [ request/verb in {1,3,4,5}, eq joint/index/1/resource/field/401/after 7 ]
# (observe and management open; a mutate needs participant 1's field 401 = 7);
# `jj-b` is permit-all. Every row is proposed (signed reads succeed) and then
# submitted; a refusal counts only if it is the Host's refusal of the submit. Rows (each a real propose + submit on the live Store):
#   r1  [a, b]  b creates 401 = 7              admitted
#   r2  [a, b]  b writes 401 7 -> 8            refused (index 1 reads 8)
#   r3  [a]     one target, index 1 absent     refused
#   r4  [b, a]  same cells, swapped: index 1 is now a, which has no
#               field 401                      refused (position, not identity)
#   r5  [a, b]  b leaves 401 = 7, creates 402  admitted
#
# Runs as a journey hook (MINI SPONSOR_WS JOURNEY_STEP_DIR). Exit 0 = every row
# matched. Last stdout line = the result table.
set -euo pipefail
D=$JOURNEY_STEP_DIR
mkdir -p "$D/req"
res=$D/jjoint-result.tsv
: >"$res"

installed() { jq -e '.type == "confirmed" and .confirmation == "installed"' "$1" >/dev/null 2>&1; }
create() { printf '{"type":"create","key":{"type":"object","field":"%s"},"value":"%s"}' "$1" "$2"; }
write() { printf '{"type":"write","key":{"type":"object","field":"%s"},"expected":"%s","value":"%s"}' "$1" "$2" "$3"; }
target() { printf '{"name":"%s","payload":{"type":"scalar","actions":[%s]}}' "$1" "$2"; }
invoke() { printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[%s]}\n' "$1"; }

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
printf '%s\n' '{"type":"any","predicates":[{"type":"memberOf","slot":"request/verb","values":["1","3","4","5"]},{"type":"eq","slot":"joint/index/1/resource/field/401/after","value":"7"}]}' >"$D/req/law-a.json"
"$MINI" workspace --action create --dir "$SPONSOR_WS" --name jj-a --storage declared \
  --predicate "$D/req/law-a.json" --fields 400-414 >"$D/create-a.out" 2>"$D/create-a.err" \
  || { echo "could not create jj-a: $(tail -1 "$D/create-a.err")" >&2; exit 1; }
"$MINI" workspace --action create --dir "$SPONSOR_WS" --name jj-b --storage declared \
  --predicate "$D/req/permit-all.json" --fields 400-414 >"$D/create-b.out" 2>"$D/create-b.err" \
  || { echo "could not create jj-b: $(tail -1 "$D/create-b.err")" >&2; exit 1; }

# The Host's encoded refusal, with its printable text runs.
reason() {
  local line hex
  line=$(tail -1 "$1" 2>/dev/null | tr '\t' ' ')
  hex=$(printf '%s' "$line" | grep -o 'refusal: [0-9a-f]*' | cut -d' ' -f2)
  if [ -n "$hex" ]; then
    printf '%s [%s]' "$line" "$(printf '%s' "$hex" | xxd -r -p | tr -c '[:print:]' ' ' | tr -s ' ')"
  else
    printf '%s' "$line"
  fi
}

# row LABEL EXPECT(admitted|refused) TARGETS-JSON
row() {
  local label=$1 expect=$2 targets=$3 rc=0 verdict=refused detail
  invoke "$targets" >"$D/req/$label.json"
  if ! "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/$label.json" \
      --proposal-id "jj-$label" >"$D/$label.propose.out" 2>"$D/$label.propose.err"; then
    printf 'FAIL\t%s\t%s\tunproposed\t-\tpropose: %s\n' "$label" "$expect" "$(reason "$D/$label.propose.err")" >>"$res"
    return 1
  fi
  "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/jj-$label/intent.json" \
    --attempt "$SPONSOR_WS/attempts/jj-$label" >"$D/$label.submit.out" 2>"$D/$label.submit.err" || rc=$?
  if installed "$SPONSOR_WS/attempts/jj-$label/outcome.json"; then
    verdict=admitted
    detail="record $(jq -r .acceptedCount "$SPONSOR_WS/attempts/jj-$label/outcome.json")"
  else
    local out=$SPONSOR_WS/attempts/jj-$label/outcome.json
    if jq -e '.type == "refused"' "$out" >/dev/null 2>&1; then
      detail="$(jq -r .phase "$out" | xxd -r -p): $(jq -r .detail "$out" | xxd -r -p)"
    else
      detail=$(reason "$D/$label.submit.err")
    fi
  fi
  local ok=ok; [ "$verdict" = "$expect" ] || ok=FAIL
  printf '%s\t%s\t%s\t%s\trc=%s\t%s\n' "$ok" "$label" "$expect" "$verdict" "$rc" "$detail" >>"$res"
  [ "$ok" = ok ]
}

fail=0
row r1 admitted "$(target jj-a "$(create 400 1)"),$(target jj-b "$(create 401 7)")" || fail=1
row r2 refused  "$(target jj-a "$(create 410 1)"),$(target jj-b "$(write 401 7 8)")" || fail=1
row r3 refused  "$(target jj-a "$(create 411 1)")" || fail=1
row r4 refused  "$(target jj-b "$(create 412 1)"),$(target jj-a "$(create 413 1)")" || fail=1
row r5 admitted "$(target jj-a "$(create 414 1)"),$(target jj-b "$(create 402 1)")" || fail=1

cat "$res" >&2
[ "$fail" = 0 ] || { echo "joint-index rows did not all match: $(grep -c FAIL "$res") FAIL" >&2; exit 1; }
echo "joint/index/1 read by position: 2 admitted, 3 refused (value, absent index, swapped order)" >&2
echo "$res"
