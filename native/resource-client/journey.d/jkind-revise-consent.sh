#!/usr/bin/env bash
# P7 (PLAN-SCOPED-REPLAY): does a kind-DEFINITION change between consent and
# admission commit an effect other than the one consented to?
# Dan prepares and signs a vote on an instance (prepare-only: the real
# observation/prepare/assemble boundary, exact call bytes retained), Alice then
# revises the kind definition, and the retained call is retried unchanged.
# Verdict row `p7-verdict`:
#   SAME-EFFECT  committed, and the instance holds exactly the consented vote
#                under its original descriptor (no defect)
#   REFUSED      the retained call refused (no defect; stricter)
#   DIVERGED     committed with an effect other than the consented one (DEFECT)
# Inputs as journey.d/jworld-kind.sh.
set -euo pipefail
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
: "${SPONSOR_WS:?}" "${SPONSOR_SUBJECT:?}"
D=$JOURNEY_STEP_DIR/jkind-revise-consent
[ ! -e "$D" ] || { echo "refusing to reuse $D" >&2; exit 2; }
mkdir -p -m 700 "$D/alice/requests" "$D/dan/requests" "$D/log"
ROWS=$D/rows.tsv
printf 'step\texpect\trc\tresult\n' >"$ROWS"
N=0
SHELL_BIN=${SHELL_BIN:-$MINI}
finish() { local rc=$?; printf '%s\n' "$ROWS"; [ "$rc" = 0 ] || echo "P7: stopped at the first failed row; see $D/log" >&2; }
trap finish EXIT
say() {
  local who=$1 line=$2 ws
  if [ "$who" = alice ]; then ws=$SPONSOR_WS; else ws=$SPONSOR_WS; fi
  N=$((N+1)); OUT=$D/log/$N.out; ERR=$D/log/$N.err
  printf '%s\n' "$line" >"$D/log/$N.line"
  if "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
      --workspace "$ws" --home "$D/$who" --line "$line" >"$OUT" 2>"$ERR"; then RC=0; else RC=$?; fi
}
ok() {
  local step=$1 who=$2 line=$3
  say "$who" "$line"
  printf '%s\t0\t%s\t%s\n' "$step" "$RC" "$([ "$RC" = 0 ] && echo PASS || echo FAIL)" >>"$ROWS"
  if [ "$RC" != 0 ]; then cat "$ERR" >&2; return 1; fi
}
check() {
  local step=$1; shift
  if "$@"; then printf '%s\ttrue\t0\tPASS\n' "$step" >>"$ROWS";
  else printf '%s\ttrue\t1\tFAIL\n' "$step" >>"$ROWS"; return 1; fi
}
turn() { local step=$1 who=$2 id=$3 line=$4; ok "$step-prepare" "$who" "$line"; ok "$step-submit" "$who" "submit $id"; }
cat >"$D/alice/requests/poll-v1.json" <<'JSON'
{"descriptor":{"revision":"1","fields":[
 {"id":"1","name":"question","meaning":"the poll question","codec":"bytes","discipline":"rom"},
 {"id":"2","name":"open","meaning":"whether the poll accepts votes","codec":"nat","discipline":"ram"},
 {"id":"3","name":"votes","meaning":"one immutable vote keyed by member subject","codec":"nat","discipline":"append"}]},
 "defaults":[{"field":"1","key":"0","value":"4c756e63683f"},{"field":"2","key":"0","value":"1"}]}
JSON
# Revision 2 changes the meaning a reader would attach to field 3 and adds a field.
jq '.descriptor.revision="2" | .descriptor.fields[2].meaning="vote weight times ten" | .descriptor.fields += [{id:"4",name:"title",meaning:"display title",codec:"bytes",discipline:"ram"}] | .defaults += [{field:"4",key:"0",value:"506f6c6c"}]' \
  "$D/alice/requests/poll-v1.json" >"$D/alice/requests/poll-v2.json"

# One member (the sponsor, whose workspace carries a birth context) defines the
# kind, owns the instance and signs the vote; the question is the definition
# change between signature and admission, not cross-member authority.
ok kind-create alice 'kind create p7-poll @poll-v1.json open'
ok instance-create alice 'create p7-one --from p7-poll open'
ok instance-before alice 'instance show p7-one'
cp "$OUT" "$D/instance-before.json"
check before-rev1 jq -e '.value.descriptor.revision=="1"' "$D/instance-before.json" >/dev/null

# Consent at height h: the real prepare/sign boundary, exact call bytes retained.
ok vote-prepare alice "instance set p7-vote p7-one votes $SPONSOR_SUBJECT 1"
"$MINI" workspace --socket "$SOCKET" --action submit --dir "$SPONSOR_WS" \
  --intent "$SPONSOR_WS/proposals/p7-vote/intent.json" \
  --attempt "$SPONSOR_WS/attempts/p7-vote" --prepare-only true \
  >"$D/log/vote-prepare-only.out" 2>"$D/log/vote-prepare-only.err" \
  || { printf 'vote-signed\t0\t1\tFAIL\n' >>"$ROWS"; cat "$D/log/vote-prepare-only.err" >&2; exit 1; }
printf 'vote-signed\t0\t0\tPASS\n' >>"$ROWS"
check call-retained test -s "$SPONSOR_WS/attempts/p7-vote/call.bin"
cp "$SPONSOR_WS/attempts/p7-vote/call.bin" "$D/consented-call.bin"
CALL=$(sha256sum "$D/consented-call.bin" | cut -d' ' -f1)

# Between consent and admission: the kind DEFINITION changes.
turn revise-kind alice p7-revise 'kind revise p7-revise p7-poll @poll-v2.json'
ok kind-after alice 'kind show p7-poll'
check kind-is-rev2 jq -e '.value.descriptor.revision=="2"' "$OUT" >/dev/null

# Admission of the unchanged consented call.
say alice 'retry p7-vote'
printf 'retry\t-\t%s\t%s\n' "$RC" "$([ "$RC" = 0 ] || [ "$RC" = 3 ] || [ "$RC" = 4 ] && echo RAN || echo FAIL)" >>"$ROWS"
cp "$OUT" "$D/retry.out"; cp "$ERR" "$D/retry.err"
check call-unchanged test "$CALL" = "$(sha256sum "$SPONSOR_WS/attempts/p7-vote/call.bin" | cut -d' ' -f1)"
ls "$SPONSOR_WS/attempts/p7-vote/" >"$D/attempt-files.txt"
ok instance-after alice 'instance show p7-one'
cp "$OUT" "$D/instance-after.json"
if [ "$RC" = 0 ]; then :; fi
RETRY_JSON=$(ls "$SPONSOR_WS"/attempts/p7-vote/retry-*.json 2>/dev/null | tail -1 || true)
[ -z "$RETRY_JSON" ] || cp "$RETRY_JSON" "$D/retry-decision.json"
voted=$(jq -r --arg s "$SPONSOR_SUBJECT" '[.value.entries[] | select(.field=="3" and .key==$s) | .value] | join(",")' "$D/instance-after.json")
rev=$(jq -r '.value.descriptor.revision' "$D/instance-after.json")
fields=$(jq -r '[.value.descriptor.fields[].id] | join(",")' "$D/instance-after.json")
before_other=$(jq -S '[.value.entries[] | select(.field!="3")]' "$D/instance-before.json")
after_other=$(jq -S '[.value.entries[] | select(.field!="3")]' "$D/instance-after.json")
if [ -n "$RETRY_JSON" ] && jq -e '.type=="refused" or .type=="contention"' "$RETRY_JSON" >/dev/null && [ -z "$voted" ]; then
  verdict=REFUSED
elif [ "$voted" = 1 ] && [ "$rev" = 1 ] && [ "$fields" = "1,2,3" ] && [ "$before_other" = "$after_other" ]; then
  verdict=SAME-EFFECT
else
  verdict=DIVERGED
fi
printf 'p7-verdict\tSAME-EFFECT|REFUSED\t-\t%s (vote=%s rev=%s fields=%s retry-rc=%s)\n' "$verdict" "$voted" "$rev" "$fields" "$RC" >>"$ROWS"
echo "P7 verdict: $verdict" >&2
[ "$verdict" != DIVERGED ]
