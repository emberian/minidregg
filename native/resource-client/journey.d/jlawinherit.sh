#!/usr/bin/env bash
# Actual room-export inheritance through Mini's signed read/write/install paths.
# Requires journey.sh J0-J5 environment; every refusal must be a decoded native
# refusal, never a transport/process failure. Parent policy details stay private.
set -euo pipefail
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
: "${SPONSOR_WS:?}" "${NEWCOMER_WS:?}" "${NEWCOMER_SUBJECT:?}"
D=$JOURNEY_STEP_DIR/jlawinherit
[ ! -e "$D" ] || { echo "refusing to reuse $D" >&2; exit 2; }
mkdir -p -m 700 "$D/alice/requests" "$D/dan/requests" "$D/log"
ROWS=$D/rows.tsv
printf 'step\texpect\trc\tresult\n' >"$ROWS"
N=0; SHELL_BIN=${SHELL_BIN:-$MINI}
finish() { local rc=$?; printf '%s\n' "$ROWS"; [ "$rc" = 0 ] || echo "JLAW-INHERIT stopped; inspect $D/log" >&2; }
trap finish EXIT
say() {
  local who=$1 line=$2 ws=$SPONSOR_WS
  [ "$who" = alice ] || ws=$NEWCOMER_WS
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
refused() {
  local step=$1 who=$2 line=$3
  say "$who" "$line"
  if [ "$RC" != 3 ] || ! grep -q '^refused:' "$ERR"; then
    printf '%s\tnative-refusal\t%s\tFAIL\n' "$step" "$RC" >>"$ROWS"; cat "$ERR" >&2; return 1
  fi
  printf '%s\tnative-refusal\t%s\tPASS\n' "$step" "$RC" >>"$ROWS"
  WORDS=$D/log/$N.words
  cat "$ERR" >"$WORDS"
  while read -r hex; do
    printf '%s' "$hex" | xxd -r -p | tr -c '[:print:]' ' ' >>"$WORDS"
  done < <(grep -oE 'encoded( refusal)?: [0-9a-f]+' "$ERR" | awk '{print $NF}' || true)
}
turn() { local step=$1 id=$2 line=$3; ok "$step-prepare" alice "$line"; ok "$step-submit" alice "submit $id"; }
# Component selectors use source physical tags and ordinary request verbs.
printf '%s\n' '{"selector":{"physicalKinds":["1"],"verbs":["2"]},"parents":[],"predicate":{"type":"any","predicates":[]}}' >"$D/alice/requests/block-write.json"
printf '%s\n' '{"selector":{"physicalKinds":["1"],"verbs":["1"]},"parents":[],"predicate":{"type":"any","predicates":[]}}' >"$D/alice/requests/block-read.json"
printf '%s\n' '{"selector":{"physicalKinds":["1"],"verbs":["3","5"]},"parents":[],"predicate":{"type":"any","predicates":[]}}' >"$D/alice/requests/block-management.json"
SECRET=987654321123456789987654321123456789987654321123456789987654321123456789987654321123456789987654321123456789987654321123456789987654321123456789987654321123456789987654321123456789
jq -n --arg secret "$SECRET" '{selector:{physicalKinds:["1"],verbs:["1"]},parents:[],predicate:{type:"le",slot:"clock/now",value:$secret}}' >"$D/alice/requests/hidden-range.json"

ok room-create alice 'room new jli-room --template workroom'
turn baseline-write jli-before "doc append jli-before jli-room/notes 'before exported restriction'"
ok baseline-read alice 'doc show jli-room/notes'
check baseline-content grep -q 'before exported restriction' "$OUT"
ok child-policy-before alice 'law export show jli-room/notes'
jq '.policy|{policyId,version,address}' "$OUT" >"$D/child-before.json"
# Dan receives only the child's observation grant, not its parent's policy.
turn child-delegate jli-child-reader "delegate jli-child-reader jli-room/notes $NEWCOMER_SUBJECT observe 50000"
ok child-publish alice 'publish jli-child-reader'
ok child-export alice 'export jli-child-reader'
REF=$(cat "$OUT")
ok child-import dan "import jli-note $REF"
ok child-signed-read dan 'doc show jli-note'

turn block-existing jli-block 'law export jli-block jli-room @block-write.json'
ok parent-baseline alice 'law export show jli-room'
POLICY=$(jq -er '.policy.policyId' "$OUT")
REVISION=$(jq -er '.policy.version' "$OUT")
ADDRESS=$(jq -er '.policy.address' "$OUT")
ok blocked-author alice "doc append jli-denied jli-room/notes 'must never commit'"
refused blocked-submit alice 'submit jli-denied'
ok read-remains-allowed dan 'doc show jli-note'
check refused-bytes-absent bash -c '! grep -q "must never commit" "$1"' _ "$OUT"
ok unchanged-child-policy alice 'law export show jli-room/notes'
jq '.policy|{policyId,version,address}' "$OUT" >"$D/child-after.json"
check child-source-unchanged cmp -s "$D/child-before.json" "$D/child-after.json"
# Accepted exact ingress is still replayed after current inherited law changes.
ok exact-retry alice 'retry jli-before'

# A new revision may deliberately inherit a pinned prior revision of itself.
# It conjoins the frozen restriction; it is not a resolved-record cycle.
jq -n --arg id "$POLICY" --arg revision "$REVISION" --arg digest "$ADDRESS" \
  '{selector:{},predicate:{type:"all",predicates:[]},parents:[{policyId:$id,facet:"descendants",selection:{type:"pinned",revision:$revision,sourceDigest:$digest}}]}' \
  >"$D/alice/requests/pinned.json"
turn pinned-baseline jli-pin 'law export jli-pin jli-room @pinned.json'
ok pinned-author alice "doc append jli-pinned-denied jli-room/notes 'pinned restriction still applies'"
refused pinned-refusal alice 'submit jli-pinned-denied'
# A head edge to this newly installed facet is an actual cycle and must refuse.
jq -n --arg id "$POLICY" '{selector:{},predicate:{type:"all",predicates:[]},parents:[{policyId:$id,facet:"descendants",selection:{type:"head"}}]}' \
  >"$D/alice/requests/cycle.json"
ok cycle-author alice 'law export jli-cycle jli-room @cycle.json'
refused cycle-install alice 'submit jli-cycle'
turn remove-export jli-clear 'law export jli-clear jli-room none'
turn write-restored jli-after "doc append jli-after jli-room/notes 'after removing export'"

# A neutral child cannot escape its room export through authority management.
turn block-management jli-mgmt 'law export jli-mgmt jli-room @block-management.json'
ok management-before alice 'law export show jli-room/notes'
jq -e '.judgedAt|select((.worldRoot|type) == "string" and (.height|type) == "string")|{worldRoot,height}' "$OUT" >"$D/management-before.json"
ok delegate-denied-prepare alice "delegate jli-delegate-denied jli-room/notes $NEWCOMER_SUBJECT observe 50000"
refused inherited-delegate alice 'submit jli-delegate-denied'
ok revoke-denied-prepare alice "revoke jli-revoke-denied jli-room/notes $NEWCOMER_SUBJECT"
refused inherited-revoke alice 'submit jli-revoke-denied'
ok management-after alice 'law export show jli-room/notes'
jq -e '.judgedAt|select((.worldRoot|type) == "string" and (.height|type) == "string")|{worldRoot,height}' "$OUT" >"$D/management-after.json"
check no-management-record cmp -s "$D/management-before.json" "$D/management-after.json"
ok denied-revoke-retains-reader dan 'doc show jli-note'
turn management-clear jli-mgmt-clear 'law export jli-mgmt-clear jli-room none'

turn block-read jli-read-block 'law export jli-read-block jli-room @block-read.json'
refused inherited-signed-read dan 'doc show jli-note'
# Public refusal must not identify a parent's source or a clause origin.
check hidden-parent-name bash -c '! grep -q "jli-room\|policy-origin\|descendants" "$1"' _ "$WORDS"
check hidden-parent-id bash -c '! grep -q "$1" "$2"' _ "$POLICY" "$WORDS"
turn hidden-range jli-range 'law export jli-range jli-room @hidden-range.json'
refused inherited-range-read dan 'doc show jli-note'
check hidden-range-value bash -c '! grep -q "$1" "$2"' _ "$SECRET" "$WORDS"

# The native field is ZMod (2^127 - 1): 1 and 2^127 collide. The first
# equality makes this law semantically true on a read; only cast injectivity
# refuses it. Both literals belong to the hidden export, not the child law.
CAST_SECRET=170141183460469231731687303715884105728
jq -n --arg secret "$CAST_SECRET" '{selector:{physicalKinds:["1"],verbs:["1"]},parents:[],predicate:{type:"any",predicates:[{type:"eq",slot:"request/verb",value:"1"},{type:"eq",slot:"request/verb",value:$secret}]}}' >"$D/alice/requests/hidden-cast.json"
turn hidden-cast jli-cast 'law export jli-cast jli-room @hidden-cast.json'
refused inherited-cast-read dan 'doc show jli-note'
check hidden-cast-value bash -c '! grep -q "$1" "$2"' _ "$CAST_SECRET" "$WORDS"
turn read-restored jli-read-clear 'law export jli-read-clear jli-room none'
ok restored-signed-read dan 'doc show jli-note'
check restored-content grep -q 'after removing export' "$OUT"
printf 'JLAW-INHERIT: existing child reuse, current exports, pinned prior revision, cycles, signed reads, hidden ancestor failures and exact replay passed\n' >&2
