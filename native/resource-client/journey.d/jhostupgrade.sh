#!/usr/bin/env bash
# HOST-UPGRADE: candidate N's Store either reopens exactly or refuses its epoch.
# Usage: jhostupgrade.sh CAND_N CAND_N1 NEW_OUT reopen|refuse
# Keeps public read/receipt evidence, never keys or the scratch Store.
set -euo pipefail
umask 077
if [ "$#" != 4 ] || [[ $4 != reopen && $4 != refuse ]]; then
  echo "usage: $0 CAND_N CAND_N1 NEW_OUT reopen|refuse" >&2; exit 2
fi
C0=$(realpath "$1") C1=$(realpath "$2") OUT=$(realpath -m "$3") EXPECTED=$4
OPERATOR=$(CDPATH='' cd -- "$(dirname -- "$0")/../../../deploy/candidate" && pwd)/run.sh
for candidate in "$C0" "$C1"; do
  for file in READY manifest.json genesis-params.example.json run.sh genesis.sh; do
    [ -f "$candidate/$file" ] || { echo "HOST-UPGRADE UNCONFIGURED missing $candidate/$file" >&2; exit 98; }
  done
  for role in host mini store verifier; do
    binary=$(jq -er --arg r "$role" '.[$r]' "$candidate/manifest.json")
    [ -x "$binary" ] || { echo "HOST-UPGRADE UNCONFIGURED missing $role $binary" >&2; exit 98; }
  done
done
[ ! -e "$OUT" ] || { echo "HOST-UPGRADE FAIL evidence already exists: $OUT" >&2; exit 2; }
mkdir -m 700 -p "$OUT"
SCRATCH=$(mktemp -d /tmp/hu.XXXXXX)
S=$SCRATCH/state
PID= CHILDREN= OUTCOME=unknown VERIFIED=false
cleanup() {
  local cleanup_bad=0 child
  if [ -n "$PID" ]; then
    if CHILDREN=$(ps -o pid= --ppid "$PID"); then :; else CHILDREN=; fi
    if kill -0 "$PID" 2>/dev/null; then kill -TERM "$PID"; fi
    if wait "$PID"; then :; else echo "hostupgrade: server exited nonzero during cleanup" >>"$OUT/cleanup.txt"; fi
    for child in $CHILDREN; do
      for ((i=0; i<100; i++)); do
        if ! kill -0 "$child" 2>/dev/null; then break; fi
        sleep 0.1
      done
      if kill -0 "$child" 2>/dev/null; then
        echo "HOST-UPGRADE FAIL Host child $child survived shutdown" >&2; cleanup_bad=1
      fi
    done
  fi
  if [ "$cleanup_bad" = 0 ]; then rm -rf -- "$SCRATCH"; else exit 1; fi
}
trap cleanup EXIT
trap 'exit 130' INT TERM
result() {
  jq -n --arg outcome "$OUTCOME" --arg expected "$EXPECTED" --arg detail "$1" \
    --argjson verified "$VERIFIED" --arg n "$C0" --arg n1 "$C1" \
    '{type:"minidregg-hostupgrade-v1",candidateN:$n,candidateN1:$n1,
      outcome:$outcome,expected:$expected,verified:$verified,detail:$detail}' >"$OUT/result.json"
}
fail() { result "$*"; echo "HOST-UPGRADE FAIL $*" | tee "$OUT/verdict.txt" >&2; exit 1; }
run() {
  local label=$1 rc=0; shift
  timeout 180 "$@" >"$OUT/$label.out" 2>"$OUT/$label.err" || rc=$?
  printf '%s\n' "$rc" >"$OUT/$label.rc"
  [ "$rc" = 0 ] || fail "$label exit $rc: $(awk 'NF {last=$0} END {print last}' "$OUT/$label.err")"
}
store_hash() {
  # Include the external anchor as well as every file/directory/symlink in Store.
  python3 - "$S/store" <<'PY'
import hashlib, pathlib, sys
root = pathlib.Path(sys.argv[1]); h = hashlib.sha256()
paths = [root] + sorted(root.rglob('*'))
anchor = pathlib.Path(str(root) + '.head-anchor')
if anchor.exists():
    paths += [anchor] + (sorted(anchor.rglob('*')) if anchor.is_dir() else [])
for p in paths:
    name = str(p.relative_to(root.parent)).encode()
    kind = b'L' if p.is_symlink() else b'D' if p.is_dir() else b'F'
    data = str(p.readlink()).encode() if p.is_symlink() else b'' if p.is_dir() else p.read_bytes()
    h.update(kind + len(name).to_bytes(8, 'little') + name + len(data).to_bytes(8, 'little') + data)
print(h.hexdigest())
PY
}
start() {
  local candidate=$1 tag=$2
  "$candidate/run.sh" serve --state "$S" >"$OUT/serve-$tag.out" 2>"$OUT/serve-$tag.err" &
  PID=$!
  printf '%s\n' "$PID" >"$S/public/server.pid"
  for ((i=0; i<600; i++)); do
    if ! kill -0 "$PID" 2>/dev/null; then return 1; fi
    if [ -S "$S/public/mini.sock" ] && grep -Eq '^mini: host process [0-9]+$' "$OUT/serve-$tag.err"; then return 0; fi
    sleep 0.1
  done
  return 1
}
stop() {
  local child
  if CHILDREN=$(ps -o pid= --ppid "$PID"); then :; else CHILDREN=; fi
  kill -TERM "$PID"
  local stop_rc=0
  wait "$PID" || stop_rc=$?
  [ "$stop_rc" = 0 ] || [ "$stop_rc" = 143 ] || fail "server did not stop cleanly (exit $stop_rc)"
  PID=
  for child in $CHILDREN; do
    for ((i=0; i<100; i++)); do
      if ! kill -0 "$child" 2>/dev/null; then break; fi
      sleep 0.1
    done
    if kill -0 "$child" 2>/dev/null; then fail "Host child $child survived clean stop"; fi
  done
  rm -f "$S/public/server.pid"
}
# Explicit clock genesis makes F/G's shipped zero example usable; E ignores the
# added v2 parameters. These are operator inputs, not fixture or artifact edits.
jq '.clock.genesisNow = 1790000000 | .clock.maxStepSeconds = 300' \
  "$C0/genesis-params.example.json" >"$SCRATCH/params.json"
run init-n "$C0/run.sh" init --manifest "$C0/manifest.json" --params "$SCRATCH/params.json" --state "$S"
MINI=$(jq -r .mini "$C0/manifest.json") HOST=$(jq -r .host "$C0/manifest.json")
CONFIG=$S/deployment/pinned-config.json WS=$S/sponsor
start "$C0" n || fail "N did not open"
run sponsor "$C0/run.sh" sponsor --state "$S"
# Exercise stopped-only upgrade against a live host before any metadata changes.
store_hash >"$OUT/live-store-before.sha256"
sha256sum "$S/state.json" "$CONFIG" >"$OUT/live-bindings-before.sha256"
rc=0
"$OPERATOR" upgrade --manifest "$C1/manifest.json" --state "$S" >"$OUT/live-upgrade.out" 2>"$OUT/live-upgrade.err" || rc=$?
[ "$rc" != 0 ] && grep -q 'upgrade requires a stopped Host' "$OUT/live-upgrade.err" || fail "upgrade did not refuse running host"
sha256sum "$S/state.json" "$CONFIG" >"$OUT/live-bindings-after.sha256"
cmp -s "$OUT/live-bindings-before.sha256" "$OUT/live-bindings-after.sha256" || fail "live upgrade changed bindings"
store_hash >"$OUT/live-store-after.sha256"
cmp -s "$OUT/live-store-before.sha256" "$OUT/live-store-after.sha256" || fail "live upgrade changed Store"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SCRATCH/permit.json"
run birth "$MINI" workspace --action create --dir "$WS" --name upgrade-cell --storage declared --fields 2,3,4,5 --predicate "$SCRATCH/permit.json"
jq -e '.type == "confirmed"' "$WS/attempts/create-upgrade-cell/outcome.json" >/dev/null || fail "birth not confirmed"
cp "$WS/attempts/create-upgrade-cell/outcome.json" "$OUT/birth-receipt.json"
write() {
  local tag=$1 field=$2 value=$3
  jq -n --arg f "$field" --arg v "$value" '{type:"minidregg-workspace-proposal-v1",action:"invoke",
    targets:[{name:"upgrade-cell",payload:{type:"scalar",actions:[{type:"create",key:{type:"object",field:$f},value:$v}]}}]}' >"$SCRATCH/request.json"
  run "$tag-propose" "$MINI" workspace --action propose --dir "$WS" --request "$SCRATCH/request.json" --proposal-id "$tag"
  run "$tag-submit" "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/$tag/intent.json" --attempt "$WS/attempts/$tag"
  jq -e '.type == "confirmed"' "$WS/attempts/$tag/outcome.json" >/dev/null || fail "$tag not confirmed"
  cp "$WS/attempts/$tag/outcome.json" "$OUT/$tag-receipt.json"
}
# Different fields retain every scalar value, rather than overwriting a witness.
write scalar-1 2 1
write scalar-2 3 7000000001
write scalar-3 4 -19
run clock-init "$MINI" clock --action init --dir "$S/clock" --host "$HOST" --config "$CONFIG" --socket "$S/public/mini.sock" \
  --key "$S/keys/clock.key" --subject "$(jq -r .clock.subject "$S/genesis-params.json")" --capability "$(jq -r .clock.tickCapabilityId "$S/genesis-params.json")"
run clock-view-before "$MINI" clock --action view --workspace "$S/clock"
TICK=$(jq -er '.now | tonumber + 1 | tostring' "$OUT/clock-view-before.out")
run clock-tick "$MINI" clock --action tick --workspace "$S/clock" --now "$TICK" --slot 123
jq -e '.type == "confirmed"' "$OUT/clock-tick.out" >/dev/null || fail "clock tick not confirmed"
run certify "$MINI" checkpoint --action certify --workspace "$WS" --control "$(jq -r .factoryControllerCapability "$S/genesis-params.json")"
jq -e '.type == "confirmed"' "$OUT/certify.out" >/dev/null || fail "certify not confirmed"
run read-n "$MINI" workspace --action read --dir "$WS" --name upgrade-cell
for pair in '2 1' '3 7000000001' '4 -19'; do
  read -r field value <<<"$pair"
  jq -e --arg f "$field" --arg v "$value" 'any(.cell.entries[]; .key.field == $f and .value == $v)' "$OUT/read-n.out" >/dev/null || fail "N value field $field does not equal $value"
done
run clock-n "$MINI" clock --action view --workspace "$S/clock"
run checkpoint-n "$MINI" checkpoint --action view --workspace "$WS"
stop
run receipts-n "$MINI" store audit --host "$HOST" --config "$CONFIG" --receipts "$OUT/receipts-n.bin"
[ -s "$OUT/receipts-n.bin" ] || fail "N audit returned no receipts"
# Plant copies this driver and inserts its seed mutation immediately here.
store_hash >"$OUT/store-before.sha256"
jq -S 'del(.storageBinary,.signatureBinary)' "$CONFIG" >"$OUT/semantic-config-before.json"
run upgrade "$OPERATOR" upgrade --manifest "$C1/manifest.json" --state "$S"
jq -S 'del(.storageBinary,.signatureBinary)' "$CONFIG" >"$OUT/semantic-config-after.json"
cmp -s "$OUT/semantic-config-before.json" "$OUT/semantic-config-after.json" || fail "upgrade changed semantic configuration"
store_hash >"$OUT/store-after-upgrade.sha256"
cmp -s "$OUT/store-before.sha256" "$OUT/store-after-upgrade.sha256" || fail "upgrade touched Store"
MINI=$(jq -r .mini "$C1/manifest.json") HOST=$(jq -r .host "$C1/manifest.json")
# Workspaces cache the local authoring Host; rebind only that client path.
for workspace in "$WS/workspace.json" "$S/clock/workspace.json"; do
  jq --arg h "$HOST" '.host = $h' "$workspace" >"$SCRATCH/workspace.json"
  mv "$SCRATCH/workspace.json" "$workspace"
done
opened=false
if start "$C1" n1; then
  # A spawned Host is not proof that its Store opened. A signed read forces the
  # receiving path and provides the actual open verdict.
  if timeout 30 "$MINI" workspace --action read --dir "$WS" --name upgrade-cell \
      >"$OUT/read-n1.out" 2>"$OUT/read-n1.err"; then opened=true; fi
fi
if [ "$opened" = true ]; then
  run clock-n1 "$MINI" clock --action view --workspace "$S/clock"
  run checkpoint-n1 "$MINI" checkpoint --action view --workspace "$WS"
  for view in read clock checkpoint; do
    cmp -s "$OUT/$view-n.out" "$OUT/$view-n1.out" || fail "$view values differ byte-for-byte under N1"
  done
  run receipts-n1 "$MINI" store audit --host "$HOST" --config "$CONFIG" --receipts "$OUT/receipts-n1.bin"
  cmp -s "$OUT/receipts-n.bin" "$OUT/receipts-n1.bin" || fail "historical receipts differ byte-for-byte under N1"
  write n1-write 5 2301
  run read-new "$MINI" workspace --action read --dir "$WS" --name upgrade-cell
  jq -e 'any(.cell.entries[]; .key.field == "5" and .value == "2301")' "$OUT/read-new.out" >/dev/null || fail "N1 new write did not read back"
  stop
  OUTCOME=reopen VERIFIED=true
else
  if kill -0 "$PID" 2>/dev/null; then stop
  else
    if wait "$PID"; then fail "N1 exited successfully without opening"; fi
    PID=
  fi
  store_hash >"$OUT/store-after-refusal.sha256"
  cmp -s "$OUT/store-before.sha256" "$OUT/store-after-refusal.sha256" || fail "N1 failed open changed Store bytes"
  refusal='durable store refused: this Store was born in another epoch ('
  cat "$OUT/serve-n1.err" >"$OUT/open-errors.txt"
  if [ -f "$OUT/read-n1.err" ]; then cat "$OUT/read-n1.err" >>"$OUT/open-errors.txt"; fi
  grep -F "$refusal" "$OUT/open-errors.txt" >"$OUT/refusal.txt" || fail "N1 open failed without a named epoch refusal: $(awk '/^minidregg-host:/ {host=$0} NF {last=$0} END {print (host ? host : last)}' "$OUT/open-errors.txt")"
  grep -Eq '(state-key codec|cell schema references|log tags|history accumulator|command codecs): Store .+, this Host .+\); re-genesis the world' "$OUT/refusal.txt" || fail "epoch refusal did not name differing parts"
  OUTCOME=refuse VERIFIED=true
fi
[ "$OUTCOME" = "$EXPECTED" ] || fail "outcome $OUTCOME differs from expected $EXPECTED (history verified=$VERIFIED)"
result "expected $EXPECTED; observed $OUTCOME"
echo "HOST-UPGRADE PASS outcome=$OUTCOME expected=$EXPECTED" | tee "$OUT/verdict.txt"
