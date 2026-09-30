#!/bin/sh
# Read-only signed boundary checks for a freshly provisioned hosted pair.
set -eu
umask 077

if [ "$#" -ne 3 ]; then
  echo "usage: $0 MINIDREGG_HOST HOSTED_PROVISION_DIRECTORY NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HOST=$1 PROVISION=$2 EVIDENCE=$3
MINI=${MINI:?set MINI to the source-matched native client}
[ -x "$HOST" ] && [ -x "$MINI" ] && [ -d "$PROVISION" ] || exit 2
[ ! -e "$EVIDENCE" ] || { echo "refusing existing evidence directory" >&2; exit 2; }
mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
PROVISION=$(CDPATH='' cd -- "$PROVISION" && pwd)
CONFIG=$PROVISION/deployment/pinned-config.json
SOCKET=$EVIDENCE/host.sock
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$EVIDENCE/host.stdout" 2>"$EVIDENCE/host.stderr" &
SERVICE_PID=$!
cleanup() { kill "$SERVICE_PID" 2>/dev/null || :; wait "$SERVICE_PID" 2>/dev/null || :; }
trap cleanup EXIT HUP INT TERM
tick=0
until [ -S "$SOCKET" ]; do
  kill -0 "$SERVICE_PID" 2>/dev/null || exit 1
  tick=$((tick + 1)); [ "$tick" -lt 120 ] || exit 1; sleep 1
done
observation_hex=$(printf '%s' 'observation refused' | od -An -tx1 -v | tr -d ' \n')
query() {
  label=$1 subject=$2 target=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg subject "$subject" --arg target "$target" --arg cap "$capability" \
    --arg nonce "$nonce" \
    '{subject:$subject,nonce:$nonce,purpose:{type:"query",kind:"object",
      target:$target,view:"resource"},
      grants:[{kind:"object",target:$target,capability:$cap}]}' \
    >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout" 2>"$EVIDENCE/$label.stderr"
}
deny_query() {
  label=$1
  shift
  if query "$label" "$@"; then
    echo "unauthorized read succeeded: $label" >&2; exit 1
  fi
  [ -s "$EVIDENCE/$label/signed-observation.bin" ] &&
    [ ! -e "$EVIDENCE/$label/view.json" ] &&
    grep -Fq 'host refused query' "$EVIDENCE/$label.stderr" &&
    grep -Fq "$observation_hex" "$EVIDENCE/$label.stderr" || {
      echo "denial lacked native observation refusal: $label" >&2; exit 1;
    }
}
deny_query b-unrelated 10 7003 98 "$PROVISION/tool-b.key" 65001
deny_query a-unrelated 8 7803 96 "$PROVISION/tool.key" 65002
query b-workroom 10 8001 98 "$PROVISION/tool-b.key" 65003
query a-workroom 8 8001 96 "$PROVISION/tool.key" 65004
expected=$(jq -er '.cell.root' "$PROVISION/b-content-read/view.json")
for label in b-workroom a-workroom; do
  jq -e --arg root "$expected" \
    '.cell.document == "8001" and .cell.entries == [] and .cell.root == $root' \
    "$EVIDENCE/$label/view.json" >/dev/null
done
printf '%s\n' "$EVIDENCE/a-workroom/view.json" "$EVIDENCE/b-workroom/view.json"
