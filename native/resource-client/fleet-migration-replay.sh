#!/bin/sh
# Replays the command transcript of Pug's agent harness (helm, akapug/helm) through
# `dregg-client-sign` -> `mini fleet-sign` on a fresh scratch Store, and checks every
# call against its stated expectation: a mapped call answers one JSON object with the
# named properties; an unmappable one exits non-zero, prints nothing on stdout and names
# its reason on stderr. Each line carries its provenance: OBSERVED (read in helm's code,
# file:line) or INFERRED (Bread's tool contract / Pug-authored commits, not seen invoked).
# The checker is then run against planted wrong expectations and must go red on each.
#
# usage: fleet-migration-replay.sh HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 ROOT=$5
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
case "$ROOT" in /*) ;; *) echo 'replay path must be absolute' >&2; exit 2;; esac
[ ! -e "$ROOT" ] && [ ! -L "$ROOT" ] || { echo 'replay directory already exists' >&2; exit 2; }
command -v jq >/dev/null 2>&1 || { echo 'jq is required' >&2; exit 2; }
mkdir -m 700 "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
OUT="$ROOT/evidence"
mkdir -m 700 "$OUT"
FIX="$ROOT/fixture"
LOG="$OUT/transcript.log"
: >"$LOG"

SERVER_PID=
stop_server() {
  if [ -n "$SERVER_PID" ] && kill -0 "$SERVER_PID" 2>/dev/null; then
    kill "$SERVER_PID" 2>/dev/null || true
  fi
  SERVER_PID=
}
trap stop_server EXIT INT TERM

"$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$FIX" \
  >"$OUT/fixture.stdout" 2>"$OUT/fixture.stderr"
SERVER_PID=$(cat "$FIX/public/server.pid")
SOCKET="$FIX/public/mini.sock"
FEE=$(jq -er '.tariffBase | tostring' "$FIX/operator.json")

# The shim is the file a harness runs; every call below goes through it.
SHIM="$HERE/dregg-client-sign"
export MINI_BIN="$MINI"
# Operator side (where the sponsor's workspace is) and the seat's own environment.
OPERATOR_HOME="$ROOT/fleet-home"
SPONSOR="$FIX/sponsor"
# The environment helm exports to EVERY signer subprocess (cell.py ENV_MAP + build_env;
# chat.py _env_extra): the Bread node URL and bearer under both names, the exempt-class
# signal, the seat's profile under both names. MINI_FLEET_HOME is the one addition.
BREAD_NODE=http://127.0.0.1:8898
SEAT_ENV="DREGG_NODE_URL=$BREAD_NODE MELD_NODE_URL=$BREAD_NODE DREGG_API_TOKEN=replay-token-not-a-secret MELD_NODE_TOKEN=replay-token-not-a-secret DREGG_COORDINATION_EXEMPT=1 DREGG_PROFILE=codex MELD_AGENT_PROFILE=codex MINI_FLEET_HOME=$OPERATOR_HOME"
OPERATOR_ENV="MINI_FLEET_HOME=$OPERATOR_HOME MINI_FLEET_SPONSOR=$SPONSOR"
mkdir -m 700 "$OPERATOR_HOME"

one_object() { jq -s -e 'length == 1' "$1" >/dev/null 2>&1; }

# check ID EXPECT -> 0 when the recorded outcome of ID meets EXPECT
#   ok:JQFILTER      exit 0, stdout exactly one JSON object, the filter is true on it
#   refuse:SUBSTR    exit non-zero, stdout empty, stderr contains SUBSTR (basic regex)
check() {
  id=$1 expect=$2
  rc=$(cat "$OUT/$id.rc")
  case "$expect" in
    ok:*)
      [ "$rc" -eq 0 ] && one_object "$OUT/$id.out" && jq -e "${expect#ok:}" "$OUT/$id.out" >/dev/null 2>&1 ;;
    refuse:*)
      [ "$rc" -ne 0 ] && [ ! -s "$OUT/$id.out" ] && grep -q -- "${expect#refuse:}" "$OUT/$id.err" ;;
    *) return 1 ;;
  esac
}

N=0
# call ID PROVENANCE EXPECT ENVSPEC -- ARGV...   (ARGV is run through the shim)
call() {
  id=$1 prov=$2 expect=$3 envspec=$4; shift 5
  N=$((N + 1))
  rc=0
  # shellcheck disable=SC2086
  env $envspec "$SHIM" "$@" >"$OUT/$id.out" 2>"$OUT/$id.err" || rc=$?
  printf '%s\n' "$rc" >"$OUT/$id.rc"
  {
    printf '## %s  [%s]\n' "$id" "$prov"
    printf '$ env %s dregg-client-sign' "$envspec"; printf ' %s' "$@"; printf '\n'
    printf 'exit %s\n' "$rc"
    printf 'stdout: '; cat "$OUT/$id.out"; [ -s "$OUT/$id.out" ] || printf '(empty)\n'
    printf 'stderr:\n'; sed 's/^/  /' "$OUT/$id.err"
    printf 'expect: %s\n\n' "$expect"
  } >>"$LOG"
  if check "$id" "$expect"; then
    printf '%s\tPASS\t%s\n' "$id" "$expect" >>"$OUT/results.tsv"
  else
    printf '%s\tRED\t%s\n' "$id" "$expect" >>"$OUT/results.tsv"
    echo "REPLAY RED at $id: expected $expect" >&2
    echo "  exit $rc; stdout: $(cat "$OUT/$id.out")" >&2
    sed 's/^/  stderr: /' "$OUT/$id.err" >&2
    exit 1
  fi
}
printf 'id\tresult\texpect\n' >"$OUT/results.tsv"

TOPIC_CHAT=helm.chat   # chat.py:131 CHAT_TOPIC
TOPIC_LAND=helm.land   # landreq.py:512 LAND_TOPIC
# chat.py:1107 digest_payload: "chat:b2b:" + blake2b-256 hex (73 bytes); landreq.py:514 LAND_TAG (78 bytes)
CHAT_PAYLOAD=chat:b2b:$(printf 'hello from codex' | b2sum -l 256 | cut -d' ' -f1)
LAND_PAYLOAD=helm.land:b2b:$(printf 'lane/x branch/y' | b2sum -l 256 | cut -d' ' -f1)

# ---- operator side: the sponsor admits the seats (INFERRED: Bread's first-use join cannot run on a seat)
call O1-join-lead INFERRED 'ok:.joined and .materialized and .balance == 20000' "$OPERATOR_ENV" -- join --profile lead --fund 20000
call O2-join-probe INFERRED 'ok:.joined and .balance == 5000' "$OPERATOR_ENV" -- join --profile probe --fund 5000
# T01 helm's first join of a seat: `join --profile SEAT --fund 0` (HELM_CHAT_JOIN_FUND default "0")
call T01-join-fund0 'OBSERVED chat.py:1350' 'ok:.joined and .materialized and .balance == 0 and (.cell | test("^[0-9]+$"))' "$OPERATOR_ENV DREGG_PROFILE=codex" -- join --profile codex --fund 0
CODEX=$(jq -er .cell "$OUT/T01-join-fund0.out")
LEAD=$(jq -er .cell "$OUT/O1-join-lead.out")
# T02 the same call from the seat's own environment (no sponsor workspace there): first-use refuses by name,
# a profile that already joined answers its balance (helm re-runs join after a cache miss, chat.py:1349)
call T02a-join-seat-no-sponsor 'OBSERVED chat.py:1350' 'refuse:needs the sponsor' "$SEAT_ENV" -- join --profile newseat --fund 0
call T02b-join-again 'OBSERVED chat.py:1350' 'ok:.joined and (.materialized | not) and .cell == "'"$CODEX"'" and .balance == 0' "$SEAT_ENV" -- join --profile codex --fund 0
# T03 a send before the seat holds the tariff (helm assumed the exempt class: fee 0): refused by the Host's book
call T03-send-unfunded 'OBSERVED chat.py:1413' 'refuse:bookRefused\|not admitted\|insufficient' "$SEAT_ENV" -- send --profile codex --to "$CODEX" --topic "$TOPIC_CHAT" "$CHAT_PAYLOAD"
# T04 funding is a transfer from a funded profile (INFERRED: Bread's `transfer` verb, Pug-authored aeca5dea1)
call T04-transfer-fund-seat INFERRED 'ok:.transferred and .committed and .amount == 2000 and .to == "'"$CODEX"'"' "$OPERATOR_ENV" -- transfer --profile lead --to "$CODEX" --amount 2000
# T05 helm's chat send: `send --profile SEAT --to OWN_CELL --topic helm.chat PAYLOAD`, payload one argv word
call T05-send-chat 'OBSERVED chat.py:1412-1414' 'ok:.sent and .agent_cell == "'"$CODEX"'" and .to == "'"$CODEX"'" and .topic == "helm.chat" and .payload == "'"$CHAT_PAYLOAD"'" and .sequence == 1 and .finality == "accepted" and (.turn_hash | test("^[0-9a-f]{64}$")) and (.receipt_hash | test("^[0-9a-f]{64}$")) and (.chain_index | type == "number")' "$SEAT_ENV" -- send --profile codex --to "$CODEX" --topic "$TOPIC_CHAT" "$CHAT_PAYLOAD"
# T06 the same call on the land topic (chat.emit_coordination_turn, landreq.py:1232)
call T06-send-land 'OBSERVED landreq.py:1232 via chat.py:1413' 'ok:.sent and .topic == "helm.land" and .sequence == 1' "$SEAT_ENV" -- send --profile codex --to "$CODEX" --topic "$TOPIC_LAND" "$LAND_PAYLOAD"
# T07 helm's second attempt (chat.py:1411 loop) is a fresh send, not a retry: a second event, sequence 2
call T07-send-chat-again 'OBSERVED chat.py:1411' 'ok:.sent and .sequence == 2' "$SEAT_ENV" -- send --profile codex --to "$CODEX" --topic "$TOPIC_CHAT" "$CHAT_PAYLOAD"
# T08 what Bread's tool also took: no --to, payload words (INFERRED, dregg-client-sign USAGE)
call T08-send-words INFERRED 'ok:.sent and .payload == "hello from codex"' "$SEAT_ENV" -- send --profile codex hello from codex
# T09 transfer (INFERRED)
call T09-transfer INFERRED 'ok:.transferred and .committed and .amount == 5' "$SEAT_ENV" -- transfer --profile codex --to "$LEAD" --amount 5
# T10 receipts (INFERRED: helm reads these over HTTP, cell.py:300-303, never through the signer)
SEND_TX=$(jq -er .turn_hash "$OUT/T05-send-chat.out")
call T10a-receipt-by-hash INFERRED 'ok:.found and .turn_hash == "'"$SEND_TX"'" and .finality == "accepted"' "$SEAT_ENV" -- receipt --profile codex --turn-hash "$SEND_TX"
call T10b-receipt-head INFERRED 'ok:.head.turns == "5"' "$SEAT_ENV" -- receipt --profile codex --head

# ---- shapes Bread's signer took (or helm passes) that Mini refuses, each by name
# T11 verbs of helm's legacy a2a binary: helm `cell status` runs `roster --json` (cell.py:881) and
# `helm cell accept|recv|heartbeat|roster` pass through verbatim (cell.py:950, PASS_VERBS)
call T11a-roster-json 'OBSERVED cell.py:881' "refuse:unknown verb 'roster'" "$SEAT_ENV" -- roster --json
call T11b-accept 'OBSERVED cell.py:950' "refuse:unknown verb 'accept'" "$SEAT_ENV" -- accept
call T11c-recv 'OBSERVED cell.py:950' "refuse:unknown verb 'recv'" "$SEAT_ENV" -- recv
call T11d-heartbeat 'OBSERVED cell.py:950' "refuse:unknown verb 'heartbeat'" "$SEAT_ENV" -- heartbeat
# T12 a planted verb no tool ever had
call T12-planted-unknown-verb PLANTED "refuse:unknown verb 'frobnicate'" "$SEAT_ENV" -- frobnicate --profile codex x
# T13 a stale cell cache from Bread: the 64-hex cell id helm cached from a Bread join
HEX64=$(printf 'ab%.0s' $(seq 32))
call T13a-send-bread-cell 'OBSERVED chat.py:1413 (value from a Bread join)' 'refuse:Bread cell id' "$SEAT_ENV" -- send --profile codex --to "$HEX64" --topic "$TOPIC_CHAT" x
call T13b-transfer-bread-cell INFERRED 'refuse:Bread cell id' "$SEAT_ENV" -- transfer --profile codex --to "$HEX64" --amount 1
call T13c-send-other-account INFERRED 'refuse:another account' "$SEAT_ENV" -- send --profile codex --to "$LEAD" x
# T14 Bread flags (INFERRED, dregg-client-sign USAGE)
call T14a-node-url-http INFERRED 'refuse:no HTTP ingress' "$SEAT_ENV" -- send --profile codex --node-url "$BREAD_NODE" x
call T14b-token-file INFERRED 'refuse:no bearer token' "$SEAT_ENV" -- send --profile codex --token-file /dev/null x
call T14c-token-argv INFERRED 'refuse:no bearer token' "$SEAT_ENV" -- send --profile codex --token abc x
call T14d-accept-tentative INFERRED 'refuse:one commitment level' "$SEAT_ENV" -- transfer --profile codex --to "$LEAD" --amount 1 --accept-tentative
call T14e-fund-on-send INFERRED 'refuse:no faucet' "$SEAT_ENV" -- send --profile codex --fund 100 x
call T14f-fund-on-transfer INFERRED 'refuse:no faucet' "$SEAT_ENV" -- transfer --profile codex --to "$LEAD" --amount 1 --fund 100
call T14g-never-joined 'OBSERVED chat.py:1413 (profile from a seat that never joined)' 'refuse:has not joined' "$SEAT_ENV" -- send --profile ghost x
# T15 the ambient Bread environment is named, not silently read: stderr of an accepted call
grep -q 'DREGG_NODE_URL is set and not read' "$OUT/T05-send-chat.err"
grep -q 'DREGG_API_TOKEN is set and not read' "$OUT/T05-send-chat.err"
grep -q 'DREGG_COORDINATION_EXEMPT is set and not read' "$OUT/T05-send-chat.err"
printf 'T15-env-notice\tPASS\tstderr of T05 names DREGG_NODE_URL, DREGG_API_TOKEN, DREGG_COORDINATION_EXEMPT\n' >>"$OUT/results.tsv"

# ---- conservation: the transcript's turns cost what the tariff says and moved what it says
call Z1-balance-codex INFERRED 'ok:.balance == '"$((2000 - 5 * FEE - 5))" "$SEAT_ENV" -- join --profile codex --fund 0

# ---- the harness itself: helm's unmodified chat._sign_send with the shim as HELM_CELL_BIN (optional:
# needs HELM_SRC, a directory holding a read-only copy of the `helm/` package, and python3).
# This probes the HARNESS side: it records what helm concludes from Mini's answers.
if [ -n "${HELM_SRC:-}" ]; then
  PROBE_RC=0
  PYTHONDONTWRITEBYTECODE=1 python3 "$HERE/fleet-migration-helm-probe.py" "$HELM_SRC" "$SHIM" "$OPERATOR_HOME" probe "$MINI" \
    >"$OUT/helm-probe.json" 2>"$OUT/helm-probe.err" || PROBE_RC=$?
  printf '%s\n' "$PROBE_RC" >"$OUT/helm-probe.rc"
  # helm must conclude SUCCESS on its first attempt, and exactly ONE turn must land
  # (cv 01a11476-1c59: without receipt_hash helm judged the send failed, re-sent, and two committed).
  N=$((N + 1))
  if [ "$PROBE_RC" -eq 0 ] && jq -e '.diag == null and .info.sent == true and (.info.receipt_hash | test("^[0-9a-f]{64}$"))' \
      "$OUT/helm-probe.json" >/dev/null 2>&1; then
    printf '%s\tPASS\t%s\n' Z2a-helm-concludes-sent 'helm _sign_send returns info, no diag' >>"$OUT/results.tsv"
  else
    printf '%s\tRED\t%s\n' Z2a-helm-concludes-sent 'helm _sign_send returns info, no diag' >>"$OUT/results.tsv"
    echo "REPLAY RED at Z2a: helm did not conclude sent: $(cat "$OUT/helm-probe.json")" >&2
    RED=1
  fi
  call Z2-probe-turns-landed INFERRED 'ok:.head.turns == "1"' "MINI_FLEET_HOME=$OPERATOR_HOME" -- receipt --profile probe --head
  [ -z "${RED:-}" ] || exit 1
fi
stop_server

# ---- the checker must go red on planted wrong expectations (it ran green on the right ones above)
plant() {
  name=$1 id=$2 expect=$3
  if check "$id" "$expect"; then
    printf '%s\tPLANT-NOT-RED\t%s\n' "$name" "$expect" >>"$OUT/results.tsv"
    echo "PLANT $name: the checker accepted a wrong expectation ($expect on $id)" >&2; exit 1
  fi
  printf '%s\tRED-AS-REQUIRED\t%s on %s\n' "$name" "$expect" "$id" >>"$OUT/results.tsv"
}
plant wrong-ok-filter T05-send-chat 'ok:.sent == false'
plant wrong-sequence T05-send-chat 'ok:.sequence == 2'
plant wrong-refusal-reason T12-planted-unknown-verb 'refuse:no such option'
plant accept-expected-of-refusal T12-planted-unknown-verb 'ok:true'
plant refuse-expected-of-accept T05-send-chat 'refuse:unknown verb'
plant unknown-verb-accepted-would-fail T12-planted-unknown-verb 'ok:.sent'

sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$SHIM" >"$OUT/binaries.sha256"
jq -n --arg calls "$N" --arg fee "$FEE" '{type:"minidregg-fleet-migration-replay-v1", calls:($calls|tonumber), fee:$fee, result:"pass"}' >"$OUT/summary.json"
printf '%s\n' "$OUT"
