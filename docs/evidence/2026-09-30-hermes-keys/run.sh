#!/bin/bash
# Hermes provider keys: per-friend credentials in hosted custody, the
# operator's pool behind the purse, and a homelab row, through the REAL
# controller reserve path (signed Mini reserve/settle on a fresh Store).
#
# usage: run.sh BIN_DIR RUN_DIR
#   BIN_DIR holds minidregg-host-p2, mini, grain-runtime,
#   mini-hermes-test-provider, minidregg-link-sqlite-store and
#   minidregg-credential-signature-verifier (copies, not links).
#
# Three fresh Stores, one grain each (tasks 74601..74604), run one after the
# other: B (friend B's key, then B revokes), A (friend A's key, caps), and C
# (no key: no-route fallthrough refused, then the pool, then the homelab row,
# then out of credit). The two upstreams are `mini-hermes-test-provider
# --route-probe`, which logs the SHA-256 of the Authorization value it got.
# The Hermes worker is the hold fixture: it keeps one prompt (and so one
# gateway lease) open while this script sends Chat Completions requests to
# the gateway with the prompt's own token, exactly as Hermes would.
set -euo pipefail
umask 077
[[ $# == 2 ]] || { echo 'usage: run.sh BIN_DIR RUN_DIR' >&2; exit 2; }
BIN=$(cd "$1" && pwd)
RUN=$2
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
HOST=$BIN/minidregg-host-p2 MINI=$BIN/mini GRAIN=$BIN/grain-runtime PROBE=$BIN/mini-hermes-test-provider
BASE=74600
TASK=$((BASE + 1)) PTASK=$((BASE + 4))
UNIT=mini-grain-controller@$TASK
UP=18931 UP2=18932 GW=18941
[[ ! -e $RUN ]] || { echo "refusing to reuse $RUN" >&2; exit 2; }
[[ $(systemctl --user show -p LoadState --value "$UNIT.service") == not-found ]] ||
  { echo "$UNIT exists" >&2; exit 2; }
mkdir -m 700 "$RUN"
RUN=$(cd "$RUN" && pwd)
EV=$RUN/evidence
mkdir -m 700 "$EV" "$RUN/etc" "$RUN/inputs"
: >"$EV/upstream-openrouter.log"; : >"$EV/upstream-homelab.log"
TABLE_TSV=$EV/table.tsv
printf 'store\tstep\tcaller\trow\thttp\tcode\tupstream_auth\texpected_auth\tpurse_after\texpected_purse\tverdict\n' >"$TABLE_TSV"

PIDS=()
SERVE_PID=
CONNECTOR_PID=
cleanup() {
  set +e
  if [[ -n $CONNECTOR_PID ]]; then exec 3>&- 2>/dev/null; kill "$CONNECTOR_PID" 2>/dev/null; wait "$CONNECTOR_PID" 2>/dev/null; fi
  systemctl --user stop "$UNIT.service" >/dev/null 2>&1
  systemctl --user reset-failed "$UNIT.service" >/dev/null 2>&1
  for unit in $(systemctl --user list-units --all --plain --no-legend "mini-grain-t${TASK}-*" | awk '{print $1}'); do
    systemctl --user stop "$unit" >/dev/null 2>&1; systemctl --user reset-failed "$unit" >/dev/null 2>&1
  done
  if [[ -n $SERVE_PID ]]; then kill "$SERVE_PID" 2>/dev/null; wait "$SERVE_PID" 2>/dev/null; fi
  for pid in "${PIDS[@]}"; do kill "$pid" 2>/dev/null; wait "$pid" 2>/dev/null; done
}
trap cleanup EXIT
fail() { echo "FAIL: $*" >&2; exit 1; }
sha() { printf '%s' "$1" | sha256sum | cut -d' ' -f1; }

# ---- upstreams: an "OpenRouter" stand-in and a "homelab" --------------------
"$PROBE" "127.0.0.1:$UP" "$EV/upstream-openrouter.log" --route-probe >/dev/null 2>"$EV/upstream-openrouter.stderr" &
PIDS+=($!)
"$PROBE" "127.0.0.1:$UP2" "$EV/upstream-homelab.log" --route-probe >/dev/null 2>"$EV/upstream-homelab.stderr" &
PIDS+=($!)
for port in $UP $UP2; do
  for _ in $(seq 1 100); do ss -ltn | grep -q "127.0.0.1:$port " && break; sleep 0.1; done
  ss -ltn | grep -q "127.0.0.1:$port " || fail "upstream $port did not listen"
done

# ---- the box's credential store and the operator's provider table ----------
CRED=$RUN/credentials CKEY=$RUN/etc/credentials.key TABLE=$RUN/etc/providers.json
mkdir -m 700 "$CRED"
head -c 32 /dev/urandom >"$CKEY"; chmod 600 "$CKEY"
table() {  # ORDER... : rows for model shared-model, first listed wins
  local rows=() name
  for name in "$@"; do
    case $name in
      openrouter) rows+=("{\"name\":\"openrouter\",\"endpoint\":\"http://127.0.0.1:$UP/v1/chat/completions\",\"kind\":\"openai-compatible\",\"models\":[\"shared-model\"],\"credential\":\"user\"}") ;;
      pool) rows+=("{\"name\":\"pool\",\"endpoint\":\"http://127.0.0.1:$UP/v1/chat/completions\",\"kind\":\"openai-compatible\",\"models\":[\"shared-model\"],\"credential\":\"pool\"}") ;;
      homelab) rows+=("{\"name\":\"homelab\",\"endpoint\":\"http://127.0.0.1:$UP2/v1/chat/completions\",\"kind\":\"openai-compatible\",\"models\":[\"shared-model\"],\"credential\":\"none\"}") ;;
    esac
  done
  local IFS=,
  printf '{"type":"mini-provider-table-v1","providers":[%s]}\n' "${rows[*]}" >"$RUN/inputs/providers.json"
  sudo install -o root -g root -m 0644 "$RUN/inputs/providers.json" "$TABLE"
  cp "$RUN/inputs/providers.json" "$EV/providers-$(IFS=-; echo "$*").json"
}
table openrouter pool homelab
KEYFLAGS=(--providers "$TABLE" --credentials "$CRED" --credentials-key "$CKEY")

# ---- fake friend tokens: never in any log, journal or store -----------------
TOKEN_A="sk-or-v1-FAKE-friendA-$(head -c 12 /dev/urandom | od -An -tx1 | tr -d ' \n')"
TOKEN_B="sk-or-v1-FAKE-friendB-$(head -c 12 /dev/urandom | od -An -tx1 | tr -d ' \n')"
TOKEN_POOL="sk-or-v1-FAKE-pool-$(head -c 12 /dev/urandom | od -An -tx1 | tr -d ' \n')"
AUTH_A=$(sha "Bearer $TOKEN_A") AUTH_B=$(sha "Bearer $TOKEN_B") AUTH_POOL=$(sha "Bearer $TOKEN_POOL")
printf 'A\tsha256:%s\nB\tsha256:%s\npool\tsha256:%s\n' "$AUTH_A" "$AUTH_B" "$AUTH_POOL" >"$EV/expected-auth.tsv"
printf '%s\n%s\n%s\n' "$TOKEN_A" "$TOKEN_B" "$TOKEN_POOL" >"$RUN/inputs/fake-tokens"

# ---- one Store with one grain ------------------------------------------------
S= BOOT= CONFIG= SOCK= STATE= JOURNAL= WORK=
store_up() {  # NAME
  S=$RUN/$1; BOOT=$S/boot
  mkdir -m 700 "$S"
  ACCEPTANCE_TASK_BASE=$BASE PROVIDER_BOOTSTRAP=1 BOOTSTRAP_ONLY=1 MINI=$MINI GRAIN=$GRAIN \
    STORE_BINARY=$BIN/minidregg-link-sqlite-store \
    SIGNATURE_BINARY=$BIN/minidregg-credential-signature-verifier \
    "$REPO/native/grain-runtime/acceptance.sh" "$HOST" "$BOOT" >"$S/bootstrap.log" 2>&1 ||
    { tail -20 "$S/bootstrap.log" >&2; fail "$1: bootstrap"; }
  CONFIG=$BOOT/deployment/continuity-config.json
  jq --argjson p "$PTASK" '.continuityProviderResourceId = $p' \
    "$BOOT/deployment/pinned-config.json" >"$CONFIG"
  mkdir -m 700 "$S/session"
  SOCK=$S/session/host.sock
  "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
    >"$S/session/serve.stdout" 2>"$S/session/serve.stderr" &
  SERVE_PID=$!
  for _ in $(seq 1 240); do [[ -S $SOCK ]] && break; kill -0 "$SERVE_PID" || fail "$1: serve died"; sleep 0.5; done
  [[ -S $SOCK ]] || fail "$1: serve socket"
}
store_down() {
  systemctl --user stop "$UNIT.service" >/dev/null 2>&1 || :
  systemctl --user reset-failed "$UNIT.service" >/dev/null 2>&1 || :
  kill "$SERVE_PID" 2>/dev/null || :; wait "$SERVE_PID" 2>/dev/null || :; SERVE_PID=
}

# A friend's workspace: only its key and claimed subject matter to `mini key`.
friend() {  # NAME SUBJECT
  local w=$RUN/friends/$1
  mkdir -p -m 700 "$RUN/friends"
  "$MINI" keygen --secret "$RUN/friends/$1.key" --public "$RUN/friends/$1.pub" >/dev/null
  "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" \
    --key "$RUN/friends/$1.key" --subject "$2" --dir "$w" >/dev/null
  od -An -tx1 -v "$RUN/friends/$1.pub" | tr -d ' \n'
}
key() {  # LABEL ARGS... (output kept as evidence)
  local label=$1; shift
  "$MINI" key "$@" "${KEYFLAGS[@]}" >"$EV/key-$label.json" 2>"$EV/key-$label.stderr"
}

controller_up() {  # PROVIDER_EXTRA_JSON RESERVE CHARGE
  STATE=$S/state JOURNAL=$S/state/journal.json WORK=$S/work
  mkdir -m 700 "$STATE" "$WORK" "$WORK/.hermes" "$S/runtime" "$S/launcher"
  cp "$REPO/deploy/grain-host/bwrap" "$S/launcher/bwrap"
  rustc -O --edition 2021 -o "$S/launcher/launch-gate" "$REPO/deploy/grain-host/launch-gate.rs" 2>"$S/launch-gate-build.log"
  cp "$REPO/native/grain-runtime/fixture/hermes-acp" "$S/runtime/hermes-acp"
  chmod 700 "$S/launcher/bwrap" "$S/runtime/hermes-acp"
  jq -n --arg mini "$MINI" --arg host "$HOST" --arg cfg "$CONFIG" --arg sock "$SOCK" \
    --arg b "$BOOT" --arg state "$STATE" --arg cwd "$S" --arg work "$WORK" --arg rt "$S/runtime" \
    --arg launcher "$S/launcher/bwrap" --arg table "$TABLE" --arg cred "$CRED" --arg ckey "$CKEY" \
    --arg t "$TASK" --arg tt "$((BASE + 2))" --arg pub "$((BASE + 3))" --arg pt "$PTASK" \
    --arg gw "127.0.0.1:$GW" --arg reserve "$2" --arg charge "$3" --argjson extra "$1" '
    {mini:$mini,host:$host,hostConfig:$cfg,hostSocket:$sock,custodyKey:($b+"/controller.key"),
     stateDir:$state,controlSocket:($state+"/control.sock"),cwd:$cwd,
     task:$t,subject:"7",capability:"71",queryCapability:"71",policyControlCapability:"72",
     toolTask:{task:$tt,subject:"8",capability:"81",queryCapability:"81",
       custodyKey:($b+"/tool.key"),parentCapability:"73",parentObserveCapability:"73",
       reserve:"2",charge:"1",
       allowedPublications:[{kind:"object",target:$pub,capability:"93",observeCapability:"93"}],
       allowedReads:[{name:"publication",kind:"object",target:$pub,observeCapability:"94",maxResultBytes:65536}]},
     providerTask:({task:$pt,subject:"9",capability:"101",queryCapability:"101",
       custodyKey:($b+"/provider.key"),parentCapability:"75",parentObserveCapability:"75",
       reserve:$reserve,charge:$charge,model:"shared-model",providers:$table,
       credentialsRoot:$cred,credentialsKey:$ckey,gatewayBind:$gw,
       maxRequestBytes:1048576,maxResponseBytes:8388608,timeoutSeconds:120,
       localFixtureHostNetwork:true} + $extra),
     commands:[{name:"hermes-acp",program:$launcher,
       args:["--workspace",$work,"--runtime-root",$rt,"--network","host","--",
         "/agent/hermes-acp","/workspace/acp-ready","/workspace/acp-release"],
       systemdScope:true,wallTimeSeconds:1500,reserve:"3",charge:"1"}]}' >"$S/controller.json"
  cp "$S/controller.json" "$EV/$(basename "$S")-controller.json"
  systemd-run --user --unit="$UNIT" --description="hermes-keys-evidence:$RUN" \
    --property=KillMode=control-group --property=RuntimeMaxSec=3600s \
    "$GRAIN" serve "$S/controller.json" >"$S/unit-start.log" 2>&1
  for _ in $(seq 1 600); do [[ -S $STATE/control.sock ]] && break; sleep 0.1; done
  [[ -S $STATE/control.sock ]] || fail "controller socket"
  mkfifo -m 600 "$S/connector.fifo"
  "$GRAIN" connect "$STATE/control.sock" <"$S/connector.fifo" >"$S/connector.log" 2>&1 &
  CONNECTOR_PID=$!
  exec 3>"$S/connector.fifo"
  printf 'attach soft\n' >&3
  wait_journal '.connection == "soft" and .pending == null' 600 || fail "soft attach"
  printf 'hermes route probe: hold this prompt open\n' >&3
  for _ in $(seq 1 1200); do [[ -e $WORK/acp-ready ]] && break; sleep 0.5; done
  [[ -e $WORK/acp-ready ]] || fail "hermes prompt did not start"
  GATEWAY_TOKEN=$(awk '$1 == "api_key:" {print $2}' "$WORK/.hermes/config.yaml")
  [[ ${#GATEWAY_TOKEN} == 64 ]] || fail "gateway token absent"
}
controller_down() {  # [SECONDS]
  : >"$WORK/acp-release"
  wait_journal '.child == null and .pending == null and .settlementDue == null and .parentHold == null' "${1:-900}" ||
    echo "note: prompt did not fully settle" >&2
  cp "$JOURNAL" "$EV/$(basename "$S")-journal-final.json"
  exec 3>&-
  wait "$CONNECTOR_PID" 2>/dev/null || :; CONNECTOR_PID=
  local invocation; invocation=$(systemctl --user show -p InvocationID --value "$UNIT.service")
  journalctl --user "_SYSTEMD_INVOCATION_ID=$invocation" -o cat --no-pager \
    >"$EV/$(basename "$S")-controller.log" 2>&1 || :
}
wait_journal() {  # EXPR SECONDS
  local deadline=$(( $(date +%s) + $2 ))
  while (( $(date +%s) < deadline )); do
    [[ -f $JOURNAL ]] && jq -e "$1" "$JOURNAL" >/dev/null 2>&1 && return 0
    sleep 0.2
  done
  return 1
}
purse() {  # signed read of the provider task: remaining/reserved
  # Runs in $(...) subshells: the nonce counter lives in a file.
  local n; n=$(( $(cat "$S/purse-counter" 2>/dev/null || echo 90000) + 1 ))
  echo "$n" >"$S/purse-counter"
  jq -n --arg t "$PTASK" --arg n "$n" \
    '{subject:"9",nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:"resource"},
      grants:[{kind:"object",target:$t,capability:"101"}]}' >"$S/purse-$n.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCK" --intent "$S/purse-$n.json" \
    --key "$BOOT/provider.key" --view resource --dir "$S/purse-$n" >/dev/null 2>"$S/purse-$n.stderr" || { echo "?"; return; }
  jq -r '.page.grain.remaining + "/" + .page.grain.reserved' "$S/purse-$n/view.json"
}
# One Chat Completions request through the gateway, as Hermes would send it.
call() {  # STEP CALLER ROW MAX_TOKENS EXPECTED_HTTP EXPECTED_CODE UPSTREAM EXPECTED_AUTH EXPECTED_PURSE
  local step=$1 caller=$2 row=$3 tokens=$4 want_http=$5 want_code=$6 want_auth=$8 want_purse=$9
  local store; store=$(basename "$S")
  local before_open before_home
  before_open=$(wc -l <"$EV/upstream-openrouter.log" 2>/dev/null || echo 0)
  before_home=$(wc -l <"$EV/upstream-homelab.log" 2>/dev/null || echo 0)
  local body; body=$(jq -nc --arg s "$store $step" --argjson t "$tokens" \
    '{model:"shared-model",messages:[{role:"user",content:$s}],max_tokens:$t}')
  local http
  http=$(curl -s -o "$EV/$store-$step.response" -w '%{http_code}' --max-time 600 \
    -H "Authorization: Bearer $GATEWAY_TOKEN" -H 'Content-Type: application/json' \
    --data-binary "$body" "http://127.0.0.1:$GW/v1/chat/completions" || echo 000)
  local code; code=$(jq -r '.error.code // "-"' "$EV/$store-$step.response" 2>/dev/null || echo "-")
  # A purse refusal keeps its attempt and hold for the operator (never resent);
  # everything else settles.
  local settle=300; [[ $want_code == no-credit ]] && settle=15
  wait_journal '.providerAttempt == null and .providerHold == null and .providerPending == null' "$settle" ||
    echo "note: $store $step left provider state for reconciliation" >&2
  local seen="-"
  local after_open after_home
  after_open=$(wc -l <"$EV/upstream-openrouter.log" 2>/dev/null || echo 0)
  after_home=$(wc -l <"$EV/upstream-homelab.log" 2>/dev/null || echo 0)
  if (( after_open > before_open )); then seen=$(tail -1 "$EV/upstream-openrouter.log" | sed 's/.*auth=//'); fi
  if (( after_home > before_home )); then seen="homelab:$(tail -1 "$EV/upstream-homelab.log" | sed 's/.*auth=//')"; fi
  local remaining; remaining=$(purse) || remaining="?"
  local verdict=PASS
  [[ $http == "$want_http" && $code == "$want_code" && $seen == "$want_auth" &&
     $remaining == "$want_purse" ]] || verdict=FAIL
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$store" "$step" "$caller" "$row" "$http" "$code" \
    "$seen" "$want_auth" "$remaining" "$want_purse" "$verdict" >>"$TABLE_TSV"
  echo "$store $step: http=$http code=$code upstream=$seen purse=$remaining $verdict"
}

# ======== Store B: friend B's own key, then B revokes =========================
store_up store-b
PUB_A=$(friend A 21)
PUB_B=$(friend B 22)
PUB_C=$(friend C 23)
printf '%s\n' "$TOKEN_A" >"$RUN/inputs/a.key"
printf '%s\n' "$TOKEN_B" >"$RUN/inputs/b.key"
printf '%s\n' "$TOKEN_POOL" >"$RUN/inputs/pool.key"
key set-a --action set --dir "$RUN/friends/A" --provider openrouter --secret - <"$RUN/inputs/a.key"
key grant-a --action grant --dir "$RUN/friends/A" --provider openrouter --runner 9 \
  --per-call 64 --per-day 3 --until 1000000
key set-b --action set --dir "$RUN/friends/B" --provider openrouter --secret - <"$RUN/inputs/b.key"
key grant-b --action grant --dir "$RUN/friends/B" --provider openrouter --runner 9 \
  --per-call 64 --per-day 10 --until 1000000
key set-pool --action set --pool true --provider pool --secret - <"$RUN/inputs/pool.key"
# A workspace that CLAIMS B's subject with its own key: a separate namespace.
"$MINI" keygen --secret "$RUN/friends/mallory.key" --public "$RUN/friends/mallory.pub" >/dev/null
"$MINI" workspace --action init --host "$HOST" --config "$CONFIG" \
  --key "$RUN/friends/mallory.key" --subject 22 --dir "$RUN/friends/mallory" >/dev/null
key revoke-mallory-claims-b --action revoke --dir "$RUN/friends/mallory" --provider openrouter
jq -e '.removed == false' "$EV/key-revoke-mallory-claims-b.json" >/dev/null || fail "claimed subject reached B"
shred -u "$RUN/inputs/a.key" "$RUN/inputs/b.key" "$RUN/inputs/pool.key"
key ls-a --action ls --dir "$RUN/friends/A"
key ls-b --action ls --dir "$RUN/friends/B"
key ls-pool --action ls --pool true
printf 'A\t21\t%s\nB\t22\t%s\nC\t23\t%s\n' "$PUB_A" "$PUB_B" "$PUB_C" >"$EV/friends.tsv"

controller_up "{\"onBehalfOf\":{\"subject\":\"22\",\"publicKey\":\"$PUB_B\"}}" 3 1
echo "store-b purse before: $(purse)" | tee "$EV/store-b-purse-before.txt"
grep -q ' 50/0$' "$EV/store-b-purse-before.txt" || fail "store-b purse did not start at 50/0"
call b1 B openrouter 16 200 - openrouter "sha256:$AUTH_B" 49/0
key revoke-b --action revoke --dir "$RUN/friends/B" --provider openrouter
call b2-after-revoke B openrouter 16 403 no-credential openrouter - 49/0
controller_down
store_down

# ======== Store A: friend A's key, caps; B's revocation does not touch A ======
store_up store-a
controller_up "{\"onBehalfOf\":{\"subject\":\"21\",\"publicKey\":\"$PUB_A\"}}" 3 1
echo "store-a purse before: $(purse)" | tee "$EV/store-a-purse-before.txt"
grep -q ' 50/0$' "$EV/store-a-purse-before.txt" || fail "store-a purse did not start at 50/0"
call a1 A openrouter 16 200 - openrouter "sha256:$AUTH_A" 49/0
call a2 A openrouter 16 200 - openrouter "sha256:$AUTH_A" 48/0
call a3-over-per-call A openrouter 128 403 per-call-cap openrouter - 48/0
call a4 A openrouter 64 200 - openrouter "sha256:$AUTH_A" 47/0
call a5-over-per-day A openrouter 16 403 per-day-cap openrouter - 47/0
key regrant-a --action grant --dir "$RUN/friends/A" --provider openrouter --runner 9 \
  --per-call 64 --per-day 10 --until 1000000
call a6-after-regrant A openrouter 16 200 - openrouter "sha256:$AUTH_A" 46/0
key grant-a-expired --action grant --dir "$RUN/friends/A" --provider openrouter --runner 9 \
  --per-call 64 --per-day 10 --until 1
call a7-grant-expired A openrouter 16 403 grant-expired openrouter - 46/0
controller_down
store_down

# ======== Store C: no key; the pool behind the purse; homelab; no credit =====
store_up store-c
controller_up '{}' 20 20
echo "store-c purse before: $(purse)" | tee "$EV/store-c-purse-before.txt"
grep -q ' 50/0$' "$EV/store-c-purse-before.txt" || fail "store-c purse did not start at 50/0"
call c1-user-row-no-key C openrouter 16 403 no-credential openrouter - 50/0
table pool openrouter homelab
call c2-pool C pool 16 200 - openrouter "sha256:$AUTH_POOL" 30/0
table homelab openrouter pool
call c3-homelab C homelab 16 200 - homelab homelab:none 10/0
table pool openrouter homelab
call c4-pool-out-of-credit C pool 16 402 no-credit openrouter - 10/0
controller_down 120
store_down
table openrouter pool homelab

# ======== no fake token anywhere but the (deleted) inputs and the upstream digests
rm -f "$RUN/inputs/fake-tokens"
hits=0
for token in "$TOKEN_A" "$TOKEN_B" "$TOKEN_POOL"; do
  n=$( (grep -rlaF -- "$token" "$RUN" 2>/dev/null || :) | wc -l)
  hits=$((hits + n))
done
jhits=$(journalctl --user --since "-3h" -o cat --no-pager 2>/dev/null | grep -cF -e "$TOKEN_A" -e "$TOKEN_B" -e "$TOKEN_POOL" || :)
printf 'files_with_a_fake_token\t%s\nuser_journal_lines_with_a_fake_token\t%s\n' "$hits" "$jhits" | tee "$EV/token-grep.tsv"
unset TOKEN_A TOKEN_B TOKEN_POOL
column -t -s $'\t' "$TABLE_TSV"
! grep -q $'\tFAIL$' "$TABLE_TSV" && [[ $hits == 0 && $jhits == 0 ]] || fail "evidence table has a FAIL or a token leaked"
echo HERMES_KEYS_EVIDENCE_PASS
