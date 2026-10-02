#!/bin/sh
# Independent newcomer provisioning on a fresh, private Mini Store.
#
#   bootstrap -> enroll newcomer (key only) -> sponsor provisions factory
#   observation + a funded account OWNED by the newcomer -> newcomer creates,
#   writes and reads its own resource with no sponsor step -> stale factory
#   observation recovery -> cold reopen and receipt-only replay.
#
# Run on the Linux host that holds the native Host/Store/verifier. Every step
# leaves cmd/stdout/stderr/exit/timing under ROOT/log; any unexpected exit
# stops the run. Expected refusals are asserted, not ignored. OLD_MINI, when
# given, is a pre-generation client used only to show the retained op91
# refusal it cannot leave; it never mutates the Store (authoring is read-only).
set -eu
umask 077

if [ "$#" -ne 5 ] && [ "$#" -ne 6 ]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY [OLD_MINI]" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 ROOT=$5 OLD_MINI=${6:-}
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
command -v jq >/dev/null 2>&1 || { echo 'jq is required' >&2; exit 2; }

"$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$ROOT" \
  >"$ROOT.bootstrap.stdout"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
mv "$ROOT.bootstrap.stdout" "$ROOT/bootstrap-handoff.stdout"
CONFIG="$ROOT/deployment/pinned-config.json"
SOCKET="$ROOT/public/mini.sock"
LOG="$ROOT/log"
mkdir -m 700 "$LOG"
printf 'step\tseconds\texit\n' >"$ROOT/timings.tsv"
printf '{"type":"all","predicates":[]}\n' >"$ROOT/permit-all.json"
printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"notes","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"2"},"value":"1"}]}}]}' \
  >"$ROOT/write-notes.json"

# step NAME EXPECT(ok|fail) COMMAND...
step() {
  name=$1 expect=$2
  shift 2
  printf '%s\n' "$*" >"$LOG/$name.cmd"
  start=$(date +%s.%N)
  set +e
  "$@" >"$LOG/$name.stdout" 2>"$LOG/$name.stderr"
  code=$?
  set -e
  end=$(date +%s.%N)
  seconds=$(echo "$end - $start" | bc)
  printf '%s\n' "$code" >"$LOG/$name.exit"
  printf '%s\n' "$seconds" >"$LOG/$name.timing"
  printf '%s\t%s\t%s\n' "$name" "$seconds" "$code" >>"$ROOT/timings.tsv"
  if [ "$expect" = ok ] && [ "$code" -ne 0 ]; then
    echo "step $name failed ($code)" >&2
    tail -20 "$LOG/$name.stderr" >&2
    exit 1
  fi
  if [ "$expect" = fail ] && [ "$code" -eq 0 ]; then
    echo "step $name unexpectedly succeeded" >&2
    exit 1
  fi
}

attempt_of() { sed -n 's/^workspace read attempt: //p' "$LOG/$1.stderr" | tail -1; }

serving_lines() { grep -c '^mini: serving ' "$ROOT/public/serve.log" 2>/dev/null || true; }

# A restart is ready only when the NEW server reports serving; an old socket
# file can outlive its server.
start_service() {
  before=$(serving_lines)
  nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >>"$ROOT/public/serve.log" 2>&1 </dev/null &
  printf '%s\n' "$!" >"$ROOT/public/server.pid"
  waited=0
  until [ "$(serving_lines)" -gt "$before" ] && [ -S "$SOCKET" ]; do
    kill -0 "$(cat "$ROOT/public/server.pid")" 2>/dev/null || { echo 'server exited' >&2; exit 1; }
    waited=$((waited + 1))
    [ "$waited" -lt 1200 ] || { echo 'server did not report serving' >&2; exit 1; }
    sleep 0.1
  done
}

# Stop the checked server, then its Host child (which exits on stdin EOF once
# any in-progress open finishes).
stop_service() {
  pid=$(cat "$ROOT/public/server.pid")
  case "$(tr '\0' ' ' <"/proc/$pid/cmdline" 2>/dev/null)" in
    *" serve "*"$SOCKET"*) ;;
    *) echo "server pid $pid is not this fixture's service" >&2; exit 1 ;;
  esac
  child=$(sed -n 's/^mini: serving .* with host process \([0-9][0-9]*\)$/\1/p' \
    "$ROOT/public/serve.log" | tail -1)
  kill -TERM "$pid"
  waited=0
  while kill -0 "$pid" 2>/dev/null; do
    waited=$((waited + 1))
    [ "$waited" -lt 600 ] || { echo "server $pid did not stop" >&2; exit 1; }
    sleep 0.1
  done
  if [ -n "$child" ]; then
    case "$(tr '\0' ' ' <"/proc/$child/cmdline" 2>/dev/null)" in
      *"$HOST"*"$ROOT/public/"*" stdio"*)
        waited=0
        while kill -0 "$child" 2>/dev/null; do
          waited=$((waited + 1))
          if [ "$waited" -eq 1200 ]; then kill -TERM "$child"; fi
          [ "$waited" -lt 1500 ] || { echo "host $child did not stop" >&2; exit 1; }
          sleep 0.1
        done ;;
    esac
  fi
  printf 'stopped %s host %s\n' "$pid" "${child:-none}" >>"$ROOT/public/stops.txt"
}
trap 'if [ -s "$ROOT/public/server.pid" ] && kill -0 "$(cat "$ROOT/public/server.pid")" 2>/dev/null; then stop_service; fi' EXIT

# 1. Key-only enrollment of the newcomer by the sponsor.
step enroll-plan ok "$MINI" enroll --action plan --sponsor-workspace "$ROOT/sponsor" \
  --factory-ref factory --name newcomer --new-key "$ROOT/newcomer.key" \
  --dir "$ROOT/attempts/newcomer"
step enroll-seal ok "$MINI" enroll --action seal --dir "$ROOT/attempts/newcomer"
step enroll-submit ok "$MINI" enroll --action submit --dir "$ROOT/attempts/newcomer"
ENROLLMENT="$ROOT/attempts/newcomer/enrollment.json"
NEWCOMER=$(jq -er '.subject' "$ENROLLMENT")
jq -e '.authority == "admitted-key-only"' "$ENROLLMENT" >/dev/null

# 2. Before provisioning, the enrolled key cannot observe the factory.
step pre-init ok "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --enrollment "$ENROLLMENT" --namespace-root "$ROOT/namespace" \
  --dir "$ROOT/newcomer-before"
step pre-import ok "$MINI" workspace --action import --dir "$ROOT/newcomer-before" \
  --name factory --kind object --target 10 --observe-capability 54
step pre-read-factory fail "$MINI" workspace --action read --dir "$ROOT/newcomer-before" \
  --name factory

# 3. Provisioning refuses a subject that was never enrolled; no account is born.
step provision-unenrolled fail "$MINI" workspace --action provision --dir "$ROOT/sponsor" \
  --name stranger --holder 4242424242 --funding 1000 \
  --account-predicate "$ROOT/permit-all.json" --factory-ref factory
[ ! -e "$ROOT/sponsor/attempts/create-account-stranger" ]

# 4. Sponsor provisions the newcomer: factory observation + funded own account.
step provision ok "$MINI" workspace --action provision --dir "$ROOT/sponsor" \
  --name newcomer --holder "$NEWCOMER" --funding 1000 \
  --account-predicate "$ROOT/permit-all.json" --factory-ref factory
PROVISION="$ROOT/sponsor/provisions/newcomer/provision.json"
jq -e --arg h "$NEWCOMER" '.holder == $h and
  .factoryObservation.authority == "admitted-factory-observation" and
  .factoryObservation.receipt.acceptedCount != null and
  (.account.birthReceipt.confirmation == "installed")' "$PROVISION" >/dev/null
OBSERVE=$(jq -er '.factoryObservation.capability' "$PROVISION")

# 5. From here on the sponsor takes no step for the newcomer's resources.
step init ok "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --enrollment "$ENROLLMENT" \
  --birth-context "$ROOT/sponsor/provisions/newcomer/birth-context.json" \
  --namespace-root "$ROOT/namespace" --dir "$ROOT/newcomer"
step create ok "$MINI" workspace --action create --dir "$ROOT/newcomer" --name notes \
  --storage declared --predicate "$ROOT/permit-all.json" --fields 2
jq -e '.provenance.birthReceipt.confirmation == "installed"' \
  "$ROOT/newcomer/refs/notes.json" >/dev/null
step read-empty ok "$MINI" workspace --action read --dir "$ROOT/newcomer" --name notes
step write-propose ok "$MINI" workspace --action propose --dir "$ROOT/newcomer" \
  --request "$ROOT/write-notes.json" --proposal-id first-write
step write-submit ok "$MINI" workspace --action submit --dir "$ROOT/newcomer" \
  --intent "$ROOT/newcomer/proposals/first-write/intent.json" \
  --attempt "$ROOT/newcomer/attempts/first-write"
step read-back ok "$MINI" workspace --action read --dir "$ROOT/newcomer" --name notes
has_one() { jq -e '[.. | objects | select(.value? == "1")] | length > 0' "$1" >/dev/null; }
has_one "$LOG/read-back.stdout"

# 6. Stale factory observation. A signed observation taken before a later
# accepted turn is exactly what a crash between observation and authoring
# leaves behind; the old layout then retains op91's refusal forever.
step import-factory ok "$MINI" workspace --action import --dir "$ROOT/newcomer" \
  --name factory --kind object --target 10 --observe-capability "$OBSERVE"
step read-factory ok "$MINI" workspace --action read --dir "$ROOT/newcomer" --name factory
STALE="$(attempt_of read-factory)/signed-observation.bin"
[ -s "$STALE" ]
step sponsor-tick ok "$MINI" workspace --action create --dir "$ROOT/sponsor" --name tick \
  --storage declared --predicate "$ROOT/permit-all.json"

if [ -n "$OLD_MINI" ]; then
  step old-init ok "$OLD_MINI" workspace --action init --host "$HOST" --config "$CONFIG" \
    --socket "$SOCKET" --enrollment "$ENROLLMENT" \
    --birth-context "$ROOT/sponsor/provisions/newcomer/birth-context.json" \
    --namespace-root "$ROOT/namespace" --dir "$ROOT/newcomer-old-client"
  mkdir -m 700 "$ROOT/newcomer-old-client/sources/create-stale-old.current"
  cp "$STALE" "$ROOT/newcomer-old-client/sources/create-stale-old.current/factory-observation.bin"
  step old-create-1 fail "$OLD_MINI" workspace --action create --dir "$ROOT/newcomer-old-client" \
    --name stale-old --storage declared --predicate "$ROOT/permit-all.json"
  step old-create-2 fail "$OLD_MINI" workspace --action create --dir "$ROOT/newcomer-old-client" \
    --name stale-old --storage declared --predicate "$ROOT/permit-all.json"
  OLD_REPLY="$ROOT/newcomer-old-client/sources/create-stale-old.current/reply.frame"
  [ "$(od -An -tu1 -N1 "$OLD_REPLY" | tr -d ' ')" = 255 ]
  [ ! -e "$ROOT/newcomer-old-client/attempts/create-stale-old" ]
fi

# 6a. Crash state: retained stale observation, no reply yet.
mkdir -m 700 "$ROOT/newcomer/sources/create-stale-crash.authoring" \
  "$ROOT/newcomer/sources/create-stale-crash.authoring/g0001"
cp "$STALE" "$ROOT/newcomer/sources/create-stale-crash.authoring/g0001/factory-observation.bin"
step stale-crash-create ok "$MINI" workspace --action create --dir "$ROOT/newcomer" \
  --name stale-crash --storage declared --predicate "$ROOT/permit-all.json"
G="$ROOT/newcomer/sources/create-stale-crash.authoring"
[ "$(od -An -tu1 -N1 "$G/g0001/reply.frame" | tr -d ' ')" = 255 ]
[ "$(od -An -tu1 -N1 "$G/g0002/reply.frame" | tr -d ' ')" = 91 ]
cmp -s "$STALE" "$G/g0001/factory-observation.bin"

# 6b. The reported state: the pre-generation client's retained op91 refusal
# before any birth call, planted as generation 1 of the same request.
if [ -n "$OLD_MINI" ]; then
  mkdir -m 700 "$ROOT/newcomer/sources/create-stale-refused.authoring" \
    "$ROOT/newcomer/sources/create-stale-refused.authoring/g0001"
  cp "$STALE" "$ROOT/newcomer/sources/create-stale-refused.authoring/g0001/factory-observation.bin"
  cp "$OLD_REPLY" "$ROOT/newcomer/sources/create-stale-refused.authoring/g0001/reply.frame"
  step stale-refused-create ok "$MINI" workspace --action create --dir "$ROOT/newcomer" \
    --name stale-refused --storage declared --predicate "$ROOT/permit-all.json"
  G="$ROOT/newcomer/sources/create-stale-refused.authoring"
  cmp -s "$OLD_REPLY" "$G/g0001/reply.frame"
  [ "$(od -An -tu1 -N1 "$G/g0002/reply.frame" | tr -d ' ')" = 91 ]
fi

# 7. Cold reopen of the same Store: full semantic replay, then receipts only.
step stop-before-reopen ok stop_service
step reopen ok start_service
step reopen-enroll-lookup ok "$MINI" enroll --action lookup --dir "$ROOT/attempts/newcomer"
step reopen-provision-lookup ok "$MINI" workspace --action provision-lookup \
  --dir "$ROOT/sponsor" --name newcomer --factory-ref factory
jq -es --slurpfile p "$PROVISION" 'last | .factoryObservation.transactionId ==
  $p[0].factoryObservation.receipt.transactionId and
  .factoryObservation.acceptedCount == $p[0].factoryObservation.receipt.acceptedCount and
  .factoryObservation.confirmation == "replayed"' "$LOG/reopen-provision-lookup.stdout" >/dev/null
step reopen-read ok "$MINI" workspace --action read --dir "$ROOT/newcomer" --name notes
has_one "$LOG/reopen-read.stdout"
step reopen-create ok "$MINI" workspace --action create --dir "$ROOT/newcomer" \
  --name after-reopen --storage declared --predicate "$ROOT/permit-all.json"

step stop ok stop_service
trap - EXIT
sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" ${OLD_MINI:+"$OLD_MINI"} "$CONFIG" \
  "$ENROLLMENT" "$PROVISION" "$ROOT/sponsor/provisions/newcomer/birth-context.json" \
  "$ROOT/newcomer/refs/notes.json" >"$ROOT/evidence.sha256"
printf '%s\n' "$ROOT/timings.tsv"
