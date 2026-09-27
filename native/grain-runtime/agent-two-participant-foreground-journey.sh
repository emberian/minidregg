#!/bin/sh
# Native, model-free foreground journey over two already-running controllers.
# The SPK fixture owns Store creation and service start. This script never
# resends a request ID after a lost response and never reconciles uncertainty.
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 RUNTIME CONFIG_A CONFIG_B status-soft-lost|api-get|hard-eof-observe NEW_EVIDENCE_DIR" >&2
  exit 2
fi
runtime=$1 config_a=$2 config_b=$3 phase=$4 evidence=$5
: "${QUALIFIED_RUNTIME_SHA256:?pin exact committed Linux grain-runtime binary}"
: "${NATIVE_PREFLIGHT_DIR:?pass completed two-recipient native preflight directory}"
for path in "$runtime" "$config_a" "$config_b" "$evidence" "$NATIVE_PREFLIGHT_DIR"; do
  case "$path" in /*) ;; *) echo "all paths must be absolute" >&2; exit 2 ;; esac
done
for path in "$runtime" "$config_a" "$config_b"; do
  [ -f "$path" ] && [ ! -L "$path" ] || exit 2
done
[ -x "$runtime" ] && [ ! -e "$evidence" ] && [ ! -L "$evidence" ] || exit 2
command -v jq >/dev/null
command -v sha256sum >/dev/null
test "$(sha256sum "$runtime" | cut -d ' ' -f 1)" = "$QUALIFIED_RUNTIME_SHA256"
sha256sum -c "$NATIVE_PREFLIGHT_DIR/input-sha256.txt" >/dev/null
for config in "$config_a" "$config_b"; do
  awk -v path="$config" '$2 == path {found++} END {exit found == 1 ? 0 : 1}' \
    "$NATIVE_PREFLIGHT_DIR/input-sha256.txt" || {
      echo "controller config is not the exact preflight input" >&2; exit 2;
    }
done
for source in "$NATIVE_PREFLIGHT_DIR/a-op55/outcome.json" \
    "$NATIVE_PREFLIGHT_DIR/b-op55/outcome.json"; do
  jq -e '.type == "confirmed" and .confirmation == "replayed"' "$source" >/dev/null
done
check_controller() {
  label=$1 config=$2 parent=$3 tool=$4 purse=$5 provider=$6
  jq -e --arg parent "$parent" --arg tool "$tool" \
    --arg purse "$purse" --arg provider "$provider" '
    .task == $parent and .toolTask.task == $tool and
    .dispatchTask.task == $purse and .providerTask.task == $provider and
    (.foregroundTool.reserve | type == "string" and test("^[1-9][0-9]*$")) and
    (.foregroundTool.charge | type == "string" and test("^(0|[1-9][0-9]*)$")) and
    .toolTask.allowedApplicationApiRoutes[0].name == "gitweb-app" and
    .toolTask.allowedApplicationApiRoutes[0].signedApiPath == "/repo.git/"
  ' "$config" >/dev/null
  socket=$(jq -er .controlSocket "$config")
  [ -S "$socket" ] || { echo "$label controller socket absent" >&2; exit 2; }
}
check_controller a "$config_a" 7920 7930 7940 7950
check_controller b "$config_b" 7921 7931 7941 7951
case "$phase" in
  status-soft-lost) command -v nc >/dev/null ;;
  api-get)
    : "${QUALIFIED_EVENT21_HOST_SHA256:?pin source-qualified event21 Host}"
    for config in "$config_a" "$config_b"; do
      test "$(jq -er .toolTask.agentApiHostSha256 "$config")" = \
        "$QUALIFIED_EVENT21_HOST_SHA256"
      host=$(jq -er .host "$config")
      test "$(sha256sum "$host" | cut -d ' ' -f 1)" = \
        "$QUALIFIED_EVENT21_HOST_SHA256"
    done
    ;;
  hard-eof-observe) command -v nc >/dev/null ;;
  *) echo "unknown phase" >&2; exit 2 ;;
esac
mkdir -m 700 "$evidence"
sha256sum "$0" "$runtime" "$config_a" "$config_b" \
  "$NATIVE_PREFLIGHT_DIR/input-sha256.txt" >"$evidence/input-sha256.txt"

run_status_lost() {
  label=$1 config=$2
  socket=$(jq -er .controlSocket "$config")
  state=$(jq -er .stateDir "$config")
  request_id=$($runtime tool-id)
  printf '%s\n' "$request_id" >"$evidence/$label.request-id"
  frame=$(jq -nc --arg id "$request_id" \
    '{requestId:$id,name:"mini_grain_status",arguments:{}}')
  printf '%s' "$frame" >"$evidence/$label.request.json"
  # Keep the soft socket open until the controller has persisted the exact
  # attempt in its private journal. Closing at write completion could detach
  # before the queued tool frame passes the active-attachment check.
  size=$(printf '%s' "$frame" | wc -c | tr -d ' ')
  fifo="$evidence/$label.input.fifo"
  mkfifo -m 600 "$fifo"
  nc -U -q 0 "$socket" <"$fifo" >/dev/null \
    2>"$evidence/$label.original-transport-error.log" &
  transport_pid=$!
  exec 3>"$fifo"
  printf 'attach terminal-v1 soft\n' >&3
  printf 'tool-v1 %s\n' "$size" >&3
  printf '%s' "$frame" >&3
  wait_index=0
  until jq -e --arg id "$request_id" '
    (.foregroundAttempt.requestId == $id) or
    any(.foregroundHistory[]?; .requestId == $id)
  ' "$state/journal.json" >/dev/null 2>&1; do
    wait_index=$((wait_index + 1))
    if [ "$wait_index" -ge 200 ]; then
      exec 3>&-
      wait "$transport_pid" || true
      echo "$label frame was not durably claimed; do not infer a native attempt" >&2
      exit 1
    fi
    sleep 0.05
  done
  exec 3>&-
  wait "$transport_pid" || true
  rm "$fifo"
  result="$evidence/$label.result.json"
  index=0
  until "$runtime" tool-result "$socket" "$request_id" >"$result" 2>"$evidence/$label.inspect-error.log"; do
    index=$((index + 1))
    [ "$index" -lt 120 ] || {
      echo "$label result not definite; retained ID requires inspection, no resend" >&2
      exit 1
    }
    sleep 1
  done
  jq -e --arg id "$request_id" --arg parent "$(jq -er .task "$config")" \
    --arg tool "$(jq -er .toolTask.task "$config")" '
    .type == "tool-complete" and .requestId == $id and .isError == false and
    (.result.text | fromjson | .parent.grain.task) == $parent and
    (.result.text | fromjson | .tool.grain.task) == $tool
  ' "$result" >/dev/null
  before=$(jq -er .nextOperationId "$state/journal.json")
  # Send the byte-identical original frame. The CLI reconstructs JSON and
  # cannot prove a same-byte retry, so the framed socket is used directly.
  duplicate_fifo="$evidence/$label.duplicate.fifo"
  mkfifo -m 600 "$duplicate_fifo"
  nc -U -q 0 "$socket" <"$duplicate_fifo" \
    >"$evidence/$label.duplicate-frames.log" \
    2>"$evidence/$label.duplicate-error.log" &
  duplicate_pid=$!
  exec 3>"$duplicate_fifo"
  printf 'attach terminal-v1 soft\n' >&3
  printf 'tool-v1 %s\n' "$size" >&3
  printf '%s' "$frame" >&3
  duplicate_index=0
  until jq -e -s --arg id "$request_id" '
    any(.[]; .type == "tool-complete" and .requestId == $id and
      .isError == true and (.result | type == "string" and
        contains("durably claimed")))
  ' "$evidence/$label.duplicate-frames.log" >/dev/null 2>&1; do
    duplicate_index=$((duplicate_index + 1))
    if [ "$duplicate_index" -ge 200 ]; then
      exec 3>&-
      wait "$duplicate_pid" || true
      echo "$label exact duplicate refusal was not delivered" >&2
      exit 1
    fi
    sleep 0.05
  done
  exec 3>&-
  wait "$duplicate_pid" || true
  rm "$duplicate_fifo"
  printf '%s\n' '{"changed":true}' >"$evidence/$label.changed-args.json"
  if "$runtime" tool "$socket" soft "$request_id" mini_grain_status \
      "$evidence/$label.changed-args.json" >"$evidence/$label.changed-result.json" \
      2>"$evidence/$label.changed-error.log"; then
    echo "$label changed-byte request unexpectedly dispatched" >&2; exit 1
  fi
  jq -e '.type == "tool-complete" and .isError == true and
    (.result | type == "string" and contains("different bytes"))' \
    "$evidence/$label.changed-result.json" >/dev/null
  after=$(jq -er .nextOperationId "$state/journal.json")
  test "$before" = "$after"
  "$runtime" tool-ack "$socket" "$request_id" >"$evidence/$label.ack.json"
  jq -e --arg id "$request_id" '
    .type == "tool-acknowledged" and .requestId == $id and
    (.operationId | type == "string")
  ' "$evidence/$label.ack.json" >/dev/null
  "$runtime" tool-result "$socket" "$request_id" >"$evidence/$label.after-ack.json"
  cmp "$result" "$evidence/$label.after-ack.json"
}

run_api_get() {
  label=$1 config=$2
  socket=$(jq -er .controlSocket "$config")
  request_id=$($runtime tool-id)
  printf '%s\n' "$request_id" >"$evidence/$label.request-id"
  jq -n '{application:"gitweb-app",method:"GET",path:"info/refs",
    query:"service=git-upload-pack",
    headers:[{name:"accept",value:"application/x-git-upload-pack-advertisement"}],
    bodyHex:""}' \
    >"$evidence/$label.args.json"
  "$runtime" tool "$socket" soft "$request_id" mini_application_api \
    "$evidence/$label.args.json" >"$evidence/$label.result.json" \
    2>"$evidence/$label.transport.log" || {
      echo "$label API result is not definite success; inspect only, never resend ID" >&2
      exit 1
    }
  jq -e --arg id "$request_id" '
    .type == "tool-complete" and .requestId == $id and .isError == false and
    (.result.isError == false) and
    (.result.text | fromjson |
      .type == "http" and .status == 200 and
      (.body_hex | type == "string" and length > 0) and
      (.headers | any((.name | ascii_downcase) == "content-type" and
        (.value | startswith("application/x-git-upload-pack-advertisement")))))
  ' "$evidence/$label.result.json" >/dev/null
  "$runtime" tool-ack "$socket" "$request_id" >"$evidence/$label.ack.json"
}

case "$phase" in
  status-soft-lost)
    run_status_lost a "$config_a"
    run_status_lost b "$config_b"
    echo "two native signed status results recovered by ID; no request replay" ;;
  api-get)
    run_api_get a "$config_a"
    run_api_get b "$config_b"
    echo "two agent API GET results confirmed; inspect native event21 receipts separately" ;;
  hard-eof-observe)
    # Hard EOF may race before dispatch or after an exact native attempt. The
    # operator must reconcile the retained ID and signed state; this phase
    # intentionally cannot declare success or begin another request.
    socket=$(jq -er .controlSocket "$config_b")
    request_id=$($runtime tool-id)
    printf '%s\n' "$request_id" >"$evidence/b.request-id"
    frame=$(jq -nc --arg id "$request_id" \
      '{requestId:$id,name:"mini_grain_status",arguments:{}}')
    printf '%s' "$frame" >"$evidence/b.request.json"
    size=$(printf '%s' "$frame" | wc -c | tr -d ' ')
    { printf 'attach terminal-v1 hard\n'; printf 'tool-v1 %s\n' "$size";
      printf '%s' "$frame"; } | nc -U -q 0 "$socket" \
        >"$evidence/b.original-transport.log" 2>&1 || true
    "$runtime" tool-result "$socket" "$request_id" \
      >"$evidence/b.read-only-result.json" 2>"$evidence/b.inspect-error.log" || true
    echo "hard EOF observation retained; operator must inspect signed Mini state before recovery" >&2
    exit 3 ;;
esac
sha256sum -c "$evidence/input-sha256.txt" >"$evidence/input-postcheck.txt"
