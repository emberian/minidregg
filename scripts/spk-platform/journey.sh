#!/bin/sh
# One protected, same-Store GitWeb journey. Commands claim a numbered action
# before any native mutation; existing/partial actions are evidence, not a
# reason to create a fresh Store or resubmit. `status` is read-only.
set -eu
umask 077

usage() {
  cat >&2 <<'EOF'
usage: journey.sh status ROOT
       journey.sh resume-base ROOT ORIGINAL_HOST CONTINUATION_HOST MINI STORE_HELPER SIGNATURE_HELPER SPK_HOST ORIGINAL_SUBMIT_RECEIPT REPLAYED_LOOKUP_RECEIPT PINNED_RUN_BASE_SOURCE
       journey.sh prepare-install ROOT QUALIFIED_HOST HOST_SHA256 OPERATOR_SOCKET APP_UID IMAGE_DIR NEW_INSTALL_JOURNAL
       journey.sh install-prepare ROOT SPK_HOST SPK_HOST_SHA256 INSTALL_JOURNAL
       journey.sh install-complete ROOT SPK_HOST SPK_HOST_SHA256 INSTALL_JOURNAL
       journey.sh delegate-observe ROOT QUALIFIED_HOST HOST_SHA256 MINI OPERATOR_SOCKET
       journey.sh prepare-resident ROOT INSTALL_JOURNAL NEW_RESIDENT_JOURNAL PRIVATE_REQUEST.json

This driver does not retry the timed-out birth, launch a resident, issue a
ticket, or dispatch browser/API traffic. Those require separate exact native
gates. Use the original r3 root; prepare.sh/run-base.sh are fresh-only.
EOF
  exit 2
}
[ "$#" -ge 2 ] || usage
ACTION=$1 ROOT=$2
shift 2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
fail() { echo "GitWeb journey: $*" >&2; exit 2; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
absolute() {
  case "$1" in /*) ;; *) fail "absolute path required" ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/') fail "noncanonical path" ;; esac
}
protected_chain() {
  chain=$1
  while :; do
    [ -d "$chain" ] && [ ! -L "$chain" ] || fail "protected directory absent or linked: $chain"
    metadata=$(stat -c '%u:%a' "$chain")
    owner=${metadata%%:*}; mode=${metadata#*:}
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory owner"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor"
    [ "$chain" = / ] && break
    chain=${chain%/*}; [ -n "$chain" ] || chain=/
  done
}
receipt() {
  [ -s "$1" ] && [ ! -L "$1" ] &&
    jq -e '.type == "confirmed" and
      ([.transactionId,.eventId,.acceptedCount,.imageBoundary] |
       all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$")))' "$1" >/dev/null
}
absolute "$ROOT"
case "$ROOT" in /var/lib/minidregg/spk/fixtures/*) ;; *) fail "not a prepared integrated fixture" ;; esac
protected_chain "$ROOT"
[ -s "$ROOT/source-stage/qualify-launch-result.json" ] || fail "signed v2 qualifier absent"
jq -e '.protocol == "mini-spk-launch-qualified-v2" and
  .rawSha256 == "2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa" and
  .launchRoot == "89066044197087243500897137644433855781716276082669749278782223953933431354679"' \
  "$ROOT/source-stage/qualify-launch-result.json" >/dev/null || fail "signed v2 qualifier differs"
JOURNEY="$ROOT/continuations/gitweb-journey"
BASE_RECEIPT="$ROOT/base/app-attempt/outcome.json"
HANDOFF="$ROOT/source-stage/install-v2-handoff.json"
base_ready() {
  receipt "$BASE_RECEIPT" &&
    jq -e '.type == "mini-spk-v2-install-handoff-v1" and
      .rawSha256 == "2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa" and
      .packageEmpty == true and .snapshotEmpty == true and
      .appBirth == (input | {acceptedCount,transactionId,eventId,imageBoundary})' \
      "$HANDOFF" "$BASE_RECEIPT" >/dev/null 2>&1 &&
    [ -s "$ROOT/base/additional-sessions.json" ] &&
    [ -s "$ROOT/base/workroom/agents/verified/birth-evidence.json" ]
}
claim() {
  name=$1
  [ -d "$ROOT/continuations" ] || mkdir -m 700 "$ROOT/continuations"
  [ ! -L "$ROOT/continuations" ] || fail "continuation root linked"
  [ -d "$JOURNEY" ] || mkdir -m 700 "$JOURNEY"
  [ ! -L "$JOURNEY" ] || fail "journey directory linked"
  protected_chain "$JOURNEY"
  [ ! -e "$JOURNEY/$name" ] && [ ! -L "$JOURNEY/$name" ] ||
    fail "action $name already attempted; reconcile retained evidence"
  mkdir -m 700 "$JOURNEY/$name" || fail "action $name already claimed"
  STEP="$JOURNEY/$name"
  printf '%s\n' "$name" >"$STEP/action.txt"
  sync -f "$STEP/action.txt"
  sync -f "$STEP"
  sync -f "$JOURNEY"
}
finish() {
  printf '%s\n' complete >"$STEP/complete.txt"
  sync -f "$STEP/complete.txt"
  sync -f "$STEP"
}

case "$ACTION" in
  status)
    [ "$#" -eq 0 ] || usage
    birth=unresolved
    if receipt "$ROOT/base/workroom/birth-attempt/outcome.json"; then birth=confirmed
    else
      for candidate in "$ROOT"/base/workroom/birth-attempt/retry-????.json; do
        [ -f "$candidate" ] || continue
        if receipt "$candidate"; then birth=confirmed-in-retained-retry; fi
      done
      if [ "$birth" = unresolved ] &&
        [ -s "$ROOT/base/workroom/birth-attempt/retry-0001.json" ] &&
        jq -e '.type == "absent"' "$ROOT/base/workroom/birth-attempt/retry-0001.json" >/dev/null; then
        birth=absent-at-last-lookup
      fi
    fi
    base=false; if base_ready; then base=true; fi
    install=none; resident=none
    if [ -d "$JOURNEY" ]; then
      if [ -s "$JOURNEY/prepare-install-0001/install-path.txt" ]; then
        install_path=$(cat "$JOURNEY/prepare-install-0001/install-path.txt")
        if [ -s "$install_path/install-completed-v2.json" ]; then install=completed
        elif [ -s "$install_path/install-prepared-v2.json" ]; then install=prepared
        else install=attempted; fi
      fi
      if [ -s "$JOURNEY/prepare-resident-0001/resident-path.txt" ]; then
        resident_path=$(cat "$JOURNEY/prepare-resident-0001/resident-path.txt")
        if [ -s "$resident_path/start-completed-v3.json" ]; then resident=completed
        elif [ -s "$resident_path/resident.json" ]; then resident=configured
        else resident=attempted; fi
      fi
    fi
    if [ "$birth" = absent-at-last-lookup ]; then next_gate=profile-and-recover-original-birth
    elif [ "$base" = false ]; then next_gate=resume-original-base
    elif [ "$install" = none ]; then next_gate=prepare-qualified-install
    elif [ "$install" = prepared ]; then next_gate=complete-original-install
    elif [ "$install" = completed ] && [ "$resident" = none ]; then next_gate=prepare-human-resident
    else next_gate=qualified-resident-browser-and-v3-agent-dispatch; fi
    jq -n --arg root "$ROOT" --arg birth "$birth" --argjson base "$base" \
      --arg install "$install" --arg resident "$resident" --arg next "$next_gate" '
      {protocol:"mini-spk-gitweb-journey-status-v1",root:$root,
       firstBirth:$birth,baseReady:$base,install:$install,resident:$resident,nextGate:$next,
       humanBrowserQualified:false,agentApiQualified:false,
       sameAppContentQualified:false,
       note:"component receipts are not final browser/API or same-app content acceptance"}'
    ;;
  resume-base)
    [ "$#" -eq 9 ] || usage
    [ ! -e "$HANDOFF" ] || fail "base already completed"
    /bin/sh "$HERE/resume-base.sh" "$ROOT" "$@"
    ;;
  prepare-install)
    [ "$#" -eq 6 ] || usage
    base_ready || fail "same-Store base receipt/handoff incomplete"
    qualified_host=$1 host_sha=$2 socket=$3 app_uid=$4 image_dir=$5 install_dir=$6
    for path in "$qualified_host" "$socket" "$image_dir" "$install_dir"; do absolute "$path"; done
    [ ! -e "$install_dir" ] || fail "INSTALL journal already exists"
    [ "$(sha "$qualified_host")" = "$host_sha" ] || fail "qualified Host pin differs"
    claim prepare-install-0001
    printf '%s\n' "$install_dir" >"$STEP/install-path.txt"
    sha256sum "$qualified_host" "$BASE_RECEIPT" "$HANDOFF" \
      "$HERE/prepare-install-config.sh" >"$STEP/input-sha256.txt"
    QUALIFIED_INSTALL_HOST_SHA256=$host_sha \
      /bin/sh "$HERE/prepare-install-config.sh" "$ROOT" "$qualified_host" \
      "$socket" "$app_uid" "$image_dir" "$install_dir" \
      >"$STEP/stdout" 2>"$STEP/stderr"
    [ -s "$install_dir/install.json" ] || fail "INSTALL config absent"
    sha256sum -c "$STEP/input-sha256.txt" >"$STEP/input-postcheck.txt"
    finish
    ;;
  install-prepare|install-complete)
    [ "$#" -eq 3 ] || usage
    base_ready || fail "same-Store base incomplete"
    spk_host=$1 spk_sha=$2 install_dir=$3
    absolute "$spk_host"; absolute "$install_dir"
    [ "$(sha "$spk_host")" = "$spk_sha" ] || fail "physical Host pin differs"
    [ -s "$install_dir/install.json" ] || fail "INSTALL config absent"
    [ "$(jq -er .miniConfig "$install_dir/install.json")" = \
      "$ROOT/base/workroom/deployment/pinned-config.json" ] || fail "INSTALL names another Store"
    if [ "$ACTION" = install-prepare ]; then
      [ ! -e "$install_dir/install-prepared-v2.json" ] || fail "INSTALL already prepared"
      name='install-prepare-0001'
    else
      [ -s "$install_dir/install-prepared-v2.json" ] || fail "INSTALL preparation absent"
      [ ! -e "$install_dir/completion-v2-author/op38-requested.json" ] ||
        fail "op38 may already be submitted; reconcile exact lookup"
      [ ! -e "$install_dir/install-completed-v2.json" ] || fail "INSTALL already completed"
      name='install-complete-0001'
    fi
    claim "$name"
    sha256sum "$spk_host" "$install_dir/install.json" >"$STEP/input-sha256.txt"
    "$spk_host" "$ACTION" "$install_dir/install.json" \
      >"$STEP/stdout" 2>"$STEP/stderr"
    if [ "$ACTION" = install-prepare ]; then
      [ -s "$install_dir/install-prepared-v2.json" ] || fail "INSTALL prepared receipt absent"
    else
      [ -s "$install_dir/install-completed-v2.json" ] || fail "INSTALL completion receipt absent"
    fi
    sha256sum -c "$STEP/input-sha256.txt" >"$STEP/input-postcheck.txt"
    finish
    ;;
  delegate-observe)
    [ "$#" -eq 4 ] || usage
    base_ready || fail "app birth absent"
    host=$1 host_sha=$2 mini=$3 socket=$4
    absolute "$host"; absolute "$mini"; absolute "$socket"
    [ "$(sha "$host")" = "$host_sha" ] || fail "capability inspector Host pin differs"
    claim delegate-observe-0001
    evidence="$ROOT/continuations/app-observe-0001"
    [ ! -e "$evidence" ] || fail "delegation evidence already exists"
    sha256sum "$host" "$mini" "$HERE/delegate-app-observe.sh" \
      "$BASE_RECEIPT" >"$STEP/input-sha256.txt"
    QUALIFIED_HOST_SHA256=$host_sha \
      /bin/sh "$HERE/delegate-app-observe.sh" "$ROOT" "$host" "$mini" \
      "$socket" "$evidence" >"$STEP/stdout" 2>"$STEP/stderr"
    [ "$(wc -l <"$evidence/delegations.jsonl")" -eq 3 ] || fail "three signed observe grants absent"
    sha256sum -c "$STEP/input-sha256.txt" >"$STEP/input-postcheck.txt"
    finish
    ;;
  prepare-resident)
    [ "$#" -eq 3 ] || usage
    base_ready || fail "same-Store base incomplete"
    install_dir=$1 resident_dir=$2 request=$3
    for path in "$install_dir" "$resident_dir" "$request"; do absolute "$path"; done
    [ -s "$install_dir/install-completed-v2.json" ] || fail "INSTALL completion absent"
    [ ! -e "$resident_dir" ] || fail "resident attempt already exists"
    jq -e '.protocol == "mini-spk-resident-config-request-v1" and
      .agents == []' "$request" >/dev/null ||
      fail "v2 agent custody is not the required v3 agent route; prepare a human-only resident first"
    claim prepare-resident-0001
    printf '%s\n' "$resident_dir" >"$STEP/resident-path.txt"
    sha256sum "$install_dir/install-completed-v2.json" "$request" \
      "$HERE/prepare-resident-config.sh" >"$STEP/input-sha256.txt"
    /bin/sh "$HERE/prepare-resident-config.sh" "$ROOT" "$install_dir" \
      "$resident_dir" "$request" >"$STEP/stdout" 2>"$STEP/stderr"
    [ -s "$resident_dir/resident.json" ] || fail "resident config absent"
    sha256sum -c "$STEP/input-sha256.txt" >"$STEP/input-postcheck.txt"
    finish
    ;;
  *) usage ;;
esac
