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
       journey.sh prepare-install ROOT QUALIFIED_HOST HOST_SHA256 OPERATOR_SOCKET APP_UID IMAGE_DIR NEW_INSTALL_JOURNAL OPERATOR_CONFIG CONFIG_SHA256 BASE_REBOUND_CONFIG BASE_REBOUND_SHA256
       journey.sh install-prepare ROOT SPK_HOST SPK_HOST_SHA256 INSTALL_JOURNAL
       journey.sh materialize-request ROOT SPK_HOST SPK_HOST_SHA256 INSTALL_JOURNAL
       journey.sh adopt-materialized ROOT SPK_HOST SPK_HOST_SHA256 INSTALL_JOURNAL
       journey.sh install-complete ROOT SPK_HOST SPK_HOST_SHA256 INSTALL_JOURNAL
       journey.sh adopt-volume ROOT INSTALL_JOURNAL SIZE_MIB
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
      ([.transactionId,.eventId,.acceptedCount,.worldRoot] |
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
      .appBirth == (input | {acceptedCount,transactionId,eventId,worldRoot})' \
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
claim_readonly() {
  prefix=$1
  [ -d "$ROOT/continuations" ] || mkdir -m 700 "$ROOT/continuations"
  [ -d "$JOURNEY" ] || mkdir -m 700 "$JOURNEY"
  protected_chain "$JOURNEY"
  exec 9>>"$JOURNEY/.readonly-action.lock"
  chmod 600 "$JOURNEY/.readonly-action.lock"
  flock -n 9 || fail "another physical adoption is active"
  for number in 0001 0002 0003 0004 0005 0006 0007 0008; do
    candidate="$JOURNEY/$prefix-$number"
    [ ! -s "$candidate/complete.txt" ] || fail "$prefix already completed"
    if [ ! -e "$candidate" ] && [ ! -L "$candidate" ]; then
      claim "$prefix-$number"
      return
    fi
  done
  fail "$prefix interrupted attempts exhausted; retain for audit"
}
selected_action() {
  prefix=$1 selected=''
  for candidate in "$JOURNEY"/"$prefix"-????; do
    [ -d "$candidate" ] || continue
    if [ -s "$candidate/complete.txt" ]; then
      [ -z "$selected" ] || fail "multiple completed $prefix actions"
      selected=$candidate
    fi
  done
  [ -n "$selected" ] || fail "completed $prefix action absent"
  printf '%s\n' "$selected"
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
      prepare_path=''
      for candidate in "$JOURNEY"/prepare-install-????; do
        [ -s "$candidate/complete.txt" ] || continue
        [ -z "$prepare_path" ] || fail "multiple completed INSTALL preparations"
        prepare_path=$candidate
      done
      if [ -n "$prepare_path" ] && [ -s "$prepare_path/install-path.txt" ]; then
        install_path=$(cat "$prepare_path/install-path.txt")
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
    [ "$#" -eq 10 ] || usage
    base_ready || fail "same-Store base receipt/handoff incomplete"
    qualified_host=$1 host_sha=$2 socket=$3 app_uid=$4 image_dir=$5 install_dir=$6
    operator_config=$7 config_sha=$8 base_rebound_config=$9 base_rebound_sha=${10}
    for path in "$qualified_host" "$socket" "$image_dir" "$install_dir" \
        "$operator_config" "$base_rebound_config"; do absolute "$path"; done
    [ ! -e "$install_dir" ] || fail "INSTALL journal already exists"
    [ "$(sha "$qualified_host")" = "$host_sha" ] || fail "qualified Host pin differs"
    [ "$(sha "$operator_config")" = "$config_sha" ] ||
      fail "operator config differs from explicit pin"
    [ "$(sha "$base_rebound_config")" = "$base_rebound_sha" ] ||
      fail "base helper rebind differs from explicit pin"
    claim_readonly prepare-install
    printf '%s\n' "$install_dir" >"$STEP/install-path.txt"
    jq -n --arg path "$operator_config" --arg sha "$config_sha" \
      --arg base "$base_rebound_config" --arg baseSha "$base_rebound_sha" '
      {protocol:"mini-spk-install-config-selection-v1",path:$path,sha256:$sha,
       baseReboundPath:$base,baseReboundSha256:$baseSha}
      ' >"$STEP/operator-config-selection.json"
    chmod 600 "$STEP/operator-config-selection.json"
    sha256sum "$qualified_host" "$BASE_RECEIPT" "$HANDOFF" \
      "$operator_config" "$base_rebound_config" "$STEP/operator-config-selection.json" \
      "$HERE/prepare-install-config.sh" "$HERE/install-config-scope.jq" \
      "$HERE/base-helper-rebind-scope.jq" \
      >"$STEP/input-sha256.txt"
    QUALIFIED_INSTALL_HOST_SHA256=$host_sha \
      /bin/sh "$HERE/prepare-install-config.sh" "$ROOT" "$qualified_host" \
      "$socket" "$app_uid" "$image_dir" "$install_dir" \
      "$operator_config" "$config_sha" "$base_rebound_config" "$base_rebound_sha" "$STEP" \
      >"$STEP/stdout" 2>"$STEP/stderr"
    [ -s "$install_dir/install.json" ] || fail "INSTALL config absent"
    jq -e --slurpfile selected "$STEP/operator-config-selection.json" '
      .miniConfig == $selected[0].path and
      .miniConfigSha256 == $selected[0].sha256
      ' "$install_dir/install.json" >/dev/null ||
      fail "INSTALL selected a different operator config"
    jq -e --slurpfile selected "$STEP/operator-config-selection.json" '
      .baseReboundMiniConfig == $selected[0].baseReboundPath and
      .baseReboundMiniConfigSha256 == $selected[0].baseReboundSha256
      ' "$STEP/host-upgrade/host-upgrade.json" >/dev/null ||
      fail "INSTALL selected a different base helper rebind"
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
    preparation=$(selected_action prepare-install)
    [ "$(cat "$preparation/install-path.txt")" = "$install_dir" ] ||
      fail "INSTALL journal differs from completed preparation"
    selected="$preparation/operator-config-selection.json"
    [ -s "$selected" ] ||
      fail "explicit operator config selection absent"
    sha256sum -c "$preparation/input-sha256.txt" >/dev/null ||
      fail "INSTALL config selection inputs changed"
    jq -e --slurpfile selected "$selected" '
      $selected[0].protocol == "mini-spk-install-config-selection-v1" and
      .miniConfig == $selected[0].path and
      .miniConfigSha256 == $selected[0].sha256
      ' "$install_dir/install.json" >/dev/null ||
      fail "INSTALL config differs from selected broker config"
    if [ "$ACTION" = install-prepare ]; then
      [ ! -e "$install_dir/install-prepared-v2.json" ] || fail "INSTALL already prepared"
      name='install-prepare-0001'
    else
      [ -s "$install_dir/install-prepared-v2.json" ] || fail "INSTALL preparation absent"
      adoption=$(selected_action adopt-materialized)
      materialize_request=$(selected_action materialize-request)
      request="$materialize_request/request.json"
      jq -e --slurpfile request "$request" \
        --slurpfile inspected "$adoption/inspection.json" '
        .protocol == "mini-spk-materialized-adoption-v1" and
        .executionClaim == "read-only-current-inspection" and
        .preparedSha256 == $request[0].preparedSha256 and
        .originalBeginSha256 == $request[0].originalBeginSha256 and
        .committedClaimSha256 == $request[0].committedClaimSha256 and
        .installed == $inspected[0]
        ' "$adoption/adoption.json" >/dev/null || fail "physical adoption changed"
      [ "$(jq -er .requestSha256 "$adoption/adoption.json")" = "$(sha "$request")" ] ||
        fail "materialization request changed"
      sha256sum -c "$adoption/input-sha256.txt" >/dev/null ||
        fail "materialized input or image changed"
      sha256sum -c "$materialize_request/input-sha256.txt" >/dev/null ||
        fail "original materialization request inputs changed"
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
  materialize-request)
    [ "$#" -eq 3 ] || usage
    base_ready || fail "same-Store base incomplete"
    spk_host=$1 spk_sha=$2 install_dir=$3
    absolute "$spk_host"; absolute "$install_dir"
    [ "$(sha "$spk_host")" = "$spk_sha" ] || fail "physical Host pin differs"
    [ -s "$install_dir/install-prepared-v2.json" ] || fail "source INSTALL claim absent"
    [ ! -e "$install_dir/install-completed-v2.json" ] || fail "INSTALL already completed"
    jq -e --arg root "$ROOT" '
      .protocol == "mini-spk-resident-install-v2" and
      .sourceSpk == ($root + "/packages/gitweb.spk") and
      .imageDir == "/var/lib/minidregg/spk/packages/sha256-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa" and
      .expectedRawSha256 == "2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa" and
      (.appUid | type == "number" and . > 0 and floor == .)
      ' "$install_dir/install.json" >/dev/null || fail "INSTALL source/image pin differs"
    prepared="$install_dir/install-prepared-v2.json"
    jq -e --slurpfile install "$install_dir/install.json" '
      .protocol == "mini-spk-install-prepared-v2" and
      .rawSha256 == $install[0].expectedRawSha256 and
      .launchRoot == "89066044197087243500897137644433855781716276082669749278782223953933431354679" and
      (.begin.volumeIdHex | type == "string" and test("^[0-9a-f]{64}$")) and
      ([.begin.transactionId,.begin.eventId,.begin.acceptedCount,.begin.worldRoot,
        .claim.transactionId,.claim.eventId,.claim.acceptedCount,.claim.worldRoot] |
        all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$")))
      ' "$prepared" >/dev/null || fail "prepared Mini claim differs"
    [ "$(sha "$ROOT/packages/gitweb.spk")" = "$(jq -er .rawSha256 "$prepared")" ] ||
      fail "signed source SPK differs from prepared claim"
    claim_readonly materialize-request
    jq -n --arg root "$ROOT" --arg install "$install_dir" \
      --arg preparedSha "$(sha "$prepared")" \
      --arg begin "$(jq -er .beginSha256 "$prepared")" \
      --arg claim "$(jq -er .committedClaimSha256 "$prepared")" \
      --arg host "$spk_host" --arg hostSha "$spk_sha" \
      --arg uid "$(jq -er .appUid "$install_dir/install.json")" '
      {protocol:"mini-spk-materialize-request-v1",fixtureRoot:$root,
       installJournal:$install,preparedSha256:$preparedSha,
       originalBeginSha256:$begin,committedClaimSha256:$claim,
       sourceSpk:($root+"/packages/gitweb.spk"),
       rawSha256:"2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa",
       inboxSpk:"/var/lib/minidregg/spk/inbox/gitweb-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa.spk",
       imageDir:"/var/lib/minidregg/spk/packages/sha256-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa",
       appUid:($uid|tonumber),spkHost:$host,spkHostSha256:$hostSha}
      ' >"$STEP/request.json"
    chmod 600 "$STEP/request.json"
    sha256sum "$prepared" "$install_dir/install.json" "$ROOT/packages/gitweb.spk" \
      "$spk_host" "$STEP/request.json" >"$STEP/input-sha256.txt"
    finish
    ;;
  adopt-materialized)
    [ "$#" -eq 3 ] || usage
    spk_host=$1 spk_sha=$2 install_dir=$3
    absolute "$spk_host"; absolute "$install_dir"
    materialize_request=$(selected_action materialize-request)
    request="$materialize_request/request.json"
    [ -s "$request" ] || fail "materialization request absent"
    sha256sum -c "$materialize_request/input-sha256.txt" >/dev/null ||
      fail "materialization request inputs changed"
    [ "$(sha "$spk_host")" = "$spk_sha" ] || fail "physical Host pin differs"
    jq -e --arg root "$ROOT" --arg install "$install_dir" \
      --arg host "$spk_host" --arg sha "$spk_sha" '
      (keys | sort) == (["protocol","fixtureRoot","installJournal",
        "preparedSha256","originalBeginSha256","committedClaimSha256",
        "sourceSpk","rawSha256","inboxSpk","imageDir","appUid",
        "spkHost","spkHostSha256"] | sort) and
      .protocol == "mini-spk-materialize-request-v1" and
      .fixtureRoot == $root and .installJournal == $install and
      .sourceSpk == ($root + "/packages/gitweb.spk") and
      .inboxSpk == "/var/lib/minidregg/spk/inbox/gitweb-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa.spk" and
      .imageDir == "/var/lib/minidregg/spk/packages/sha256-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa" and
      .rawSha256 == "2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa" and
      (.appUid | type == "number" and . > 0 and floor == .) and
      .spkHost == $host and .spkHostSha256 == $sha and
      ([.preparedSha256,.originalBeginSha256,.committedClaimSha256] |
        all(.[]; type == "string" and test("^[0-9a-f]{64}$")))
      ' "$request" >/dev/null || fail "materialization request malformed"
    [ "$(sha "$install_dir/install-prepared-v2.json")" = "$(jq -er .preparedSha256 "$request")" ] ||
      fail "prepared source claim changed"
    jq -e --slurpfile request "$request" '
      .beginSha256 == $request[0].originalBeginSha256 and
      .committedClaimSha256 == $request[0].committedClaimSha256 and
      .rawSha256 == $request[0].rawSha256
      ' "$install_dir/install-prepared-v2.json" >/dev/null ||
      fail "materialization request differs from source claim"
    [ "$(sha "$ROOT/packages/gitweb.spk")" = "$(jq -er .rawSha256 "$request")" ] ||
      fail "signed source SPK changed"
    image=$(jq -er .imageDir "$request") uid=$(jq -er .appUid "$request")
    absolute "$image"
    [ -d "$image" ] && [ ! -L "$image" ] || fail "root-published image absent"
    protected_chain "$image"
    claim_readonly adopt-materialized
    "$spk_host" inspect-installed "$image" "$uid" >"$STEP/inspection.json" \
      2>"$STEP/inspection.stderr" || fail "installed signed image inspection refused"
    jq -e --slurpfile request "$request" '
      .protocol == "mini-spk-installed-inspection-v1" and
      .imageDir == $request[0].imageDir and .appUid == $request[0].appUid and
      .rawSha256 == $request[0].rawSha256 and .rawLength == "14045864" and
      .signedAppId == "6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash" and
      .signedAppVersion == "10" and
      .signedManifestSha256 == "3ef23992c6ee79e5b684cec632d4552c5b34889348ae63acaaedb42b9616024f" and
      .signedBridgeConfigSha256 == "49d196f64ca2ce672a378581a8376ada53b27614bba522bbaec042237f0e70a2"
      ' "$STEP/inspection.json" >/dev/null || fail "installed physical identity differs"
    jq -n --slurpfile request "$request" --slurpfile inspection "$STEP/inspection.json" '
      {protocol:"mini-spk-materialized-adoption-v1",executionClaim:"read-only-current-inspection",
       requestSha256:null,preparedSha256:$request[0].preparedSha256,
       originalBeginSha256:$request[0].originalBeginSha256,
       committedClaimSha256:$request[0].committedClaimSha256,
       installed:$inspection[0]}' >"$STEP/adoption.json"
    jq --arg sha "$(sha "$request")" '.requestSha256=$sha' "$STEP/adoption.json" \
      >"$STEP/adoption.tmp"
    mv "$STEP/adoption.tmp" "$STEP/adoption.json"
    sha256sum "$request" "$install_dir/install-prepared-v2.json" \
      "$ROOT/packages/gitweb.spk" "$spk_host" "$image/package.spk" \
      "$STEP/inspection.json" "$STEP/adoption.json" >"$STEP/input-sha256.txt"
    sha256sum -c "$STEP/input-sha256.txt" >"$STEP/input-postcheck.txt"
    finish
    ;;
  adopt-volume)
    [ "$#" -eq 2 ] || usage
    install_dir=$1 size_mib=$2
    absolute "$install_dir"
    case "$size_mib" in ''|0*|*[!0-9]*) fail "volume size must be canonical MiB" ;; esac
    [ "$size_mib" -ge 64 ] && [ "$size_mib" -le 16384 ] ||
      fail "volume size outside root helper bounds"
    materialize_adoption=$(selected_action adopt-materialized)
    [ -s "$materialize_adoption/adoption.json" ] &&
      [ -s "$install_dir/install-completed-v2.json" ] ||
      fail "signed INSTALL completion or physical image adoption absent"
    prepared="$install_dir/install-prepared-v2.json"
    source_id=$(jq -er .begin.volumeIdHex "$prepared")
    case "$source_id" in *[!0-9a-f]*|'') fail "source volume ID malformed" ;; esac
    [ "${#source_id}" -eq 64 ] || fail "source volume ID length differs"
    uid=$(jq -er .appUid "$install_dir/install.json")
    deployment=$(jq -er .deploymentId "$install_dir/install.json")
    host_id=$(jq -er .hostId "$install_dir/install.json")
    witness=/run/minidregg/spk/volume-attest/8401.witness
    protected_chain "${witness%/*}"
    [ -f "$witness" ] && [ ! -L "$witness" ] &&
      [ "$(stat -c '%u:%a:%h' "$witness")" = '0:644:1' ] ||
      fail "root-published volume witness absent"
    witness_before=$(stat -c '%d:%i:%s:%Y:%Z' "$witness")
    witness_sha=$(sha "$witness")
    [ "$(wc -l <"$witness")" -eq 13 ] || fail "volume witness length differs"
    quota=$((size_mib * 1048576))
    [ "$(sed -n '1p' "$witness")" = 'DREGG/SPK-VAR-CUSTODY/v1' ] &&
      [ "$(sed -n '2p' "$witness")" = "deployment_id=$deployment" ] &&
      [ "$(sed -n '3p' "$witness")" = "host_id=$host_id" ] &&
      [ "$(sed -n '4p' "$witness")" = 'resource=8401' ] &&
      [ "$(sed -n '5p' "$witness")" = "volume_id=$source_id" ] &&
      [ "$(sed -n '6p' "$witness")" = "app_uid=$uid" ] &&
      [ "$(sed -n '7p' "$witness")" = "quota_bytes=$quota" ] &&
      [ "$(sed -n '8p' "$witness")" = 'backing=/var/lib/minidregg/spk/images/8401.ext4' ] &&
      [ "$(sed -n '11p' "$witness")" = "backing_size=$quota" ] &&
      [ "$(sed -n '13p' "$witness")" = 'mount=/var/lib/minidregg/spk/vars/8401' ] ||
      fail "volume witness differs from source INSTALL/physical quota"
    claim_readonly adopt-volume
    jq -n --arg install "$install_dir" --arg prepared "$(sha "$prepared")" \
      --arg completed "$(sha "$install_dir/install-completed-v2.json")" \
      --arg volume "$source_id" --arg witness "$witness" \
      --arg witnessSha "$witness_sha" --argjson size "$size_mib" '
      {protocol:"mini-spk-volume-adoption-v1",executionClaim:"read-only-root-witness",
       installJournal:$install,preparedSha256:$prepared,completedSha256:$completed,
       sourceVolumeIdHex:$volume,sizeMiB:$size,rootWitness:$witness,
       rootWitnessSha256:$witnessSha}
      ' >"$STEP/adoption.json"
    chmod 600 "$STEP/adoption.json"
    sha256sum "$prepared" "$install_dir/install-completed-v2.json" \
      "$install_dir/install.json" "$witness" "$STEP/adoption.json" \
      >"$STEP/input-sha256.txt"
    sha256sum -c "$STEP/input-sha256.txt" >"$STEP/input-postcheck.txt"
    [ "$(sha "$witness")" = "$witness_sha" ] &&
      [ "$(stat -c '%d:%i:%s:%Y:%Z' "$witness")" = "$witness_before" ] ||
      fail "root volume witness changed during adoption"
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
    volume_action=$(selected_action adopt-volume)
    volume_adoption="$volume_action/adoption.json"
    jq -e --arg install "$install_dir" \
      --arg volume "$(jq -er .begin.volumeIdHex "$install_dir/install-prepared-v2.json")" '
      .protocol == "mini-spk-volume-adoption-v1" and
      .executionClaim == "read-only-root-witness" and .installJournal == $install and
      .sourceVolumeIdHex == $volume and
      .rootWitness == "/run/minidregg/spk/volume-attest/8401.witness" and
      (.sizeMiB | type == "number" and . >= 64 and . <= 16384 and floor == .)
      ' "$volume_adoption" >/dev/null ||
      fail "volume adoption malformed"
    [ "$(jq -er .completedSha256 "$volume_adoption")" = \
      "$(sha "$install_dir/install-completed-v2.json")" ] ||
      fail "INSTALL completion changed after volume adoption"
    sha256sum -c "$volume_action/input-sha256.txt" >/dev/null ||
      fail "source or physical volume changed after adoption"
    [ ! -e "$resident_dir" ] || fail "resident attempt already exists"
    jq -e '.protocol == "mini-spk-resident-config-request-v1" and
      (.agents | type == "array" and all(.[]; .protocol == "mini-spk-agent-api-v3"))' \
      "$request" >/dev/null ||
      fail "journey requires explicit v3 lifetime agent routes (or no agents)"
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
