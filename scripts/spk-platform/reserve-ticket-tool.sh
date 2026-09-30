#!/bin/sh
# One ordinary AgentGrain reserve(3) for the next event22 ticket issue.
# This is a custody wrapper around Mini's existing submit/lookup transport.
# A lost submit reply is lookup-only; no second reserve is authorized here.
set -eu
umask 077

fail() { echo "ticket tool reserve: $*" >&2; exit 2; }
absolute() { case "$1" in /*) ;; *) fail "absolute path required" ;; esac; }
chain() {
  node=$1
  while :; do
    [ -d "$node" ] && [ ! -L "$node" ] || fail "protected directory absent"
    meta=$(stat -c '%u:%a' "$node")
    owner=${meta%%:*}; mode=${meta#*:}
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory owner"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor"
    [ "$node" = / ] && break
    node=${node%/*}; [ -n "$node" ] || node=/
  done
}
private() {
  absolute "$1"; chain "${1%/*}"
  [ -f "$1" ] && [ ! -L "$1" ] || fail "private file unavailable: $1"
  meta=$(stat -c '%u:%a:%h:%s' "$1")
  case "$meta" in "$(id -u):600:1:"*) ;; *) fail "private file custody drift: $1" ;; esac
  size=${meta##*:}; [ "$size" -gt 0 ] && [ "$size" -le "${2:-65536}" ] ||
    fail "private file size refused: $1"
}
sha() { sha256sum "$1" | cut -d ' ' -f1; }
pin_binary() {
  absolute "$1"; chain "${1%/*}"
  [ -f "$1" ] && [ -x "$1" ] && [ ! -L "$1" ] || fail "binary unavailable"
  binary_meta=$(stat -c '%u:%a:%h' "$1")
  binary_owner=${binary_meta%%:*}
  binary_mode=${binary_meta#*:}; binary_mode=${binary_mode%%:*}
  binary_links=${binary_meta##*:}
  { [ "$binary_owner" = 0 ] || [ "$binary_owner" = "$(id -u)" ]; } ||
    fail "binary owner differs"
  [ "$binary_links" = 1 ] && [ $((0$binary_mode & 022)) -eq 0 ] ||
    fail "binary custody drift"
  printf '%s' "$2" | grep -Eq '^[0-9a-f]{64}$' || fail "bad binary digest"
  [ "$(sha "$1")" = "$2" ] || fail "binary changed"
}
root() {
  ROOT=$1; absolute "$ROOT"; chain "$ROOT"
  [ "$(stat -c '%u:%a' "$ROOT")" = "$(id -u):700" ] ||
    fail "reserve root custody drift"
}
load_active() {
  root "$1"; private "$ROOT/active.json" 4096
  ATTEMPT=$(jq -er .attempt "$ROOT/active.json")
  MINI=$(jq -er .mini "$ROOT/active.json")
  HOST=$(jq -er .host "$ROOT/active.json")
  CONFIG=$(jq -er .config "$ROOT/active.json")
  SOCKET=$(jq -er .socket "$ROOT/active.json")
  KEY=$(jq -er .key "$ROOT/active.json")
  pin_binary "$MINI" "$(jq -er .miniSha256 "$ROOT/active.json")"
  pin_binary "$HOST" "$(jq -er .hostSha256 "$ROOT/active.json")"
  private "$CONFIG"; private "$KEY" 32
  [ "$(stat -c %s "$KEY")" -eq 32 ] || fail "signer is not raw32"
  absolute "$SOCKET"; chain "${SOCKET%/*}"
  [ -S "$SOCKET" ] && [ ! -L "$SOCKET" ] || fail "operator socket absent"
  absolute "$ATTEMPT"; chain "$ATTEMPT"
  [ "$ATTEMPT" = "$ROOT/$(jq -er .route "$ROOT/active.json")-$(jq -er .nonce "$ROOT/active.json")" ] ||
    fail "active attempt path differs"
  [ "$(stat -c '%u:%a' "$ATTEMPT")" = "$(id -u):700" ] ||
    fail "attempt custody drift"
  private "$ATTEMPT/intent.json"
  jq -e --arg config "$(sha "$CONFIG")" --arg key "$(sha "$KEY")" \
    --arg intent "$(sha "$ATTEMPT/intent.json")" '
    .configSha256 == $config and .keySha256 == $key and
    .intentSha256 == $intent' "$ROOT/active.json" >/dev/null ||
    fail "retained reserve inputs changed"
  private "$ATTEMPT/native/call.bin" 12102759
  jq -e --arg call "$(sha "$ATTEMPT/native/call.bin")" \
    '.type == "mini-spk-ticket-tool-reserve-active-v1" and
     .charge == "3" and .callSha256 == $call' "$ROOT/active.json" >/dev/null ||
    fail "active exact call changed"
}

if [ "$#" -eq 10 ] && [ "$1" = prepare ]; then
  MINI=$2 HOST=$3 CONFIG=$4 SOCKET=$5 KEY=$6 ROOT=$7 ROUTE=$8 NONCE=$9
  MINI_SHA=${10}
  fail "prepare also requires HOST_SHA; see usage"
fi

if [ "$#" -eq 11 ] && [ "$1" = prepare ]; then
  MINI=$2 HOST=$3 CONFIG=$4 SOCKET=$5 KEY=$6 ROOT=$7 ROUTE=$8 NONCE=$9
  MINI_SHA=${10} HOST_SHA=${11}
  case "$ROUTE" in alice-web|bob-web|alice-api|hermes-a|hermes-b) ;;
    *) fail "unallocated issue route" ;; esac
  printf '%s' "$NONCE" | grep -Eq '^[1-9][0-9]{0,11}$' || fail "reserve nonce refused"
  pin_binary "$MINI" "$MINI_SHA"; pin_binary "$HOST" "$HOST_SHA"
  private "$CONFIG"; private "$KEY" 32
  [ "$(stat -c %s "$KEY")" -eq 32 ] || fail "signer is not raw32"
  absolute "$SOCKET"; chain "${SOCKET%/*}"
  [ -S "$SOCKET" ] && [ ! -L "$SOCKET" ] || fail "operator socket absent"
  root "$ROOT"
  [ ! -e "$ROOT/active.json" ] && [ ! -L "$ROOT/active.json" ] ||
    fail "prior reserve/issue unresolved"
  ATTEMPT=$ROOT/$ROUTE-$NONCE
  [ ! -e "$ATTEMPT" ] && [ ! -L "$ATTEMPT" ] || fail "attempt exists"
  mkdir -m 700 "$ATTEMPT"
  QUERY_NONCE=$((NONCE + 1))
  jq -n --arg nonce "$QUERY_NONCE" '
    {subject:"8",nonce:$nonce,purpose:{type:"query",kind:"object",
      target:"7902",view:"resource"},
     grants:[{kind:"object",target:"7902",capability:"81"}]}
    ' >"$ATTEMPT/before-intent.json"
  chmod 600 "$ATTEMPT/before-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$ATTEMPT/before-intent.json" --key "$KEY" --view resource \
    --dir "$ATTEMPT/before" >"$ATTEMPT/query.stdout" 2>"$ATTEMPT/query.stderr" ||
    fail "source-current tool query refused"
  chmod 600 "$ATTEMPT/query.stdout" "$ATTEMPT/query.stderr"
  private "$ATTEMPT/before/view.json" 1048576
  private "$ATTEMPT/before/challenge.json" 1048576
  jq -e '.cell.grain.task == "7902" and .cell.grain.status == "1" and
    .cell.grain.reserved == "0" and
    (.cell.grain.remaining | tonumber >= 3)' \
    "$ATTEMPT/before/view.json" >/dev/null ||
    fail "tool is not settled with at least 3 remaining"
  jq -n --arg nonce "$NONCE" \
    --slurpfile read "$ATTEMPT/before/view.json" \
    --slurpfile challenge "$ATTEMPT/before/challenge.json" '
    {grain:{task:"7902",subject:"8",capability:"81",observeCapability:"81",
      schemaVersion:"1",expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
      expectedTargetRoot:$read[0].cell.root,
      context:{operationId:$nonce,payload:"one event22 ticket birth reserve"},
      before:($read[0].cell.grain | {generation,status,remaining,reserved}),
      operation:{type:"reserve",amount:"3"},publications:[]},
     grants:[{kind:"object",target:"7902",capability:"81"}],intentNonce:$nonce}
    ' >"$ATTEMPT/intent.json"
  chmod 600 "$ATTEMPT/intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$ATTEMPT/intent.json" --intent-kind grain-intent \
    --key "$KEY" --dir "$ATTEMPT/native" --prepare-only true \
    >"$ATTEMPT/prepare.stdout" 2>"$ATTEMPT/prepare.stderr" ||
    fail "source reserve prepare refused; no native send"
  chmod 600 "$ATTEMPT/prepare.stdout" "$ATTEMPT/prepare.stderr"
  private "$ATTEMPT/native/call.bin" 12102759
  jq -n --arg route "$ROUTE" --arg nonce "$NONCE" \
    --arg attempt "$ATTEMPT" --arg mini "$MINI" --arg miniSha "$MINI_SHA" \
    --arg host "$HOST" --arg hostSha "$HOST_SHA" --arg config "$CONFIG" \
    --arg configSha "$(sha "$CONFIG")" --arg socket "$SOCKET" --arg key "$KEY" \
    --arg keySha "$(sha "$KEY")" --arg call "$(sha "$ATTEMPT/native/call.bin")" \
    --arg intent "$(sha "$ATTEMPT/intent.json")" '
    {type:"mini-spk-ticket-tool-reserve-active-v1",route:$route,nonce:$nonce,
     charge:"3",attempt:$attempt,mini:$mini,miniSha256:$miniSha,
     host:$host,hostSha256:$hostSha,config:$config,configSha256:$configSha,
     socket:$socket,key:$key,keySha256:$keySha,callSha256:$call,
     intentSha256:$intent}
    ' >"$ATTEMPT/active-candidate.json"
  chmod 600 "$ATTEMPT/active-candidate.json"
  (set -C; cat "$ATTEMPT/active-candidate.json" >"$ROOT/active.json") ||
    fail "another reserve became active"
  chmod 600 "$ROOT/active.json"
  sync -f "$ROOT/active.json" "$ROOT" "$ATTEMPT/native/call.bin"
  echo "exact reserve prepared at $ATTEMPT; send once only after review"
  exit 0
fi

if [ "$#" -eq 2 ] && [ "$1" = send ]; then
  load_active "$2"
  [ ! -e "$ATTEMPT/send-requested.json" ] && [ ! -L "$ATTEMPT/send-requested.json" ] ||
    fail "reserve submit already requested; lookup only"
  jq -n --arg call "$(sha "$ATTEMPT/native/call.bin")" '
    {type:"mini-spk-ticket-tool-reserve-send-requested-v1",callSha256:$call}
    ' >"$ATTEMPT/send-candidate.json"
  chmod 600 "$ATTEMPT/send-candidate.json"
  (set -C; cat "$ATTEMPT/send-candidate.json" >"$ATTEMPT/send-requested.json") ||
    fail "reserve submit raced"
  chmod 600 "$ATTEMPT/send-requested.json"
  sync -f "$ATTEMPT/send-requested.json" "$ATTEMPT" "$ROOT"
  "$MINI" retry --attempt "$ATTEMPT/native" --mode submit --socket "$SOCKET" ||
    fail "submit outcome uncertain; use lookup, never send again"
  echo "reserve submit returned; use lookup to confirm exact accepted receipt"
  exit 0
fi

if [ "$#" -eq 2 ] && [ "$1" = lookup ]; then
  load_active "$2"
  private "$ATTEMPT/send-requested.json" 4096
  jq -e --arg call "$(sha "$ATTEMPT/native/call.bin")" '
    .type == "mini-spk-ticket-tool-reserve-send-requested-v1" and
    .callSha256 == $call' "$ATTEMPT/send-requested.json" >/dev/null ||
    fail "one-send marker differs"
  "$MINI" retry --attempt "$ATTEMPT/native" --mode lookup --socket "$SOCKET" ||
    fail "exact reserve lookup uncertain; no second send"
  latest=$(find "$ATTEMPT/native" -maxdepth 1 -type f -name 'retry-*.json' |
    sort | tail -1)
  [ -n "$latest" ] || fail "lookup produced no outcome"
  private "$latest" 1048576
  jq -e '.type == "confirmed" and
    (.confirmation == "installed" or .confirmation == "replayed") and
    (.transactionId | type == "string") and
    (.eventId | type == "string") and
    (.acceptedCount | type == "string") and
    (.worldRoot | type == "string")' "$latest" >/dev/null ||
    fail "reserve not confirmed"
  if [ ! -e "$ATTEMPT/confirmed.json" ]; then
    jq -n --arg call "$(sha "$ATTEMPT/native/call.bin")" \
      --slurpfile outcome "$latest" '
      {type:"mini-spk-ticket-tool-reserve-confirmed-v1",callSha256:$call,
       receipt:($outcome[0] | {transactionId,eventId,acceptedCount,worldRoot})}
      ' >"$ATTEMPT/confirmed.json"
    chmod 600 "$ATTEMPT/confirmed.json"
    sync -f "$ATTEMPT/confirmed.json" "$ATTEMPT"
  else
    private "$ATTEMPT/confirmed.json" 4096
    jq -e --arg call "$(sha "$ATTEMPT/native/call.bin")" \
      --slurpfile outcome "$latest" '
      .type == "mini-spk-ticket-tool-reserve-confirmed-v1" and
      .callSha256 == $call and
      .receipt == ($outcome[0] | {transactionId,eventId,acceptedCount,worldRoot})
      ' "$ATTEMPT/confirmed.json" >/dev/null || fail "reserve receipt changed"
  fi
  if [ ! -e "$ATTEMPT/after-view.json" ]; then
    NONCE=$(jq -er .nonce "$ROOT/active.json")
    after_index=0
    while :; do
      suffix=$(printf '%04d' "$after_index")
      after_dir=$ATTEMPT/after-query-$suffix
      after_intent=$ATTEMPT/after-intent-$suffix.json
      [ ! -e "$after_dir" ] && [ ! -L "$after_dir" ] &&
        [ ! -e "$after_intent" ] && [ ! -L "$after_intent" ] && break
      after_index=$((after_index + 1))
      [ "$after_index" -le 9999 ] || fail "readback evidence names exhausted"
    done
    QUERY_NONCE=$((NONCE + 2 + after_index))
    jq -n --arg nonce "$QUERY_NONCE" '
      {subject:"8",nonce:$nonce,purpose:{type:"query",kind:"object",
        target:"7902",view:"resource"},
       grants:[{kind:"object",target:"7902",capability:"81"}]}
      ' >"$after_intent"
    chmod 600 "$after_intent"
    "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
      --intent "$after_intent" --key "$KEY" --view resource \
      --dir "$after_dir" \
      >"$ATTEMPT/after-query-$suffix.stdout" \
      2>"$ATTEMPT/after-query-$suffix.stderr" ||
      fail "reserved tool current readback unavailable"
    chmod 600 "$ATTEMPT/after-query-$suffix.stdout" \
      "$ATTEMPT/after-query-$suffix.stderr"
    private "$after_dir/view.json" 1048576
    jq -e --slurpfile before "$ATTEMPT/before/view.json" '
      .cell.grain.task == "7902" and .cell.grain.status == "3" and
      .cell.grain.generation == $before[0].cell.grain.generation and
      .cell.grain.reserved == "3" and
      (.cell.grain.remaining | tonumber) ==
        (($before[0].cell.grain.remaining | tonumber) - 3)
      ' "$after_dir/view.json" >/dev/null ||
      fail "source-current reserve post-state differs"
    (set -C; cat "$after_dir/view.json" >"$ATTEMPT/after-view.json") ||
      fail "reserved readback raced"
    chmod 600 "$ATTEMPT/after-view.json"
    sync -f "$ATTEMPT/after-view.json" "$ATTEMPT"
  else
    private "$ATTEMPT/after-view.json" 1048576
  fi
  echo "exact reserve receipt retained at $ATTEMPT/confirmed.json"
  exit 0
fi

if [ "$#" -eq 3 ] && [ "$1" = advance-ticket ]; then
  load_active "$2"
  ISSUE=$3; absolute "$ISSUE"; chain "$ISSUE"
  [ "$(stat -c '%u:%a' "$ISSUE")" = "$(id -u):700" ] ||
    fail "ticket issue custody drift"
  STAGE=${ISSUE%/*}
  [ "$ISSUE" = "$STAGE/issue" ] || fail "ticket issue path differs"
  private "$STAGE/stage.json" 65536
  SCOPE=$(jq -er .scope "$STAGE/stage.json")
  private "$SCOPE"
  ROUTE=$(jq -er .route "$ROOT/active.json")
  case "$ROUTE" in alice-web|bob-web|alice-api|hermes-a|hermes-b) ;;
    *) fail "active reserve is not for an event22 ticket" ;; esac
  [ "$(jq -er .route "$SCOPE")" = "$ROUTE" ] ||
    fail "accepted ticket route differs from active reserve"
  private "$ATTEMPT/confirmed.json" 4096
  private "$ATTEMPT/after-view.json" 1048576
  private "$ISSUE/plan.bin" 12102759
  private "$ISSUE/plan-inspected.json" 1048576
  private "$ISSUE/ingress.bin" 12102759
  private "$ISSUE/submit-marker.json" 4096
  private "$ISSUE/receipt-anchor.json" 4096
  probe_index=0
  while :; do
    PROBE=$ATTEMPT/issue-plan-$(printf '%04d' "$probe_index").json
    [ ! -e "$PROBE" ] && [ ! -L "$PROBE" ] && break
    probe_index=$((probe_index + 1))
    [ "$probe_index" -le 9999 ] || fail "plan probe names exhausted"
  done
  "$HOST" "$CONFIG" inspect application-grain-share-issue-plan \
    "$ISSUE/plan.bin" "$PROBE" ||
    fail "accepted issue plan source inspection refused"
  chmod 600 "$PROBE"
  jq -e --slurpfile retained "$ISSUE/plan-inspected.json" \
    '. == $retained[0]' "$PROBE" >/dev/null ||
    fail "ticket plan inspection changed"
  jq -e --slurpfile after "$ATTEMPT/after-view.json" '
    .type == "application-grain-share-issue-plan-v1" and
    .finalizedGrainBirth.tool.task == "7902" and
    .finalizedGrainBirth.tool.capability == "81" and
    .finalizedGrainBirth.tool.observeCapability == "81" and
    .finalizedGrainBirth.tool.root == $after[0].cell.root and
    .finalizedGrainBirth.tool.before ==
      ($after[0].cell.grain | {generation,status,remaining,reserved}) and
    .finalizedGrainBirth.parent.task == "7901"
    ' "$PROBE" >/dev/null ||
    fail "event22 did not consume exact retained reserve post-state"
  index=0
  while :; do
    stem=$(printf 'issue-lookup-%04d' "$index")
    [ ! -e "$ATTEMPT/$stem.stdout" ] && [ ! -e "$ATTEMPT/$stem.stderr" ] && break
    index=$((index + 1)); [ "$index" -le 9999 ] || fail "lookup evidence names exhausted"
  done
  "$MINI" grain-share-issue-lookup --socket "$SOCKET" --attempt "$ISSUE" \
    >"$ATTEMPT/$stem.stdout" 2>"$ATTEMPT/$stem.stderr" ||
    fail "exact event22 lookup uncertain; active reserve retained"
  chmod 600 "$ATTEMPT/$stem.stdout" "$ATTEMPT/$stem.stderr"
  jq -e --slurpfile anchor "$ISSUE/receipt-anchor.json" '
    .type == "confirmed" and .confirmation == "replayed" and
    {transactionId,eventId,acceptedCount,worldRoot} == $anchor[0].receipt
    ' "$ATTEMPT/$stem.stdout" >/dev/null ||
    fail "event22 receipt differs from retained anchor"
  NONCE=$(jq -er .nonce "$ROOT/active.json")
  ARCHIVE=$ROOT/closed-$ROUTE-$NONCE.json
  [ ! -e "$ARCHIVE" ] && [ ! -L "$ARCHIVE" ] || fail "closure already exists"
  jq -n --arg route "$ROUTE" --arg nonce "$NONCE" \
    --arg reserve "$(sha "$ATTEMPT/native/call.bin")" \
    --arg issue "$(sha "$ISSUE/ingress.bin")" \
    --arg plan "$(sha "$ISSUE/plan.bin")" \
    --slurpfile reserveReceipt "$ATTEMPT/confirmed.json" \
    --slurpfile issueReceipt "$ISSUE/receipt-anchor.json" '
    {type:"mini-spk-ticket-tool-reserve-closed-v1",route:$route,nonce:$nonce,
     reserveCallSha256:$reserve,issueIngressSha256:$issue,issuePlanSha256:$plan,
     reserveReceipt:$reserveReceipt[0].receipt,
     issueReceipt:$issueReceipt[0].receipt}
    ' >"$ATTEMPT/closure-candidate.json"
  chmod 600 "$ATTEMPT/closure-candidate.json"
  if [ -e "$ATTEMPT/closure.json" ]; then
    private "$ATTEMPT/closure.json" 4096
    cmp -s "$ATTEMPT/closure-candidate.json" "$ATTEMPT/closure.json" ||
      fail "prior closure evidence differs"
  else
    (set -C; cat "$ATTEMPT/closure-candidate.json" >"$ATTEMPT/closure.json") ||
      fail "closure write raced"
    chmod 600 "$ATTEMPT/closure.json"
    sync -f "$ATTEMPT/closure.json" "$ATTEMPT"
  fi
  mv "$ROOT/active.json" "$ARCHIVE"
  sync -f "$ARCHIVE" "$ROOT"
  echo "accepted event22 consumed exact reserve; archived at $ARCHIVE"
  exit 0
fi

echo "usage: $0 prepare MINI HOST CONFIG SOCKET KEY ROOT ROUTE NONCE MINI_SHA HOST_SHA" >&2
echo "       $0 send ROOT" >&2
echo "       $0 lookup ROOT" >&2
echo "       $0 advance-ticket ROOT EXACT_EVENT22_STAGE/issue" >&2
exit 2
