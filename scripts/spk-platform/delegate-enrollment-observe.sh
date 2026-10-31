#!/bin/sh
# One observe-only grant for event28. Native Mini retains the prepared call;
# after a send marker, recovery is exact lookup only.
set -eu
umask 077
fail() { echo "enrollment observe: $*" >&2; exit 2; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
absolute() {
  case "$1" in /*) ;; *) fail "absolute path required" ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/')
    fail "canonical path required" ;;
  esac
}
private_dir() {
  [ -d "$1" ] && [ ! -L "$1" ] || fail "private directory missing"
  [ "$(stat -c '%u:%a' "$1")" = "$(id -u):700" ] || fail "private directory owner/mode"
}
private_file() {
  [ -f "$1" ] && [ ! -L "$1" ] || fail "private file missing"
  [ "$(stat -c '%u:%a' "$1")" = "$(id -u):600" ] || fail "private file owner/mode"
}
protected_chain() {
  path=$1
  while :; do
    [ -d "$path" ] && [ ! -L "$path" ] || fail "directory ancestor absent or linked"
    owner=$(stat -c '%u' "$path")
    mode=$(stat -c '%a' "$path")
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory ancestor"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor"
    [ "$path" = / ] && break
    path=${path%/*}; [ -n "$path" ] || path=/
  done
}
protected_binary() {
  [ -f "$1" ] && [ ! -L "$1" ] && [ -x "$1" ] || fail "binary absent or linked"
  owner=$(stat -c '%u' "$1"); mode=$(stat -c '%a' "$1")
  { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign binary"
  [ $((0$mode & 022)) -eq 0 ] || fail "writable binary"
  protected_chain "${1%/*}"
}
load() {
  attempt=$1; absolute "$attempt"; private_dir "$attempt"; private_file "$attempt/pin.json"
  private_dir "$attempt/native"; private_file "$attempt/native/call.bin"
  private_file "$attempt/intent.json"
  root=$(jq -er .root "$attempt/pin.json")
  mini=$(jq -er .mini "$attempt/pin.json")
  socket=$(jq -er .socket "$attempt/pin.json")
  host=$(jq -er .host "$attempt/pin.json")
  config=$(jq -er .config "$attempt/pin.json")
  overlay=$(jq -er .overlay "$attempt/pin.json")
  absolute "$config"
  protected_binary "$mini"; protected_binary "$host"
  protected_chain "$root"; protected_chain "${overlay%/*}"
  protected_chain "${config%/*}"; protected_chain "${socket%/*}"
  [ -S "$socket" ] && [ ! -L "$socket" ] || fail "operator socket changed"
  private_file "$overlay"; private_file "$config"
  stage=$(jq -er .stage "$attempt/pin.json")
  if [ "$stage" != - ]; then
    absolute "$stage"; protected_chain "${stage%/*}"
    private_dir "$stage"; private_dir "$stage/issue"
    private_file "$stage/issue/receipt-anchor.json"; private_file "$stage/issue/plan.bin"
    [ "$(sha "$stage/issue/receipt-anchor.json")" = \
      "$(jq -er .issueReceiptSha256 "$attempt/pin.json")" ] || fail "event22 receipt anchor changed"
    [ "$(sha "$stage/issue/plan.bin")" = \
      "$(jq -er .issuePlanSha256 "$attempt/pin.json")" ] || fail "event22 plan changed"
  fi
  jq -e --arg mini "$(sha "$mini")" --arg host "$(sha "$host")" \
    --arg config "$(sha "$config")" --arg overlay "$(sha "$overlay")" \
    --arg call "$(sha "$attempt/native/call.bin")" \
    --arg intent "$(sha "$attempt/intent.json")" \
    '.type == "mini-spk-enrollment-observe-attempt-v1" and
     .miniSha256 == $mini and .hostSha256 == $host and
     .configSha256 == $config and .overlaySha256 == $overlay and
     .callSha256 == $call and .intentSha256 == $intent' \
    "$attempt/pin.json" >/dev/null || fail "retained pin differs"
}
if [ "$#" -eq 13 ] && [ "$1" = prepare ]; then
  root=$2 host=$3 config=$4 mini=$5 socket=$6 overlay=$7 route=$8 kind=$9
  stage=${10}; attempt=${11}; host_sha=${12}; mini_sha=${13}
  for p in "$root" "$host" "$config" "$mini" "$socket" "$overlay" "$attempt"; do absolute "$p"; done
  case "$root" in /var/lib/minidregg/spk/fixtures/*) ;; *) fail "fixture root" ;; esac
  case "$attempt" in "$root"/continuations/*) ;; *) fail "attempt path" ;; esac
  private_dir "${attempt%/*}"; private_file "$overlay"
  protected_chain "$root"; protected_chain "${overlay%/*}"
  protected_chain "${config%/*}"; protected_chain "${socket%/*}"
  [ ! -e "$attempt" ] && [ ! -L "$attempt" ] || fail "attempt already exists"
  protected_binary "$host"; protected_binary "$mini"
  [ -S "$socket" ] && [ ! -L "$socket" ] || fail "operator socket missing"
  [ "$(sha "$host")" = "$host_sha" ] && [ "$(sha "$mini")" = "$mini_sha" ] || fail "binary pin"
  private_file "$config"
  allocation=$root/source-stage/agent-allocation.json
  [ "$(sha "$allocation")" = "$(jq -er .allocationSha256 "$overlay")" ] || fail "allocation changed"
  jq -e --arg a "$allocation" '.type == "mini-spk-enrollment-observe-overlay-v1" and .allocation == $a and
    ([.grants[].childCapability] | unique | length) == 11 and
    all(.grants[]; .parentSubject == "8" and .verbs == ["observe"])' "$overlay" >/dev/null || fail "overlay shape"
  spec=$(jq -c --arg r "$route" --arg k "$kind" '[.grants[] | select(.route == $r and .kind == $k)] | if length == 1 then .[0] else error("grant missing") end' "$overlay") || fail "grant not allocated"
  resource=$(printf '%s\n' "$spec" | jq -er .resource)
  parent=$(printf '%s\n' "$spec" | jq -er .parentCapability)
  child=$(printf '%s\n' "$spec" | jq -er .childCapability)
  holder=$(printf '%s\n' "$spec" | jq -er .holder)
  case "$route" in
    alice-web|alice-api) [ "$holder" = 8 ] || fail "Alice holder"; recipient_key=$root/base/workroom/tool.key ;;
    bob-web) [ "$holder" = 9 ] || fail "Bob holder"; recipient_key=$root/base/workroom/member.key ;;
    hermes-a) [ "$holder" = 10 ] || fail "Hermes A holder"; recipient_key=$root/base/workroom/agents/hermes-a/controller.key ;;
    hermes-b) [ "$holder" = 20 ] || fail "Hermes B holder"; recipient_key=$root/base/workroom/agents/hermes-b/controller.key ;;
    *) fail "unknown route" ;;
  esac
  owner_key=$root/base/workroom/tool.key
  [ -f "$owner_key" ] && [ -f "$recipient_key" ] || fail "signer unavailable"
  case "$kind" in
    app) [ "$resource:$parent" = 8401:141 ] && [ "$stage" = - ] || fail "app parent" ;;
    manifest) [ "$resource:$parent" = 8402:143 ] && [ "$stage" = - ] || fail "manifest parent" ;;
    ticket)
      absolute "$stage"; private_dir "$stage"; private_dir "$stage/issue"
      private_file "$stage/preview-plan.json"
      private_file "$stage/preview-plan.bin"; private_file "$stage/issue/plan.bin"
      private_file "$stage/issue/receipt-anchor.json"
      cmp -s "$stage/preview-plan.bin" "$stage/issue/plan.bin" ||
        fail "accepted event22 plan differs from reviewed ticket scope"
      jq -e --arg resource "$resource" --arg parent "$parent" \
        --arg child "$child" --arg holder "$holder" '
        .type == "application-grain-share-issue-plan-v1" and
        .request.spec.ticket.resource == $resource and
        .request.spec.ticketOwnerCapability == $parent and
        .request.spec.ticket.participant.ticketObserveCapability == $child and
        .request.spec.ticket.participant.subject == $holder' \
        "$stage/preview-plan.json" >/dev/null || fail "event22 ticket selection differs"
      jq -e '.type == "minidregg-grain-share-issue-receipt-anchor-v1" and
        (.receipt.acceptedCount | type == "string")' "$stage/issue/receipt-anchor.json" >/dev/null || fail "event22 receipt absent"
      ;;
    *) fail "unknown kind" ;;
  esac
  mkdir -m 700 "$attempt"
  "$(dirname "$0")/prepare-enrollment-observe-overlay.sh" "$root" \
    "$attempt/expected-overlay.json" >"$attempt/overlay-verify.stdout" ||
    fail "approved append-only overlay cannot be reproduced"
  cmp -s "$overlay" "$attempt/expected-overlay.json" ||
    fail "delegation overlay differs from retained allocation and approved IDs"
  printf '%s\n' "$spec" >"$attempt/spec.json"; chmod 600 "$attempt/spec.json"
  # Readback probes may use nonce+4..+10003; adjacent child IDs must not overlap.
  nonce=$((2000000 + child * 20000))
  query() {
    label=$1 subject=$2 capability=$3 key=$4 suffix=$5 view=$6
    jq -n --arg subject "$subject" --arg nonce "$((nonce + suffix))" \
      --arg target "$resource" --arg cap "$capability" --arg view "$view" '
      {subject:$subject,nonce:$nonce,purpose:{type:"query",kind:"object",target:$target,view:$view},
       grants:[{kind:"object",target:$target,capability:$cap}]}' >"$attempt/$label-intent.json"
    chmod 600 "$attempt/$label-intent.json"
    "$mini" query --host "$host" --config "$config" --socket "$socket" \
      --intent "$attempt/$label-intent.json" --key "$key" --view "$view" \
      --dir "$attempt/$label" >"$attempt/$label.stdout" 2>"$attempt/$label.stderr"
  }
  query parent-cap 8 "$parent" "$owner_key" 0 capability
  "$host" "$config" inspect view-object-capability "$attempt/parent-cap/view.bin" \
    "$attempt/parent-inspected.json" || fail "parent cap inspection"
  jq -e --arg p "$parent" --arg resource "$resource" '
    .kind == "object" and .head.id == $p and
    .head.holder == {type:"subject",subject:"8"} and
    (.head.targets | index($resource) != null) and
    (.head.verbs | index("observe") != null and index("delegate") != null)' \
    "$attempt/parent-inspected.json" >/dev/null || fail "parent lacks delegated observe authority"
  query parent-resource 8 "$parent" "$owner_key" 1 resource
  jq -e --slurpfile p "$attempt/parent-cap/challenge.json" '
    .domain == $p[0].domain and .semantics == $p[0].semantics and
    .imageBoundary == $p[0].imageBoundary and
    .signing[0].authorityRoot == $p[0].signing[0].authorityRoot' \
    "$attempt/parent-resource/challenge.json" >/dev/null || fail "current parent changed"
  jq -n --slurpfile cap "$attempt/parent-inspected.json" \
    --slurpfile current "$attempt/parent-resource/challenge.json" \
    --slurpfile view "$attempt/parent-resource/view.json" \
    --arg target "$resource" --arg holder "$holder" --arg child "$child" \
    --arg nonce "$((nonce + 2))" --arg commandNonce "$((nonce + 3))" '
    $cap[0].head as $p | $current[0] as $c |
    {subject:"8",nonce:$nonce,purpose:{type:"prepare",draft:{type:"delegate-source",
      command:{kind:"object",domain:$c.domain,semantics:$c.semantics,subject:"8",
        nonce:$commandNonce,expectedTargetRoot:$view[0].page.root,parentId:$p.id,
        target:$target,expectedPreRoot:$c.signing[0].authorityRoot,
        child:($p + {id:$child,parent:$p.id,holder:{type:"subject",subject:$holder},
          targets:[$target],verbs:["observe"],ancestors:(($p.ancestors + [$p.id]) | unique)})}}},
      grants:[{kind:"object",target:$target,capability:$p.id}]}' >"$attempt/intent.json"
  chmod 600 "$attempt/intent.json"
  "$mini" submit --host "$host" --config "$config" --socket "$socket" \
    --intent "$attempt/intent.json" --key "$owner_key" --prepare-only true \
    --dir "$attempt/native" >"$attempt/prepare.stdout" 2>"$attempt/prepare.stderr" ||
    fail "native delegation prepare refused"
  issue_plan_sha=; issue_receipt_sha=
  if [ "$stage" != - ]; then
    issue_plan_sha=$(sha "$stage/issue/plan.bin")
    issue_receipt_sha=$(sha "$stage/issue/receipt-anchor.json")
  fi
  jq -n --arg root "$root" --arg host "$host" --arg config "$config" --arg mini "$mini" \
    --arg socket "$socket" --arg overlay "$overlay" --arg route "$route" --arg kind "$kind" \
    --arg stage "$stage" --arg issuePlanSha256 "$issue_plan_sha" \
    --arg issueReceiptSha256 "$issue_receipt_sha" \
    --arg resource "$resource" --arg child "$child" --arg holder "$holder" \
    --arg hostSha256 "$host_sha" --arg miniSha256 "$mini_sha" \
    --arg configSha256 "$(sha "$config")" --arg overlaySha256 "$(sha "$overlay")" \
    --arg callSha256 "$(sha "$attempt/native/call.bin")" --arg intentSha256 "$(sha "$attempt/intent.json")" '
    {type:"mini-spk-enrollment-observe-attempt-v1",root:$root,host:$host,config:$config,mini:$mini,
     socket:$socket,overlay:$overlay,route:$route,kind:$kind,stage:$stage,
     issuePlanSha256:$issuePlanSha256,issueReceiptSha256:$issueReceiptSha256,
     resource:$resource,
     child:$child,holder:$holder,hostSha256:$hostSha256,miniSha256:$miniSha256,
     configSha256:$configSha256,overlaySha256:$overlaySha256,
     callSha256:$callSha256,intentSha256:$intentSha256}' >"$attempt/pin.json"
  chmod 600 "$attempt/pin.json"
  echo "observe delegation prepared at $attempt; send once after review"
  exit 0
fi
if [ "$#" -eq 2 ] && [ "$1" = send ]; then
  load "$2"
  [ ! -e "$attempt/send-requested.json" ] || fail "already sent; lookup only"
  jq -n --arg call "$(sha "$attempt/native/call.bin")" \
    '{type:"mini-spk-enrollment-observe-send-v1",callSha256:$call}' >"$attempt/send-candidate.json"
  chmod 600 "$attempt/send-candidate.json"
  (set -C; cat "$attempt/send-candidate.json" >"$attempt/send-requested.json") || fail "send raced"
  chmod 600 "$attempt/send-requested.json"
  "$mini" retry --attempt "$attempt/native" --mode submit --socket "$socket" ||
    fail "delegation uncertain; exact lookup only"
  echo "delegation sent; lookup exact receipt"
  exit 0
fi
if [ "$#" -eq 2 ] && [ "$1" = lookup ]; then
  load "$2"; private_file "$attempt/send-requested.json"
  jq -e --arg call "$(sha "$attempt/native/call.bin")" '
    .type == "mini-spk-enrollment-observe-send-v1" and .callSha256 == $call' \
    "$attempt/send-requested.json" >/dev/null || fail "send marker differs"
  "$mini" retry --attempt "$attempt/native" --mode lookup --socket "$socket" ||
    fail "delegation lookup uncertain; no second send"
  latest=$(find "$attempt/native" -maxdepth 1 -type f -name 'retry-*.json' | sort | tail -1)
  [ -n "$latest" ] && [ ! -L "$latest" ] || fail "lookup outcome absent"
  jq -e '.type == "confirmed" and
    (.confirmation == "installed" or .confirmation == "replayed") and
    (.transactionId|type == "string") and (.eventId|type == "string") and
    (.acceptedCount|type == "string") and (.imageBoundary|type == "string")' \
    "$latest" >/dev/null || fail "delegation not accepted"
  if [ ! -e "$attempt/confirmed.json" ]; then
    candidate=$(mktemp "$attempt/confirmed-candidate-XXXXXXXX.json")
    jq -n --arg call "$(sha "$attempt/native/call.bin")" --slurpfile o "$latest" '
      {type:"mini-spk-enrollment-observe-confirmed-v1",callSha256:$call,
       receipt:($o[0]|{transactionId,eventId,acceptedCount,imageBoundary})}' \
      >"$candidate"
    chmod 600 "$candidate"
    ln "$candidate" "$attempt/confirmed.json" || fail "confirmed publication raced"
    rm "$candidate"
  else
    private_file "$attempt/confirmed.json"
    jq -e --arg call "$(sha "$attempt/native/call.bin")" --slurpfile o "$latest" '
      .type == "mini-spk-enrollment-observe-confirmed-v1" and .callSha256 == $call and
      .receipt == ($o[0]|{transactionId,eventId,acceptedCount,imageBoundary})' \
      "$attempt/confirmed.json" >/dev/null || fail "receipt changed"
  fi
  if [ ! -e "$attempt/child-inspected.json" ]; then
    route=$(jq -er .route "$attempt/pin.json")
    holder=$(jq -er .holder "$attempt/pin.json")
    resource=$(jq -er .resource "$attempt/pin.json")
    child=$(jq -er .child "$attempt/pin.json")
    case "$route" in
      alice-web|alice-api) recipient_key=$root/base/workroom/tool.key ;;
      bob-web) recipient_key=$root/base/workroom/member.key ;;
      hermes-a) recipient_key=$root/base/workroom/agents/hermes-a/controller.key ;;
      hermes-b) recipient_key=$root/base/workroom/agents/hermes-b/controller.key ;;
      *) fail "unknown retained route" ;;
    esac
    index=0
    while :; do
      suffix=$(printf '%04d' "$index")
      probe=$attempt/child-query-$suffix
      [ ! -e "$probe" ] && [ ! -L "$probe" ] &&
        [ ! -e "$attempt/child-inspected-$suffix.json" ] &&
        [ ! -L "$attempt/child-inspected-$suffix.json" ] &&
        [ ! -e "$attempt/child-intent-$suffix.json" ] &&
        [ ! -L "$attempt/child-intent-$suffix.json" ] && break
      index=$((index + 1)); [ "$index" -le 9999 ] || fail "readback names exhausted"
    done
    nonce=$((2000000 + child * 20000 + 4 + index))
    jq -n --arg subject "$holder" --arg nonce "$nonce" \
      --arg resource "$resource" --arg cap "$child" '
      {subject:$subject,nonce:$nonce,purpose:{type:"query",kind:"object",
       target:$resource,view:"capability"},
       grants:[{kind:"object",target:$resource,capability:$cap}]}' \
      >"$attempt/child-intent-$suffix.json"
    chmod 600 "$attempt/child-intent-$suffix.json"
    "$mini" query --host "$host" --config "$config" --socket "$socket" \
      --intent "$attempt/child-intent-$suffix.json" --key "$recipient_key" \
      --view capability --dir "$probe" \
      >"$attempt/child-query-$suffix.stdout" 2>"$attempt/child-query-$suffix.stderr" ||
      fail "confirmed grant recipient readback uncertain; retry lookup"
    "$host" "$config" inspect view-object-capability "$probe/view.bin" \
      "$attempt/child-inspected-$suffix.json" || fail "child cap inspection"
    jq -e --arg child "$child" --arg holder "$holder" --arg resource "$resource" '
      .kind == "object" and .head.id == $child and
      .head.holder == {type:"subject",subject:$holder} and
      (.head.targets | index($resource) != null) and
      .head.verbs == ["observe"]' "$attempt/child-inspected-$suffix.json" >/dev/null ||
      fail "confirmed child grant differs"
    ln "$attempt/child-inspected-$suffix.json" "$attempt/child-inspected.json" ||
      fail "child readback publication raced"
  fi
  private_file "$attempt/child-inspected.json"
  child=$(jq -er .child "$attempt/pin.json")
  holder=$(jq -er .holder "$attempt/pin.json")
  resource=$(jq -er .resource "$attempt/pin.json")
  jq -e --arg child "$child" --arg holder "$holder" --arg resource "$resource" '
    .kind == "object" and .head.id == $child and
    .head.holder == {type:"subject",subject:$holder} and
    (.head.targets | index($resource) != null) and .head.verbs == ["observe"]' \
    "$attempt/child-inspected.json" >/dev/null || fail "retained child readback differs"
  matching=0
  for inspected in "$attempt"/child-inspected-[0-9][0-9][0-9][0-9].json; do
    if [ -f "$inspected" ] && [ ! -L "$inspected" ] &&
       cmp -s "$inspected" "$attempt/child-inspected.json"; then matching=1; break; fi
  done
  [ "$matching" -eq 1 ] || fail "retained child readback lacks exact native inspection"
  echo "observe delegation exact receipt retained at $attempt/confirmed.json"
  exit 0
fi
fail "usage: $0 prepare ROOT HOST CONFIG MINI SOCKET OVERLAY ROUTE app|manifest|ticket STAGE|- NEW_ATTEMPT HOST_SHA MINI_SHA | send ATTEMPT | lookup ATTEMPT"
