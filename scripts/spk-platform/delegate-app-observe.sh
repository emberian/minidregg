#!/bin/sh
# Continue the existing Store with separately held observe-only app grants.
# Requires the source-owned view-object-capability inspector; no codec or
# issuer/policy epoch is reconstructed by this script.
set -eu
umask 077
if [ "$#" -ne 5 ]; then
  echo "usage: $0 PREPARED_ROOT QUALIFIED_HOST MINI OPERATOR_SOCKET NEW_EVIDENCE" >&2
  exit 2
fi
ROOT=$1 HOST=$2 MINI=$3 SOCKET=$4 EVIDENCE=$5
fail() { echo "app observe delegation: $*" >&2; exit 2; }
absolute() {
  case "$1" in /*) ;; *) fail "absolute path required" ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/') fail "canonical path required" ;; esac
}
protected() {
  directory=$1
  while :; do
    [ -d "$directory" ] && [ ! -L "$directory" ] || fail "directory absent or linked"
    metadata=$(stat -c '%u:%a' "$directory")
    owner=${metadata%%:*}; mode=${metadata#*:}
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory owner"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor"
    [ "$directory" = / ] && break
    directory=${directory%/*}; [ -n "$directory" ] || directory=/
  done
}
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
for path in "$ROOT" "$HOST" "$MINI" "$SOCKET" "$EVIDENCE"; do absolute "$path"; done
case "$ROOT" in /var/lib/minidregg/spk/fixtures/*) ;; *) fail "unexpected fixture root" ;; esac
case "$EVIDENCE" in "$ROOT"/continuations/*) ;; *) fail "evidence must be under fixture continuations" ;; esac
protected "$ROOT"; protected "${EVIDENCE%/*}"
protected "${HOST%/*}"; protected "${MINI%/*}"; protected "${SOCKET%/*}"
[ ! -e "$EVIDENCE" ] && [ ! -L "$EVIDENCE" ] || fail "attempt already exists; reconcile retained calls"
[ -x "$HOST" ] && [ ! -L "$HOST" ] && [ -x "$MINI" ] && [ ! -L "$MINI" ] || fail "qualified executable absent"
[ -S "$SOCKET" ] && [ ! -L "$SOCKET" ] || fail "operator socket absent"
: "${QUALIFIED_HOST_SHA256:?set the source-qualified inspector Host SHA}"
[ "$(sha "$HOST")" = "$QUALIFIED_HOST_SHA256" ] || fail "Host hash mismatch"
CONFIG="$ROOT/base/workroom/deployment/pinned-config.json"
ALLOCATION="$ROOT/source-stage/agent-allocation.json"
MANIFEST="$ROOT/source-stage/base-executable-sha256.txt"
for file in "$CONFIG" "$ALLOCATION" "$MANIFEST"; do
  protected "${file%/*}"
  [ -s "$file" ] && [ ! -L "$file" ] || fail "retained fixture input absent"
done
CONFIG_SHA=$(awk -v file="$CONFIG" '$2 == file { print $1 }' "$MANIFEST")
MINI_SHA=$(awk -v file="$MINI" '$2 == file { print $1 }' "$MANIFEST")
[ "$(sha "$CONFIG")" = "$CONFIG_SHA" ] && [ "$(sha "$MINI")" = "$MINI_SHA" ] || fail "base config/client pin differs"
ALLOCATION_SHA=$(sha "$ALLOCATION")
jq -e '.app == "8401" and
  ([.humans[] | select(.route == "bob-web") | [.subject,.plannedCaps.appObserve]] == [["9","184"]]) and
  ([.agents[] | [.route,.controller.subject,.plannedCaps.appObserve]] ==
    [["hermes-a","10","274"],["hermes-b","20","374"]])' "$ALLOCATION" >/dev/null || fail "allocation differs"
mkdir -m 700 "$EVIDENCE"
sha256sum "$HOST" "$MINI" "$CONFIG" "$ALLOCATION" >"$EVIDENCE/input-sha256.txt"
query() {
  label=$1 subject=$2 capability=$3 key=$4 nonce=$5 view=$6
  jq -n --arg subject "$subject" --arg capability "$capability" --arg nonce "$nonce" --arg view "$view" '
    {subject:$subject,nonce:$nonce,purpose:{type:"query",kind:"object",target:"8401",view:$view},
     grants:[{kind:"object",target:"8401",capability:$capability}]}' >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" --view "$view" \
    --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout"
}
for route in bob-web hermes-a hermes-b; do
  case "$route" in
    bob-web) subject=9; child=184; key="$ROOT/base/workroom/member.key" ;;
    hermes-a) subject=10; child=274; key="$ROOT/base/workroom/agents/hermes-a/controller.key" ;;
    hermes-b) subject=20; child=374; key="$ROOT/base/workroom/agents/hermes-b/controller.key" ;;
  esac
  nonce=$((970000 + child * 10))
  owner_key="$ROOT/base/workroom/tool.key"
  query "$route-parent" 8 141 "$owner_key" "$nonce" capability
  "$HOST" "$CONFIG" inspect view-object-capability "$EVIDENCE/$route-parent/view.bin" \
    "$EVIDENCE/$route-parent/head.json"
  jq -e '.kind == "object" and .head.id == "141" and
    .head.holder == {type:"subject",subject:"8"} and
    (.head.targets | index("8401") != null) and
    (.head.verbs | index("observe") != null and index("delegate") != null)' \
    "$EVIDENCE/$route-parent/head.json" >/dev/null || fail "parent cannot delegate observation"
  query "$route-owner" 8 141 "$owner_key" "$((nonce + 1))" resource
  # A current signed query authenticates the parent. Refuse drift between the
  # retained parent and target reads; Mini checks again when preparing/submitting.
  jq -e --slurpfile parent "$EVIDENCE/$route-parent/challenge.json" '
    .domain == $parent[0].domain and .semantics == $parent[0].semantics and
    .worldRoot == $parent[0].worldRoot and
    .authorityRoot == $parent[0].authorityRoot' \
    "$EVIDENCE/$route-owner/challenge.json" >/dev/null || fail "current authority changed; retain attempt"
  jq -n --slurpfile cap "$EVIDENCE/$route-parent/head.json" \
    --slurpfile current "$EVIDENCE/$route-owner/challenge.json" \
    --slurpfile resource "$EVIDENCE/$route-owner/view.json" \
    --arg holder "$subject" --arg child "$child" --arg nonce "$((nonce + 2))" \
    --arg commandNonce "$((nonce + 3))" '
    $cap[0].head as $p | $current[0] as $c |
    {subject:"8",nonce:$nonce,purpose:{type:"prepare",draft:{type:"delegate-source",
      command:{kind:"object",domain:$c.domain,semantics:$c.semantics,subject:"8",nonce:$commandNonce,
        expectedTargetRoot:$resource[0].cell.root,parentId:$p.id,target:"8401",
        expectedPreRoot:$c.authorityRoot,
        child:($p + {id:$child,parent:$p.id,holder:{type:"subject",subject:$holder},
          targets:["8401"],verbs:["observe"],ancestors:(($p.ancestors + [$p.id]) | unique)})}}},
      grants:[{kind:"object",target:"8401",capability:$p.id}]}' >"$EVIDENCE/$route-delegate-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$route-delegate-intent.json" --key "$owner_key" \
    --dir "$EVIDENCE/$route-delegate" >"$EVIDENCE/$route-delegate.stdout"
  jq -e '.type == "confirmed" and
    (.confirmation == "installed" or .confirmation == "recoveredAfterUncertainResponse")' \
    "$EVIDENCE/$route-delegate/outcome.json" >/dev/null || fail "delegation not freshly confirmed"
  query "$route-observe" "$subject" "$child" "$key" "$((nonce + 4))" resource
  jq -e --slurpfile before "$EVIDENCE/$route-owner/view.json" \
    '.cell.root == $before[0].cell.root' "$EVIDENCE/$route-observe/view.json" >/dev/null || fail "app state changed during delegation"
  jq -cn --arg route "$route" --arg subject "$subject" --arg child "$child" \
    --slurpfile receipt "$EVIDENCE/$route-delegate/outcome.json" \
    '{route:$route,subject:$subject,app:"8401",capability:$child,verbs:["observe"],receipt:$receipt[0]}' \
    >>"$EVIDENCE/delegations.jsonl"
done
[ "$(sha "$CONFIG")" = "$CONFIG_SHA" ] && [ "$(sha "$ALLOCATION")" = "$ALLOCATION_SHA" ] || fail "fixture input drift"
sha256sum -c "$EVIDENCE/input-sha256.txt" >"$EVIDENCE/input-check.txt"
echo "three observe-only app delegations confirmed; retained receipts and recipient reads at $EVIDENCE"
