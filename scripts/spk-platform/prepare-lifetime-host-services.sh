#!/bin/sh
# Build the A/B event26 operator service table from two source-inspected,
# accepted event27 route handoffs. This writes a private Host config and asks
# the pinned source Host to reselect both grants read-only on its current Store;
# op80 and the event26 receiver still perform their own fresh admission.
set -eu
umask 077

fail() { echo "lifetime Host services: $*" >&2; exit 2; }
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
  [ -f "$1" ] && [ ! -L "$1" ] || fail "private file absent: $1"
  meta=$(stat -c '%u:%a:%h:%s' "$1")
  case "$meta" in "$(id -u):600:1:"*) ;; *) fail "private file custody drift: $1" ;; esac
  size=${meta##*:}; [ "$size" -gt 0 ] && [ "$size" -le "${2:-1048576}" ] ||
    fail "private file size refused: $1"
}

[ "$#" -eq 6 ] || fail "usage: $0 QUALIFIED_HOST HOST_SHA256 BASE_HOST_CONFIG A_ROUTE_DIR B_ROUTE_DIR NEW_OUTPUT_DIR"
HOST=$1 HOST_SHA=$2 BASE=$3 A=$4 B=$5 OUT=$6
absolute "$HOST"; chain "${HOST%/*}"
[ -f "$HOST" ] && [ -x "$HOST" ] && [ ! -L "$HOST" ] ||
  fail "qualified Host unavailable"
printf '%s' "$HOST_SHA" | grep -Eq '^[0-9a-f]{64}$' || fail "Host digest refused"
[ "$(sha256sum "$HOST" | cut -d ' ' -f1)" = "$HOST_SHA" ] ||
  fail "qualified Host changed"
private "$BASE"
for dir in "$A" "$B"; do
  absolute "$dir"; chain "$dir"
  [ "$(stat -c '%u:%a' "$dir")" = "$(id -u):700" ] || fail "route directory custody drift"
  private "$dir/controller-route-v3.json"
  private "$dir/resident-custody-v3.json"
  private "$dir/accepted-grant.json"
  private "$dir/source-grant-ingress.bin" 12102759
  private "$dir/SHA256SUMS"
  (cd "$dir" && sha256sum -c SHA256SUMS >/dev/null) || fail "route source manifest changed"
done
absolute "$OUT"; chain "${OUT%/*}"
[ ! -e "$OUT" ] && [ ! -L "$OUT" ] || fail "output exists"
jq -e '
  .agentLifetimeDispatchFixed == null and
  .agentLifetimeDispatchServices == null and .agentDispatchFixed == null and
  (.providerServices | type == "array" and length == 2)
  ' "$BASE" >/dev/null || fail "base Host has conflicting or absent service pins"

for pair in "workroom-app:$A" "coding-app:$B"; do
  expected=${pair%%:*}; dir=${pair#*:}
  jq -e --arg expected "$expected" \
    --slurpfile custody "$dir/resident-custody-v3.json" \
    --slurpfile grant "$dir/accepted-grant.json" '
    def decimal: type == "string" and test("^(0|[1-9][0-9]*)$");
    .name == $expected and
    .appResource == "8401" and .packageManifest? == null and
    .signedApiPath == "/repo.git/" and
    .grantAttemptDir != null and
    .grantIssueIndex == $grant[0].grantIssueIndex and
    .grantResource == $grant[0].grantResource and
    .grantDigest == $grant[0].grantDigest and
    .grantInitializedRoot == $grant[0].grantInitializedRoot and
    .grantIssueReceipt == $grant[0].grantIssueReceipt and
    .originalIssueReceipt == $grant[0].originalEvent22Receipt and
    .dispatchSelectors.issueIndex == $grant[0].originalEvent22Index and
    .ticketResource == $grant[0].ticketResource and
    .sessionResource == $grant[0].session and
    .participantSubject == $grant[0].subject and
    .parentTask == $grant[0].parentTask and
    $custody[0].protocol == "mini-spk-agent-lifetime-custody-v3" and
    $custody[0].lineage.appResource == .appResource and
    $custody[0].lineage.sessionResource == .sessionResource and
    $custody[0].lineage.ticketResource == .ticketResource and
    $custody[0].lineage.originalIssueIndex == .dispatchSelectors.issueIndex and
    $custody[0].lineage.originalIssueReceipt == .originalIssueReceipt and
    $custody[0].lineage.grantIssueIndex == .grantIssueIndex and
    $custody[0].lineage.grantIssueReceipt == .grantIssueReceipt and
    $custody[0].lineage.grantDigest == .grantDigest and
    $custody[0].lineage.grantInitializedRoot == .grantInitializedRoot and
    $custody[0].lineage.grantResource == .grantResource and
    $custody[0].lineage.parentTask == .parentTask and
    $custody[0].lineage.purseTask == .purseResource and
    $custody[0].packageManifest == .dispatchSelectors.packageManifest and
    $custody[0].snapshotManifest == .dispatchSelectors.snapshotManifest and
    $custody[0].sessionObserveCapability == .dispatchSelectors.sessionObserve and
    $custody[0].manifestObserveCapability == .dispatchSelectors.manifestObserve and
    $custody[0].enrollmentObserveCapability == .dispatchSelectors.enrollmentObserve and
    $custody[0].grantObserveCapability == $grant[0].grantObserveCapability and
    ([.grantIssueIndex,.grantResource,.dispatchSelectors.issueIndex,
      .ticketResource,.parentTask,.purseResource] | all(.[]; decimal)) and
    (if $expected == "workroom-app" then
       .sessionResource == "8420" and .ticketResource == "8520" and
       .grantResource == "8530" and .parentTask == "7920" and
       .purseResource == "7940" and .participantSubject == "10"
     else
       .sessionResource == "8422" and .ticketResource == "8521" and
       .grantResource == "8531" and .parentTask == "7921" and
       .purseResource == "7941" and .participantSubject == "20"
     end)
    ' "$dir/controller-route-v3.json" >/dev/null || fail "route/grant/custody identity differs"
  jq -er .canonicalIngressHex "$dir/accepted-grant.json" |
    xxd -r -p | cmp -s - "$dir/source-grant-ingress.bin" ||
    fail "source-selected grant ingress differs"
done

mkdir -m 700 "$OUT"
jq -n --slurpfile base "$BASE" \
  --slurpfile ar "$A/controller-route-v3.json" \
  --slurpfile ac "$A/resident-custody-v3.json" \
  --slurpfile br "$B/controller-route-v3.json" \
  --slurpfile bc "$B/resident-custody-v3.json" '
  def smallnat: if type == "string" and test("^(0|[1-9][0-9]{0,14})$")
    then tonumber else error("Host selector exceeds exact jq integer bound") end;
  def service($r;$c):
    {legacy:{issueIndex:($r.dispatchSelectors.issueIndex|smallnat),
      ticketResource:($r.ticketResource|smallnat),
      packageManifest:($r.dispatchSelectors.packageManifest|smallnat),
      snapshotManifest:($r.dispatchSelectors.snapshotManifest|smallnat),
      sessionObserve:($r.dispatchSelectors.sessionObserve|smallnat),
      manifestObserve:($r.dispatchSelectors.manifestObserve|smallnat),
      enrollmentObserve:($r.dispatchSelectors.enrollmentObserve|smallnat),
      parentTask:($r.parentTask|smallnat),
      parentCapability:($c.parentCapability|smallnat),
      parentObserve:($c.parentObserve|smallnat),
      purseTask:($r.purseResource|smallnat),
      purseCapability:($c.purseCapability|smallnat),
      purseObserve:($c.purseObserve|smallnat),
      payerSubject:($c.payerSubject|smallnat),
      reserveAmount:($c.reserveAmount|smallnat),
      maximumCharge:($c.maximumCharge|smallnat)},
     grantIssueIndex:($r.grantIssueIndex|smallnat),
     grantResource:($r.grantResource|smallnat),
     grantObserveCapability:($c.grantObserveCapability|smallnat)};
  $base[0] + {agentLifetimeDispatchServices:[service($ar[0];$ac[0]),
    service($br[0];$bc[0])]}
  ' >"$OUT/host-config.json"
chmod 600 "$OUT/host-config.json"
jq -e '.agentLifetimeDispatchFixed == null and
  (.agentLifetimeDispatchServices | length == 2 and .[0] != .[1]) and
  .agentLifetimeDispatchServices[0].legacy.ticketResource == 8520 and
  .agentLifetimeDispatchServices[1].legacy.ticketResource == 8521' \
  "$OUT/host-config.json" >/dev/null || fail "assembled Host table differs"
# The final config must replay-select each exact event27 ingress on the same
# Store through the pinned source Host. A retained JSON alone is not authority.
for pair in "a:$A" "b:$B"; do
  name=${pair%%:*}; dir=${pair#*:}
  "$HOST" "$OUT/host-config.json" inspect-accepted-agent-lifetime-grant \
    "$dir/source-grant-ingress.bin" "$OUT/reinspected-$name.json" \
    >"$OUT/reinspect-$name.stdout" 2>"$OUT/reinspect-$name.stderr" ||
    fail "current source grant inspection refused"
  chmod 600 "$OUT/reinspected-$name.json" \
    "$OUT/reinspect-$name.stdout" "$OUT/reinspect-$name.stderr"
  jq -e --slurpfile original "$dir/accepted-grant.json" \
    '. == $original[0]' "$OUT/reinspected-$name.json" >/dev/null ||
    fail "current Store grant projection differs"
done
[ "$(sha256sum "$HOST" | cut -d ' ' -f1)" = "$HOST_SHA" ] ||
  fail "qualified Host changed during read-only replay"
sha256sum "$HOST" "$BASE" "$A/controller-route-v3.json" "$A/resident-custody-v3.json" \
  "$A/accepted-grant.json" "$B/controller-route-v3.json" \
  "$B/resident-custody-v3.json" "$B/accepted-grant.json" \
  "$OUT/host-config.json" "$OUT/reinspected-a.json" "$OUT/reinspected-b.json" \
  >"$OUT/SHA256SUMS"
chmod 600 "$OUT/SHA256SUMS"
echo "A/B lifetime Host service candidate prepared at $OUT; read-only grant reinspection only"
