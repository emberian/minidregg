#!/usr/bin/env bash
# journey.d/jwell.sh — realm wells (K-WELL, MUD J-MUD-2's kernel rows), on the
# journey's fresh Store, after J5 (which enrolled the third key).
#
# Roles: A = the sponsor (realm founder), B = the newcomer (a player),
# R = the third key (the referee). A creates the realm `tidewrack`, then births
# two wells in it, `gold` and `kelp` (`mini well new`, an account born --in the
# realm whose law is the predicate below), and opens a root account `purse`
# whose owner grant B holds (`workspace create --kind account --owner B`). A delegates `mintAsset` on gold to R, and on kelp to B; the well law
# names only A and R as minters, so B's kelp grant is refused by the LAW.
#
# The well law (both wells): any [ request/verb in {observe, transfer,
# delegate, burnAsset}, request/subject in {A, R} ] — every verb but mintAsset
# is the well's ordinary owner traffic; mintAsset is the founder's or the
# referee's. A burn is the holder's: it targets the debited account under that
# account's law (B's purse: permit-all), with B's own owner grant.
#
# Rows (expect admitted|refused; a refusal is the Host's encoded reason):
#   r-mints-20-gold-to-b     R's delegated mintAsset on gold, law names R  -> admitted
#   r-mints-kelp-no-grant    R presents its gold grant for kelp            -> refused noGrant
#   b-mints-gold-no-grant    B presents its purse grant for gold           -> refused noGrant
#   b-mints-kelp-not-law     B holds mintAsset on kelp; the law names A,R  -> refused lawRefused
#   a-mints-5-kelp-to-b      the founder's owner grant on kelp             -> admitted
#   b-burns-5-gold           B burns from its own purse                    -> admitted
#   b-overburns-gold         B burns 100 holding 15                        -> refused bookRefused
#   r-burns-b-gold           R presents its gold grant to debit B's purse  -> refused noGrant
#   mint-credit-asset        a mint naming the credit asset's well         -> refused creditWell
#   mint-root-account        a mint naming a root account (no realm)       -> refused notRealmWell
#   conservation-gold/kelp   ledger: holders + well = 0, −well = Σmint − Σburn
#   credit-well-unchanged    the credit asset's well is the same before and after
#   cold-reopen-audit        service stopped: `audit` re-admits every record
#   cold-ledger-equal        the cold ledger equals the live one (book root and wells)
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS NEWCOMER_WS
# NEWCOMER_SUBJECT SPONSOR_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR.
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
TW=$W/third-workspace
mkdir -p "$D/req"
rows=$D/well-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

run() { # NAME cmd...
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
host_refused() {
  [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG" "$D/$1.err"
}
refusal_text() {
  grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' ' | cut -c1-200
}
row() { # NAME EXPECT(admitted|refused) [REASON]
  local name=$1 expect=$2 reason=${3:-} got detail
  if [ "$(cat "$D/$name.rc")" = 0 ]; then got=admitted
  elif host_refused "$name"; then got=refused
  else got=client-error
  fi
  detail=$([ "$got" = refused ] && refusal_text "$name" || tail -1 "$D/$name.err" | cut -c1-200)
  [ "$got" = admitted ] && detail=$(jq -c '{op,well,account,amount}' "$D/$name.out" 2>/dev/null | tail -1)
  printf '%s\texpect=%s%s\tgot=%s\t%s\n' "$name" "$expect" "${reason:+ $reason}" "$got" "$detail" >>"$rows"
  if [ "$got" != "$expect" ]; then bad=$((bad + 1))
  elif [ -n "$reason" ] && [[ "$detail" != *"$reason"* ]]; then bad=$((bad + 1))
    echo "$name refused for the wrong reason (want $reason)" >&2
  fi
}
check() { # NAME EXPECT GOT [DETAIL] — GOT must equal EXPECT; DETAIL is printed only
  local name=$1 expect=$2 got=$3 detail=${4:-}
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$name" "$expect" "$got" "$detail" >>"$rows"
  [ "$expect" = "$got" ] || bad=$((bad + 1))
}
ok() { # NAME
  [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; cat "$rows" >&2; exit 1; }
}
ledger() { # OUT — the operator-local ledger read of the live Store
  "$HOST" "$CONFIG" well-ledger "$1" >"$1.out" 2>"$1.err" || { echo "well-ledger failed: $(tail -1 "$1.err")" >&2; exit 1; }
}
well_json() { # LEDGER ASSET -> the well row
  jq -c --arg a "$2" '.wells[] | select(.asset == $a)' "$1"
}

A=$SPONSOR_SUBJECT
B=$NEWCOMER_SUBJECT
R=$(jq -r .subject "$TW/workspace.json")
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
jq -n --arg a "$A" --arg r "$R" '{type:"any",predicates:[
  {type:"memberOf",slot:"request/verb",values:["1","2","3","9"]},
  {type:"memberOf",slot:"request/subject",values:[$a,$r]}]}' >"$D/req/well-law.json"

# The realm, its two wells, and B's purse.
run create-realm "$MINI" workspace --action create --dir "$SPONSOR_WS" --name tidewrack --storage declared \
  --predicate "$D/req/permit-all.json"; ok create-realm
run well-new-gold "$MINI" well --action new --dir "$SPONSOR_WS" --name gold --in tidewrack \
  --law "$D/req/well-law.json"; ok well-new-gold
run well-new-kelp "$MINI" well --action new --dir "$SPONSOR_WS" --name kelp --in tidewrack \
  --law "$D/req/well-law.json"; ok well-new-kelp
# B's purse: a root account the founder opens for B (B holds its owner grant).
run b-purse "$MINI" workspace --action create --dir "$SPONSOR_WS" --name purse-b --storage declared \
  --kind account --owner "$B" --predicate "$D/req/permit-all.json"; ok b-purse
pcap=$(jq -r .operationCapability "$SPONSOR_WS/refs/purse-b.json")
run b-import-purse "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name purse --kind account \
  --target "$(jq -r .target "$SPONSOR_WS/refs/purse-b.json")" --observe-capability "$pcap" \
  --operation-capability "$pcap"; ok b-import-purse
realm=$(jq -r .target "$SPONSOR_WS/refs/tidewrack.json")
gold=$(jq -r .target "$SPONSOR_WS/refs/gold.json")
kelp=$(jq -r .target "$SPONSOR_WS/refs/kelp.json")
purse=$(jq -r .target "$NEWCOMER_WS/refs/purse.json")
jq -e --arg r "$realm" '.birth.resources[0].room == $r and .birth.resources[0].kind == "account"' \
  "$SPONSOR_WS/sources/create-gold.json" >/dev/null || { echo "gold's birth source is not an account in the realm" >&2; exit 1; }

# A delegates mintAsset on gold to R and on kelp to B.
delegate() { # ID WELL RECIPIENT-SUBJECT RECIPIENT-WS
  jq -n --arg n "$2" --arg r "$3" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,
    recipient:$r,verbs:["observe","mintAsset"],maxCost:"50000"}' >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/$1.json" \
    --proposal-id "$1"; ok "$1-propose"
  run "$1-submit" "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
    --intent "$SPONSOR_WS/proposals/$1/intent.json" --attempt "$SPONSOR_WS/attempts/$1"; ok "$1-submit"
  run "$1-publish" "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id "$1" \
    --attempt "$SPONSOR_WS/attempts/$1"; ok "$1-publish"
  run "$1-import" "$MINI" workspace --action import --dir "$4" --name "$2" \
    --from-ref "$SPONSOR_WS/proposals/$1/recipient-reference.json"; ok "$1-import"
}
delegate grant-r-gold gold "$R" "$TW"
delegate grant-b-kelp kelp "$B" "$NEWCOMER_WS"
rgold=$(jq -r .observeCapability "$TW/refs/gold.json")
bpurse=$(jq -r .operationCapability "$NEWCOMER_WS/refs/purse.json")

ledger "$D/ledger-before.json"
credit=$(jq -r .creditAsset "$D/ledger-before.json")
creditBefore=$(jq -r .creditWell "$D/ledger-before.json")
# a root account: B's purse has no realm
run r-mints-20-gold-to-b "$MINI" well --action mint --dir "$TW" --well gold --account "$purse" --amount 20
row r-mints-20-gold-to-b admitted
run r-mints-kelp-no-grant "$MINI" well --action mint --dir "$TW" --well "$kelp" --account "$purse" \
  --amount 5 --capability "$rgold"
row r-mints-kelp-no-grant refused noGrant
run b-mints-gold-no-grant "$MINI" well --action mint --dir "$NEWCOMER_WS" --well "$gold" --account purse \
  --amount 5 --capability "$bpurse"
row b-mints-gold-no-grant refused noGrant
run b-mints-kelp-not-law "$MINI" well --action mint --dir "$NEWCOMER_WS" --well kelp --account purse --amount 5
row b-mints-kelp-not-law refused lawRefused
run a-mints-5-kelp-to-b "$MINI" well --action mint --dir "$SPONSOR_WS" --well kelp --account "$purse" --amount 5
row a-mints-5-kelp-to-b admitted
run b-burns-5-gold "$MINI" well --action burn --dir "$NEWCOMER_WS" --well "$gold" --account purse --amount 5
row b-burns-5-gold admitted
run b-overburns-gold "$MINI" well --action burn --dir "$NEWCOMER_WS" --well "$gold" --account purse --amount 100
row b-overburns-gold refused bookRefused
run r-burns-b-gold "$MINI" well --action burn --dir "$TW" --well "$gold" --account "$purse" --amount 1 \
  --capability "$rgold"
row r-burns-b-gold refused noGrant
run mint-credit-asset "$MINI" well --action mint --dir "$TW" --well "$credit" --account "$purse" --amount 1 \
  --capability "$rgold"
row mint-credit-asset refused creditWell
run mint-root-account "$MINI" well --action mint --dir "$NEWCOMER_WS" --well "$purse" --account "$gold" \
  --amount 1 --capability "$bpurse"
row mint-root-account refused notRealmWell

# Conservation and the audit identity, from the ledger.
ledger "$D/ledger-after.json"
for pair in "gold:$gold:20:5" "kelp:$kelp:5:0"; do
  IFS=: read -r name asset mintedSum burnedSum <<<"$pair"
  wrow=$(well_json "$D/ledger-after.json" "$asset")
  w=$(jq -r .well <<<"$wrow"); h=$(jq -r .holdersSum <<<"$wrow"); t=$(jq -r .total <<<"$wrow")
  r=$(jq -r .realm <<<"$wrow")
  check "conservation-$name" "realm=$realm holders+well=0 -well=$((mintedSum - burnedSum))" \
    "realm=$r holders+well=$((h + w)) -well=$((-w))" "well=$w holders=$h total=$t"
done
check credit-well-unchanged "creditWell=$creditBefore creditTotal=0" \
  "creditWell=$(jq -r .creditWell "$D/ledger-after.json") creditTotal=$(jq -r .creditTotal "$D/ledger-after.json")" \
  "credit asset $credit"

# Cold reopen: stop our service, audit the closed Store, read the ledger cold,
# then start the service again on the same socket (the runner checks it is ours).
pid=$(cat "$W/public/server.pid")
kids=$(pgrep -P "$pid" | tr '\n' ' ')
kill -TERM "$pid"
for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
for k in $kids; do for i in $(seq 1 100); do kill -0 "$k" 2>/dev/null || break; sleep 0.1; done; done
"$HOST" "$CONFIG" audit >"$D/audit.out" 2>"$D/audit.err"; arc=$?
check cold-reopen-audit "exit=0" "exit=$arc"
printf 'cold-reopen-audit-detail\t%s\n' "$(cat "$D/audit.out" "$D/audit.err" | tail -1 | cut -c1-160)" >>"$rows"
ledger "$D/ledger-cold.json"
check cold-ledger-equal "$(jq -c '{bookRoot,creditWell,wells}' "$D/ledger-after.json")" \
  "$(jq -c '{bookRoot,creditWell,wells}' "$D/ledger-cold.json")"
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-kwell.log" 2>&1 </dev/null &
echo "$!" >"$W/public/server.pid"
for i in $(seq 1 600); do [ -S "$SOCKET" ] && break; sleep 0.1; done

cat "$rows" >&2
n=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $n well rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$n/$n well rows as expected: R mints gold by grant+law; no-grant, law-refused, overburn, credit and rootless refused by name; conservation, credit untouched, cold audit and ledger equal" >&2
echo "$rows"
