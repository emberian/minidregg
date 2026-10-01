#!/bin/sh
# Two independently credentialed Mini Stores exchange one selected content
# version through a real fn node.
#
#   Store A (source):    its own genesis, domain and sponsor key. A creates a
#                        content resource with a selected atom and an
#                        unselected atom, then publishes only the selected one.
#   Store B (recipient): its own genesis, domain and sponsor key. B enrolls A's
#                        PUBLIC key under A's home subject (A signs the
#                        possession header in a separate process; no process
#                        holds both secrets), creates an inbox, delegates a
#                        child capability on it to that subject and installs
#                        the exact owner-subject law the release receiver
#                        requires.
#   fn:                  a freshly initialized fn Store and node from the
#                        supplied launcher. fn is semi-untrusted transport:
#                        acceptance or retrieval is never Mini admission.
#
# Phases then run through `mini selected-exchange`: prepare and publish under
# A's key, receive-transport into B's served Store, exact retry,
# verify-transport. Disclosure, tampered-article, tampered-packet, wrong-signer
# and wrong-root cases are checked at their recorded boundaries.
#
# Usage: selected-exchange-journey.sh HOST MINI STORE VERIFIER FN_LAUNCHER FN_CORE NEW_ROOT
# Optional environment: FN_OPENSSL_PREFIX, FN_PORT (default 11241),
#   SOURCE_DOMAIN/SOURCE_SUBJECT (8611/7), RECIPIENT_DOMAIN/RECIPIENT_SUBJECT (8612/8).
# Every service started here is stopped on exit. Nothing is ACKed at fn.
set -eu
umask 077

if [ "$#" -ne 7 ]; then
  echo "usage: $0 HOST MINI STORE VERIFIER FN_LAUNCHER FN_CORE NEW_ROOT" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 FN_LAUNCHER=$5 FN_CORE=$6 ROOT=$7
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
NEWPARTICIPANT=$HERE/newparticipant-acceptance.sh
SCRIPT=$HERE/selected-exchange-journey.sh
for executable in "$HOST" "$MINI" "$STORE" "$VERIFIER" "$FN_LAUNCHER" "$NEWPARTICIPANT"; do
  case "$executable" in /*) ;; *) echo "path must be absolute: $executable" >&2; exit 2;; esac
  [ -x "$executable" ] || { echo "not executable: $executable" >&2; exit 2; }
done
[ -f "$FN_CORE" ] || { echo "fn runtime image missing: $FN_CORE" >&2; exit 2; }
for tool in jq sha256sum openssl od ss; do
  command -v "$tool" >/dev/null 2>&1 || { echo "$tool is required" >&2; exit 2; }
done
case "$ROOT" in /*) ;; *) echo 'root must be absolute' >&2; exit 2;; esac
[ ! -e "$ROOT" ] && [ ! -L "$ROOT" ] || { echo 'root already exists' >&2; exit 2; }
FN_PORT=${FN_PORT:-11241}
SOURCE_DOMAIN=${SOURCE_DOMAIN:-8611} SOURCE_SUBJECT=${SOURCE_SUBJECT:-7}
RECIPIENT_DOMAIN=${RECIPIENT_DOMAIN:-8612} RECIPIENT_SUBJECT=${RECIPIENT_SUBJECT:-8}
[ "$SOURCE_DOMAIN" != "$RECIPIENT_DOMAIN" ] || { echo 'domains must differ' >&2; exit 2; }
[ "$SOURCE_SUBJECT" != "$RECIPIENT_SUBJECT" ] || {
  echo 'the recipient enrolls the source owner at its home subject; sponsor subjects must differ' >&2; exit 2;
}
if ss -ltnH | awk '{print $4}' | grep -Eq "(^|:)${FN_PORT}\$"; then
  echo "fn port $FN_PORT already occupied" >&2; exit 2
fi

mkdir -m 700 "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
A=$ROOT/a B=$ROOT/b FN=$ROOT/fn X=$ROOT/exchange-contract N=$ROOT/negative
TIMINGS=$ROOT/timings.tsv
printf 'step\tseconds\n' >"$TIMINGS"
sha256sum "$SCRIPT" "$NEWPARTICIPANT" "$HOST" "$MINI" "$STORE" "$VERIFIER" \
  "$FN_LAUNCHER" "$FN_CORE" >"$ROOT/input-sha256.txt"

FN_PID=
cleanup() {
  for pidfile in "$A/public/server.pid" "$B/public/server.pid"; do
    [ -f "$pidfile" ] || continue
    pid=$(cat "$pidfile")
    kill "$pid" 2>/dev/null || true
  done
  [ -z "$FN_PID" ] || kill "$FN_PID" 2>/dev/null || true
}
trap cleanup EXIT INT TERM

now() { date +%s.%N; }
STEP_START=
begin() { STEP_NAME=$1; STEP_START=$(now); echo "== $1" >&2; }
end() {
  printf '%s\t%s\n' "$STEP_NAME" \
    "$(echo "$(now) $STEP_START" | awk '{printf "%.3f", $1 - $2}')" >>"$TIMINGS"
}
confirmed() {
  jq -e --arg kind "$2" '.type == "confirmed" and .confirmation == $kind and
    (all(.transactionId, .eventId, .acceptedCount, .worldRoot;
      type == "string" and test("^(0|[1-9][0-9]*)$")))' "$1" >/dev/null
}
refused_admission() {
  jq -e '.type == "refused" and .phase == "61646d697373696f6e"' "$1" >/dev/null
}
hexfile() { od -An -tx1 -v "$1" | tr -d ' \n'; }
hexstr() { printf '%s' "$1" | od -An -tx1 -v | tr -d ' \n'; }
digest() { sha256sum "$1" | awk '{print $1}'; }
count_in() { # occurrences of a literal string in a binary file
  LC_ALL=C grep -a -o -F -- "$2" "$1" | wc -l | tr -d ' '
}
stop_service() {
  pidfile=$1/public/server.pid
  pid=$(cat "$pidfile")
  kill "$pid"
  n=0
  while kill -0 "$pid" 2>/dev/null; do
    n=$((n + 1)); [ "$n" -le 100 ] || { echo "service $pid did not stop" >&2; exit 1; }
    sleep 0.1
  done
  rm -f "$pidfile"
}
start_service() {
  root=$1
  socket=$root/public/mini.sock
  rm -f "$socket"
  nohup "$MINI" serve --host "$HOST" --config "$root/deployment/pinned-config.json" \
    --socket "$socket" >>"$root/public/serve.log" 2>&1 </dev/null &
  printf '%s\n' "$!" >"$root/public/server.pid"
  n=0
  until [ -S "$socket" ]; do
    kill -0 "$(cat "$root/public/server.pid")" 2>/dev/null || { echo 'service exited' >&2; exit 1; }
    n=$((n + 1)); [ "$n" -le 1200 ] || { echo 'socket timeout' >&2; exit 1; }
    sleep 0.1
  done
}
store_image() { # complete logical image of a Store, for equality checks
  "$STORE" read-to "$1/store" "$2"
}
# One signed resource or policy query by an explicit key and grant.
signed_query() {
  side_root=$1 key=$2 subject=$3 target=$4 capability=$5 view=$6 dir=$7
  jq -n --arg subject "$subject" --arg target "$target" --arg cap "$capability" \
    --arg view "$view" --arg nonce "$(od -An -tu8 -N8 /dev/urandom | tr -d ' ')" \
    '{subject:$subject,nonce:$nonce,
      purpose:{type:"query",kind:"object",target:$target,view:$view},
      grants:[{kind:"object",target:$target,capability:$cap}]}' >"$dir.intent.json"
  set -- --host "$HOST" --config "$side_root/deployment/pinned-config.json"
  if [ -f "$side_root/public/server.pid" ]; then set -- "$@" --socket "$side_root/public/mini.sock"; fi
  "$MINI" query "$@" --intent "$dir.intent.json" --key "$key" --view "$view" --dir "$dir" \
    >"$dir.stdout"
}
ws_submit() { # workspace, proposal id, attempt name
  "$MINI" workspace --action submit --dir "$1" \
    --intent "$1/proposals/$2/intent.json" --intent-kind intent \
    --attempt "$1/attempts/$3" >"$1/$3.stdout"
  confirmed "$1/attempts/$3/outcome.json" installed
}

# --- 1. Two independent Stores ------------------------------------------------
begin store-a-bootstrap
NEWPARTICIPANT_DOMAIN=$SOURCE_DOMAIN NEWPARTICIPANT_SPONSOR_SUBJECT=$SOURCE_SUBJECT \
  "$NEWPARTICIPANT" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$A" >"$ROOT/a-handoff.path"
end
begin store-b-bootstrap
NEWPARTICIPANT_DOMAIN=$RECIPIENT_DOMAIN NEWPARTICIPANT_SPONSOR_SUBJECT=$RECIPIENT_SUBJECT \
  "$NEWPARTICIPANT" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$B" >"$ROOT/b-handoff.path"
end
A_PUBLIC=$(hexfile "$A/sponsor.pub")
B_PUBLIC=$(hexfile "$B/sponsor.pub")
[ "$A_PUBLIC" != "$B_PUBLIC" ] || { echo 'sponsor keys unexpectedly equal' >&2; exit 1; }
# Each genesis enrolls exactly its own sponsor key; neither knows the other.
jq -e --arg k "$A_PUBLIC" --arg s "$SOURCE_SUBJECT" '.enrollments | length == 1 and
  .[0].key.publicKey == $k and .[0].key.subject == $s' "$A/genesis.json" >/dev/null
jq -e --arg k "$B_PUBLIC" --arg s "$RECIPIENT_SUBJECT" '.enrollments | length == 1 and
  .[0].key.publicKey == $k and .[0].key.subject == $s' "$B/genesis.json" >/dev/null
# The newcomer keys generated by the bootstrap fixture are not used here.
B_SEMANTICS=$(jq -er '.semantics' "$B/profile.json")

# --- 2. Source content: one selected and one unselected atom -------------------
SELECTED_TEXT="Selected note from Store A: the one version A chose to publish."
UNSELECTED_TEXT="Unselected draft in Store A: must never leave Store A."
begin a-create-notes
printf '%s\n' '{"type":"all","predicates":[]}' >"$A/open-law.json"
"$MINI" workspace --action create --dir "$A/sponsor" --name notes --storage content \
  --predicate "$A/open-law.json" >"$A/create-notes.stdout"
NOTES_TARGET=$(jq -er '.target' "$A/sponsor/refs/notes.json")
NOTES_OWNER_CAP=$(jq -er '.operationCapability' "$A/sponsor/refs/notes.json")
jq -n --arg sel "$(hexstr "$SELECTED_TEXT")" --arg uns "$(hexstr "$UNSELECTED_TEXT")" \
  '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"notes",
    payload:{type:"content",actions:[
      {type:"createAtom",atom:"7401",kind:{type:"text"},payload:$sel},
      {type:"createAtom",atom:"7402",kind:{type:"text"},payload:$uns}]}}]}' \
  >"$A/atoms-request.json"
"$MINI" workspace --action propose --dir "$A/sponsor" --request "$A/atoms-request.json" \
  --proposal-id atoms >"$A/atoms-propose.stdout"
ws_submit "$A/sponsor" atoms create-atoms
end
printf '%s' "$SELECTED_TEXT" >"$ROOT/selected-payload.bin"
begin a-signed-source-read
signed_query "$A" "$A/sponsor.key" "$SOURCE_SUBJECT" "$NOTES_TARGET" "$NOTES_OWNER_CAP" \
  resource "$A/source-read"
end
jq -e --arg sel "$(hexstr "$SELECTED_TEXT")" --arg uns "$(hexstr "$UNSELECTED_TEXT")" \
  '.cell.entries | length == 2 and
   any(.[]; .type == "atom" and .id == "7401" and .payload == $sel) and
   any(.[]; .type == "atom" and .id == "7402" and .payload == $uns)' \
  "$A/source-read/view.json" >/dev/null

# --- 3. B introduces A's home identity (A's public key only) -------------------
begin b-plan-home-identity
"$MINI" enroll --action plan --sponsor-workspace "$B/sponsor" --factory-ref factory \
  --name source-owner --new-public-key "$A/sponsor.pub" --home-subject "$SOURCE_SUBJECT" \
  --dir "$B/attempts/source-owner" >"$B/enroll-plan.json"
end
begin a-sign-possession
# A's process reads only B's retained Plan and command inspection, and A's own key.
"$MINI" enroll --action possess --dir "$B/attempts/source-owner" --key "$A/sponsor.key" \
  --subject "$SOURCE_SUBJECT" --output "$A/possession-for-b.sig" >"$A/possession.json"
end
begin b-seal-submit-home-identity
"$MINI" enroll --action seal --dir "$B/attempts/source-owner" \
  --possession-signature "$A/possession-for-b.sig" >"$B/enroll-seal.json"
"$MINI" enroll --action submit --dir "$B/attempts/source-owner" >"$B/enroll-submit.json"
end
jq -e --arg s "$SOURCE_SUBJECT" --arg k "$A_PUBLIC" '.type ==
  "minidregg-participant-enrollment-result-v1" and .subject == $s and .publicKey == $k and
  .keyPath == null and .authority == "admitted-key-only"' \
  "$B/attempts/source-owner/enrollment.json" >/dev/null
# B's attempt never names A's secret key.
if grep -r -l -F "$A/sponsor.key" "$B" >/dev/null 2>&1; then
  echo "B's state names A's secret key path" >&2; exit 1
fi

# --- 4. B's inbox, delegation to A's home subject, and the release law ---------
begin b-create-inbox
"$MINI" workspace --action create --dir "$B/sponsor" --name inbox --storage content \
  --predicate "$A/open-law.json" >"$B/create-inbox.stdout"
INBOX=$(jq -er '.target' "$B/sponsor/refs/inbox.json")
end
begin b-delegate-to-home-subject
jq -n --arg r "$SOURCE_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",
  name:"inbox",recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' \
  >"$B/delegate-request.json"
"$MINI" workspace --action propose --dir "$B/sponsor" --request "$B/delegate-request.json" \
  --proposal-id grant-source-owner >"$B/delegate-propose.stdout"
ws_submit "$B/sponsor" grant-source-owner grant-source-owner
"$MINI" workspace --action publish-delegation --dir "$B/sponsor" \
  --proposal-id grant-source-owner --attempt "$B/sponsor/attempts/grant-source-owner" \
  >"$B/publish-delegation.stdout"
REF=$B/sponsor/proposals/grant-source-owner/recipient-reference.json
jq -e --arg r "$SOURCE_SUBJECT" --arg t "$INBOX" '.type == "minidregg-delegated-reference-v1"
  and .recipient == $r and .target == $t' "$REF" >/dev/null
RECIPIENT_CAP=$(jq -er '.capability' "$REF")
end
begin b-install-release-law
jq -n --arg s "$SOURCE_SUBJECT" '{type:"minidregg-workspace-proposal-v1",
  action:"install-policy",name:"inbox",
  predicate:{type:"eq",slot:"request/subject",value:$s}}' >"$B/law-request.json"
"$MINI" workspace --action propose --dir "$B/sponsor" --request "$B/law-request.json" \
  --proposal-id release-law >"$B/law-propose.stdout"
ws_submit "$B/sponsor" release-law release-law
end
begin b-sponsor-read-after-law
# Observation: under the only law the release receiver accepts, B's own sponsor
# can no longer read the inbox.
if "$MINI" workspace --action read --dir "$B/sponsor" --name inbox \
    >"$B/sponsor-read-after-law.stdout" 2>"$B/sponsor-read-after-law.stderr"; then
  echo 'B-sponsor-read-after-law: admitted' >"$B/sponsor-read-after-law.verdict"
else
  echo 'B-sponsor-read-after-law: refused' >"$B/sponsor-read-after-law.verdict"
fi
end

# A's home identity reads B's current law and inbox root: the roots a release
# must pin come from a fresh authorized recipient read.
begin a-reads-recipient-law
signed_query "$B" "$A/sponsor.key" "$SOURCE_SUBJECT" "$INBOX" "$RECIPIENT_CAP" policy \
  "$B/owner-policy-read"
signed_query "$B" "$A/sponsor.key" "$SOURCE_SUBJECT" "$INBOX" "$RECIPIENT_CAP" resource \
  "$B/owner-inbox-read"
end
jq -e --arg s "$SOURCE_SUBJECT" '.predicate == {"type":"eq","slot":"request/subject","value":$s}' \
  "$B/owner-policy-read/view.json" >/dev/null
jq -e '.cell.entries == []' "$B/owner-inbox-read/view.json" >/dev/null
POLICY_ROOT=$(jq -er '.address' "$B/owner-policy-read/view.json")
AUTHORITY_ROOT=$(jq -er '.authorityRoot' "$B/owner-inbox-read/challenge.json")
TARGET_ROOT=$(jq -er '.cell.root' "$B/owner-inbox-read/view.json")

# --- 5. fn node ----------------------------------------------------------------
begin fn-provision
mkdir -m 700 "$FN"
cat >"$FN/fn-helper.sh" <<EOF
#!/bin/sh
${FN_OPENSSL_PREFIX:+export FN_OPENSSL_PREFIX=$FN_OPENSSL_PREFIX}
exec $FN_LAUNCHER "\$@"
EOF
chmod 500 "$FN/fn-helper.sh"
FNX=$FN/fn-helper.sh
cat >"$FN/fn.toml" <<EOF
[store]
path = "$FN/store"
[listener]
host = "127.0.0.1"
port = $FN_PORT
tls_cert = "$FN/tls-cert.pem"
tls_key = "$FN/tls-key.pem"
[control]
path = "$FN/control.sock"
[auth]
required = true
protected_only = true
path = "$FN/auth.toml"
EOF
openssl req -x509 -newkey rsa:2048 -sha256 -nodes -days 2 -subj /CN=localhost \
  -addext subjectAltName=DNS:localhost,IP:127.0.0.1 \
  -keyout "$FN/tls-key.pem" -out "$FN/tls-cert.pem" >"$FN/cert.log" 2>&1
"$FNX" --fn operator "$FN/fn.toml" init --max-article-octets 1048576 fn.test \
  >"$FN/init.stdout" 2>"$FN/init.stderr"
openssl rand -hex 32 >"$FN/posting-password"
{ cat "$FN/posting-password"; cat "$FN/posting-password"; } | \
  "$FNX" --fn operator "$FN/fn.toml" principal set-password selected-mini-publisher --posting \
  >"$FN/principal.stdout" 2>"$FN/principal.stderr"
nohup "$FNX" --fn operator "$FN/fn.toml" run >"$FN/run.log" 2>&1 </dev/null &
FN_PID=$!
n=0
until [ -S "$FN/control.sock" ] && grep -q "^LISTENING $FN_PORT" "$FN/run.log"; do
  kill -0 "$FN_PID" 2>/dev/null || { echo 'fn node exited' >&2; tail -20 "$FN/run.log" >&2; exit 1; }
  n=$((n + 1)); [ "$n" -le 600 ] || { echo 'fn node start timeout' >&2; exit 1; }
  sleep 0.5
done
"$FNX" --fn consumer bootstrap "$FN/control.sock" >"$FN/bootstrap.stdout"
"$FNX" --fn consumer register "$FN/control.sock" selected-mini-gateway fn.test \
  "$FN/registered.fncu" >"$FN/register.stdout"
"$FNX" --fn consumer-inspect "$FN/registered.fncu" >"$FN/registered.inspect"
end
inspect_field() { tr ' ' '\n' <"$FN/registered.inspect" | sed -n "s/^$1=//p"; }
jq -n --arg h "$(inspect_field history)" --arg i "$(inspect_field incarnation)" \
  --arg c "$(inspect_field consumer)" --arg p "$(inspect_field principal)" \
  --arg q "$(inspect_field query)" --argjson qv "$(inspect_field query-version)" \
  --argjson vv "$(inspect_field view-version)" --argjson re "$(inspect_field registration-epoch)" \
  '{consumer:$c,history:$h,incarnation:$i,principal:$p,query:$q,
    queryVersion:$qv,registrationEpoch:$re,viewVersion:$vv}' >"$FN/scope.json"
jq -n --arg cert "$FN/tls-cert.pem" --arg pw "$FN/posting-password" --argjson port "$FN_PORT" \
  '{type:"minidregg-fn-post-v1",port:$port,username:"selected-mini-publisher",
    passwordFile:$pw,certificatePath:$cert}' >"$FN/post-config.json"

# --- 6. The exchange contract --------------------------------------------------
# Owner-side fields name A's key; recipient-side reads name A's home identity
# at B, the only subject B's release law admits (see the verdict file above).
jq -n --arg host "$HOST" --arg src "$A/deployment/pinned-config.json" \
  --arg rcp "$B/deployment/pinned-config.json" \
  --arg query "$A/source-read/signed-observation.bin" \
  --arg payload "$ROOT/selected-payload.bin" --arg payloadSha "$(digest "$ROOT/selected-payload.bin")" \
  --arg owner "$A/sponsor.key" --arg delegate "$NOTES_OWNER_CAP" \
  --arg domain "$RECIPIENT_DOMAIN" --arg semantics "$B_SEMANTICS" --arg target "$INBOX" \
  --arg policy "$POLICY_ROOT" --arg subject "$SOURCE_SUBJECT" \
  --arg nonce "$(od -An -tu4 -N4 /dev/urandom | tr -d ' ')" \
  --arg post "$FN/post-config.json" --arg fnx "$FNX" --arg core "$FN_CORE" \
  --arg scope "$FN/scope.json" --arg control "$FN/control.sock" \
  --arg rcap "$RECIPIENT_CAP" --arg auth "$AUTHORITY_ROOT" --arg troot "$TARGET_ROOT" \
  --arg socket "$B/public/mini.sock" --arg gateway "$B/sponsor.key" \
  --arg qintent "$ROOT/verify-intent.json" \
  --arg mid "<m9-$(od -An -tx4 -N8 /dev/urandom | tr -d ' ')@mini.invalid>" \
  '{type:"minidregg-selected-exchange-v1",releaseProfile:"public-peerable-v2",
    host:$host,sourceConfig:$src,recipientConfig:$rcp,sourceSignedQuery:$query,
    sourceAtom:"7401",selectedPayload:$payload,selectedPayloadSha256:$payloadSha,
    ownerKey:$owner,sourceDelegateCapability:$delegate,destinationDomain:$domain,
    destinationSemantics:$semantics,destinationTarget:$target,group:"fn.test",
    messageId:$mid,policyRoot:$policy,keysetRoot:"0",epoch:"1",ownerSubject:$subject,
    ownerNonce:$nonce,expiresAt:"1000000",from:"store-a@example.invalid",
    date:"Wed, 30 Sep 2026 06:00:00 +0000",subject:"Selected note from Store A",
    privatePostConfig:$post,fnBinary:$fnx,fnRuntimeImage:$core,fnScope:$scope,
    fnControl:$control,recipientCapability:$rcap,recipientAuthorityRoot:$auth,
    recipientTargetRoot:$troot,recipientSocket:$socket,recipientOperatorSocket:$socket,
    gatewayKey:$gateway,recipientQueryIntent:$qintent,recipientQueryKey:$owner}' \
  >"$ROOT/contract.json"
jq -n --arg s "$SOURCE_SUBJECT" --arg t "$INBOX" --arg c "$RECIPIENT_CAP" \
  --arg nonce "$(od -An -tu8 -N8 /dev/urandom | tr -d ' ')" \
  '{subject:$s,nonce:$nonce,purpose:{type:"query",kind:"object",target:$t,view:"resource"},
    grants:[{kind:"object",target:$t,capability:$c}]}' >"$ROOT/verify-intent.json"
exchange() { "$MINI" selected-exchange --phase "$1" --contract "$ROOT/contract.json" --state-dir "$X"; }

# --- 7. Source phases under A's key (A's service stopped: direct Host) ---------
stop_service "$A"
begin prepare
exchange prepare >"$ROOT/prepare.stdout"
end
begin publish
exchange publish >"$ROOT/publish.stdout"
end
jq -e '.type == "minidregg-selected-fn-post-v1" and .status == "accepted"' \
  "$X/source-publish/fn-post-result.json" >/dev/null

# Disclosure: the packet carries the selected bytes once and the unselected zero
# times. The positive control keeps the absence check from being vacuous.
[ "$(count_in "$X/packet.bin" "$SELECTED_TEXT")" = 1 ]
[ "$(count_in "$X/packet.bin" "$UNSELECTED_TEXT")" = 0 ]
[ "$(count_in "$A/source-read/view.json" "$(hexstr "$UNSELECTED_TEXT")")" -ge 1 ]

# --- 8. Recipient phases (B served; readback with B stopped: direct Host) ------
begin receive-transport
exchange receive-transport >"$ROOT/receive.stdout"
end
POLL=$X/transport/$(cat "$X/transport/selected")
confirmed "$X/recipient-attempt/request-0000.outcome.json" installed
cmp "$POLL/packet.bin" "$X/packet.bin"
# What fn actually stored: its base64 body decodes to exactly the packet, which
# carries the selected text once and the unselected text zero times.
tr -d '\r' <"$POLL/stored.eml" | awk 'body { print } /^$/ { body = 1 }' | base64 -d \
  >"$ROOT/fn-stored-body.bin"
cmp "$ROOT/fn-stored-body.bin" "$X/packet.bin"
[ "$(count_in "$ROOT/fn-stored-body.bin" "$SELECTED_TEXT")" = 1 ]
[ "$(count_in "$ROOT/fn-stored-body.bin" "$UNSELECTED_TEXT")" = 0 ]
begin exact-retry
exchange receive-transport >"$ROOT/receive-retry.stdout"
exchange publish >"$ROOT/publish-retry.stdout"
end
confirmed "$X/recipient-attempt/request-0001.outcome.json" replayed
for f in 0000 0001; do
  jq -S '{transactionId,eventId,acceptedCount,worldRoot}' \
    "$X/recipient-attempt/request-$f.outcome.json" >"$ROOT/receipt-$f.json"
done
cmp "$ROOT/receipt-0000.json" "$ROOT/receipt-0001.json"
[ "$(find "$X/source-publish" -name 'fn-post-attempt*' | wc -l | tr -d ' ')" = 1 ]
store_image "$B" "$ROOT/b-image-after-admission.bin"

# --- 9. Refusals at their boundaries -------------------------------------------
mkdir -m 700 "$N"
# 9a. fn transport boundary: an expected article that differs from what fn
# stored (altered Subject) refuses in the Host before any packet or ingress.
begin tampered-article
sed 's/^Subject: Selected note from Store A/Subject: Selected note from Store Z/' \
  "$X/article.eml" >"$N/tampered-article.eml"
if cmp -s "$X/article.eml" "$N/tampered-article.eml"; then echo 'tamper did not change the article' >&2; exit 1; fi
mkdir -m 700 "$N/tampered-article"
if "$HOST" "$B/deployment/pinned-config.json" selected-release-fn-legacy-poll \
    "$FNX" "$FN/scope.json" "$FN/control.sock" "$N/tampered-article.eml" \
    "$RECIPIENT_CAP" "$AUTHORITY_ROOT" "$TARGET_ROOT" \
    "$N/tampered-article/cursor.fncu" "$N/tampered-article/report.fn-r" \
    "$N/tampered-article/stored.eml" "$N/tampered-article/packet.bin" \
    "$N/tampered-article/ingress.bin" "$N/tampered-article/result.json" \
    >"$N/tampered-article.stdout" 2>"$N/tampered-article.stderr"; then
  echo 'tampered expected article unexpectedly projected' >&2; exit 1
fi
grep -q 'fn stored article lacks exact selected owner source suffix' "$N/tampered-article.stderr"
[ ! -e "$N/tampered-article/packet.bin" ]
[ ! -e "$N/tampered-article/ingress.bin" ]
end
# 9b-d. Recipient admission boundary. Each candidate is wrapped for B's current
# inbox and submitted to B's served Store; each must refuse with no write.
signed_query "$B" "$A/sponsor.key" "$SOURCE_SUBJECT" "$INBOX" "$RECIPIENT_CAP" resource \
  "$N/inbox-after-admission"
POST_AUTHORITY=$(jq -er '.authorityRoot' "$N/inbox-after-admission/challenge.json")
POST_ROOT=$(jq -er '.cell.root' "$N/inbox-after-admission/view.json")
submit_negative() { # label packet target-root
  "$HOST" "$B/deployment/pinned-config.json" selected-release-ingress \
    "$2" "$RECIPIENT_CAP" "$POST_AUTHORITY" "$3" "$N/$1-ingress.bin"
  if "$MINI" selected-release-submit --host "$HOST" --config "$B/deployment/pinned-config.json" \
      --socket "$B/public/mini.sock" --ingress "$N/$1-ingress.bin" --dir "$N/$1-attempt" \
      >"$N/$1.stdout" 2>"$N/$1.stderr"; then
    echo "$1 unexpectedly installed" >&2; exit 1
  fi
  refused_admission "$N/$1-attempt/request-0000.outcome.json"
}
# A's image moved with event14; further releases select from a fresh signed read.
signed_query "$A" "$A/sponsor.key" "$SOURCE_SUBJECT" "$NOTES_TARGET" "$NOTES_OWNER_CAP" \
  resource "$N/source-read-now"
FRESH_QUERY_HEX=$(hexfile "$N/source-read-now/signed-observation.bin")
make_release() { # label nonce-offset signing-key: a fresh, never-admitted release
  mkdir -m 700 "$N/$1"
  jq --arg q "$FRESH_QUERY_HEX" --argjson d "$2" \
    '.signedQueryHex = $q | .ownerNonce = "\(.ownerNonce | tonumber + $d)"' \
    "$X/request.json" >"$N/$1/request.json"
  "$HOST" "$A/deployment/pinned-config.json" selected-release-prepare \
    "$N/$1/request.json" "$N/$1/preimage.bin"
  "$MINI" selected-release-sign --host "$HOST" --config "$A/deployment/pinned-config.json" \
    --preimage "$N/$1/preimage.bin" --key "$3" --output "$N/$1/signature.bin"
  "$HOST" "$A/deployment/pinned-config.json" selected-release-assemble \
    "$N/$1/preimage.bin" "$N/$1/signature.bin" \
    store-a@example.invalid 'Wed, 30 Sep 2026 06:00:00 +0000' 'Selected note from Store A' \
    "$N/$1/packet.bin" "$N/$1/article.eml"
}
begin tampered-packet
# A fresh release correctly signed by A, then one byte of the selected content
# changed. The untampered release is the positive control below.
make_release control 3 "$A/sponsor.key"
python3 - "$N/control/packet.bin" "$N/tampered-packet.bin" "$SELECTED_TEXT" <<'PY'
import sys
data = open(sys.argv[1], 'rb').read()
text = sys.argv[3].encode()
at = data.index(text)
tampered = data[:at] + b'Z' + data[at + 1:]
assert tampered != data and len(tampered) == len(data)
open(sys.argv[2], 'wb').write(tampered)
PY
submit_negative tampered-packet "$N/tampered-packet.bin" "$POST_ROOT"
end
begin wrong-signer
# B's own sponsor key signs a release naming A's home subject: B's credential
# cannot impersonate A at B.
make_release wrong-signer 1 "$B/sponsor.key"
submit_negative wrong-signer "$N/wrong-signer/packet.bin" "$POST_ROOT"
end
begin wrong-root
# Correctly signed by A, wrapped for a wrong recipient target root.
make_release wrong-root 2 "$A/sponsor.key"
submit_negative wrong-root "$N/wrong-root/packet.bin" 1
end
store_image "$B" "$ROOT/b-image-after-refusals.bin"
cmp "$ROOT/b-image-after-admission.bin" "$ROOT/b-image-after-refusals.bin"
# Positive control: the untampered control release, through the same wrapper and
# the same current roots, is admitted. Each refusal above therefore turns on its
# one mutation (byte, signer, root), not on the wrapper.
begin positive-control
"$HOST" "$B/deployment/pinned-config.json" selected-release-ingress \
  "$N/control/packet.bin" "$RECIPIENT_CAP" "$POST_AUTHORITY" "$POST_ROOT" "$N/control-ingress.bin"
"$MINI" selected-release-submit --host "$HOST" --config "$B/deployment/pinned-config.json" \
  --socket "$B/public/mini.sock" --ingress "$N/control-ingress.bin" --dir "$N/control-attempt" \
  >"$N/control.stdout"
confirmed "$N/control-attempt/request-0000.outcome.json" installed
end

# --- 10. Corrected verify-transport, end to end --------------------------------
stop_service "$B"
begin verify-transport
exchange verify-transport >"$ROOT/verify.stdout"
end
jq -e '.type == "minidregg-selected-exchange-verified-v1" and .transportOnly == true' \
  "$X/readback-0001/selected-exchange.json" >/dev/null
kill "$FN_PID"; wait "$FN_PID" 2>/dev/null || true; FN_PID=

# --- 11. Public summary (no secrets, no raw signatures) ------------------------
sha256sum "$SCRIPT" "$NEWPARTICIPANT" "$HOST" "$MINI" "$STORE" "$VERIFIER" \
  "$FN_LAUNCHER" "$FN_CORE" >"$ROOT/final-input-sha256.txt"
cmp "$ROOT/input-sha256.txt" "$ROOT/final-input-sha256.txt"
jq -n --slurpfile receipt "$ROOT/receipt-0000.json" \
  --arg aPub "$A_PUBLIC" --arg bPub "$B_PUBLIC" \
  --arg aDomain "$SOURCE_DOMAIN" --arg bDomain "$RECIPIENT_DOMAIN" \
  --arg aSubject "$SOURCE_SUBJECT" --arg bSubject "$RECIPIENT_SUBJECT" \
  --arg inbox "$INBOX" --arg notes "$NOTES_TARGET" --arg rcap "$RECIPIENT_CAP" \
  --arg packet "$(digest "$X/packet.bin")" --arg article "$(digest "$X/article.eml")" \
  --arg stored "$(digest "$POLL/stored.eml")" --arg report "$(digest "$POLL/report.fn-r")" \
  --arg bImage "$(digest "$ROOT/b-image-after-refusals.bin")" \
  --arg enrollment "$(digest "$B/attempts/source-owner/enrollment.json")" \
  --arg lockout "$(cat "$B/sponsor-read-after-law.verdict")" \
  --arg readback "$(digest "$X/readback-0001/signed-observation.bin")" \
  --arg tamperStderr "$(cat "$N/tampered-article.stderr")" \
  --slurpfile tp "$N/tampered-packet-attempt/request-0000.outcome.json" \
  --slurpfile ws "$N/wrong-signer-attempt/request-0000.outcome.json" \
  --slurpfile wr "$N/wrong-root-attempt/request-0000.outcome.json" \
  --slurpfile pc "$N/control-attempt/request-0000.outcome.json" \
  '{type:"minidregg-selected-exchange-two-credentials-v1",
    storeA:{domain:$aDomain,sponsorSubject:$aSubject,sponsorPublicKey:$aPub,notes:$notes},
    storeB:{domain:$bDomain,sponsorSubject:$bSubject,sponsorPublicKey:$bPub,inbox:$inbox,
      homeIdentityEnrollmentSha256:$enrollment,recipientCapability:$rcap,
      logicalImageSha256:$bImage,sponsorReadAfterReleaseLaw:$lockout},
    packetSha256:$packet,articleSha256:$article,fnStoredArticleSha256:$stored,
    fnReportSha256:$report,recipientReceipt:$receipt[0],readbackObservationSha256:$readback,
    disclosure:{packetSelected:1,packetUnselected:0,
      fnStoredBodyEqualsPacket:true,fnStoredBodySelected:1,fnStoredBodyUnselected:0},
    refusals:{
      tamperedExpectedArticle:{boundary:"Host selected-release-fn-legacy-poll",
        stderr:$tamperStderr,packetOrIngressWritten:false},
      tamperedPacket:$tp[0],wrongSigner:$ws[0],wrongRoot:$wr[0],
      bImageUnchangedByRefusals:true},
    positiveControl:($pc[0] | {confirmation,transactionId,eventId,acceptedCount}),
    claims:"transport only: no fn-e verdict, event17 coverage or fn cursor ACK"}' \
  >"$ROOT/public-summary.json"
printf 'selected exchange with two credentials PASS: %s\n' "$ROOT"
