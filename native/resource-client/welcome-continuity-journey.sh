#!/usr/bin/env bash
# Fresh receiving-path evidence for authenticated key-only welcome continuity.
# Fixture dependencies: genesis.sh and genesis-params.example.json beside this file.
# No builds. VERIFIER is the credential-signature verifier; HOST also supplies the
# independent local continuity verifier. Only this script's service PID is stopped.
set -euo pipefail
umask 077
if [[ $# != 5 || ${1:-} == --help ]]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW-ABSOLUTE-RUNROOT" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 RUN=$5
# The signing-consent provider (client_consent.rs): a signing step refuses without MINI_LOCAL_HOST,
# MINI_CONSENT_HOST and MINI_CONSENT_CONFIG together. It ships beside the Host; CONSENT_HOST overrides.
CONSENT_HOST=${CONSENT_HOST:-$(dirname -- "$HOST")/minidregg-client-consent}
[[ -x $CONSENT_HOST ]] || { echo "signing-consent provider not executable: $CONSENT_HOST (set CONSENT_HOST)" >&2; exit 2; }
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
for path in "$HOST" "$MINI" "$STORE" "$VERIFIER" "$RUN"; do
  [[ $path == /* ]] || { echo "path must be absolute: $path" >&2; exit 2; }
done
for binary in "$HOST" "$MINI" "$STORE" "$VERIFIER"; do
  [[ -x $binary ]] || { echo "not executable: $binary" >&2; exit 2; }
done
for tool in jq sha256sum mktemp; do command -v "$tool" >/dev/null; done
[[ ! -e $RUN && ! -L $RUN ]] || { echo "refusing existing run root: $RUN" >&2; exit 2; }
mkdir "$RUN"
RUN=$(CDPATH='' cd -- "$RUN" && pwd)
mkdir "$RUN/logs" "$RUN/fixture" "$RUN/proofs"
ROWS=$RUN/rows.tsv
printf 'step\tverdict\n' >"$ROWS"
SERVER=
SOCKET_DIR=$(mktemp -d /tmp/mini-continuity.XXXXXX)
SOCKET=$SOCKET_DIR/host.sock
printf '%s\n' "$SOCKET_DIR" >"$RUN/socket-directory.txt"
stop_server() {
  if [[ -n $SERVER ]]; then
    kill "$SERVER" 2>/dev/null || true
    wait "$SERVER" 2>/dev/null || true
    SERVER=
    # This socket was created by the child we just reaped; no other socket is touched.
    [[ ! -S $SOCKET ]] || rm "$SOCKET"
  fi
}
trap stop_server EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
run() {
  local label=$1; shift
  if JOIN_OPCODE_LOG="$RUN/logs/$label.ops" "$@" >"$RUN/logs/$label.out" 2>"$RUN/logs/$label.err"; then
    printf '%s\tPASS\n' "$label" >>"$ROWS"
  else
    local rc=$?
    printf '%s\tFAIL(%s)\n' "$label" "$rc" >>"$ROWS"
    echo "continuity journey failed at $label; see $RUN/logs/$label.err" >&2
    return "$rc"
  fi
}
refused() {
  local label=$1; shift
  if JOIN_OPCODE_LOG="$RUN/logs/$label.ops" "$@" >"$RUN/logs/$label.out" 2>"$RUN/logs/$label.err"; then
    printf '%s\tUNEXPECTED-SUCCESS\n' "$label" >>"$ROWS"
    echo "expected refusal at $label" >&2
    return 1
  fi
  printf '%s\tPASS(refused)\n' "$label" >>"$ROWS"
}
start_server() {
  local label=$1
  "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$RUN/logs/$label.out" 2>"$RUN/logs/$label.err" &
  SERVER=$!
  printf '%s\n' "$SERVER" >"$RUN/$label.pid"
  for ((i=0; i<600; i++)); do
    [[ ! -S $SOCKET ]] || return 0
    kill -0 "$SERVER" 2>/dev/null || { echo "service exited; see $RUN/logs/$label.err" >&2; return 1; }
    sleep 0.1
  done
  echo "service socket did not appear" >&2
  return 1
}

run sponsor-key "$MINI" keygen --secret "$RUN/sponsor.key" --public "$RUN/sponsor.pub"
run clock-key "$MINI" keygen --secret "$RUN/clock.key" --public "$RUN/clock.pub"
PUBLIC=$(od -An -tx1 -v "$RUN/sponsor.pub" | tr -d ' \n')
CLOCK_PUBLIC=$(od -An -tx1 -v "$RUN/clock.pub" | tr -d ' \n')
cp "$HERE/genesis-params.example.json" "$RUN/params.json"
run genesis sh "$HERE/genesis.sh" "$RUN/params.json" "$PUBLIC" "$CLOCK_PUBLIC" \
  "$HOST" "$STORE" "$VERIFIER" "$RUN/fixture"
run bootstrap "$MINI" bootstrap --host "$HOST" --config "$RUN/fixture/operator.json" \
  --source "$RUN/fixture/genesis.json" --dir "$RUN/deployment"
CONFIG=$RUN/deployment/pinned-config.json
# A join has no --host: its local author, inspect and signing steps select the semantic Host and the
# consent provider by these three variables, together. The sponsor steps pass --host and sign through
# the workspace, so naming the variables there would only widen what they read.
LOCAL=(env MINI_LOCAL_HOST="$HOST" MINI_CONSENT_HOST="$CONSENT_HOST" MINI_CONSENT_CONFIG="$CONFIG")
start_server service-first
# The SSH process seam is a local test shim; the real public socket proxy and
# version-2 pinned remote envelopes run unchanged. Only framing is logged here.
cat >"$RUN/proxy.py" <<'PROXY'
import os,struct,subprocess,sys
p=subprocess.Popen([os.environ['JOIN_MINI'],'socket-proxy','--socket',os.environ['JOIN_SOCKET']],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def read(stream,n):
 b=b''
 while len(b)<n:
  x=stream.read(n-len(b))
  if not x: raise EOFError()
  b+=x
 return b
try:
 while True:
  h=read(sys.stdin.buffer,4); b=read(sys.stdin.buffer,struct.unpack('<I',h)[0])
  off=5+struct.unpack('<I',b[1:5])[0]+(32 if b[0]==2 else 0)
  with open(os.environ['JOIN_OPCODE_LOG'],'a') as log: log.write(str(b[off])+'\n')
  if b[off]==89 and os.environ.get('JOIN_REFUSE_LOOKUP')=='1':
   r=bytes([255])+b'fixture-refused'
   sys.stdout.buffer.write(struct.pack('<I',len(r))+r);sys.stdout.buffer.flush();continue
  p.stdin.write(h+b);p.stdin.flush()
  h=read(p.stdout,4);b=read(p.stdout,struct.unpack('<I',h)[0])
  sys.stdout.buffer.write(h+b);sys.stdout.buffer.flush()
except EOFError: pass
finally:
 p.stdin.close();p.wait(timeout=10)
PROXY
printf '#!/bin/sh\necho "debug1: Entering interactive session." >&2\nexec /usr/bin/python3 "%s/proxy.py"\n' "$RUN" >"$RUN/ssh-shim"
printf '#!/bin/sh\nexit 23\n' >"$RUN/ssh-disconnected"
chmod 700 "$RUN/ssh-shim" "$RUN/ssh-disconnected"
export MINI_SSH=$RUN/ssh-shim JOIN_MINI=$MINI JOIN_SOCKET=$SOCKET
WS=$RUN/sponsor-workspace
run sponsor-workspace "$MINI" workspace --action init --dir "$WS" --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --key "$RUN/sponsor.key" --subject "$(jq -r '.sponsor.subject' "$RUN/params.json")" \
  --birth-context "$RUN/fixture/sponsor-birth-context.json" --namespace-root "$RUN/namespace" --no-prerotation
run factory-import "$MINI" workspace --action import --dir "$WS" --name factory --kind object \
  --target "$(jq -r .factoryId "$RUN/params.json")" \
  --observe-capability "$(jq -r .sponsor.factoryObserveCapabilityId "$RUN/params.json")" \
  --control-capability "$(jq -r .factoryControllerCapability "$RUN/params.json")"
run participant-key "$MINI" join --key "$RUN/participant.key"
ENROLL=$RUN/enrollment
run enrollment-plan "$MINI" enroll --action plan --sponsor-workspace "$WS" --factory-ref factory \
  --name key-only --new-public-key "$RUN/participant.pub" \
  --next-public-key "$RUN/participant.key.next.pub" --next-cosign "$RUN/participant.key.next.cosign" --dir "$ENROLL"
run sponsor-offer "$MINI" enroll --action offer --dir "$ENROLL"
cp "$RUN/logs/sponsor-offer.out" "$RUN/offer.json"
JOIN=$RUN/participant
run participant-possession "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --sponsor-plan "$RUN/offer.json" \
  --dir "$JOIN" --remote test-deployment
jq -r .possessionSignature "$RUN/logs/participant-possession.out" | xxd -r -p >"$RUN/possession.bin"
run enrollment-seal "$MINI" enroll --action seal --dir "$ENROLL" --possession-signature "$RUN/possession.bin"
# Build an untrusted welcome claiming admission before the sealed ingress exists
# in the journal. Source lookup must report absent without submitting it.
python3 - "$RUN/offer.json" "$ENROLL/ingress.bin" "$RUN/unadmitted-welcome.json" <<'JSON'
import hashlib,json,sys
p=json.load(open(sys.argv[1]));b=open(sys.argv[2],'rb').read()
r={k:p[k] for k in ['subject','keyId','publicKey']}
r.update(type='minidregg-participant-enrollment-result-v1',authority='admitted-key-only',keyPath=None,
 receipt=dict(transactionId='1',eventId='1',acceptedCount='0',worldRoot='1'))
json.dump(dict(type='minidregg-participant-join-welcome-v1',enrollment=r,birthContext=None,
 ingressHex=b.hex(),ingressSha256=hashlib.sha256(b).hexdigest()),open(sys.argv[3],'w'))
JSON
cp -a "$JOIN" "$RUN/unadmitted-join"
refused absent-lookup "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/unadmitted-welcome.json" \
  --dir "$RUN/unadmitted-join" --remote test-deployment --verifier "$HOST"
[[ $(cat "$RUN/logs/absent-lookup.ops") == 89 && ! -e $RUN/unadmitted-join/workspace ]]
grep -q 'not a confirmed admitted key' "$RUN/logs/absent-lookup.err"
run enrollment-submit "$MINI" enroll --action submit --dir "$ENROLL"
jq -e '.receipt.acceptedCount == "1"' "$RUN/logs/enrollment-submit.out" >/dev/null
# The enrollment receipt is now historical; baseline must still select its exact point.
printf '%s\n' '{"type":"all","predicates":[]}' >"$RUN/open-law.json"
run intervening-resource "$MINI" workspace --action create --dir "$WS" --name later --storage stream \
  --predicate "$RUN/open-law.json"
run sponsor-welcome "$MINI" enroll --action welcome --dir "$ENROLL"
cp "$RUN/logs/sponsor-welcome.out" "$RUN/welcome.json"
cp -a "$JOIN" "$RUN/disconnected-join"
refused unresolved-lookup "${LOCAL[@]}" MINI_SSH="$RUN/ssh-disconnected" "$MINI" join --key "$RUN/participant.key" \
  --welcome "$RUN/welcome.json" --dir "$RUN/disconnected-join" --remote test-deployment --verifier "$HOST"
grep -q 'lookup unresolved.*no submission' "$RUN/logs/unresolved-lookup.err"
[[ ! -e $RUN/disconnected-join/workspace ]]
cp -a "$JOIN" "$RUN/refused-join"
refused refused-lookup "${LOCAL[@]}" JOIN_REFUSE_LOOKUP=1 "$MINI" join --key "$RUN/participant.key" \
  --welcome "$RUN/welcome.json" --dir "$RUN/refused-join" --remote test-deployment --verifier "$HOST"
grep -q 'Host refused op89' "$RUN/logs/refused-lookup.err"
[[ $(cat "$RUN/logs/refused-lookup.ops") == 89 && ! -e $RUN/refused-join/workspace ]]
cp -a "$JOIN" "$RUN/forged-join"
jq '.enrollment.receipt.worldRoot = (if .enrollment.receipt.worldRoot == "0" then "1" else "0" end)' \
  "$RUN/welcome.json" >"$RUN/forged-welcome.json"
refused forged-receipt "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/forged-welcome.json" \
  --dir "$RUN/forged-join" --remote test-deployment --verifier "$HOST"
grep -q 'receipt differs from exact read-only' "$RUN/logs/forged-receipt.err"
[[ $(cat "$RUN/logs/forged-receipt.ops") == 89 && ! -e $RUN/forged-join/workspace ]]
# Let source-owned assembly generate canonical ingress with a changed signature.
dd if=/dev/zero of="$RUN/zero-signature.bin" bs=64 count=1 status=none
run assemble-wrong-possession "$HOST" "$CONFIG" enroll-key-assemble "$ENROLL/plan.bin" \
  "$ENROLL/sponsor-signature.bin" "$RUN/zero-signature.bin" \
  "$RUN/participant.key.next.pub" "$RUN/participant.key.next.cosign" "$RUN/wrong-possession.bin"
rewrite_ingress() {
  python3 - "$RUN/welcome.json" "$1" "$2" <<'JSON'
import hashlib,json,sys
v=json.load(open(sys.argv[1]));b=open(sys.argv[2],'rb').read()
v.update(ingressHex=b.hex(),ingressSha256=hashlib.sha256(b).hexdigest())
json.dump(v,open(sys.argv[3],'w'))
JSON
}
rewrite_ingress "$RUN/wrong-possession.bin" "$RUN/wrong-possession-welcome.json"
cp -a "$JOIN" "$RUN/wrong-possession-join"
refused wrong-possession "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/wrong-possession-welcome.json" \
  --dir "$RUN/wrong-possession-join" --remote test-deployment --verifier "$HOST"
grep -q 'sealed ingress differs' "$RUN/logs/wrong-possession.err"
[[ ! -e $RUN/logs/wrong-possession.ops && ! -e $RUN/wrong-possession-join/workspace ]]
run other-key "$MINI" keygen --secret "$RUN/other.key" --public "$RUN/other.pub"
run other-plan "$MINI" enroll --action plan --sponsor-workspace "$WS" --factory-ref factory \
  --name other --new-public-key "$RUN/other.pub" \
  --next-public-key "$RUN/other.key.next.pub" --next-cosign "$RUN/other.key.next.cosign" --dir "$RUN/other-enrollment"
run assemble-wrong-command "$HOST" "$CONFIG" enroll-key-assemble "$RUN/other-enrollment/plan.bin" \
  "$ENROLL/sponsor-signature.bin" "$RUN/possession.bin" \
  "$RUN/other.key.next.pub" "$RUN/other.key.next.cosign" "$RUN/wrong-command.bin"
rewrite_ingress "$RUN/wrong-command.bin" "$RUN/wrong-command-welcome.json"
cp -a "$JOIN" "$RUN/wrong-command-join"
refused wrong-command "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/wrong-command-welcome.json" \
  --dir "$RUN/wrong-command-join" --remote test-deployment --verifier "$HOST"
grep -q 'sealed ingress differs' "$RUN/logs/wrong-command.err"
[[ ! -e $RUN/logs/wrong-command.ops && ! -e $RUN/wrong-command-join/workspace ]]
# Interrupt proof verification after confirmed lookup has reached durable storage.
# The pinned wrapper stays unchanged; only the owned fault-injection marker moves.
{
  printf '#!/bin/sh\n'
  printf 'if [ "$2" = continuity-verify ] && [ -f "%s/proof-fault" ]; then exit 78; fi\n' "$RUN"
  printf 'exec "%s" "$@"\n' "$HOST"
} >"$RUN/verifier-wrapper"
chmod 700 "$RUN/verifier-wrapper"
touch "$RUN/proof-fault"
cp -a "$JOIN" "$RUN/interrupted-join"
refused interrupted-baseline "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/welcome.json" \
  --dir "$RUN/interrupted-join" --remote test-deployment --verifier "$RUN/verifier-wrapper"
# 89 = the read-only enrollment lookup; 144 twice = the key-status reads that check the participant
# key's next-key commitment against the Host (pre-rotation is the enrollment default); 151 = the
# continuity baseline. Never 88: no join path submits an enrollment.
[[ $(cat "$RUN/logs/interrupted-baseline.ops") == $'89\n144\n144\n151' && ! -s $RUN/logs/interrupted-baseline.out ]]
[[ -f $RUN/interrupted-join/join/authenticated-receipt.json && ! -d $RUN/interrupted-join/workspace/receipt-continuity ]]
rm "$RUN/proof-fault"
run resume-baseline "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/welcome.json" \
  --dir "$RUN/interrupted-join" --remote test-deployment --verifier "$RUN/verifier-wrapper"
[[ $(cat "$RUN/logs/resume-baseline.ops") == $'144\n151' ]]   # no 89: the confirmed frame is retained
jq -e '.continuity.point.height == "1"' "$RUN/logs/resume-baseline.out" >/dev/null
refused missing-verifier "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/welcome.json" \
  --dir "$JOIN" --remote test-deployment
run authenticated-welcome "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/welcome.json" \
  --dir "$JOIN" --remote test-deployment --verifier "$HOST"
jq -e '.continuity.status == "established" and .continuity.point.height == "1"' "$RUN/logs/authenticated-welcome.out" >/dev/null
[[ $(cat "$RUN/logs/authenticated-welcome.ops") == $'89\n144\n144\n151' ]]
CUSTODY=$JOIN/workspace/receipt-continuity
jq -e --slurpfile r "$ENROLL/enrollment.json" \
  '.point == {height:$r[0].receipt.acceptedCount,worldRoot:$r[0].receipt.worldRoot}' "$CUSTODY/anchor.json" >/dev/null
[[ -z $(find "$JOIN/workspace/refs" -type f -print -quit) ]]
cp "$CUSTODY/anchor.json" "$RUN/anchor-established.json"
run repeated-welcome "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/welcome.json" \
  --dir "$JOIN" --remote test-deployment --verifier "$HOST"
[[ $(cat "$RUN/logs/repeated-welcome.ops") == 144 ]]   # the key status only: no lookup (89), no new baseline (151)
cmp "$CUSTODY/anchor.json" "$RUN/anchor-established.json"
mv "$CUSTODY/anchor.json" "$RUN/anchor.saved.json"
refused lost-custody "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/welcome.json" \
  --dir "$JOIN" --remote test-deployment --verifier "$HOST"
[[ ! -e $CUSTODY/anchor.json && $(cat "$RUN/logs/lost-custody.ops") == 144 && ! -s $RUN/logs/lost-custody.out ]]
mv "$RUN/anchor.saved.json" "$CUSTODY/anchor.json"
mv "$JOIN/workspace" "$RUN/workspace.saved"
refused lost-whole-workspace "${LOCAL[@]}" "$MINI" join --key "$RUN/participant.key" --welcome "$RUN/welcome.json" \
  --dir "$JOIN" --remote test-deployment --verifier "$HOST"
[[ ! -e $JOIN/workspace && ! -e $RUN/logs/lost-whole-workspace.ops && ! -s $RUN/logs/lost-whole-workspace.out ]]
grep -q 'workspace custody is missing' "$RUN/logs/lost-whole-workspace.err"
mv "$RUN/workspace.saved" "$JOIN/workspace"
# No participant welcome path submitted an enrollment, including uncertainty.
! grep -qx 88 "$RUN"/logs/*.ops
sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" "$HERE/genesis.sh" \
  "$RUN/params.json" "$0" >"$RUN/provenance.sha256"
printf 'KEY-ONLY WELCOME RECEIVING PASS\n%s\n' "$ROWS"
