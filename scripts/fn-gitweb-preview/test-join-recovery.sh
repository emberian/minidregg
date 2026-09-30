#!/bin/sh
# Command-fake checks for retained fn projection and Mini reply-loss handling.
set -eu
umask 077
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
scratch=$(mktemp -d)
scratch=$(CDPATH='' cd -- "$scratch" && pwd -P)
trap 'if [ "${KEEP_TEST_SCRATCH:-0}" != 1 ]; then rm -rf "$scratch"; fi' EXIT HUP INT TERM
[ "${KEEP_TEST_SCRATCH:-0}" = 1 ] && echo "test scratch: $scratch" >&2
mkdir -m 700 "$scratch/state" "$scratch/inputs" "$scratch/export"

cat >"$scratch/host" <<'EOF'
#!/bin/sh
set -eu
shift
case $1 in
selected-release-fn-poll)
  shift
  if [ ! -f "$MOCK_ROOT/poll-failed" ]; then
    printf partial >"$7"
    : >"$MOCK_ROOT/poll-failed"
    exit 3
  fi
  printf cursor >"$7"
  printf report >"$8"
  printf source >"$9"
  printf packet >"${10}"
  printf ingress >"${11}"
  printf '%s\n' '{"type":"selected-release-fn-poll-v1","status":"candidate-unacknowledged"}' >"${12}"
  ;;
selected-release-fn-ack)
  shift
  printf '%s\n' '{"type":"selected-release-fn-ack-v1","fnAck":"durable-accepted"}' >"$5"
  ;;
*) exit 3 ;;
esac
EOF
cat >"$scratch/mini" <<'EOF'
#!/bin/sh
set -eu
operation=$1
shift
case $operation in
selected-release-submit|selected-release-lookup)
  while [ "$#" -gt 0 ]; do
    case $1 in --dir|--attempt) out=$2; shift 2 ;; *) shift ;; esac
  done
  mkdir -p "$out"
  case $operation in
    selected-release-submit) name=request-0001 ; kind=confirmed ;;
    selected-release-lookup) name=request-0002 ; kind=absent ;;
  esac
  if [ "$kind" = confirmed ]; then
    printf '%s\n' '{"type":"confirmed","confirmation":"installed","transactionId":"42","eventId":"43","acceptedCount":"4","worldRoot":"44"}' >"$out/$name.outcome.json"
  else
    printf '%s\n' '{"type":"absent"}' >"$out/$name.outcome.json"
  fi
  ;;
query)
  while [ "$#" -gt 0 ]; do
    case $1 in --dir) out=$2; shift 2 ;; *) shift ;; esac
  done
  mkdir -m 700 "$out"
  if [ -f "$MOCK_ROOT/wrong-atom" ]; then atom=999; else atom=42; fi
  od -An -tx1 -v "$MOCK_ROOT/state/packet.bin" | tr -d ' \n' >"$MOCK_ROOT/packet-query.hex"
  jq -n --arg atom "$atom" --rawfile payload "$MOCK_ROOT/packet-query.hex" \
    '{page:{entries:[{type:"atom",id:$atom,kind:{type:"inlineObject",schema:"11"},
      tombstonedAt:null,payload:$payload}]}}' >"$out/view.json"
  ;;
*) exit 3 ;;
esac
EOF
chmod 700 "$scratch/host" "$scratch/mini"
for name in sourceConfig recipientConfig sourceSignedQuery sourceViewBin privatePostConfig fnBinary fnScope exportResult gitRawFile; do
  printf '%s\n' "$name" >"$scratch/inputs/$name"
done
for name in selection.json expected-payload.bin; do printf '%s\n' "$name" >"$scratch/export/$name"; done
printf packet >"$scratch/state/packet.bin"
mkdir -m 700 "$scratch/state/source-publish"
printf '%s\n' '{"status":"accepted"}' >"$scratch/state/source-publish/fn-post-result.json"
jq -n --arg base "$scratch" '{host:($base+"/host"),mini:($base+"/mini"),
  sourceConfig:($base+"/inputs/sourceConfig"),recipientConfig:($base+"/inputs/recipientConfig"),
  sourceSignedQuery:($base+"/inputs/sourceSignedQuery"),sourceViewBin:($base+"/inputs/sourceViewBin"),
  privatePostConfig:($base+"/inputs/privatePostConfig"),fnBinary:($base+"/inputs/fnBinary"),
  fnScope:($base+"/inputs/fnScope"),exportResult:($base+"/export/exportResult"),
  gitRawFile:($base+"/inputs/gitRawFile"),selectedFile:($base+"/state/packet.bin"),
  selectedFileSha256:"",fnControl:($base+"/control"),recipientSocket:($base+"/recipient.sock"),
  recipientOperatorSocket:($base+"/operator.sock"),recipientCapability:"61",
  recipientAuthorityRoot:"2",recipientTargetRoot:"3",destinationTarget:"600",
  gatewayKey:($base+"/gateway.key"),recipientQueryIntent:($base+"/query.json"),
  recipientQueryKey:($base+"/query.key")}' >"$scratch/contract.json"
jq --arg sha "$(shasum -a 256 "$scratch/state/packet.bin" | awk '{print $1}')" \
  '.selectedFileSha256=$sha' "$scratch/contract.json" >"$scratch/contract.tmp"
mv "$scratch/contract.tmp" "$scratch/contract.json"
shasum -a 256 "$scratch/contract.json" | awk '{print $1}' >"$scratch/state/contract.sha256"
shasum -a 256 "$scratch/host" | awk '{print $1}' >"$scratch/state/host.sha256"
shasum -a 256 "$scratch/mini" | awk '{print $1}' >"$scratch/state/mini.sha256"
printf '%s\n' exportResult >"$scratch/export/exportResult"
shasum -a 256 "$scratch/inputs/sourceConfig" "$scratch/inputs/recipientConfig" \
  "$scratch/inputs/sourceSignedQuery" "$scratch/inputs/sourceViewBin" \
  "$scratch/inputs/privatePostConfig" "$scratch/inputs/fnBinary" \
  "$scratch/inputs/fnScope" "$scratch/export/exportResult" \
  "$scratch/inputs/gitRawFile" "$scratch/export/selection.json" \
  "$scratch/export/expected-payload.bin" >"$scratch/state/inputs.sha256"
export MOCK_ROOT="$scratch"
if "$here/join.sh" receive "$scratch/contract.json" "$scratch/state" >"$scratch/first.log" 2>&1; then
  echo 'lost first poll unexpectedly accepted' >&2; exit 1
fi
[ -f "$scratch/state/poll-0001/cursor.fncu" ] && [ ! -e "$scratch/state/poll-selected" ]
if ! "$here/join.sh" receive "$scratch/contract.json" "$scratch/state" >"$scratch/second.log" 2>&1; then
  cat "$scratch/second.log" >&2; exit 1
fi
[ "$(cat "$scratch/state/poll-selected")" = poll-0002 ]
if "$here/join.sh" receive "$scratch/contract.json" "$scratch/state" >"$scratch/third.log" 2>&1; then
  echo 'stale confirmed receipt survived latest absent lookup' >&2; exit 1
fi
grep -q 'latest recipient lookup does not confirm installation' "$scratch/third.log"
[ ! -e "$scratch/state/recipient-confirmed.json" ] || {
  echo 'stale recipient convenience receipt survived latest absent lookup' >&2; exit 1;
}
if "$here/join.sh" cover-plan "$scratch/contract.json" "$scratch/state" >"$scratch/cover-absent.log" 2>&1; then
  echo 'coverage plan accepted stale recipient receipt' >&2; exit 1
fi
grep -q 'latest recipient lookup does not confirm installation' "$scratch/cover-absent.log"
mkdir -m 700 "$scratch/state/frontier"
cp "$scratch/state/recipient-attempt/request-0001.outcome.json" "$scratch/state/frontier/confirmed.json"
printf ingress >"$scratch/state/frontier/ingress.bin"
if "$here/join.sh" ack "$scratch/contract.json" "$scratch/state" >"$scratch/ack-absent.log" 2>&1; then
  echo 'fn ACK accepted stale recipient receipt' >&2; exit 1
fi
grep -q 'latest recipient lookup does not confirm installation' "$scratch/ack-absent.log"
[ ! -e "$scratch/state/ack-0001.json" ]

# A retained accepted receipt and event17 are sufficient to exercise exact
# query target/atom checks; this fake never claims Mini authority.
rm "$scratch/state/recipient-attempt/request-0002.outcome.json"
"$here/join.sh" ack "$scratch/contract.json" "$scratch/state" >"$scratch/ack1.log" 2>&1
"$here/join.sh" ack "$scratch/contract.json" "$scratch/state" >"$scratch/ack2.log" 2>&1
[ "$(cat "$scratch/state/ack-selected")" = ack-0002.json ]
printf '%s\n' '{"purpose":{"type":"query","kind":"object","target":"999","view":"resource"},"grants":[{"kind":"object","target":"999","capability":"61"}]}' >"$scratch/query.json"
if "$here/join.sh" verify "$scratch/contract.json" "$scratch/state" >"$scratch/verify-wrong.log" 2>&1; then
  echo 'wrong destination query accepted' >&2; exit 1
fi
printf '%s\n' '{"purpose":{"type":"query","kind":"object","target":"600","view":"resource"},"grants":[{"kind":"object","target":"600","capability":"61"}]}' >"$scratch/query.json"
touch "$scratch/wrong-atom"
if "$here/join.sh" verify "$scratch/contract.json" "$scratch/state" >"$scratch/verify-atom.log" 2>&1; then
  echo 'matching payload at unrelated AtomId accepted' >&2; exit 1
fi
grep -q 'lacks exact accepted event13 atom' "$scratch/verify-atom.log"
rm "$scratch/wrong-atom"
"$here/join.sh" verify "$scratch/contract.json" "$scratch/state" >"$scratch/verify.log" 2>&1
[ "$(cat "$scratch/state/readback-selected")" = recipient-readback-0002 ]
dd if=/dev/zero of="$scratch/state/packet.bin" bs=1024 count=100 2>/dev/null
jq --arg sha "$(shasum -a 256 "$scratch/state/packet.bin" | awk '{print $1}')" \
  '.selectedFileSha256=$sha' "$scratch/contract.json" >"$scratch/contract.tmp"
mv "$scratch/contract.tmp" "$scratch/contract.json"
shasum -a 256 "$scratch/contract.json" | awk '{print $1}' >"$scratch/state/contract.sha256"
"$here/join.sh" verify "$scratch/contract.json" "$scratch/state" >"$scratch/verify-large.log" 2>&1
[ "$(cat "$scratch/state/readback-selected")" = recipient-readback-0003 ]
dd if=/dev/zero of="$scratch/state/article.eml" bs=1048577 count=1 2>/dev/null
if "$here/join.sh" publish "$scratch/contract.json" "$scratch/state" >"$scratch/publish-oversize.log" 2>&1; then
  echo 'oversize assembled article reached publication' >&2; exit 1
fi
grep -q 'assembled signed article exceeds qualified fn 1MiB admission cap' "$scratch/publish-oversize.log"
echo 'join recovery command-fake PASS: partial poll, latest absent, ACK reentry, exact target/atom, 100KiB readback, oversize article refusal'
