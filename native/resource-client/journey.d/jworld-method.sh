#!/usr/bin/env bash
# Real Mini shell journey for member-defined poll kinds. Uses journey.sh's
# existing live Store and two provisioned workspaces; no simulated Host/network.
# Run this hook with JOURNEY_STEP_DIR, MINI, HOST, CONFIG, SOCKET, SPONSOR_WS,
# NEWCOMER_WS and NEWCOMER_SUBJECT from a source-matched transaction9 candidate with fresh compute activation.
# NEWCOMER must have no admitted runs on the current compute day; ownerBudget
# must cover 1M proofWork (as in jsync.sh: NEWPARTICIPANT_OWNER_BUDGET=1000000000000).
# With a placeholder pay tariff, JOURNEY_WORLD supplies genesis + pay/observer.
# Exit zero requires useful effects, current law, actual quota/debits, and replay.
set -euo pipefail
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
: "${SPONSOR_WS:?}" "${NEWCOMER_WS:?}" "${NEWCOMER_SUBJECT:?}"
echo 'JWORLD-METHOD prerequisites: fresh after-core activation; newcomer usedSteps=0; ownerBudget >= 1000000 (bootstrap with NEWPARTICIPANT_OWNER_BUDGET=1000000000000).' >&2
D=$JOURNEY_STEP_DIR/jworld-method
[ ! -e "$D" ] || { echo "refusing to reuse $D" >&2; exit 2; }
mkdir -p -m 700 "$D/alice/requests" "$D/dan/requests" "$D/log"
ROWS=$D/rows.tsv
printf 'step\texpect\trc\tresult\n' >"$ROWS"
N=0
FOREIGN_KEY=0; [ "$NEWCOMER_SUBJECT" != 0 ] || FOREIGN_KEY=1
SHELL_BIN=${SHELL_BIN:-$MINI}
finish() { local rc=$?; printf '%s\n' "$ROWS"; [ "$rc" = 0 ] || echo "JWORLD-METHOD: stopped at the first failed row; see $D/log" >&2; }
trap finish EXIT
say() {
  local who=$1 line=$2 ws
  if [ "$who" = alice ]; then ws=$SPONSOR_WS; else ws=$NEWCOMER_WS; fi
  N=$((N+1)); OUT=$D/log/$N.out; ERR=$D/log/$N.err
  printf '%s\n' "$line" >"$D/log/$N.line"
  if "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
      --workspace "$ws" --home "$D/$who" --line "$line" >"$OUT" 2>"$ERR"; then RC=0; else RC=$?; fi
}
ok() {
  local step=$1 who=$2 line=$3
  say "$who" "$line"
  printf '%s\t0\t%s\t%s\n' "$step" "$RC" "$([ "$RC" = 0 ] && echo PASS || echo FAIL)" >>"$ROWS"
  if [ "$RC" != 0 ]; then cat "$ERR" >&2; return 1; fi
}
check() {
  local step=$1; shift
  if "$@"; then printf '%s\ttrue\t0\tPASS\n' "$step" >>"$ROWS";
  else printf '%s\ttrue\t1\tFAIL\n' "$step" >>"$ROWS"; return 1; fi
}
turn() { local step=$1 who=$2 id=$3 line=$4; ok "$step-prepare" "$who" "$line"; ok "$step-submit" "$who" "submit $id"; }
refused_turn() {
  local step=$1 who=$2 id=$3 line=$4 reason=${5:-}
  # The read-authorized preparation may refuse the exact budget/law already;
  # it is not necessary (or possible) to obtain a signing plan for that refusal.
  say "$who" "$line"
  local stage=prepare
  if [ "$RC" = 0 ]; then
    printf '%s\t0\t0\tPASS\n' "$step-prepare" >>"$ROWS"
    stage=submit
    say "$who" "submit $id"
  fi
  if [ "$RC" != 3 ] || ! grep -q '^refused:' "$ERR" || { [ -n "$reason" ] && ! grep -q "$reason" "$ERR"; }; then
    printf '%s\trefused%s\t%s\tFAIL\n' "$step" "$reason" "$RC" >>"$ROWS"; cat "$ERR" >&2; return 1
  fi
  printf '%s-%s\trefused%s\t%s\tPASS\n' "$step" "$stage" "$reason" "$RC" >>"$ROWS"
}
export_ref() {
  local id=$1 name=$2
  ok "$id-publish" alice "publish $id"
  ok "$id-export" alice "export $id"
  local value; value=$(cat "$OUT")
  ok "$id-import" dan "import $name $value"
}
# Tiny member-authored Nock: close the poll and record its actual vote count.
python3 - "$D/alice/requests/close-program.json" <<'PROGRAM'
import json,sys
def mat(n):
    if n == 0: return [1]
    b = n.bit_length(); c = b.bit_length()
    return [0] * c + [1] + [(b >> i) & 1 for i in range(c - 1)] + [(n >> i) & 1 for i in range(b)]
def jam(noun):
    out, table = [], {}
    def go(n):
        key = ("a", n) if isinstance(n, int) else ("c", n)
        if key in table:
            p = table[key]
            if isinstance(n, int) and n.bit_length() <= p.bit_length(): out.extend([0] + mat(n))
            else: out.extend([1, 1] + mat(p))
            return
        table[key] = len(out)
        if isinstance(n, int): out.extend([0] + mat(n))
        else: out.extend([1, 0]); go(n[0]); go(n[1])
    go(noun)
    atom = sum(bit << i for i, bit in enumerate(out))
    return atom.to_bytes((atom.bit_length() + 7) // 8, "little")
def atom_of(b): return int.from_bytes(b, "little")
def cord(s): return int.from_bytes(s.encode(), "little")
def core(battery): return ((1, (battery, (0, 0))), 0)   # [[1 gate] 0], gate [battery [0 0]]
battery=(((1,cord("open")),(1,0)),(((1,cord("count")),(0,109)),(1,0)))
abi={"evaluator":"nock","version":"5","context":"pinned","arm":"2","fuel":"10000",
 "sample":[{"target":"0","slot":"world/resource/field/3/count/before","key":"votes","type":"nat"}],
 "outputs":[{"key":"open","target":"0","field":"90","type":"nat"},{"key":"count","target":"0","field":"91","type":"nat"}],"libraries":[]}
json.dump({"jam":jam(core(battery)).hex(),"abi":abi},open(sys.argv[1],"w"))
PROGRAM
ok program-create alice 'program create wm-close @close-program.json open'
PROGRAM_ID=$(jq -er '.programId' "$SPONSOR_WS/programs/wm-close.json")
jq -n --arg program "$PROGRAM_ID" '{descriptor:{revision:"1",fields:[
 {id:"2",name:"open",meaning:"poll accepts votes",codec:"nat",discipline:"ram"},
 {id:"3",name:"votes",meaning:"one vote by subject",codec:"nat",discipline:"append"},
 {id:"4",name:"tally",meaning:"number of votes at closure",codec:"nat",discipline:"ram"},
 {id:"5",name:"methods",meaning:"dregg/world/method-table/v1",codec:"bytes",discipline:"rom"}]},
 defaults:[{field:"2",key:"0",value:"1"},{field:"4",key:"0",value:"0"},
 {field:"5",key:"0",value:[{name:"close",program:$program,outputs:[{output:"90",field:"2",key:"0"},{output:"91",field:"4",key:"0"}]}]}]}' >"$D/alice/requests/poll.json"
ok kind-create alice 'kind create wm-poll @poll.json open'
ok instance-create alice 'create wm-one --from wm-poll open'
ok inspect-method alice 'instance show wm-one'
check method-is-world-resident jq -e --arg program "$PROGRAM_ID" '.value.methods[0].program==$program' "$OUT" >/dev/null
turn vote alice wm-vote 'instance set wm-vote wm-one votes 7 1'
turn close alice wm-close-call 'instance call wm-close-call wm-one close'
ok inspect-result alice 'instance show wm-one'
check method-result jq -e '.value.entries|any(.field=="2" and .key=="0" and .value=="0")' "$OUT" >/dev/null
check method-tally jq -e '.value.entries|any(.field=="4" and .key=="0" and .value=="1")' "$OUT" >/dev/null
# The old descriptor/table stays attached to its instance after revision.
jq '.descriptor.revision="2" | .defaults|=map(if .field=="5" then .value=[] else . end)' "$D/alice/requests/poll.json" >"$D/alice/requests/poll-v2.json"
turn revise alice wm-revise 'kind revise wm-revise wm-poll @poll-v2.json'
ok old-method-stable alice 'instance show wm-one'
check retained-method jq -e '.value.descriptor.revision=="1" and .value.methods[0].name=="close"' "$OUT" >/dev/null
ok new-instance alice 'create wm-two --from wm-poll open'
ok new-definition-used alice 'instance show wm-two'
check new-method-table jq -e '.value.descriptor.revision=="2" and .value.methods==[]' "$OUT" >/dev/null
# Current export remains restrictive authority even over a checked old method.
printf '%s\n' '{"selector":{"physicalKinds":["18"],"verbs":["2"]},"parents":[],"predicate":{"type":"any","predicates":[]}}' >"$D/alice/requests/sealed.json"
turn export-seal alice wm-seal 'law export wm-seal wm-poll @sealed.json'
refused_turn checked-method-restricted alice wm-blocked 'instance call wm-blocked wm-one close'
# Exact proposal ID reuses the original signed claim after the definition/export moves.
ok retained-call alice 'instance call wm-close-call wm-one close'
check retained-intent test -s "$SPONSOR_WS/proposals/wm-close-call/intent.bin"

# Consume quota through a real world method; never seed usage or edit Book.
ok_external() {
  local step=$1; shift
  N=$((N+1)); OUT=$D/log/$N.out; ERR=$D/log/$N.err
  printf '%q ' "$@" >"$D/log/$N.line"; printf '\n' >>"$D/log/$N.line"
  if "$@" >"$OUT" 2>"$ERR"; then RC=0; else RC=$?; fi
  printf '%s\t0\t%s\t%s\n' "$step" "$RC" "$([ "$RC" = 0 ] && echo PASS || echo FAIL)" >>"$ROWS"
  if [ "$RC" != 0 ]; then cat "$ERR" >&2; return 1; fi
}
payer_snapshot() {
  local label=$1
  ok_external "$label-signed-account" "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name wm-payer
  cp "$OUT" "$D/$label.json"
}
uncharged() {
  local label=$1 before=$2
  payer_snapshot "$label"
  check "$label-no-usage-or-debit" jq -e --slurpfile before "$D/$before.json" \
    '.computeQuote==$before[0].computeQuote and .balances==$before[0].balances' "$D/$label.json" >/dev/null
}
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/permit-all.json"
for account in wm-payer wm-other; do
  ok_external "provision-$account" "$MINI" workspace --action provision --dir "$SPONSOR_WS" \
    --name "$account" --holder "$NEWCOMER_SUBJECT" --funding 1000 \
    --account-predicate "$D/permit-all.json" --factory-ref factory
  provision=$SPONSOR_WS/provisions/$account/provision.json
  ok_external "import-$account" "$MINI" workspace --action import --dir "$NEWCOMER_WS" \
    --name "$account" --kind account --target "$(jq -er '.account.target' "$provision")" \
    --observe-capability "$(jq -er '.account.ownerCapability' "$provision")" \
    --operation-capability "$(jq -er '.account.ownerCapability' "$provision")" \
    --control-capability "$(jq -er '.account.controlCapability' "$provision")" --provenance "$provision"
done
payer_snapshot initial
check fresh-compute-subject jq -e --arg subject "$NEWCOMER_SUBJECT" \
  '.computeQuote.subject==$subject and .computeQuote.usedSteps=="0" and
   .computeQuote.freeSteps=="1000000" and .computeQuote.creditsPerStep=="1"' "$D/initial.json" >/dev/null || {
  echo 'JWORLD-METHOD requires an active source quote and a newcomer with zero admitted usage today; use the dedicated fresh after-core fixture.' >&2
  exit 1
}
# Only replace the invalid fresh tariff, via actual signed pay control.
# PayBookReceiver.bookPatch [] appends no rows and preserves the existing book.
if ! jq -e '.computeQuote.creditAsset != null' "$D/initial.json" >/dev/null; then
  test -n "${JOURNEY_WORLD:-}"
  ok_external current-pay-view python3 - "$CONFIG" "$SOCKET" "$D/pay-view.bin" <<'PAYVIEW'
import socket,struct,sys
config=open(sys.argv[1],"rb").read()
body=b"\x01"+struct.pack("<I",len(config))+config+bytes([107])
with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
    s.connect(sys.argv[2]); s.sendall(struct.pack("<I",len(body))+body)
    def exact(n):
        out=b""
        while len(out)<n:
            part=s.recv(n-len(out))
            if not part: raise RuntimeError("short pay-view response")
            out+=part
        return out
    reply=exact(struct.unpack("<I",exact(4))[0])
assert reply[0]==107, repr(reply[:100])
open(sys.argv[3],"wb").write(reply[1:])
PAYVIEW
  ok_external inspect-pay-view "$HOST" "$CONFIG" inspect pay-view "$D/pay-view.bin" "$D/pay-view.json"
  ok_external tariff-source python3 - "$D/pay-view.json" "$JOURNEY_WORLD/genesis.json" "$D/tariff.json" <<'TARIFF'
import json,sys
view,genesis=(json.load(open(p)) for p in sys.argv[1:3])
tariff={"version":str(int(view["tariff"]["version"])+1),"asset":"0",
 "mint":"8525966c00f39ff54ef5e537a4736af436494d1f1681c659bd98e37ac28beff1",
 "tokenProgram":"06ddf6e1ee758fde18425dbce46ccddab61afc4d83b90d27febdf928d8a18bfc",
 "decimals":"6","creditPerAtomic":"1","maxPerObservation":"2000000000",
 "minTickSlots":"1500","nodeHourRate":"5952380","enrolIndex":None,
 "journalFloor":"1000000","slashCallerPermille":"500"}
json.dump({"control":genesis["payObserver"]["controlCapability"],"book":[],"tariff":tariff},open(sys.argv[3],"w"))
TARIFF
  ok_external install-compute-tariff "$MINI" pay book --dir "$JOURNEY_WORLD/pay/observer" --source "$D/tariff.json"
fi
payer_snapshot ready
check fixture-credit-asset jq -e '.computeQuote.creditAsset=="0" and (.balances|any(.[0]=="0" and .[1]=="1000"))' "$D/ready.json" >/dev/null
QUOTA_DAY=$(jq -er '.computeQuote.day' "$D/ready.json")
# Exact jsync.sh bytecode: 10*n+30 source-counted steps. ABI5/pinned retains
# its target/slot shape; fuel is the actual 1M synchronous ceiling.
python3 - "$D/dan/requests/quota-program.json" <<'QUOTAPROGRAM'
import json,sys
gate="c5855fc892e320581c76e196c804d3be8ae1e3301354f7b1212bcc716ea2133b0836046ec846c321e247c3cab4003d5d98dc5919dd0b6cc1dd167cac0a"
abi={"evaluator":"nock","version":"5","context":"pinned","arm":"2","fuel":"1000000",
 "sample":[{"target":"0","slot":f"world/resource/field/{field}/0/before","key":key,"type":"nat"}
           for field,key in [(2,"n"),(3,"c")]],
 "outputs":[{"key":"c","target":"0","field":"3","type":"nat"}],"libraries":[]}
json.dump({"jam":gate,"abi":abi},open(sys.argv[1],"w"))
QUOTAPROGRAM
ok quota-program-create dan 'program create wm-quota-program @quota-program.json open'
QUOTA_PROGRAM=$(jq -er '.programId' "$NEWCOMER_WS/programs/wm-quota-program.json")
jq -n --arg program "$QUOTA_PROGRAM" '{descriptor:{revision:"1",fields:[
 {id:"2",name:"iterations",meaning:"Nock loop iterations",codec:"nat",discipline:"ram"},
 {id:"3",name:"calls",meaning:"completed method calls",codec:"nat",discipline:"ram"},
 {id:"4",name:"methods",meaning:"dregg/world/method-table/v1",codec:"bytes",discipline:"rom"}]},
 defaults:[{field:"2",key:"0",value:"99997"},{field:"3",key:"0",value:"0"},
 {field:"4",key:"0",value:[{name:"count",program:$program,outputs:[{output:"3",field:"3",key:"0"}]}]}]}' \
 >"$D/dan/requests/quota-kind.json"
ok quota-kind-create dan 'kind create wm-quota-kind @quota-kind.json open'
ok quota-instance-create dan 'create wm-quota --from wm-quota-kind open'
# Useful poll computation under the SAME quota subject, after the free cut.
cp "$D/alice/requests/poll.json" "$D/dan/requests/paid-poll.json"
ok paid-poll-kind-create dan 'kind create wm-paid-poll @paid-poll.json open'
ok paid-poll-instance-create dan 'create wm-paid-one --from wm-paid-poll open'
turn paid-poll-vote dan wm-paid-vote 'instance set wm-paid-vote wm-paid-one votes 7 1'
payer_snapshot before-boundary
check fresh-before-boundary jq -e --arg day "$QUOTA_DAY" \
 '.computeQuote.day==$day and .computeQuote.usedSteps=="0"' "$D/before-boundary.json" >/dev/null
ok boundary-prepare dan 'instance call wm-boundary wm-quota count'
check exact-million-claim jq -e '.purpose.draft.command.run.steps=="1000000" and (.purpose.draft.command.targets|length)==1' \
 "$NEWCOMER_WS/proposals/wm-boundary/intent.json" >/dev/null
ok boundary-submit dan 'submit wm-boundary'
ok boundary-method-result dan 'instance show wm-quota'
check boundary-counter jq -e '.value.entries|any(.field=="3" and .key=="0" and .value=="1")' "$OUT" >/dev/null
payer_snapshot boundary
check free-million-admitted-without-debit jq -e --arg day "$QUOTA_DAY" --slurpfile before "$D/before-boundary.json" \
 '.computeQuote.day==$day and .computeQuote.usedSteps=="1000000" and .balances==$before[0].balances and
  .computeQuote.bookRoot==$before[0].computeQuote.bookRoot' "$D/boundary.json" >/dev/null
turn shorten-loop dan wm-short-loop 'instance set wm-short-loop wm-quota iterations 0 0'
refused_turn exhausted-free-quota dan wm-unfunded 'instance call wm-unfunded wm-quota count'
uncharged unfunded boundary
say dan 'instance call wm-under-ceiling wm-quota count --fund wm-payer --max-compute-credits 29'
check explicit-credit-ceiling-refused test "$RC" = 1
check explicit-credit-ceiling-named grep -q 'above consent ceiling 29' "$ERR"
check refused-ceiling-created-no-intent test ! -e "$NEWCOMER_WS/proposals/wm-under-ceiling/intent.bin"
uncharged ceiling boundary
# Deliberately inconsistent local reference hints still read via actual grants.
# Neither hint supplies transfer authority for its selected payer.
PAYER_TARGET=$(jq -er '.target' "$NEWCOMER_WS/refs/wm-payer.json")
PAYER_CAP=$(jq -er '.operationCapability' "$NEWCOMER_WS/refs/wm-payer.json")
OTHER_TARGET=$(jq -er '.target' "$NEWCOMER_WS/refs/wm-other.json")
OTHER_CAP=$(jq -er '.operationCapability' "$NEWCOMER_WS/refs/wm-other.json")
OBJECT_CAP=$(jq -er '.operationCapability' "$NEWCOMER_WS/refs/wm-quota.json")
ok_external import-wrong-payer "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name wm-wrong-payer \
 --kind account --target "$OTHER_TARGET" --observe-capability "$OTHER_CAP" --operation-capability "$PAYER_CAP"
ok_external import-wrong-cap "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name wm-wrong-cap \
 --kind account --target "$PAYER_TARGET" --observe-capability "$PAYER_CAP" --operation-capability "$OBJECT_CAP"
refused_turn wrong-payer-refused dan wm-bad-payer 'instance call wm-bad-payer wm-quota count --fund wm-wrong-payer --max-compute-credits 30'
uncharged bad-payer boundary
ok_external wrong-payer-balance-unchanged "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name wm-other
check wrong-payer-no-debit jq -e '.balances|any(.[0]=="0" and .[1]=="1000")' "$OUT" >/dev/null
refused_turn wrong-capability-refused dan wm-bad-cap 'instance call wm-bad-cap wm-quota count --fund wm-wrong-cap --max-compute-credits 30'
uncharged bad-cap boundary
ok paid-loop-prepare dan 'instance call wm-paid-loop wm-quota count --fund wm-payer --max-compute-credits 30'
check exact-funded-thirty jq -e '.admittedSteps=="30" and .credits=="30" and .maxComputeCredits=="30"' \
 "$NEWCOMER_WS/proposals/wm-paid-loop/compute-consent.json" >/dev/null
check funding-is-final-leg jq -e '.purpose.draft.command as $c | $c.run.steps=="30" and
 ($c.targets|length)==2 and $c.targets[0].payload.type=="world" and
 $c.targets[1].kind=="account" and $c.targets[1].payload.type=="computeFunding" and
 $c.targets[1].payload.credits=="30"' "$NEWCOMER_WS/proposals/wm-paid-loop/intent.json" >/dev/null
cp "$NEWCOMER_WS/proposals/wm-paid-loop/intent.bin" "$D/paid-loop-original.bin"
ok paid-loop-submit dan 'submit wm-paid-loop'
ok paid-loop-result dan 'instance show wm-quota'
check funded-counter jq -e '.value.entries|any(.field=="3" and .key=="0" and .value=="2")' "$OUT" >/dev/null
payer_snapshot paid-loop
check atomic-thirty-charge jq -e --arg day "$QUOTA_DAY" --slurpfile before "$D/boundary.json" \
 '.computeQuote.day==$day and .computeQuote.usedSteps=="1000030" and
  .computeQuote.bookRoot!=$before[0].computeQuote.bookRoot and (.balances|any(.[0]=="0" and .[1]=="970"))' \
 "$D/paid-loop.json" >/dev/null
ok paid-poll-prepare dan 'instance call wm-paid-close wm-paid-one close --fund wm-payer --max-compute-credits 1000'
POLL_STEPS=$(jq -er '.admittedSteps' "$NEWCOMER_WS/proposals/wm-paid-close/compute-consent.json")
check paid-poll-real-charge jq -e '.credits==.admittedSteps and (.credits|tonumber)>0' \
 "$NEWCOMER_WS/proposals/wm-paid-close/compute-consent.json" >/dev/null
cp "$NEWCOMER_WS/proposals/wm-paid-close/intent.bin" "$D/paid-close-original.bin"
ok paid-poll-submit dan 'submit wm-paid-close'
ok paid-poll-result dan 'instance show wm-paid-one'
check paid-poll-closed-and-tallied jq -e \
 '(.value.entries|any(.field=="2" and .key=="0" and .value=="0")) and
  (.value.entries|any(.field=="4" and .key=="0" and .value=="1"))' "$OUT" >/dev/null
payer_snapshot paid-poll
check useful-method-charge jq -e --arg day "$QUOTA_DAY" --arg steps "$POLL_STEPS" \
 '.computeQuote.day==$day and (.computeQuote.usedSteps|tonumber)==(1000030+($steps|tonumber)) and
  (.balances|any(.[0]=="0" and (.[1]|tonumber)==(970-($steps|tonumber))))' "$D/paid-poll.json" >/dev/null
# Retained exact bytes after state and Book moved: success is replay, not a new run.
ok paid-loop-retained dan 'instance call wm-paid-loop wm-quota count --fund wm-payer --max-compute-credits 30'
check paid-loop-exact-intent cmp "$D/paid-loop-original.bin" "$NEWCOMER_WS/proposals/wm-paid-loop/intent.bin"
ok paid-loop-retry dan 'submit wm-paid-loop'
uncharged paid-loop-retry paid-poll
ok paid-close-retained dan 'instance call wm-paid-close wm-paid-one close --fund wm-payer --max-compute-credits 1000'
check paid-close-exact-intent cmp "$D/paid-close-original.bin" "$NEWCOMER_WS/proposals/wm-paid-close/intent.bin"
ok paid-close-retry dan 'submit wm-paid-close'
uncharged paid-close-retry paid-poll
ok retry-counter-read dan 'instance show wm-quota'
check retry-did-not-run-again jq -e '.value.entries|any(.field=="3" and .key=="0" and .value=="2")' "$OUT" >/dev/null

printf 'JWORLD-METHOD: PASS\n' >&2
