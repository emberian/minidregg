#!/usr/bin/env bash
# Real Mini shell journey for member-defined poll kinds. Uses journey.sh's
# existing live Store and two provisioned workspaces; no simulated Host/network.
# Run this hook with JOURNEY_STEP_DIR, MINI, HOST, CONFIG, SOCKET, SPONSOR_WS,
# NEWCOMER_WS and NEWCOMER_SUBJECT from a source-matched transaction9 candidate with fresh compute activation.
# Exit zero requires both descriptor behavior AND current exported-law admission.
set -euo pipefail
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
: "${SPONSOR_WS:?}" "${NEWCOMER_WS:?}" "${NEWCOMER_SUBJECT:?}"
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
  ok "$step-prepare" "$who" "$line"
  say "$who" "submit $id"
  if [ "$RC" != 3 ] || ! grep -q '^refused:' "$ERR" || { [ -n "$reason" ] && ! grep -q "$reason" "$ERR"; }; then
    printf '%s\trefused%s\t%s\tFAIL\n' "$step" "$reason" "$RC" >>"$ROWS"; cat "$ERR" >&2; return 1
  fi
  printf '%s\trefused%s\t%s\tPASS\n' "$step" "$reason" "$RC" >>"$ROWS"
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
printf 'JWORLD-METHOD: PASS\n' >&2
