#!/usr/bin/env bash
# Offline authoring/control-flow fixtures, not Host admission qualification.
set -euo pipefail
umask 077
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
HELPER=$HERE/jpay-claim-law.sh
RUN=$(mktemp -d /tmp/jpay-claim-law-fixture.XXXXXX)
# Preserve fixtures for inspection; they contain no keys or real signed calls.
printf 'fixtures: %s\n' "$RUN"
mkdir "$RUN/ws" "$RUN/ws/refs" "$RUN/fixture"
export FIXTURE=$RUN/fixture
cat >"$RUN/fake-mini" <<'FAKE'
#!/usr/bin/env bash
set -euo pipefail
cmd=$1; shift
dir= intent= config= mode= prepare=
while (($#)); do
  case "$1" in
    --dir|--attempt) dir=$2;;
    --intent) intent=$2;;
    --config) config=$2;;
    --mode) mode=$2;;
    --prepare-only) prepare=$2;;
    --host|--socket|--key|--view) :;;
    *) echo "unexpected mini argument $1" >&2; exit 90;;
  esac
  shift 2
done
jq -nc --arg cmd "$cmd" --arg dir "$dir" --arg mode "$mode" --arg prepare "$prepare" \
  '{cmd:$cmd,dir:$dir,mode:$mode,prepare:$prepare}' >>"$FIXTURE/calls"
matches() {
 jq -e --slurpfile live "$FIXTURE/current.json" '
  .purpose.draft.declaration |
  .expected==$live[0].expected and .expectedPreRoot==$live[0].root
 ' "$1" >/dev/null
}
case "$cmd" in
  query)
    mkdir "$dir"
    cp "$FIXTURE/policy.json" "$dir/view.json"
    cp "$FIXTURE/challenge.json" "$dir/challenge.json"
    printf 'offline signed-observation placeholder' >"$dir/signed-observation.bin"
    cat "$dir/view.json"
    if [[ -f $FIXTURE/race ]]; then cp "$FIXTURE/new-head.json" "$FIXTURE/current.json"; fi;;
  submit)
    [[ $prepare == true ]] || { echo 'must prepare only' >&2; exit 91; }
    mkdir "$dir"
    cp "$intent" "$dir/intent.json"
    matches "$intent" || { echo 'fixture: exact preimage differs' >&2; exit 3; }
    cp "$config" "$dir/config.json"
    printf '{"format":"offline-fixture"}\n' >"$dir/attempt.json"
    cp "$intent" "$dir/call.bin";;
  retry)
    if [[ $mode == submit ]]; then
      matches "$dir/intent.json" || { echo 'fixture: exact preimage differs' >&2; exit 3; }
    elif [[ $mode != lookup ]]; then exit 92; fi
    printf '{"fixture":true,"mode":"%s"}\n' "$mode";;
  *) echo "unexpected mini command $cmd" >&2; exit 93;;
esac
FAKE
chmod 755 "$RUN/fake-mini"
printf '{"public":"fixture config"}\n' >"$RUN/config.json"
jq -n --arg root "$RUN" '
 {type:"minidregg-participant-workspace-v1",subject:"11",
  host:($root+"/Host"),config:($root+"/config.json"),key:($root+"/KEY-MUST-NOT-EXIST"),
  socket:($root+"/mini.sock")}
' >"$RUN/ws/workspace.json"
printf '%s\n' '{"type":"minidregg-participant-reference-v1","name":"factory","kind":"object","target":"7","observeCapability":"8","controlCapability":"9"}' >"$RUN/ws/refs/factory.json"
jq -n '
 def eq($s;$v): {type:"eq",slot:$s,value:$v};
 def neg($p): {type:"not",predicate:$p};
 def allp($p): {type:"all",predicates:$p};
 def anyp($p): {type:"any",predicates:$p};
 allp([{type:"monotone",slot:"edited/by/operator"},
       anyp([eq("request/verb";"4"),eq("request/subject";"11")])]) as $base |
 {type:"policy",policyId:"934",version:"9007199254740999",
  address:"999999999999999999999999999999999999999999999999999999999999",
  domain:"224",semantics:"225",previous:"116",canonical:"00",text:"edited ordinary base",
  predicate:allp([neg(eq("request/subject";"40")),neg(eq("request/subject";"41")),
   anyp([allp([eq("request/subject";"30"),eq("authority/operation/pay-self-enrol";"1")]),
    allp([neg(eq("request/subject";"30")),neg(eq("authority/operation/pay-self-enrol";"1")),$base])])])}
' >"$FIXTURE/original.json"
printf '%s\n' '{"authorityRoot":"888888888888888888888888888888888888888888888888888888888888"}' >"$FIXTURE/original-challenge.json"
jq -n '{expected:{version:"9007199254741000",address:"222"},root:"333"}' >"$FIXTURE/new-head.json"
reset_fixture() {
 cp "$FIXTURE/original.json" "$FIXTURE/policy.json"
 cp "$FIXTURE/original-challenge.json" "$FIXTURE/challenge.json"
 jq -n --slurpfile p "$FIXTURE/policy.json" --slurpfile c "$FIXTURE/challenge.json" \
   '{expected:{version:$p[0].version,address:$p[0].address},root:$c[0].authorityRoot}' >"$FIXTURE/current.json"
 : >"$FIXTURE/calls"
 if [[ -f $FIXTURE/race ]]; then mv "$FIXTURE/race" "$FIXTURE/race.used"; fi
}
run_helper() {
 "$HELPER" --mini "$RUN/fake-mini" --workspace "$RUN/ws" --name factory --dir "$RUN/$1"
}
expect_rc() {
 local expected=$1; shift
 local rc=0
 "$@" >"$RUN/last.stdout" 2>"$RUN/last.stderr" || rc=$?
 [[ $rc == "$expected" ]] || { cat "$RUN/last.stderr" >&2; echo "expected $expected got $rc" >&2; exit 1; }
}
N=0
pass() { N=$((N+1)); printf 'PASS %s: %s\n' "$N" "$*"; }
reset_fixture
run_helper prepared
jq -e -s 'map(.cmd)==["query","submit"] and .[1].prepare=="true"' "$FIXTURE/calls" >/dev/null
[[ ! -e $RUN/KEY-MUST-NOT-EXIST ]]
pass 'default signs a prepared call only, without reading key contents'
jq -e --slurpfile p "$FIXTURE/original.json" --slurpfile c "$FIXTURE/original-challenge.json" '
 .purpose.draft.declaration as $d | $p[0] as $p |
 $d.expected == {version:$p.version,address:$p.address} and
 $d.expectedPreRoot==$c[0].authorityRoot and
 $d.source.policyId==$p.policyId and $d.source.domain==$p.domain and
 $d.source.semantics==$p.semantics and $d.source.previous==$p.address and
 $d.source.version=="9007199254741000" and
 $d.source.predicate.predicates[0:-1]==$p.predicate.predicates[0:-1] and
 $d.source.predicate.predicates[-1].predicates[0]==$p.predicate.predicates[-1].predicates[0] and
 $d.source.predicate.predicates[-1].predicates[1].predicates[0:2]==$p.predicate.predicates[-1].predicates[1].predicates[0:2] and
 $d.source.predicate.predicates[-1].predicates[1].predicates[2].predicates[1].predicates[1]==
   $p.predicate.predicates[-1].predicates[1].predicates[2]
' "$RUN/prepared/intent.json" >/dev/null
pass 'complete edited base, confinement and decimal metadata retained exactly'
"$HELPER" --mini "$RUN/fake-mini" --dir "$RUN/prepared" --apply >/dev/null
jq -e -s 'map(.cmd)==["query","submit","retry"] and .[-1].mode=="submit"' "$FIXTURE/calls" >/dev/null
pass 'explicit apply uses exactly retained call, without another query or prepare'
cp "$FIXTURE/new-head.json" "$FIXTURE/current.json"
expect_rc 3 "$HELPER" --mini "$RUN/fake-mini" --dir "$RUN/prepared" --apply
jq -e -s '[.[]|select(.cmd=="query")]|length==1' "$FIXTURE/calls" >/dev/null
pass 'concurrent head change remains a mismatch at apply, never rebased'
"$HELPER" --mini "$RUN/fake-mini" --dir "$RUN/prepared" --lookup >/dev/null
jq -e -s '.[-1].cmd=="retry" and .[-1].mode=="lookup"' "$FIXTURE/calls" >/dev/null
pass 'uncertain recovery uses retained-call lookup'
printf 'changed\n' >>"$RUN/prepared/submit/call.bin"
count=$(wc -l <"$FIXTURE/calls")
expect_rc 64 "$HELPER" --mini "$RUN/fake-mini" --dir "$RUN/prepared" --apply
[[ $(wc -l <"$FIXTURE/calls") == "$count" ]]
pass 'changed retained call refuses before any client action'
reset_fixture
touch "$FIXTURE/race"
expect_rc 3 run_helper raced
jq -e --slurpfile p "$FIXTURE/original.json" '
 .purpose.draft.declaration.expected.version==$p[0].version and
 .purpose.draft.declaration.expected.address==$p[0].address
' "$RUN/raced/intent.json" >/dev/null
[[ ! -e $RUN/raced/prepared.json ]]
pass 'query-to-prepare race preserves old exact preimage and produces no prepared marker'
reset_fixture
jq '.predicate.predicates[-1].predicates[1].predicates[0].predicate.value="31"' "$FIXTURE/original.json" >"$FIXTURE/policy.json"
expect_rc 5 run_helper bad-observer
jq -e -s 'map(.cmd)==["query"]' "$FIXTURE/calls" >/dev/null
pass 'changed observer confinement refuses before submit'
reset_fixture
jq '.predicate.predicates[0].predicate.slot="another/slot"' "$FIXTURE/original.json" >"$FIXTURE/policy.json"
expect_rc 5 run_helper bad-ticker
pass 'unknown ticker wrapper refuses'
reset_fixture
jq '.predicate.predicates[-1].predicates[1].predicates[2]={type:"eq",slot:"pay/claim/authorized",value:"1"}' "$FIXTURE/original.json" >"$FIXTURE/policy.json"
expect_rc 5 run_helper existing-claim
pass 'existing claim slot refuses ambiguous duplicate extension'
reset_fixture
"$HELPER" --mini "$RUN/fake-mini" --workspace "$RUN/ws" --name factory --dir "$RUN/dry" --dry >/dev/null
jq -e -s 'map(.cmd)==["query"]' "$FIXTURE/calls" >/dev/null
[[ -s $RUN/dry/intent.json && ! -e $RUN/dry/submit ]]
pass 'dry mode only retains signed query and authored intent'
reset_fixture
printf '{"authorityRoot":123}\n' >"$FIXTURE/challenge.json"
expect_rc 5 run_helper bad-root
pass 'malformed authority root refuses before signing an update'
printf '%s offline fixture checks passed; no real Host, key, or service used.\n' "$N"
