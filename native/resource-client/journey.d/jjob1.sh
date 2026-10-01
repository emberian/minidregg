#!/usr/bin/env bash
# journey.d/jjob1.sh — COMPUTE C1 JOB-LAW: the job law installs on fresh cells, and every edge of the
# lifecycle (COMPUTE.md §2.3) is driven with the right subject and with a wrong subject or a wrong
# time; every refusal is asserted by the CLAUSE the Host names: the refusal must carry the clause
# exactly as deploy/shell/templates/job/law.job.shell spells it, with the write guard dropped (the
# Host's `LawLeaf.explained`).
#
# The law is law.job.json bound at CALLER = the sponsor (A), PROGRAM = collatz's programId (born
# here), WINDOW = 100. The truth slot is K-RAN's: clause 22 is `ran PROGRAM`, which the controller
# projects only for a run claim it re-executed (`mini job --action truth` carries one); the money
# edges are the job-money receiver's turns (`mini job --action fund|claim|settle`), and the same
# edges as ordinary writes are refused (clause 44 where no earlier clause refuses first).
#
# Self-contained (the J-JOB-MONEY / J-NOCK-3 hook contract): HOST, MINI, STORE, VERIFIER,
# JOURNEY_STEP_DIR, JOB_PROGRAMS (collatz.jam) exported; it bootstraps its own fresh Store
# (newparticipant-acceptance.sh, the J0 fixture, with B = subject 21 enrolled at genesis holding
# account 121), and stops what it starts. Run it from a short root (SUN_LEN).
#
# Jobs (each its own cell; A orders and funds, B = subject 21 provides):
#   job1  order, fund, claim, answer, truth (anyone, window), decide->3 (match), settle; then closed
#   job2  claim, stall past answerBy: decide->3 refused, decide->4 (stall), settle
#   job3  void: B before claimBy refused, A any time admitted, settle
#   job4  answer, decide->3 early refused, truth late refused, decide->3 by timeout
#   job5  claim late refused; void by B after claimBy admitted
#   job6  synchronous: truth in state 1 by A refused, by B admitted, decide 1->3
# Exit 0 = every row matched. Last stdout line = rows.tsv.
set -uo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR JOB_PROGRAMS; do
  if [ -z "${!name:-}" ]; then echo "jjob1: $name is required" >&2; exit 2; fi
done
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
TPL=$(CDPATH='' cd -- "$HERE/../../deploy/shell/templates/job" && pwd)
D=$JOURNEY_STEP_DIR/jjob1
[ ! -e "$D" ] || { echo "jjob1: refusing to reuse $D" >&2; exit 2; }
mkdir -p "$D/req"
ROWS=$D/rows.tsv
printf 'verdict\tjob\trow\texpected\tobserved\n' >"$ROWS"
PASS=0 TOTAL=0
A=7 B=21
W=$D/w

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
row() {  # row JOB NAME EXPECTED OBSERVED OK(0/1)
  TOTAL=$((TOTAL + 1))
  local v=FAIL; [ "$5" = 0 ] && { v=PASS; PASS=$((PASS + 1)); }
  printf '%s\t%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$3" "$4" >>"$ROWS"
  printf '%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$4" >&2
}
stop() { [ -s "$W/public/server.pid" ] && kill "$(cat "$W/public/server.pid")" 2>/dev/null; }
trap stop EXIT
started=$(date +%s)

# ---- the Store: A (the sponsor, 7, account 7) and B (21, account 121)
run keygen "$MINI" keygen --secret "$D/b.key" --public "$D/b.pub"
BPUB=$(od -An -tx1 -v "$D/b.pub" | tr -d ' \n')
cat >"$D/extra.json" <<EOF
[{"key":{"keyId":"7021","keyEpoch":"2","algorithm":"1","subject":"21","publicKey":"$BPUB",
  "activeFrom":"0","activeUntil":"1000000"},"accountId":"121","spendCapabilityId":"1021",
  "controlCapabilityId":"2021","factoryObserveCapabilityId":"3021","initialBalance":"1000000",
  "accountPredicate":{"type":"all","predicates":[]}}]
EOF
NEWPARTICIPANT_OWNER_BUDGET=4000000 EXTRA_GENESIS_ENROLLMENTS="$D/extra.json" \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W" >"$D/fixture.out" 2>"$D/fixture.err" \
  || { echo "jjob1: fixture failed: $(tail -1 "$D/fixture.err")" >&2; exit 1; }
CONFIG=$W/deployment/pinned-config.json SOCK=$W/public/mini.sock
WS_A=$W/sponsor WS_B=$D/b-ws
run init-b "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
  --key "$D/b.key" --subject "$B" --dir "$WS_B"
run purse-a "$MINI" workspace --action import --dir "$WS_A" --name purse --kind account --target 7 \
  --observe-capability 41 --operation-capability 41
run purse-b "$MINI" workspace --action import --dir "$WS_B" --name purse --kind account --target 121 \
  --observe-capability 1021 --operation-capability 1021
cat >"$D/req/tariff.json" <<'EOF'
{"control":"53","book":[],"tariff":{"version":"1","asset":"0",
 "mint":"8585858585858585858585858585858585858585858585858585858585858585",
 "tokenProgram":"0606060606060606060606060606060606060606060606060606060606060606","decimals":"6",
 "creditPerAtomic":"1","maxPerObservation":"2000000000","minTickSlots":"1500","nodeHourRate":"5952380",
 "enrolIndex":null,"journalFloor":"1000000","slashCallerPermille":"500"}}
EOF
run tariff "$MINI" pay book --dir "$WS_A" --source "$D/req/tariff.json"
row all "fresh Store: A sponsors; B enrolled (account 121); the operator's tariff (slash split 500)" "setup" \
  "init-b=$(cat "$D/init-b.rc") purses=$(cat "$D/purse-a.rc")$(cat "$D/purse-b.rc") tariff=$(cat "$D/tariff.rc")" \
  "$([ "$(cat "$D/init-b.rc")$(cat "$D/purse-a.rc")$(cat "$D/purse-b.rc")$(cat "$D/tariff.rc")" = 0000 ]; echo $?)"
# collatz: reads job field 2 as `input`, writes field 15 (truth).
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/open.json"
PID=$(python3 - "$CONFIG" "$SOCK" "$JOB_PROGRAMS/collatz.jam" "$D/collatz.check.json" <<'PY'
import json, socket, struct, sys
cfg = open(sys.argv[1], "rb").read(); sock = sys.argv[2]; jam = open(sys.argv[3], "rb").read()
abi = {"version": "2", "arm": "2", "fuel": "5000000",
       "sample": [{"target": "0", "slot": "resource/field/2/before", "key": "input", "type": "nat"}],
       "outputs": [{"key": "truth", "target": "0", "field": "15", "type": "nat"}], "libraries": []}
payload = struct.pack("<I", len(jam)) + jam + json.dumps(abi).encode()
s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.connect(sock)
body = bytes([1]) + struct.pack("<I", len(cfg)) + cfg + bytes([131]) + payload
s.sendall(struct.pack("<I", len(body)) + body)
def exact(n):
    out = b""
    while len(out) < n:
        c = s.recv(n - len(out))
        if not c: raise SystemExit("short")
        out += c
    return out
n = struct.unpack("<I", exact(4))[0]; reply = exact(n)
v = json.loads(reply[1:]); json.dump(v, open(sys.argv[4], "w")); print(v["programId"])
PY
)
run birth-collatz "$MINI" workspace --action create --dir "$WS_A" --name collatz --storage nock \
  --predicate "$D/req/open.json" --program "$D/collatz.check.json"
row all "collatz born (the job program: input field 2, truth field 15)" "born" \
  "rc=$(cat "$D/birth-collatz.rc") programId=${PID:0:20}..." "$([ "$(cat "$D/birth-collatz.rc")" = 0 ] && [ -n "$PID" ]; echo $?)"

bind() { sed -e "s/{CALLER}/$A/g" -e "s/{PROGRAM}/$PID/g" -e 's/{NEG_WINDOW}/-100/g' -e 's/{WINDOW}/100/g'; }
bind <"$TPL/law.job.json" >"$D/req/law.json"
jq -e '.type == "all" and (.predicates | length) == 45' "$D/req/law.json" >/dev/null \
  || { echo "jjob1: bound law is not 45 clauses" >&2; exit 1; }
grep -v '^--' "$TPL/law.job.shell" | bind >"$D/law.shell"
# clause K as the Host names it: the shell spelling, write guard dropped.
clause() { sed -n "$(($1 + 1))p" "$D/law.shell" | sed -e 's/;$//' -e 's/not (verb == write), //'; }

# refusal WS ID: the Host's outcome as "phase: detail", or the pre-submit refusal line.
refusal() {
  local a=$1/attempts/jjob1-$2
  if [ -f "$a/outcome.json" ] && jq -e '.type == "refused"' "$a/outcome.json" >/dev/null 2>&1; then
    printf '%s: %s' "$(jq -r '.phase // empty' "$a/outcome.json" | xxd -r -p)" "$(jq -r '.detail // empty' "$a/outcome.json" | xxd -r -p)"
  elif [ -f "$a/pre-submit-refusal.json" ]; then
    printf '%s: %s' "$(jq -r '.stage // empty' "$a/pre-submit-refusal.json")" "$(grep -m1 '^refused:' "$D/$2-submit.err" 2>/dev/null)"
  elif [ -s "$D/$2-submit.err" ]; then
    tail -1 "$D/$2-submit.err"
  else
    printf 'propose: %s' "$(grep -m1 '^refused:' "$D/$2-propose.err" 2>/dev/null || tail -1 "$D/$2-propose.err" 2>/dev/null)"
  fi
}
c() { printf '{"type":"create","key":{"type":"object","field":"%s"},"value":"%s"}' "$1" "$2"; }
u() { printf '{"type":"write","key":{"type":"object","field":"%s"},"expected":"%s","value":"%s"}' "$1" "$2" "$3"; }
# attempt WS ID NAME ACTION... -> 0 iff admitted
attempt() {
  local ws=$1 id=$2 name=$3; shift 3
  local acts; acts=$(IFS=,; echo "$*")
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"%s","payload":{"type":"scalar","actions":[%s]}}]}\n' \
    "$name" "$acts" >"$D/req/$id.json"
  run "$id-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$id.json" --proposal-id "jjob1-$id"
  [ "$(cat "$D/$id-propose.rc")" = 0 ] || return 1
  run "$id-submit" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/jjob1-$id/intent.json" --attempt "$ws/attempts/jjob1-$id"
  [ "$(cat "$D/$id-submit.rc")" = 0 ] && jq -e '.type == "confirmed"' "$ws/attempts/jjob1-$id/outcome.json" >/dev/null 2>&1
}
admit() {
  local job=$1 id=$1-$2 label=$3 ws=$4; shift 4
  attempt "$ws" "$id" "$@"; local r=$?
  row "$job" "$label" "admitted" "$([ $r = 0 ] && echo admitted || echo "refused [$(refusal "$ws" "$id" | cut -c1-200)]")" "$r"
}
deny() {  # deny JOB ID LABEL CLAUSE WS NAME ACTION...
  local job=$1 id=$1-$2 label=$3 k=$4 ws=$5; shift 5
  local want; want=$(clause "$k")
  attempt "$ws" "$id" "$@"; local r=$? why; why=$(refusal "$ws" "$id")
  row "$job" "$label" "refused, clause $k: $want" "$([ $r = 0 ] && echo admitted || echo "[$why]")" \
    "$([ $r != 0 ] && [[ "$why" == *"law-denied: $want"* ]]; echo $?)"
}
# the job client's turns (money: fund, claim, settle; the ran truth turn)
mj() { local name=$1; shift; run "$name" "$MINI" job "$@"; }
jadmit() {  # jadmit JOB ID LABEL WS ACTION FLAGS...
  local job=$1 id=$1-$2 label=$3 ws=$4 action=$5; shift 5
  mj "$id" --action "$action" --dir "$ws" "$@"
  local r; r=$(cat "$D/$id.rc")
  row "$job" "$label" "admitted" "$([ "$r" = 0 ] && tail -1 "$D/$id.out" | cut -c1-200 || echo "refused [$(tail -1 "$D/$id.err" | cut -c1-200)]")" "$([ "$r" = 0 ]; echo $?)"
}
jdeny() {  # jdeny JOB ID LABEL CLAUSE WS ACTION FLAGS...
  local job=$1 id=$1-$2 label=$3 k=$4 ws=$5 action=$6; shift 6
  local want; want=$(clause "$k")
  mj "$id" --action "$action" --dir "$ws" "$@"
  local why; why=$(tail -1 "$D/$id.err")
  row "$job" "$label" "refused, clause $k: $want" "$([ "$(cat "$D/$id.rc")" = 0 ] && echo admitted || echo "[$why]")" \
    "$([ "$(cat "$D/$id.rc")" != 0 ] && [[ "$why" == *"$want"* ]]; echo $?)"
}
WS=$WS_A
view() { run "$1" "$MINI" clock --action view --workspace "$WS_A"; jq -r .now "$D/$1.out"; }
tick() { run "tick-$1" "$MINI" clock --action tick --workspace "$WS_A" --control 53 --now "$1"; }

# ---- cells: each created by A under the job law, delegated observe+mutate to B, imported by B
T=$(view v0)
[[ $T =~ ^[0-9]+$ ]] || { echo "jjob1: no clock view: $(tail -1 "$D/v0.err")" >&2; exit 1; }
for j in 1 2 3 4 5 6; do
  n=jjob1-$j
  run "create-$j" "$MINI" workspace --action create --dir "$WS_A" --name "$n" --storage declared --predicate "$D/req/law.json" \
    --fields 0-15
  row "job$j" "A creates $n under the 45-clause job law" "created" "rc=$(cat "$D/create-$j.rc")" "$(cat "$D/create-$j.rc")"
  jq -n --arg r "$B" --arg n "$n" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,
    recipient:$r,verbs:["observe","mutate"],maxCost:"500000"}' >"$D/req/grant-$j.json"
  run "grant-$j-propose" "$MINI" workspace --action propose --dir "$WS_A" --request "$D/req/grant-$j.json" --proposal-id "jjob1-grant-$j"
  run "grant-$j-submit" "$MINI" workspace --action submit --dir "$WS_A" --intent "$WS_A/proposals/jjob1-grant-$j/intent.json" \
    --attempt "$WS_A/attempts/jjob1-grant-$j"
  run "grant-$j-publish" "$MINI" workspace --action publish-delegation --dir "$WS_A" --proposal-id "jjob1-grant-$j" \
    --attempt "$WS_A/attempts/jjob1-grant-$j"
  run "import-$j" "$MINI" workspace --action import --dir "$WS_B" --name "$n" \
    --from-ref "$WS_A/proposals/jjob1-grant-$j/recipient-reference.json"
  row "job$j" "A delegates observe+mutate to B (clause 0: the caller delegates); B imports" "imported" \
    "grant=$(jq -r .type "$WS_A/attempts/jjob1-grant-$j/outcome.json" 2>/dev/null) import rc=$(cat "$D/import-$j.rc")" \
    "$([ "$(cat "$D/import-$j.rc")" = 0 ]; echo $?)"
done

N1=$((T + 10)); CB=$((N1 + 60)); AB=$((N1 + 600)); FA=$((N1 + 100))
tick "$N1"
row all "tick to N1 = $N1" "now $N1" "now=$(view v1)" "$([ "$(view v1b)" = "$N1" ]; echo $?)"
# A declared cell is born holding no field, declaring fields 0-15 (K-FIELD-CLOSURE), so the order
# creates every field it writes. Born unfunded: escrow, provider, providerAcct and bond are 0
# (clauses 11, 12); A funds it by a money turn.
ORDER=("$(c 0 0)" "$(c 1 "$PID")" "$(c 2 5)" "$(c 3 "$A")" "$(c 4 7)" "$(c 5 100)" "$(c 6 "$CB")" "$(c 7 "$AB")" \
  "$(c 8 0)" "$(c 9 0)" "$(c 10 0)" "$(c 11 0)")
CLAIM=("$(u 0 0 1)" "$(u 9 0 "$B")" "$(u 10 0 121)" "$(u 11 0 100)")
# collatz(5) = 5
ANSWER=("$(u 0 1 2)" "$(c 12 5)" "$(c 13 1)" "$(c 14 "$FA")")
claim() { jadmit "$1" "$2" "$3" "$WS_B" claim --job "$(jq -r .target "$WS_A/refs/jjob1-${1#job}.json")" --bond 100 --account purse --name "jjob1-${1#job}"; }
fund() { jadmit "$1" fund "A funds it: escrow 0 -> price, from A's account into the job's held account (money turn)" "$WS_A" fund --name "jjob1-${1#job}" --account purse; }

# ---- job1: the challenged-and-upheld path
deny job1 o-b "order by B (not the caller)" 3 "$WS_B" jjob1-1 "${ORDER[@]}"
deny job1 o-funded "order by A born claiming escrow 100" 11 "$WS_A" jjob1-1 "${ORDER[@]:0:8}" "$(c 8 100)" "$(c 9 0)" "$(c 10 0)" "$(c 11 0)"
admit job1 o-a "order by A: price 100, unfunded, claimBy +60, answerBy +600" "$WS_A" jjob1-1 "${ORDER[@]}"
deny job1 f-plain "A sets escrow = price by an ordinary write (no receiver)" 44 "$WS_A" jjob1-1 "$(u 8 0 100)"
fund job1
deny job1 c-wrong "B claims naming A the provider" 28 "$WS_B" jjob1-1 "$(u 0 0 1)" "$(u 9 0 "$A")" "$(u 10 0 121)" "$(u 11 0 100)"
deny job1 c-low "B claims with bond 50 < price 100" 30 "$WS_B" jjob1-1 "$(u 0 0 1)" "$(u 9 0 "$B")" "$(u 10 0 121)" "$(u 11 0 50)"
deny job1 c-plain "B claims by an ordinary write (a bond no Book transfer backs)" 44 "$WS_B" jjob1-1 "${CLAIM[@]}"
claim job1 c-ok "B claims with bond 100 (money turn: the bond moves into the held account)"
deny job1 a-a "A posts the answer (not the provider)" 31 "$WS_A" jjob1-1 "${ANSWER[@]}"
deny job1 a-short "B posts finalAt = now + 50 (window 100)" 35 "$WS_B" jjob1-1 "$(u 0 1 2)" "$(c 12 5)" "$(c 13 1)" "$(c 14 $((N1 + 50)))"
admit job1 a-ok "B posts output 5 (collatz(5)), finalAt = now + 100" "$WS_B" jjob1-1 "${ANSWER[@]}"
deny job1 a-again "B posts a second answer (output 6)" 18 "$WS_B" jjob1-1 "$(u 12 5 6)"
deny job1 d4-early "decide -> 4 with no truth" 39 "$WS_A" jjob1-1 "$(u 0 2 4)"
deny job1 t-forge "A writes truth 5 WITHOUT a run claim" 22 "$WS_A" jjob1-1 "$(c 15 5)"
jadmit job1 t-ok "A writes the truth WITH the run claim: the kernel re-executes collatz on the job's sample (ran)" "$WS_A" truth --name jjob1-1
deny job1 t-again "truth rewritten 5 -> 6" 21 "$WS_A" jjob1-1 "$(u 15 5 6)"
deny job1 d4-match "decide -> 4 when truth = output" 39 "$WS_A" jjob1-1 "$(u 0 2 4)"
deny job1 close-2 "close an undecided job (2 -> 6)" 2 "$WS_A" jjob1-1 "$(u 0 2 6)" "$(u 8 100 0)" "$(u 11 100 0)"
admit job1 d3 "decide -> 3 (truth = output)" "$WS_B" jjob1-1 "$(u 0 2 3)"
deny job1 close-bond "close 3 -> 6 keeping the bond" 43 "$WS_B" jjob1-1 "$(u 0 3 6)" "$(u 8 100 0)"
deny job1 close-plain "close 3 -> 6 by an ordinary write (no payout)" 44 "$WS_B" jjob1-1 "$(u 0 3 6)" "$(u 8 100 0)" "$(u 11 100 0)"
jadmit job1 close "close 3 -> 6: settle pays B price + bond (money turn)" "$WS_B" settle --name jjob1-1
deny job1 reopen "re-open the closed job (6 -> 3)" 2 "$WS_A" jjob1-1 "$(u 0 6 3)"
attempt "$WS_A" job1-undeclared jjob1-1 "$(c 16 1)"; rund=$?; whyd=$(refusal "$WS_A" job1-undeclared)
row job1 "A creates field 16 on the CLOSED job (a field the cell never declared)" "refused by name: undeclaredField 16" \
  "$([ $rund = 0 ] && echo admitted || echo "[$whyd]")" "$([ $rund != 0 ] && [[ "$whyd" == *"undeclaredField 16"* ]]; echo $?)"

# ---- job3: void
admit job3 o-a "order" "$WS_A" jjob1-3 "${ORDER[@]}"
fund job3
deny job3 v-b "B voids before claimBy" 41 "$WS_B" jjob1-3 "$(u 0 0 5)"
admit job3 v-a "A (the caller) voids at once" "$WS_A" jjob1-3 "$(u 0 0 5)"
jadmit job3 close "close 5 -> 6: settle returns the escrow to A" "$WS_A" settle --name jjob1-3

# ---- job2, job4, job5, job6: ordered (and claimed / answered) at N1
admit job2 o-a "order" "$WS_A" jjob1-2 "${ORDER[@]}"
fund job2
claim job2 c-ok "B claims"
admit job4 o-a "order" "$WS_A" jjob1-4 "${ORDER[@]}"
fund job4
claim job4 c-ok "B claims"
admit job4 a-ok "B answers, finalAt = N1 + 100" "$WS_B" jjob1-4 "${ANSWER[@]}"
deny job4 d3-early "B takes decide -> 3 inside the window with no truth (closing early)" 38 "$WS_B" jjob1-4 "$(u 0 2 3)"
admit job5 o-a "order" "$WS_A" jjob1-5 "${ORDER[@]}"
fund job5
admit job6 o-a "order" "$WS_A" jjob1-6 "${ORDER[@]}"
fund job6
claim job6 c-ok "B claims"
jdeny job6 t1-a "A runs the truth in state 1 (only the provider may)" 24 "$WS_A" truth --name jjob1-6
deny job6 d3-norun "decide 1 -> 3 with no run on the cell" 37 "$WS_B" jjob1-6 "$(u 0 1 3)"
jadmit job6 t1-b "B runs it in state 1 (the synchronous path: B's own run claim)" "$WS_B" truth --name jjob1-6
deny job6 a-after "B posts an answer after its own run" 36 "$WS_B" jjob1-6 "${ANSWER[@]}"
admit job6 d3 "decide 1 -> 3" "$WS_A" jjob1-6 "$(u 0 1 3)"

# ---- past answerBy (and claimBy, finalAt)
N2=$((AB + 1))
tick "$N2"
row all "tick to N2 = answerBy + 1 = $N2" "now $N2" "now=$(view v2)" "$([ "$(view v2b)" = "$N2" ]; echo $?)"
deny job2 d3-stall "decide 1 -> 3 on a stalled job" 37 "$WS_B" jjob1-2 "$(u 0 1 3)"
admit job2 d4-stall "decide 1 -> 4: the stall forfeits the bond" "$WS_A" jjob1-2 "$(u 0 1 4)"
jadmit job2 close "close 4 -> 6: settle splits the forfeited bond (money turn)" "$WS_A" settle --name jjob1-2
jdeny job4 t-late "truth after finalAt" 26 "$WS_A" truth --name jjob1-4
admit job4 d3-timeout "decide 2 -> 3 by timeout (no truth, now > finalAt)" "$WS_B" jjob1-4 "$(u 0 2 3)"
deny job5 c-late "B claims after claimBy" 27 "$WS_B" jjob1-5 "${CLAIM[@]}"
admit job5 v-b "B voids after claimBy" "$WS_B" jjob1-5 "$(u 0 0 5)"

# ---- management: nobody installs a new law on a job, the caller included. The Host does not name
# the clause of an install refused at admission (`undisclosed: request refused`), so the row pairs
# the refusal with a control: the same install by A on a cell whose law is `all []` is admitted.
run create-ctl "$MINI" workspace --action create --dir "$WS_A" --name jjob1-ctl --storage declared --predicate "$D/req/open.json" --fields 0-15
install() {  # install ID NAME -> 0 iff installed
  jq -n --arg n "$2" '{type:"minidregg-workspace-proposal-v1",action:"install-policy",name:$n,predicate:{type:"all",predicates:[]}}' >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$WS_A" --request "$D/req/$1.json" --proposal-id "jjob1-$1"
  run "$1-submit" "$MINI" workspace --action submit --dir "$WS_A" --intent "$WS_A/proposals/jjob1-$1/intent.json" \
    --attempt "$WS_A/attempts/jjob1-$1"
  jq -e '.type == "confirmed"' "$WS_A/attempts/jjob1-$1/outcome.json" >/dev/null 2>&1
}
install install-ctl jjob1-ctl; rctl=$?
install install-job jjob1-2; rjob=$?
why=$(refusal "$WS_A" install-job)
row job2 "A installs all [] over the job law (clause 0: install by nobody); control: the same install on an all [] cell" \
  "job refused at admission; control installed" "job=[$why] control=$([ $rctl = 0 ] && echo installed || echo "refused [$(refusal "$WS_A" install-ctl)]")" \
  "$([ $rjob != 0 ] && [ $rctl = 0 ] && [[ "$why" == *admission* ]]; echo $?)"

verdict="J-JOB-1 $([ $PASS = $TOTAL ] && echo PASS || echo FAIL) $PASS/$TOTAL ($(( $(date +%s) - started )) s)"
echo "$verdict"
echo "$verdict" >&2
echo "$ROWS"
[ $PASS = $TOTAL ]
