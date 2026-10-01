#!/usr/bin/env bash
# journey.d/jjob1.sh — COMPUTE C1 JOB-LAW: a hand-written job law installs on fresh cells of
# the journey's Store, and every edge of the lifecycle (COMPUTE.md §2.3) is driven with the
# right subject and with a wrong subject or a wrong time; every refusal is asserted by the
# CLAUSE the Host names (P-LAW's J13 style): the refusal line must carry the clause exactly as
# deploy/shell/templates/job/law.job.shell spells it, with the write guard dropped (the Host's
# `LawLeaf.explained`). Ran with the hook contract (journey.sh header): MINI, SPONSOR_WS,
# NEWCOMER_WS, SPONSOR_SUBJECT, NEWCOMER_SUBJECT, JOURNEY_WORLD, JOURNEY_STEP_DIR exported.
#
# The law is deploy/shell/templates/job/law.job.json bound at CALLER = the sponsor (A),
# PROGRAM = 42, WINDOW = 100. **This tree has no K-RAN**, so nothing projects the run slot
# `run/program/42`; the hook binds RAN_SLOT to a STAND-IN, `resource/field/16/after` of the
# job cell itself, and drives the run-dependent edges (truth) with that slot set BY HAND. On
# this tree the stand-in is forgeable by anyone who may write the cell; the forge row below
# shows only that the law refuses a truth without the slot. With K-RAN (the integrator's
# `final`) the binding is RAN_SLOT = run/program/{PROGRAM}, a slot only the controller
# projects, and the truth rows carry a real run claim.
#
# Jobs (each its own cell; A orders, B = the newcomer provides):
#   job1  order, claim, answer, truth (anyone, window), decide->3 (match), close; then closed
#   job2  claim, stall past answerBy: decide->3 refused, decide->4 (stall), close
#   job3  void: B before claimBy refused, A any time admitted, close
#   job4  answer, decide->3 early refused, truth late refused, decide->3 by timeout
#   job5  claim late refused; void by B after claimBy admitted
#   job6  synchronous: truth in state 1 by A refused, by B admitted, decide 1->3
# Exit 0 = every row matched. Last stdout line = rows.tsv.
set -uo pipefail
umask 077
for name in MINI SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR; do
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
A=$SPONSOR_SUBJECT B=$NEWCOMER_SUBJECT
CONTROL=$(jq -r .factoryControllerCapability "$JOURNEY_WORLD/genesis.json")
RAN=resource/field/16/after
# A job cell declares its sixteen fields (K-FIELD-CLOSURE) and, on this tree, field 16: the run slot's
# hand-set stand-in. With K-RAN the stand-in goes and so does field 16 (FIELDS=0-15); until then the
# law does not freeze field 16, so a closed job here still admits a write to it.
FIELDS=0-16
bind() { sed -e "s/{CALLER}/$A/g" -e 's/{PROGRAM}/42/g' -e 's/{NEG_WINDOW}/-100/g' -e 's/{WINDOW}/100/g' \
  -e "s#{RAN_SLOT}#$RAN#g"; }
bind <"$TPL/law.job.json" >"$D/req/law.json"
jq -e '.type == "all" and (.predicates | length) == 44' "$D/req/law.json" >/dev/null \
  || { echo "jjob1: bound law is not 44 clauses" >&2; exit 1; }
# The Host renders a resource/field slot as `field N`, so the stand-in's clause reads `field 16 == 1`.
grep -v '^--' "$TPL/law.job.shell" | bind | sed "s#slot \"$RAN\"#field 16#g" >"$D/law.shell"
# clause K as the Host names it: the shell spelling, write guard dropped.
clause() { sed -n "$(($1 + 1))p" "$D/law.shell" | sed -e 's/;$//' -e 's/not (verb == write), //'; }

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
row() {  # row JOB NAME EXPECTED OBSERVED OK(0/1)
  TOTAL=$((TOTAL + 1))
  local v=FAIL; [ "$5" = 0 ] && { v=PASS; PASS=$((PASS + 1)); }
  printf '%s\t%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$3" "$4" >>"$ROWS"
  printf '%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$4" >&2
}
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
WS_A=$SPONSOR_WS WS_B=$NEWCOMER_WS
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
# undeclared JOB ID LABEL FIELD WS NAME ACTION...: refused by the field closure, naming FIELD.
undeclared() {
  local job=$1 id=$1-$2 label=$3 f=$4 ws=$5; shift 5
  attempt "$ws" "$id" "$@"; local r=$? why; why=$(refusal "$ws" "$id")
  row "$job" "$label" "refused: undeclaredField $f" "$([ $r = 0 ] && echo admitted || echo "[$(printf '%s' "$why" | cut -c1-240)]")" \
    "$([ $r != 0 ] && [[ "$why" == *"undeclaredField $f"* ]]; echo $?)"
}
view() { run "$1" "$MINI" clock --action view --workspace "$WS_A"; jq -r .now "$D/$1.out"; }
tick() { run "tick-$1" "$MINI" clock --action tick --workspace "$WS_A" --control "$CONTROL" --now "$1"; }
started=$(date +%s)

# ---- cells: each created by A under the job law, delegated observe+mutate to B, imported by B
T=$(view v0)
[[ $T =~ ^[0-9]+$ ]] || { echo "jjob1: no clock view: $(tail -1 "$D/v0.err")" >&2; exit 1; }
for j in 1 2 3 4 5 6; do
  n=jjob1-$j
  run "create-$j" "$MINI" workspace --action create --dir "$WS_A" --name "$n" --storage declared --predicate "$D/req/law.json" \
    --fields "$FIELDS"
  row "job$j" "A creates $n under the 44-clause job law" "created" "rc=$(cat "$D/create-$j.rc")" "$(cat "$D/create-$j.rc")"
  jq -n --arg r "$B" --arg n "$n" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,
    recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/grant-$j.json"
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
# A declared cell is born holding no field, only its declaration (K-FIELD-CLOSURE,
# Kernel/NativeHostGenesis.lean `declaredCell`), so the order creates every field it writes.
ORDER=("$(c 0 0)" "$(c 1 42)" "$(c 2 5)" "$(c 3 "$A")" "$(c 4 70)" "$(c 5 100)" "$(c 6 "$CB")" "$(c 7 "$AB")" \
  "$(c 8 100)" "$(c 11 0)")
CLAIM=("$(u 0 0 1)" "$(c 9 "$B")" "$(c 10 80)" "$(u 11 0 100)")
ANSWER=("$(u 0 1 2)" "$(c 12 77)" "$(c 13 1345)" "$(c 14 "$FA")")

# ---- job1: the challenged-and-upheld path
deny job1 o-b "order by B (not the caller)" 3 "$WS_B" jjob1-1 "${ORDER[@]}"
admit job1 o-a "order by A: price 100, escrow 100, claimBy +60, answerBy +600" "$WS_A" jjob1-1 "${ORDER[@]}"
deny job1 c-wrong "B claims naming A the provider" 28 "$WS_B" jjob1-1 "$(u 0 0 1)" "$(c 9 "$A")" "$(c 10 80)" "$(u 11 0 100)"
deny job1 c-low "B claims with bond 50 < price 100" 30 "$WS_B" jjob1-1 "$(u 0 0 1)" "$(c 9 "$B")" "$(c 10 80)" "$(u 11 0 50)"
admit job1 c-ok "B claims with bond 100" "$WS_B" jjob1-1 "${CLAIM[@]}"
deny job1 a-a "A posts the answer (not the provider)" 31 "$WS_A" jjob1-1 "${ANSWER[@]}"
deny job1 a-short "B posts finalAt = now + 50 (window 100)" 35 "$WS_B" jjob1-1 "$(u 0 1 2)" "$(c 12 77)" "$(c 13 1345)" "$(c 14 $((N1 + 50)))"
admit job1 a-ok "B posts output 77, steps 1345, finalAt = now + 100" "$WS_B" jjob1-1 "${ANSWER[@]}"
deny job1 a-again "B posts a second answer (output 78)" 18 "$WS_B" jjob1-1 "$(u 12 77 78)"
deny job1 d4-early "decide -> 4 with no truth" 39 "$WS_A" jjob1-1 "$(u 0 2 4)"
deny job1 t-forge "A writes truth 77 WITHOUT the run slot" 22 "$WS_A" jjob1-1 "$(c 15 77)"
admit job1 t-ok "A writes truth 77 with the run slot (stand-in field 16 := 1, set by hand)" "$WS_A" jjob1-1 "$(c 15 77)" "$(c 16 1)"
deny job1 t-again "truth rewritten 77 -> 78 (with the run slot)" 21 "$WS_A" jjob1-1 "$(u 15 77 78)"
deny job1 d4-match "decide -> 4 when truth = output" 39 "$WS_A" jjob1-1 "$(u 0 2 4)"
deny job1 close-2 "close an undecided job (2 -> 6)" 2 "$WS_A" jjob1-1 "$(u 0 2 6)" "$(u 8 100 0)" "$(u 11 100 0)"
admit job1 d3 "decide -> 3 (truth = output)" "$WS_B" jjob1-1 "$(u 0 2 3)"
deny job1 close-bond "close 3 -> 6 keeping the bond" 43 "$WS_B" jjob1-1 "$(u 0 3 6)" "$(u 8 100 0)"
admit job1 close "close 3 -> 6, escrow 0, bond 0" "$WS_B" jjob1-1 "$(u 0 3 6)" "$(u 8 100 0)" "$(u 11 100 0)"
deny job1 reopen "re-open the closed job (6 -> 3)" 2 "$WS_A" jjob1-1 "$(u 0 6 3)"
# K-FIELD-CLOSURE: the law freezes every field the job declares, but a Pred cannot say "no other
# field"; the kernel refuses a write that creates an undeclared one BY NAME, before the law runs.
undeclared job1 new-field "B creates field 20 on the closed job (the law alone would admit it)" 20 "$WS_B" jjob1-1 "$(c 20 1)"

# ---- job3: void
admit job3 o-a "order" "$WS_A" jjob1-3 "${ORDER[@]}"
deny job3 v-b "B voids before claimBy" 41 "$WS_B" jjob1-3 "$(u 0 0 5)"
admit job3 v-a "A (the caller) voids at once" "$WS_A" jjob1-3 "$(u 0 0 5)"
admit job3 close "close 5 -> 6, escrow 0" "$WS_A" jjob1-3 "$(u 0 5 6)" "$(u 8 100 0)"

# ---- job2, job4, job5, job6: ordered (and claimed / answered) at N1
admit job2 o-a "order" "$WS_A" jjob1-2 "${ORDER[@]}"
admit job2 c-ok "B claims" "$WS_B" jjob1-2 "${CLAIM[@]}"
admit job4 o-a "order" "$WS_A" jjob1-4 "${ORDER[@]}"
admit job4 c-ok "B claims" "$WS_B" jjob1-4 "${CLAIM[@]}"
admit job4 a-ok "B answers, finalAt = N1 + 100" "$WS_B" jjob1-4 "${ANSWER[@]}"
deny job4 d3-early "B takes decide -> 3 inside the window with no truth (closing early)" 38 "$WS_B" jjob1-4 "$(u 0 2 3)"
admit job5 o-a "order" "$WS_A" jjob1-5 "${ORDER[@]}"
admit job6 o-a "order" "$WS_A" jjob1-6 "${ORDER[@]}"
admit job6 c-ok "B claims" "$WS_B" jjob1-6 "${CLAIM[@]}"
deny job6 t1-a "A runs the truth in state 1 (only the provider may)" 24 "$WS_A" jjob1-6 "$(c 15 77)" "$(c 16 1)"
deny job6 d3-norun "decide 1 -> 3 with no run on the cell" 37 "$WS_B" jjob1-6 "$(u 0 1 3)"
admit job6 t1-b "B runs it in state 1 (the synchronous path; run slot by hand)" "$WS_B" jjob1-6 "$(c 15 77)" "$(c 16 1)"
deny job6 a-after "B posts an answer after its own run" 36 "$WS_B" jjob1-6 "${ANSWER[@]}"
admit job6 d3 "decide 1 -> 3" "$WS_A" jjob1-6 "$(u 0 1 3)"

# ---- past answerBy (and claimBy, finalAt)
N2=$((AB + 1))
tick "$N2"
row all "tick to N2 = answerBy + 1 = $N2" "now $N2" "now=$(view v2)" "$([ "$(view v2b)" = "$N2" ]; echo $?)"
deny job2 d3-stall "decide 1 -> 3 on a stalled job" 37 "$WS_B" jjob1-2 "$(u 0 1 3)"
admit job2 d4-stall "decide 1 -> 4: the stall forfeits the bond" "$WS_A" jjob1-2 "$(u 0 1 4)"
admit job2 close "close 4 -> 6" "$WS_A" jjob1-2 "$(u 0 4 6)" "$(u 8 100 0)" "$(u 11 100 0)"
deny job4 t-late "truth after finalAt" 26 "$WS_A" jjob1-4 "$(c 15 77)" "$(c 16 1)"
admit job4 d3-timeout "decide 2 -> 3 by timeout (no truth, now > finalAt)" "$WS_B" jjob1-4 "$(u 0 2 3)"
deny job5 c-late "B claims after claimBy" 27 "$WS_B" jjob1-5 "${CLAIM[@]}"
admit job5 v-b "B voids after claimBy" "$WS_B" jjob1-5 "$(u 0 0 5)"

# ---- management: nobody installs a new law on a job, the caller included. The Host does not name
# the clause of an install refused at admission (`undisclosed: request refused`), so the row pairs
# the refusal with a control: the same install by A on a cell whose law is `all []` is admitted.
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/open.json"
run create-ctl "$MINI" workspace --action create --dir "$WS_A" --name jjob1-ctl --storage declared --predicate "$D/req/open.json"
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
