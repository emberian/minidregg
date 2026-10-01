#!/usr/bin/env bash
# K-CLOCK (MUD.md item 3) + CLOCK-SUBJECT: the deployment's one clock, on the
# journey's Store, ticked by its dedicated clock subject.
#
# Journey hook contract (journey.sh header): executed with MINI, SPONSOR_WS,
# NEWCOMER_WS, JOURNEY_WORLD and JOURNEY_STEP_DIR exported, against the live
# journey service. Exit 0 = PASS. The verdict line `K-CLOCK PASS n/n` is the
# last stderr line and the line before the last stdout line; the last stdout
# line is the deciding artifact (rows.tsv).
#
# The ticker is the real one (`mini clock --action tick`) run from the clock
# subject's own workspace ($JOURNEY_WORLD/clock, `mini clock --action init`)
# under its genesis C_tick; the law is an ordinary resource law over
# `clock/now`, judged by the Host.
#
# Rows 1-9 are K-CLOCK's, with the clock subject ticking: the genesis clock is 0;
# a resource whose law is `any [not (verb 2), leSlotsOff field/5/after clock/now 0]`
# is created; writing 100 before any tick is refused by the law at admission; the
# clock subject ticks 100 and the view reads now=100; the byte-identical write is
# admitted; ticks at 50 and 100 are refused clockNotAdvancing; the newcomer
# presenting the clock subject's C_tick is refused capabilityRejected.
# CLOCK-SUBJECT rows: the sponsor is refused with C_tick and with its factory
# control capability (no tick authority); the clock subject's key is refused a
# birth (the factory law confines it); a signed READ under a positive clock law
# (`any [verb = 2, leSlotsOff field/1/after clock/now 0]`) is refused before
# the tick and admitted after it, naming the clock it was judged at; the
# observer (a second ticker, subject 31; 30 is the pay observer) ticks with a chain slot; the wall-clock
# tick; a tick whose reply is lost resolves as `replayed` on the next run; 200
# ephemeral ticks leave no attempt dir and 200 journal lines; 20 ephemeral reads
# leave no attempt dir and 20 journal lines.
# K-ORDER-WIDE rows (after the wall-clock tick, so clock/now is real unix time,
# about 1.79e9): 20 signed reads of the same positive clock law answered; a write
# at or below the clock admitted and one ahead of it refused naming the clock
# clause; a write of 2^126 (outside R = [-2^123, 2^123)) refused as
# law-input-range naming the clause and both values; 2^126 under the open law refused as
# law-input-range naming the two integers whose field images collide (its pair delta
# 2^127 reads as 1); 2^125 + 2^40 read under the clock law refused naming the clause; a
# fresh MUD sheet (law.management ; law.sheet, every timestamp field 0) takes an
# owner strike, the referee (the newcomer) charges its balance to now + 100, the
# next strike is refused by clause 10 (bal <= now) and admitted once the clock
# passes the balance.
set -uo pipefail
umask 077
for name in MINI SPONSOR_WS NEWCOMER_WS JOURNEY_WORLD JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jclock: $name is required" >&2; exit 2; fi
done
D=$JOURNEY_STEP_DIR/jclock
[ ! -e "$D" ] || { echo "jclock: refusing to reuse $D" >&2; exit 2; }
mkdir -p "$D"
ROWS=$D/rows.tsv
printf 'verdict\tstep\texpected\tobserved\n' >"$ROWS"
PASS=0 TOTAL=0
CONTROL=$(jq -r .factoryControllerCapability "$JOURNEY_WORLD/genesis.json")
CLOCK_WS=$JOURNEY_WORLD/clock
OBSERVER_WS=$JOURNEY_WORLD/observer
C_TICK=$(jq -r '.clockTickers[0].capability' "$JOURNEY_WORLD/genesis.json")
CLOCK_SUBJECT=$(jq -r '.clockTickers[0].subject' "$JOURNEY_WORLD/genesis.json")
for ws in "$CLOCK_WS" "$OBSERVER_WS"; do
  [ -f "$ws/workspace.json" ] || { echo "jclock: missing clock workspace $ws" >&2; exit 2; }
done

run() {  # run NAME CMD... : stdout/stderr/rc retained under $D
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
rc() { cat "$D/$1.rc"; }
row() {  # row NAME EXPECTED OBSERVED OK(0/1)
  TOTAL=$((TOTAL + 1))
  local v=FAIL; [ "$4" = 0 ] && { v=PASS; PASS=$((PASS + 1)); }
  printf '%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$3" >>"$ROWS"
  printf '%s\t%s\t%s\n' "$v" "$1" "$3" >&2
}
# reason NAME: the Host's refusal detail of a clock outcome, decoded from hex.
reason() { jq -r '.detail // empty' "$D/$1.out" 2>/dev/null | xxd -r -p 2>/dev/null | sed 's/.*Reject\.//'; }
# refusal NAME: the attempt's retained Host outcome as "phase: detail" (hex-decoded), or,
# when the Host refused before submission (a law refusal at prepare names its clause),
# "stage: <the Host's refusal line>" from the retained pre-submit refusal.
refusal() {
  local a=$SPONSOR_WS/attempts/clock-$1
  if [ -f "$a/outcome.json" ]; then
    printf '%s: %s' "$(jq -r '.phase // empty' "$a/outcome.json" | xxd -r -p)" "$(jq -r '.detail // empty' "$a/outcome.json" | xxd -r -p)"
  elif [ -f "$a/pre-submit-refusal.json" ]; then
    printf '%s: %s' "$(jq -r '.stage // empty' "$a/pre-submit-refusal.json")" "$(grep -m1 '^refused:' "$D/$1-submit.err" 2>/dev/null)"
  fi
}
view() { run "$1" "$MINI" clock --action view --workspace "$CLOCK_WS"; }
attempt_dirs() { find "$1/clock-attempts" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | wc -l; }
journal_lines() { cat "$1"/clock-journal.tsv.1 "$1"/clock-journal.tsv 2>/dev/null | wc -l; }
now_of() { jq -r .now "$D/$1.out" 2>/dev/null; }
tick() {  # tick NAME WS [--capability C] [--now N] [--slot S] : a clock workspace uses its own C_tick
  local name=$1 ws=$2; shift 2
  run "$name" "$MINI" clock --action tick --workspace "$ws" "$@"
}
REQ=$D/requests; mkdir -p "$REQ"
# A timestamp field: a mutate may not write field 5 ahead of the clock
# (field/5/after <= clock/now + 0), in the shape every MUD sheet clause has:
# `any [not (verb = 2), positive slot-to-slot atom]`. Signed reads now see the clock
# (CLOCK-SUBJECT, `read_law_sees_clock`), but the guard is still load-bearing here: a
# read before field 5 exists has no `resource/field/5/after`, so the unguarded atom
# would fail closed on the owner's own reads.
printf '%s\n' '{"type":"any","predicates":[{"type":"not","predicate":{"type":"eq","slot":"request/verb","value":"2"}},{"type":"leSlotsOff","left":"resource/field/5/after","right":"clock/now","offset":"0"}]}' >"$REQ/stamp-le-now.json"
write_req() {  # write_req VALUE : create field 5 of `timed`
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"timed","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"5"},"value":"%s"}]}}]}\n' "$1"
}
attempt_write() {  # attempt_write ID VALUE -> rc 0 iff admitted and installed
  write_req "$2" >"$REQ/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$REQ/$1.json" --proposal-id "clock-$1" || true
  [ "$(rc "$1-propose")" = 0 ] || return 1
  run "$1-submit" "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
    --intent "$SPONSOR_WS/proposals/clock-$1/intent.json" --attempt "$SPONSOR_WS/attempts/clock-$1"
  [ "$(rc "$1-submit")" = 0 ] && jq -e '.type == "confirmed"' "$SPONSOR_WS/attempts/clock-$1/outcome.json" >/dev/null 2>&1
}
started=$(date +%s)

view v0
row "genesis clock" "now 0 slot 0" "rc=$(rc v0) now=$(now_of v0) slot=$(jq -r .slot "$D/v0.out" 2>/dev/null)" \
  "$([ "$(rc v0)" = 0 ] && [ "$(now_of v0)" = 0 ] && [ "$(jq -r .slot "$D/v0.out")" = 0 ]; echo $?)"

run create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name timed --storage declared --predicate "$REQ/stamp-le-now.json" --fields 5
row "create resource under law any[not verb 2, leSlotsOff field/5/after clock/now 0]" "created" "rc=$(rc create)" "$([ "$(rc create)" = 0 ]; echo $?)"

attempt_write w-early 100; r=$?; why=$(refusal w-early)
row "create field 5 = 100 at clock 0" "refused at prepare by the law, naming the clock clause (row 5 is the byte-identical create after the tick)" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) outcome=[$why]" \
  "$([ $r != 0 ] && [[ "$why" == 'prepare: refused: law-denied: '*'clock/now'* ]]; echo $?)"

tick t100 "$CLOCK_WS" --now 100
view v1
row "clock subject ticks now=100" "confirmed; view now=100 day=0" "rc=$(rc t100) $(jq -r .type "$D/t100.out" 2>/dev/null) now=$(now_of v1) day=$(jq -r .day "$D/v1.out" 2>/dev/null)" \
  "$([ "$(rc t100)" = 0 ] && [ "$(now_of v1)" = 100 ] && [ "$(jq -r .day "$D/v1.out")" = 0 ]; echo $?)"

attempt_write w-after 100; r=$?
row "same create at clock 100" "admitted (confirmed)" "admitted=$([ $r = 0 ] && echo yes || echo no) $(refusal w-after | cut -c1-120)" "$([ $r = 0 ]; echo $?)"

tick t50 "$CLOCK_WS" --now 50
row "tick behind: now=50" "refused clockNotAdvancing" "rc=$(rc t50) $(reason t50)" \
  "$([ "$(rc t50)" != 0 ] && [ "$(reason t50)" = clockNotAdvancing ]; echo $?)"
tick t100b "$CLOCK_WS" --now 100
row "tick at the current time: now=100" "refused clockNotAdvancing" "rc=$(rc t100b) $(reason t100b)" \
  "$([ "$(rc t100b)" != 0 ] && [ "$(reason t100b)" = clockNotAdvancing ]; echo $?)"

tick tnew "$NEWCOMER_WS" --capability "$C_TICK" --now 150
row "newcomer presents the clock subject's C_tick, now=150" "refused capabilityRejected" "rc=$(rc tnew) $(reason tnew)" \
  "$([ "$(rc tnew)" != 0 ] && [ "$(reason tnew)" = capabilityRejected ]; echo $?)"

view v2
row "clock after refusals" "now=100" "now=$(now_of v2)" "$([ "$(now_of v2)" = 100 ]; echo $?)"

# --- CLOCK-SUBJECT -------------------------------------------------------------
tick tsp "$SPONSOR_WS" --capability "$C_TICK" --now 150
row "sponsor presents C_tick (not its own), now=150" "refused capabilityRejected" "rc=$(rc tsp) $(reason tsp)" \
  "$([ "$(rc tsp)" != 0 ] && [ "$(reason tsp)" = capabilityRejected ]; echo $?)"
tick tspc "$SPONSOR_WS" --capability "$CONTROL" --now 150
row "sponsor presents its factory control capability (K-CLOCK's route), now=150" "refused capabilityRejected" \
  "rc=$(rc tspc) $(reason tspc)" "$([ "$(rc tspc)" != 0 ] && [ "$(reason tspc)" = capabilityRejected ]; echo $?)"

# The clock subject's key, in a participant workspace of its own, asks for a birth.
CPW=$D/clock-participant; mkdir -p -m 700 "$D/clock-ns"
run cinit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --key "$JOURNEY_WORLD/clock.key" --subject "$CLOCK_SUBJECT" \
  --birth-context "$JOURNEY_WORLD/clock-birth-context.json" --namespace-root "$D/clock-ns" --dir "$CPW"
printf '%s\n' '{"type":"all","predicates":[]}' >"$REQ/permit.json"
run cbirth "$MINI" workspace --action create --dir "$CPW" --name squat --storage declared --predicate "$REQ/permit.json"
cwhy=$(cat "$D/cbirth.err" "$D/cbirth.out" 2>/dev/null | grep -m1 -o 'law-denied: .*' | cut -c1-140)
row "clock subject asks the factory for a birth" "refused by the factory law (tickers are confined)" \
  "init rc=$(rc cinit) birth rc=$(rc cbirth) [$cwhy]" \
  "$([ "$(rc cinit)" = 0 ] && [ "$(rc cbirth)" != 0 ] && [ -n "$cwhy" ]; echo $?)"

# A signed read under a positive clock law: reads open at the time in field 1.
printf '%s\n' '{"type":"any","predicates":[{"type":"eq","slot":"request/verb","value":"2"},{"type":"leSlotsOff","left":"resource/field/1/after","right":"clock/now","offset":"0"}]}' >"$REQ/opens-at.json"
run ocreate "$MINI" workspace --action create --dir "$SPONSOR_WS" --name opens --storage declared --predicate "$REQ/opens-at.json"
# Field 1 exists from birth (at 0); the stamp is a guarded write 0 -> 200.
printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"opens","payload":{"type":"scalar","actions":[{"type":"write","key":{"type":"object","field":"1"},"expected":"0","value":"200"}]}}]}\n' >"$REQ/o-stamp.json"
run o-stamp-propose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$REQ/o-stamp.json" --proposal-id clock-o-stamp
run o-stamp-submit "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
  --intent "$SPONSOR_WS/proposals/clock-o-stamp/intent.json" --attempt "$SPONSOR_WS/attempts/clock-o-stamp"
run rbefore "$MINI" workspace --action read --dir "$SPONSOR_WS" --name opens --ephemeral true
rwhy=$(grep -m1 '^refused: law-denied' "$D/rbefore.err" 2>/dev/null | cut -c1-140)
row "owner's signed read at clock 100 of a resource opening at 200" "refused law-denied on the clock clause" \
  "create rc=$(rc ocreate) stamp rc=$(rc o-stamp-submit) read rc=$(rc rbefore) [$rwhy]" \
  "$([ "$(rc ocreate)" = 0 ] && [ "$(rc o-stamp-submit)" = 0 ] && [ "$(rc rbefore)" != 0 ] && [[ "$rwhy" == *clock/now* ]]; echo $?)"
tick t200 "$CLOCK_WS" --now 200
run rafter "$MINI" workspace --action read --dir "$SPONSOR_WS" --name opens --ephemeral true
judged=$(jq -r '.judgedAt.clock.now // empty' "$D/rafter.out" 2>/dev/null)
row "the same read after the clock subject ticks 200" "answered; judgedAt.clock.now = 200" \
  "tick rc=$(rc t200) read rc=$(rc rafter) judgedAt.now=$judged height=$(jq -r '.judgedAt.height // empty' "$D/rafter.out" 2>/dev/null)" \
  "$([ "$(rc t200)" = 0 ] && [ "$(rc rafter)" = 0 ] && [ "$judged" = 200 ]; echo $?)"

# These 20 reads run at clock 200; the K-ORDER-WIDE rows below repeat them at real
# unix time (the native order width was 29 until K-ORDER-WIDE: r1 of CLOCK-SUBJECT).
before=$(find "$SPONSOR_WS/attempts" -mindepth 1 -maxdepth 1 | wc -l)
srcs=$(find "$SPONSOR_WS/sources" -mindepth 1 -maxdepth 1 | wc -l)
rl0=$(cat "$SPONSOR_WS"/read-journal.tsv 2>/dev/null | wc -l); rfail=0
for i in $(seq 1 20); do
  "$MINI" workspace --action read --dir "$SPONSOR_WS" --name opens --ephemeral true >"$D/r20.out" 2>"$D/r20.err" || rfail=$((rfail + 1))
done
after=$(find "$SPONSOR_WS/attempts" -mindepth 1 -maxdepth 1 | wc -l)
srcs1=$(find "$SPONSOR_WS/sources" -mindepth 1 -maxdepth 1 | wc -l)
rl=$(( $(cat "$SPONSOR_WS"/read-journal.tsv | wc -l) - rl0 ))
row "20 ephemeral signed reads" "20 answered; no new attempt dir or source; 20 read-journal lines" \
  "failed=$rfail attempts $before->$after sources $srcs->$srcs1 journal=+$rl" \
  "$([ $rfail = 0 ] && [ "$before" = "$after" ] && [ "$srcs" = "$srcs1" ] && [ $rl = 20 ]; echo $?)"

tick tobs "$OBSERVER_WS" --now 300 --slot 7
view v4
row "observer (second ticker) ticks chain time now=300 slot=7" "confirmed; view now=300 slot=7" \
  "rc=$(rc tobs) $(jq -r .type "$D/tobs.out" 2>/dev/null) now=$(now_of v4) slot=$(jq -r .slot "$D/v4.out" 2>/dev/null)" \
  "$([ "$(rc tobs)" = 0 ] && [ "$(now_of v4)" = 300 ] && [ "$(jq -r .slot "$D/v4.out")" = 7 ]; echo $?)"

wall=$(date +%s)
tick twall "$CLOCK_WS"
view v3
asserted=$(jq -r .asserted.now "$D/twall.out" 2>/dev/null)
row "wall-clock tick by the clock subject (the v1 ticker)" "confirmed; view now = asserted ≈ date +%s; slot carried 7" \
  "rc=$(rc twall) asserted=$asserted view=$(now_of v3) wall=$wall slot=$(jq -r .slot "$D/v3.out" 2>/dev/null)" \
  "$([ "$(rc twall)" = 0 ] && [ "$(now_of v3)" = "$asserted" ] && [ "$asserted" -ge "$wall" ] && [ "$asserted" -le $((wall + 60)) ] && [ "$(jq -r .slot "$D/v3.out")" = 7 ]; echo $?)"

base=$((asserted + 1))
tick tlost "$CLOCK_WS" --now "$base" --abandon-after-submit true
held=$(attempt_dirs "$CLOCK_WS")
tick tnext "$CLOCK_WS" --now $((base + 1))
replayed=$(jq -r '.resolvedRetained[0].confirmation // empty' "$D/tnext.out" 2>/dev/null)
view v5
row "a tick whose reply is lost, then the next run" "1 attempt held; next run resolves it replayed, then ticks; 0 attempts left" \
  "abandoned=$(jq -r .type "$D/tlost.out" 2>/dev/null) held=$held retained=$replayed next=$(jq -r .confirmation "$D/tnext.out" 2>/dev/null) now=$(now_of v5) left=$(attempt_dirs "$CLOCK_WS")" \
  "$([ "$(jq -r .type "$D/tlost.out")" = abandoned ] && [ "$held" = 1 ] && [ "$replayed" = replayed ] && [ "$(rc tnext)" = 0 ] && [ "$(now_of v5)" = $((base + 1)) ] && [ "$(attempt_dirs "$CLOCK_WS")" = 0 ]; echo $?)"

lines0=$(journal_lines "$CLOCK_WS"); failed=0; maxheld=0; t0=$(date +%s)
for i in $(seq 1 200); do
  "$MINI" clock --action tick --workspace "$CLOCK_WS" --now $((base + 1 + i)) >"$D/t200x.out" 2>"$D/t200x.err" || failed=$((failed + 1))
  h=$(attempt_dirs "$CLOCK_WS"); [ "$h" -gt "$maxheld" ] && maxheld=$h
done
lines=$(( $(journal_lines "$CLOCK_WS") - lines0 ))
view v6
row "200 ephemeral ticks by the clock subject" "200 confirmed; at most 1 attempt dir at any time, 0 after; 200 journal lines" \
  "failed=$failed maxHeld=$maxheld left=$(attempt_dirs "$CLOCK_WS") journal=+$lines now=$(now_of v6) ($(( $(date +%s) - t0 )) s)" \
  "$([ $failed = 0 ] && [ "$maxheld" -le 1 ] && [ "$(attempt_dirs "$CLOCK_WS")" = 0 ] && [ $lines = 200 ] && [ "$(now_of v6)" = $((base + 201)) ]; echo $?)"

# --- K-ORDER-WIDE: laws over clock/now at real unix time -------------------------------
# turn WS ID REQUEST -> rc 0 iff installed; the Host's refusal line is in $D/ID-submit.err
turn() {
  local ws=$1 id=$2 req=$3
  run "$id-propose" "$MINI" workspace --action propose --dir "$ws" --request "$req" --proposal-id "clock-$id" || true
  [ "$(rc "$id-propose")" = 0 ] || return 1
  run "$id-submit" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/clock-$id/intent.json" --attempt "$ws/attempts/clock-$id"
  [ "$(rc "$id-submit")" = 0 ] && jq -e '.type == "confirmed"' "$ws/attempts/clock-$id/outcome.json" >/dev/null 2>&1
}
refused_line() { cat "$D/$1-submit.err" "$D/$1-propose.err" 2>/dev/null | grep -m1 '^refused:' | cut -c1-400; }
writes() {  # writes NAME FIELD:EXPECTED:VALUE... : one invoke of guarded writes
  local name=$1; shift
  printf '%s\n' "$@" | jq -R 'split(":") | {type:"write",key:{type:"object",field:.[0]},expected:.[1],value:.[2]}' \
    | jq -s --arg n "$name" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$n,payload:{type:"scalar",actions:.}}]}'
}
FAR=85070591730234615865843651857942052864   # 2^126: outside R, and 2^126 - now is past 2^125
view vw
NOW=$(now_of vw)

rl0=$(cat "$SPONSOR_WS"/read-journal.tsv 2>/dev/null | wc -l); rfail=0
for i in $(seq 1 20); do
  "$MINI" workspace --action read --dir "$SPONSOR_WS" --name opens --ephemeral true >"$D/rw20.out" 2>"$D/rw20.err" || rfail=$((rfail + 1))
done
judged=$(jq -r '.judgedAt.clock.now // empty' "$D/rw20.out" 2>/dev/null)
rl=$(( $(cat "$SPONSOR_WS"/read-journal.tsv | wc -l) - rl0 ))
row "20 signed reads at real unix time (field 1 = 200, law any[verb 2, field 1 <= clock/now])" \
  "20 answered, judged at the wall clock" "failed=$rfail journal=+$rl judgedAt.now=$judged view.now=$NOW [$(head -c 160 "$D/rw20.err")]" \
  "$([ $rfail = 0 ] && [ $rl = 20 ] && [ "$judged" = "$NOW" ] && [ "$NOW" -ge "$wall" ]; echo $?)"

writes timed 5:100:200 >"$REQ/w-unix.json"
turn "$SPONSOR_WS" w-unix "$REQ/w-unix.json"; r=$?
row "write field 5 := 200 at clock $NOW (law field 5 <= clock/now)" "admitted (confirmed)" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) [$(refused_line w-unix)]" "$([ $r = 0 ]; echo $?)"

writes timed 5:200:$((NOW + 1000000)) >"$REQ/w-ahead.json"
turn "$SPONSOR_WS" w-ahead "$REQ/w-ahead.json"; r=$?; why=$(refused_line w-ahead)
row "write field 5 := now + 10^6" "refused law-denied on the clock clause (eval refuses; not an input-range refusal)" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) [$why]" \
  "$([ $r != 0 ] && [[ "$why" == 'refused: law-denied: '*'clock/now'* ]]; echo $?)"

writes timed 5:200:$FAR >"$REQ/w-far.json"
turn "$SPONSOR_WS" w-far "$REQ/w-far.json"; r=$?; why=$(refused_line w-far)
row "write field 5 := 2^126 (outside R)" "refused law-input-range naming the clause and both values" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) [$why]" \
  "$([ $r != 0 ] && [[ "$why" == 'refused: law-input-range: '*'field 5 <= slot "clock/now" + 0'*"left $FAR"*"right $NOW"* ]]; echo $?)"

# Under the open law, 2^126 in field 1 makes the pair delta 2 * 2^126 = 2^127, whose image in
# ZMod (2^127 - 1) is that of 1: the cast check refuses, and prepare names the two integers.
run fcreate "$MINI" workspace --action create --dir "$SPONSOR_WS" --name far --storage declared --predicate "$REQ/permit.json"
P127=170141183460469231731687303715884105728
writes far 1:0:$FAR >"$REQ/far-alias.json"
turn "$SPONSOR_WS" far-alias "$REQ/far-alias.json"; r=$?; why=$(refused_line far-alias)
row "write field 1 := 2^126 under the open law (pair delta 2^127, image of 1)" "refused law-input-range naming the two integers" \
  "create rc=$(rc fcreate) admitted=$([ $r = 0 ] && echo yes || echo no) [$why]" \
  "$([ "$(rc fcreate)" = 0 ] && [ $r != 0 ] && [[ "$why" == 'refused: law-input-range: values '*"$P127"*'same image in the native field'* ]]; echo $?)"
# The read side: 2^125 + 2^40 (past the order width from now, still its own field image) written
# under the open law, then the clock law installed.
FARR=42535295865117307932921827028482654208
writes far 1:0:$FARR >"$REQ/far-stamp.json"
turn "$SPONSOR_WS" far-stamp "$REQ/far-stamp.json"; fs=$?
jq -n --slurpfile p "$REQ/opens-at.json" '{type:"minidregg-workspace-proposal-v1",action:"install-policy",name:"far",predicate:$p[0]}' >"$REQ/far-law.json"
turn "$SPONSOR_WS" far-law "$REQ/far-law.json"; fl=$?
run rfar "$MINI" workspace --action read --dir "$SPONSOR_WS" --name far --ephemeral true
why=$(grep -m1 '^refused:' "$D/rfar.err" 2>/dev/null | cut -c1-400)
row "signed read of field 1 = 2^125 + 2^40 under any[verb 2, field 1 <= clock/now]" "refused law-input-range naming the clause and both values" \
  "stamp=$fs law=$fl read rc=$(rc rfar) [$why]" \
  "$([ $fs = 0 ] && [ $fl = 0 ] && [ "$(rc rfar)" != 0 ] && [[ "$why" == 'refused: law-input-range: '*'clock/now'*"left $FARR"*"right $NOW"* ]]; echo $?)"

# A MUD sheet (deploy/shell/templates/mud/sheet): the sponsor is the sheet's subject {S} and the
# founder; the newcomer is the referee {REF}. Every timestamp field (bal 3, eq 4, respawn 9) starts at 0.
MUD=$(CDPATH='' cd -- "$(dirname -- "$0")/../../../deploy/shell/templates/mud" && pwd)
S=$(jq -r .subject "$SPONSOR_WS/workspace.json"); REF=$(jq -r .subject "$NEWCOMER_WS/workspace.json")
SHEET=tidewrack-sheet-$S
subst() {
  sed -e "s/{S}/$S/g" -e "s/{REF}/$REF/g" -e "s/{W_FOUNDER}/$S/g" -e "s/{REALM}/tidewrack/g" -e "s/{HOME}/$(jq -r .shrine "$MUD/tidewrack/realm.json")/g" \
    $(jq -r '.constants | to_entries[] | select(.key != "derivation") | "-e s/{\(.key)}/\(.value)/g"' "$MUD/tidewrack/realm.json")
}
subst <"$MUD/law.management.json" >"$REQ/sheet-mgmt.json"
jq -n --slurpfile m "$MUD/law.management.json" --slurpfile s "$MUD/sheet/law.sheet.json" \
  '{type:"all",predicates:([$m[0]] + $s[0].predicates)}' | subst >"$REQ/sheet-law.json"
# init.sheet.json creates all 15 fields; field 1 exists from birth, so it is a guarded write 0 -> HOME.
subst <"$MUD/sheet/init.sheet.json" | jq '.targets[0].payload.actions |= map(if .key.field == "1" then {type:"write",key,expected:"0",value} else . end)' >"$REQ/sheet-init.json"
run screate "$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$SHEET" --storage declared --predicate "$REQ/sheet-mgmt.json"
turn "$SPONSOR_WS" sheet-init "$REQ/sheet-init.json"; si=$?
jq -n --arg r "$REF" --arg n "$SHEET" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$REQ/sheet-grant.json"
turn "$SPONSOR_WS" sheet-grant "$REQ/sheet-grant.json"; sg=$?
run sheet-publish "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id clock-sheet-grant --attempt "$SPONSOR_WS/attempts/clock-sheet-grant"
run sheet-import "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name "$SHEET" --from-ref "$SPONSOR_WS/proposals/clock-sheet-grant/recipient-reference.json"
jq -n --slurpfile p "$REQ/sheet-law.json" --arg n "$SHEET" '{type:"minidregg-workspace-proposal-v1",action:"install-policy",name:$n,predicate:$p[0]}' >"$REQ/sheet-install.json"
turn "$SPONSOR_WS" sheet-install "$REQ/sheet-install.json"; sl=$?
row "MUD sheet birth: create under law.management, init 15 fields, grant the referee, install law.management ; law.sheet" "every step confirmed" \
  "create rc=$(rc screate) init=$si grant=$sg publish rc=$(rc sheet-publish) import rc=$(rc sheet-import) law=$sl [$(refused_line sheet-init)$(refused_line sheet-install)]" \
  "$([ "$(rc screate)" = 0 ] && [ $si = 0 ] && [ $sg = 0 ] && [ "$(rc sheet-publish)" = 0 ] && [ "$(rc sheet-import)" = 0 ] && [ $sl = 0 ]; echo $?)"

view vs; NOW=$(now_of vs)
writes "$SHEET" 7:0:1 8:0:$S >"$REQ/strike1.json"
turn "$SPONSOR_WS" strike1 "$REQ/strike1.json"; r=$?
row "fresh sheet (bal 0, eq 0, respawn 0): the owner's strike at clock $NOW" "admitted (clause 10: bal 0 <= now; every clock clause decided)" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) [$(refused_line strike1)]" "$([ $r = 0 ]; echo $?)"

BAL=$((NOW + 100))
writes "$SHEET" 3:0:$BAL 7:1:0 8:$S:0 >"$REQ/pay1.json"
turn "$NEWCOMER_WS" pay1 "$REQ/pay1.json"; r=$?
row "the referee charges the strike: bal := now + 100, intent cleared" "admitted (clause 28: now <= bal - COST; clause 30)" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) [$(refused_line pay1)]" "$([ $r = 0 ]; echo $?)"

writes "$SHEET" 7:0:1 8:0:$S >"$REQ/strike2.json"
turn "$SPONSOR_WS" strike2 "$REQ/strike2.json"; r=$?; why=$(refused_line strike2)
row "the owner strikes again inside the cooldown (bal = now + 100)" "refused law-denied by clause 10 (field 3 before <= clock/now)" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) [$why]" \
  "$([ $r != 0 ] && [[ "$why" == 'refused: law-denied: '*'field 3 before <= slot "clock/now"'* ]]; echo $?)"

tick tbal "$CLOCK_WS" --now $((BAL + 1))
writes "$SHEET" 7:0:1 8:0:$S >"$REQ/strike3.json"
turn "$SPONSOR_WS" strike3 "$REQ/strike3.json"; r=$?
row "the clock subject ticks past the balance; the owner strikes" "tick confirmed; strike admitted" \
  "tick rc=$(rc tbal) admitted=$([ $r = 0 ] && echo yes || echo no) [$(refused_line strike3)]" \
  "$([ "$(rc tbal)" = 0 ] && [ $r = 0 ]; echo $?)"

verdict="K-CLOCK $([ $PASS = $TOTAL ] && echo PASS || echo FAIL) $PASS/$TOTAL ($(( $(date +%s) - started )) s)"
echo "$verdict"
echo "$verdict" >&2
echo "$ROWS"
[ $PASS = $TOTAL ]
