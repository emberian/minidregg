#!/usr/bin/env bash
# journey.d/jclosure.sh — K-FIELD-CLOSURE: a declared cell holds only the fields it declares.
#
# A law is a Pred over named slots, so no law can say "no field other than these". The kernel
# says it: a declared cell is born with its declaration (`--fields 2,3`, or `--fields open`), and
# the Host refuses a write that changes any other field BY NAME (`undeclaredField N`), at
# preparation, before the law runs. A cell created without `--fields` declares none.
#
#   board     a board of fields 2,3 under the open law; A fills it and SEALS it (a law freezing
#             fields 2 and 3 on every write), then delegates observe+mutate to B.
#             A moves field 2 -> refused by the seal (law-denied); B creates field 20 -> refused
#             undeclaredField 20 (the seal alone would admit it: it names no field 20).
#   plain     fields {2}: field 2 created; field 3 refused undeclaredField 3.
#   default   no --fields: field 2 refused undeclaredField 2 (default-closed).
#   open      --fields open: field 20 created and read back (the open-kind pole).
# Ran with the hook contract (journey.sh header): MINI, SPONSOR_WS, NEWCOMER_WS, SPONSOR_SUBJECT,
# NEWCOMER_SUBJECT, JOURNEY_STEP_DIR exported. Exit 0 = every row matched; last stdout line = rows.tsv.
set -uo pipefail
umask 077
for name in MINI SPONSOR_WS NEWCOMER_WS NEWCOMER_SUBJECT JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jclosure: $name is required" >&2; exit 2; fi
done
D=$JOURNEY_STEP_DIR/jclosure
[ ! -e "$D" ] || { echo "jclosure: refusing to reuse $D" >&2; exit 2; }
mkdir -p "$D/req"
ROWS=$D/rows.tsv
printf 'verdict\tcell\trow\texpected\tobserved\n' >"$ROWS"
PASS=0 TOTAL=0
WS_A=$SPONSOR_WS WS_B=$NEWCOMER_WS B=$NEWCOMER_SUBJECT

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
row() {  # row CELL NAME EXPECTED OBSERVED OK(0/1)
  TOTAL=$((TOTAL + 1))
  local v=FAIL; [ "$5" = 0 ] && { v=PASS; PASS=$((PASS + 1)); }
  printf '%s\t%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$3" "$4" >>"$ROWS"
  printf '%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$4" >&2
}
refusal() {
  local a=$1/attempts/jcl-$2
  if [ -f "$a/outcome.json" ] && jq -e '.type == "refused"' "$a/outcome.json" >/dev/null 2>&1; then
    printf '%s: %s' "$(jq -r '.phase // empty' "$a/outcome.json" | xxd -r -p)" "$(jq -r '.detail // empty' "$a/outcome.json" | xxd -r -p)"
  elif [ -s "$D/$2-submit.err" ]; then
    tail -1 "$D/$2-submit.err"
  else
    printf 'propose: %s' "$(grep -m1 '^refused:' "$D/$2-propose.err" 2>/dev/null || tail -1 "$D/$2-propose.err" 2>/dev/null)"
  fi
}
c() { printf '{"type":"create","key":{"type":"object","field":"%s"},"value":"%s"}' "$1" "$2"; }
u() { printf '{"type":"write","key":{"type":"object","field":"%s"},"expected":"%s","value":"%s"}' "$1" "$2" "$3"; }
attempt() {  # attempt WS ID NAME ACTION... -> 0 iff admitted
  local ws=$1 id=$2 name=$3; shift 3
  local acts; acts=$(IFS=,; echo "$*")
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"%s","payload":{"type":"scalar","actions":[%s]}}]}\n' \
    "$name" "$acts" >"$D/req/$id.json"
  run "$id-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$id.json" --proposal-id "jcl-$id"
  [ "$(cat "$D/$id-propose.rc")" = 0 ] || return 1
  run "$id-submit" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/jcl-$id/intent.json" --attempt "$ws/attempts/jcl-$id"
  [ "$(cat "$D/$id-submit.rc")" = 0 ] && jq -e '.type == "confirmed"' "$ws/attempts/jcl-$id/outcome.json" >/dev/null 2>&1
}
admit() {  # admit CELL ID LABEL WS NAME ACTION...
  local cell=$1 id=$2 label=$3 ws=$4; shift 4
  attempt "$ws" "$id" "$@"; local r=$?
  row "$cell" "$label" admitted "$([ $r = 0 ] && echo admitted || echo "refused [$(refusal "$ws" "$id" | cut -c1-200)]")" "$r"
}
undeclared() {  # undeclared CELL ID LABEL FIELD WS NAME ACTION...
  local cell=$1 id=$2 label=$3 f=$4 ws=$5; shift 5
  attempt "$ws" "$id" "$@"; local r=$? why; why=$(refusal "$ws" "$id")
  row "$cell" "$label" "refused: undeclaredField $f" "$([ $r = 0 ] && echo admitted || echo "[$(printf '%s' "$why" | cut -c1-240)]")" \
    "$([ $r != 0 ] && [[ "$why" == *"undeclaredField $f"* ]] && [[ "$why" != *law-denied* ]]; echo $?)"
}
create() {  # create NAME LAW [FIELDS]
  local extra=(); [ -n "${3:-}" ] && extra=(--fields "$3")
  run "create-$1" "$MINI" workspace --action create --dir "$WS_A" --name "$1" --storage declared --predicate "$2" "${extra[@]}"
  row "$1" "A creates $1 (fields: ${3:-none declared})" created "rc=$(cat "$D/create-$1.rc") $(tail -1 "$D/create-$1.err" | cut -c1-160)" \
    "$(cat "$D/create-$1.rc")"
}
field_of() {  # field_of WS NAME FIELD -> value or absent
  run "read-$2-$3" "$MINI" workspace --action read --dir "$1" --name "$2"
  jq -r --arg f "$3" '[.cell.entries[]? | select(.key.field == $f) | .value][0] // "absent"' "$D/read-$2-$3.out"
}
started=$(date +%s)

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/open-law.json"
# The seal: every write leaves fields 2 and 3 as they are (a present delta of 0). Nothing in it
# names field 20, and no Pred atom can.
cat >"$D/req/seal-law.json" <<'EOF'
{"type":"any","predicates":[
  {"type":"not","predicate":{"type":"eq","slot":"request/verb","value":"2"}},
  {"type":"all","predicates":[
    {"type":"eq","slot":"resource/field/2/delta","value":"0"},
    {"type":"eq","slot":"resource/field/3/delta","value":"0"}]}]}
EOF

# ---- the sealed board
create kcl-board "$D/req/open-law.json" 2,3
admit board fill "A fills the board: field 2 = 1, field 3 = 7" "$WS_A" kcl-board "$(c 2 1)" "$(c 3 7)"
jq -n '{type:"minidregg-workspace-proposal-v1",action:"install-policy",name:"kcl-board",predicate:input}' \
  "$D/req/seal-law.json" >"$D/req/seal.json"
run seal-propose "$MINI" workspace --action propose --dir "$WS_A" --request "$D/req/seal.json" --proposal-id jcl-seal
run seal-submit "$MINI" workspace --action submit --dir "$WS_A" --intent "$WS_A/proposals/jcl-seal/intent.json" \
  --attempt "$WS_A/attempts/jcl-seal"
row board "A seals the board (install: every write leaves fields 2 and 3 as they are)" installed \
  "$(jq -r '.type + " " + (.confirmation // "")' "$WS_A/attempts/jcl-seal/outcome.json" 2>/dev/null)" \
  "$(jq -e '.type == "confirmed"' "$WS_A/attempts/jcl-seal/outcome.json" >/dev/null 2>&1; echo $?)"
jq -n --arg r "$B" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"kcl-board",
  recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/grant.json"
run grant-propose "$MINI" workspace --action propose --dir "$WS_A" --request "$D/req/grant.json" --proposal-id jcl-grant
run grant-submit "$MINI" workspace --action submit --dir "$WS_A" --intent "$WS_A/proposals/jcl-grant/intent.json" \
  --attempt "$WS_A/attempts/jcl-grant"
run grant-publish "$MINI" workspace --action publish-delegation --dir "$WS_A" --proposal-id jcl-grant \
  --attempt "$WS_A/attempts/jcl-grant"
run import "$MINI" workspace --action import --dir "$WS_B" --name kcl-board \
  --from-ref "$WS_A/proposals/jcl-grant/recipient-reference.json"
row board "A delegates observe+mutate on the sealed board to B; B imports" imported "import rc=$(cat "$D/import.rc")" \
  "$(cat "$D/import.rc")"
attempt "$WS_A" move "kcl-board" "$(u 2 1 2)"; r=$?; why=$(refusal "$WS_A" move)
row board "A moves field 2 (1 -> 2) on the sealed board" "refused: law-denied (the seal)" "$([ $r = 0 ] && echo admitted || echo "[$(printf '%s' "$why" | cut -c1-200)]")" \
  "$([ $r != 0 ] && [[ "$why" == *law-denied* ]]; echo $?)"
undeclared board covert "B creates field 20 on the sealed board (a covert field; the seal names no field 20)" 20 "$WS_B" kcl-board "$(c 20 1)"
undeclared board covert-a "A, the owner, creates field 20 on the sealed board" 20 "$WS_A" kcl-board "$(c 20 1)"
got=$(field_of "$WS_A" kcl-board 20)
row board "read: field 20 absent on the board" absent "$got" "$([ "$got" = absent ]; echo $?)"

# ---- a plain declared cell
create kcl-plain "$D/req/open-law.json" 2
admit plain p2 "A creates field 2 (declared)" "$WS_A" kcl-plain "$(c 2 5)"
undeclared plain p3 "A creates field 3 (undeclared) under the open law" 3 "$WS_A" kcl-plain "$(c 3 5)"
undeclared plain p23 "A writes field 2 and creates field 3 in one turn: refused whole" 3 "$WS_A" kcl-plain "$(u 2 5 6)" "$(c 3 5)"
got=$(field_of "$WS_A" kcl-plain 2)
row plain "read: field 2 still 5 (the refused turn changed nothing)" 5 "$got" "$([ "$got" = 5 ]; echo $?)"

# ---- default: no --fields declares none
create kcl-default "$D/req/open-law.json"
undeclared default d2 "A creates field 2 on a cell that declared no field" 2 "$WS_A" kcl-default "$(c 2 1)"

# ---- the open-kind pole
create kcl-open "$D/req/open-law.json" open
admit open o20 "A creates field 20 on an open cell" "$WS_A" kcl-open "$(c 20 1)"
got=$(field_of "$WS_A" kcl-open 20)
row open "read: field 20 = 1" 1 "$got" "$([ "$got" = 1 ]; echo $?)"

verdict="K-FIELD-CLOSURE $([ $PASS = $TOTAL ] && echo PASS || echo FAIL) $PASS/$TOTAL ($(( $(date +%s) - started )) s)"
echo "$verdict"
echo "$verdict" >&2
echo "$ROWS"
[ $PASS = $TOTAL ]
