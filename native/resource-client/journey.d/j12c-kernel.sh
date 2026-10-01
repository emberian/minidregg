#!/usr/bin/env bash
# journey.d/j12c-kernel.sh — the content action annotate (K-CONTENT-ACTIONS),
# on the journey's fresh Store, after J5 (which enrolled the third key).
#
# Parties: A = sponsor (owns `paper` and `notes`); R = the newcomer, a reviewer
# holding observe+mutate on `paper` under paper's law "R writes no body record"
# (the scope form is K-FIELDS' `fields = {annotations}`); B = the third key,
# observe+mutate on `notes` only; C and D = two keys enrolled here: C observes
# `paper` and observe+mutates `notes`; D observes `notes` only.
# The one-atom `quote` rows moved to journey.d/j12t-kernel.sh: `quote` is
# gone, replaced by range transclusion with disclosure at transclusion time.
# Rows:
#   r-annotates-line2         R annotates line 2 at the revision it read    -> installed
#   r-edits-line2             R edits line 2 (law: R writes no body)        -> refused
#   r-edit-left-paper         paper's root after R's refused edit           -> unchanged
#   a-edits-line2             A edits line 2                                -> installed
#   r-annotation-reads-stale  R's annotation, read after A's edit           -> fresh=false
#   r-annotates-stale         R annotates at the old revision               -> refused (staleAtom)
#   d-reads-paper             D reads paper                                 -> refused
#   a-edits-line2-again       A edits line 2 again                          -> installed
#   notes-root-agrees         C and A read the same notes root             -> equal
#   audit                     Host audit re-admits every accepted record   -> re-admitted
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS NEWCOMER_WS
# NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Exit 0 = every row as
# expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
TW=$W/third-workspace
mkdir -p "$D/req"
rows=$D/content-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

run() { # NAME cmd...
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
host_refused() {
  [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG\|host refused\|host returned refused" "$D/$1.err"
}
retained_outcome() { # NAME -> phase/detail of a retained refused outcome, if any
  local dir; dir=$(grep -o 'workspace attempt: .*' "$D/$1.err" | tail -1 | cut -d' ' -f3)
  [ -n "$dir" ] && [ -f "$dir/outcome.json" ] || return 0
  printf 'outcome %s phase %s: %s' "$(jq -r .type "$dir/outcome.json")" \
    "$(jq -r .phase "$dir/outcome.json" | xxd -r -p)" "$(jq -r .detail "$dir/outcome.json" | xxd -r -p)"
}
refusal_text() {
  { retained_outcome "$1"; echo; grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' '; grep -o 'host refused [a-z]*' "$D/$1.err" | tail -1; } | tr '\n' ' ' | cut -c1-200
}
row() { # NAME EXPECT GOT DETAIL
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"
  [ "$2" = "$3" ] || bad=$((bad + 1))
}
outcome() { # NAME -> installed|refused|client-error
  if [ "$(cat "$D/$1.rc")" = 0 ]; then echo installed
  elif host_refused "$1"; then echo refused
  else echo client-error; fi
}
detail() { if [ "$(outcome "$1")" = refused ]; then refusal_text "$1"; else tail -1 "$D/$1.err" | cut -c1-200; fi; }
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -3 "$D/$1.err")" >&2; exit 1; }; }
attempt_of() { grep -o 'workspace read attempt: .*' "$D/$1.err" | tail -1 | cut -d' ' -f4; }
read_view() { # NAME WS RESOURCE
  run "$1" "$MINI" workspace --action read --dir "$2" --name "$3"
}
atom() { # READNAME ATOMID -> the atom's record as JSON
  jq -c --arg a "$2" '.cell.entries[] | select(.type == "atom" and .id == $a)' "$D/$1.out"
}
invoke() { # NAME WS RESOURCE ACTIONS-JSON  (propose + submit)
  local name=$1 ws=$2 res=$3 actions=$4
  jq -n --arg r "$res" --argjson a "$actions" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$r,payload:{type:"content",actions:$a}}]}' \
    >"$D/req/$name.json"
  run "$name-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$name.json" --proposal-id "$name"
  if [ "$(cat "$D/$name-propose.rc")" != 0 ]; then cp "$D/$name-propose.rc" "$D/$name.rc"
    cp "$D/$name-propose.err" "$D/$name.err"; : >"$D/$name.out"; return; fi
  run "$name" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/$name/intent.json" --attempt "$ws/attempts/$name"
}
delegate() { # NAME FROM-WS RESOURCE RECIPIENT-SUBJECT VERBS-JSON TO-WS LOCALNAME
  jq -n --arg n "$3" --arg r "$4" --argjson v "$5" \
    '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,recipient:$r,verbs:$v,maxCost:"50000"}' \
    >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$2" --request "$D/req/$1.json" --proposal-id "$1"; ok "$1-propose"
  run "$1-submit" "$MINI" workspace --action submit --dir "$2" \
    --intent "$2/proposals/$1/intent.json" --attempt "$2/attempts/$1"; ok "$1-submit"
  run "$1-publish" "$MINI" workspace --action publish-delegation --dir "$2" --proposal-id "$1" \
    --attempt "$2/attempts/$1"; ok "$1-publish"
  run "$1-import" "$MINI" workspace --action import --dir "$6" --name "$7" \
    --from-ref "$2/proposals/$1/recipient-reference.json"; ok "$1-import"
}
enroll() { # NAME -> workspace at $W/NAME-workspace; prints subject
  local A=$W/attempts/$1
  run "$1-keygen" "$MINI" keygen --secret "$W/$1.key" --public "$W/$1.pub"; ok "$1-keygen"
  run "$1-plan" "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
    --name "$1-1" --new-key "$W/$1.key" --dir "$A"; ok "$1-plan"
  run "$1-seal" "$MINI" enroll --action seal --dir "$A"; ok "$1-seal"
  run "$1-enroll" "$MINI" enroll --action submit --dir "$A"; ok "$1-enroll"
  run "$1-init" "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --enrollment "$A/enrollment.json" --dir "$W/$1-workspace"; ok "$1-init"
  jq -r .subject "$D/$1-enroll.out"
}
hexof() { printf '%s' "$1" | xxd -p | tr -d '\n'; }

R_SUBJECT=$NEWCOMER_SUBJECT
B_SUBJECT=$(jq -r .subject "$TW/workspace.json" 2>/dev/null || true)
[ -n "$B_SUBJECT" ] && [ "$B_SUBJECT" != null ] || B_SUBJECT=$(jq -r .subject "$JOURNEY_RUN/steps/J5/submit.out")
C_SUBJECT=$(enroll carol); CW=$W/carol-workspace
D_SUBJECT=$(enroll dave); DW=$W/dave-workspace

# paper's law: a mutation by R writes no body record (reads, delegations, installs pass).
jq -n --arg r "$R_SUBJECT" '{type:"any",predicates:[
  {type:"not",predicate:{type:"eq",slot:"request/verb",value:"2"}},
  {type:"not",predicate:{type:"eq",slot:"request/subject",value:$r}},
  {type:"eq",slot:"content/writes/body",value:"0"}]}' >"$D/req/paper-law.json"
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create-paper "$MINI" workspace --action create --dir "$SPONSOR_WS" --name paper --storage content \
  --predicate "$D/req/paper-law.json"; ok create-paper
run create-notes "$MINI" workspace --action create --dir "$SPONSOR_WS" --name notes --storage content \
  --predicate "$D/req/permit-all.json"; ok create-notes
paper=$(jq -r .target "$SPONSOR_WS/refs/paper.json")
notes=$(jq -r .target "$SPONSOR_WS/refs/notes.json")

L1=$(hexof "the first line"); L2=$(hexof "the second line"); L2b=$(hexof "the second line, revised"); L2c=$(hexof "the second line, final")
invoke a-writes "$SPONSOR_WS" paper "$(jq -n --arg d "$paper" --arg l1 "$L1" --arg l2 "$L2" '[
  {type:"createDocument",rootElement:"1",schema:"0",body:{type:"runs",runs:[]}},
  {type:"createAtom",atom:"1001",kind:{type:"text"},payload:$l1},
  {type:"createAtom",atom:"1002",kind:{type:"text"},payload:$l2}]')"; ok a-writes

delegate grant-r "$SPONSOR_WS" paper "$R_SUBJECT" '["observe","mutate"]' "$NEWCOMER_WS" paper
delegate grant-b "$SPONSOR_WS" notes "$B_SUBJECT" '["observe","mutate"]' "$TW" notes
delegate grant-c-paper "$SPONSOR_WS" paper "$C_SUBJECT" '["observe"]' "$CW" paper
delegate grant-c-notes "$SPONSOR_WS" notes "$C_SUBJECT" '["observe","mutate"]' "$CW" notes
delegate grant-d "$SPONSOR_WS" notes "$D_SUBJECT" '["observe"]' "$DW" notes
run d-import-paper "$MINI" workspace --action import --dir "$DW" --name paper --kind object \
  --target "$paper" --observe-capability "$(jq -r .observeCapability "$DW/refs/notes.json")"; ok d-import-paper

# R reads, annotates line 2 at its revision, then tries to edit it.
read_view r-read1 "$NEWCOMER_WS" paper; ok r-read1
rev1=$(atom r-read1 1002 | jq -r .revision)
invoke r-annotates-line2 "$NEWCOMER_WS" paper "$(jq -n --arg rv "$rev1" --arg b "$(hexof 'cite this')" \
  '[{type:"annotate",annotation:"7001",atom:"1002",revision:$rv,body:$b}]')"
row r-annotates-line2 installed "$(outcome r-annotates-line2)" "$(detail r-annotates-line2)"

read_view r-read2 "$NEWCOMER_WS" paper; ok r-read2
root_before=$(jq -r .cell.root "$D/r-read2.out")
before=$(atom r-read2 1002 | jq -c 'del(.type,.id,.canonical)')
invoke r-edits-line2 "$NEWCOMER_WS" paper "$(jq -n --argjson b "$before" --arg p "$L2b" \
  '[{type:"editAtom",atom:"1002",before:$b,kind:{type:"text"},payload:$p,tombstone:false}]')"
row r-edits-line2 refused "$(outcome r-edits-line2)" "$(detail r-edits-line2); the same grant installed r-annotates-line2"
read_view r-read3 "$NEWCOMER_WS" paper; ok r-read3
root_after=$(jq -r .cell.root "$D/r-read3.out")
row r-edit-left-paper unchanged "$([ "$root_before" = "$root_after" ] && echo unchanged || echo moved)" "root $root_after"

# A edits line 2; R's annotation goes stale and a fresh annotate at the old revision is refused.
read_view a-read1 "$SPONSOR_WS" paper; ok a-read1
before=$(atom a-read1 1002 | jq -c 'del(.type,.id,.canonical)')
invoke a-edits-line2 "$SPONSOR_WS" paper "$(jq -n --argjson b "$before" --arg p "$L2b" \
  '[{type:"editAtom",atom:"1002",before:$b,kind:{type:"text"},payload:$p,tombstone:false}]')"
row a-edits-line2 installed "$(outcome a-edits-line2)" "$(detail a-edits-line2)"
read_view r-read4 "$NEWCOMER_WS" paper; ok r-read4
fresh=$(jq -r '.cell.entries[] | select(.type == "annotation" and .id == "7001") | .fresh' "$D/r-read4.out")
row r-annotation-reads-stale false "$fresh" "annotation 7001 fresh=$fresh"
invoke r-annotates-stale "$NEWCOMER_WS" paper "$(jq -n --arg rv "$rev1" --arg b "$(hexof 'again')" \
  '[{type:"annotate",annotation:"7002",atom:"1002",revision:$rv,body:$b}]')"
row r-annotates-stale refused "$(outcome r-annotates-stale)" "$(detail r-annotates-stale)"

# A edits line 2 again; D (notes only) is refused a read of paper.
read_view a-read2 "$SPONSOR_WS" paper; ok a-read2
before=$(atom a-read2 1002 | jq -c 'del(.type,.id,.canonical)')
invoke a-edits-line2-again "$SPONSOR_WS" paper "$(jq -n --argjson b "$before" --arg p "$L2c" \
  '[{type:"editAtom",atom:"1002",before:$b,kind:{type:"text"},payload:$p,tombstone:false}]')"
row a-edits-line2-again installed "$(outcome a-edits-line2-again)" "$(detail a-edits-line2-again)"
read_view d-reads-paper "$DW" paper
row d-reads-paper refused "$(outcome d-reads-paper)" "$(detail d-reads-paper)"
# Audit: R's refused edit and D's refused read moved no root (checked above for paper);
# notes' root is the same through D's refused read.
read_view a-read-notes "$SPONSOR_WS" notes; ok a-read-notes
read_view c-read-notes2 "$CW" notes; ok c-read-notes2
n1=$(jq -r .cell.root "$D/c-read-notes2.out"); n2=$(jq -r .cell.root "$D/a-read-notes.out")
row notes-root-agrees equal "$([ "$n1" = "$n2" ] && echo equal || echo differs)" "notes root C=$n1 A=$n2"
# The Host's audit re-admits every accepted record (annotate among them)
# at its original prefix from the durable image.
run audit "$HOST" "$CONFIG" audit
row audit re-admitted "$(grep -q "every signed ingress re-admitted" "$D/audit.out" && echo re-admitted || echo "rc=$(cat "$D/audit.rc")")" "$(head -1 "$D/audit.out"; tail -1 "$D/audit.err")"

cat "$rows" >&2
total=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $total content rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$total/$total content rows as expected: annotate admitted and stale after edit, R's edit refused by paper's law, D refused paper" >&2
echo "$rows"
