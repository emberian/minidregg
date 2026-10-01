#!/usr/bin/env bash
# journey.d/j12e.sh — the element tree (K-ELEMENT-TREE): a document's order is
# its tree's pre-order walk, a transclusion has a place at line N, and an
# insert costs one edit however many went to the same spot before it.
# Runs on the journey's fresh Store after J5 (and after K12C/K12T when they run).
#
# Parties: A = sponsor (owns `epaper`, `ewall`, `wpaper`); R = the newcomer,
# observe on epaper and ewall: a reader; E = a newly enrolled writer with
# observe+mutate on wpaper (the J12W-equivalent rows).
# Rows:
#   a-writes-five            createDocument + five lines, one command          -> installed
#   five-lines               A's doc show                                      -> p1|p2|p3|p4|p5
#   transclude-at-3          A transcludes ewall w2..w4 `--at 3`               -> installed
#   transclusion-at-line-3   line 3 of A's doc show                            -> the embed of that transclusion
#   order-after-transclude   the lines                                         -> p1|p2|T|p3|p4|p5
#   move-5-to-1              doc-move --from 5 --to 1                          -> installed
#   order-after-move         the lines                                         -> p4|p1|p2|T|p3|p5
#   remove-line-2            doc-remove --line 2 (p1)                          -> installed
#   order-after-remove       the lines                                         -> p4|p2|T|p3|p5
#   removed-atom-stays       p1's atom record; its element's parent            -> present, detached
#   hundred-nested-inserts   100 x doc-insert --at 3 (each between p2 and the last one) -> 100/100
#   hundred-in-place         lines 3, 102, 103 and the count                   -> n100|n1|T|105
#   sections-nest            two sections; B spliced into A                    -> installed installed
#   cycle-refused            A spliced into B (B is below A)                   -> refused: cycle
#   stale-element-refused    a move naming the root's revision before a move   -> refused: staleElement
#   reader-order-equals-owner R's doc show order and numbering                 -> equal
#   w-* (J12W, hand-equivalent: `doc pull/push` are not on this tree)
#     w-writes-four          wpaper: four lines                                -> installed
#     w-edit-and-insert      edit lines 1 and 3, insert between 2 and 3, one command -> installed
#     w-order                the lines                                         -> one'|two|new|three'|four
#     w-a-edits-2            A edits line 2                                    -> installed
#     w-e-stale-line         E edits line 2 from its read before A's edit      -> refused: staleAtom
#     w-nothing-landed       line 2                                            -> A's text
#     w-e-edits-4            E reads again and edits line 4                    -> installed
#     w-strike-3             A strikes line 3                                  -> installed
#     w-numbering            live lines and struck lines                       -> 4 live, 1 struck, numbered 1..4
#   restart-identical        stop and restart the service; A's doc show        -> identical
#   audit                    Host audit re-admits every accepted record        -> re-admitted
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
mkdir -p "$D/req"
rows=$D/element-tree-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
host_refused() {
  [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG\|host refused\|host returned refused\|refused" "$D/$1.err"
}
retained_outcome() {
  local dir; dir=$(grep -o 'workspace attempt: .*' "$D/$1.err" | tail -1 | cut -d' ' -f3)
  [ -n "$dir" ] && [ -f "$dir/outcome.json" ] || return 0
  printf 'outcome %s phase %s: %s' "$(jq -r .type "$dir/outcome.json")" \
    "$(jq -r .phase "$dir/outcome.json" | xxd -r -p)" "$(jq -r .detail "$dir/outcome.json" | xxd -r -p)"
}
refusal_text() {
  { retained_outcome "$1"; echo; grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' '; tail -1 "$D/$1.err"; } | tr '\n' ' ' | cut -c1-400
}
row() { printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"; [ "$2" = "$3" ] || bad=$((bad + 1)); }
outcome() {
  if [ "$(cat "$D/$1.rc")" = 0 ]; then echo installed
  elif host_refused "$1"; then echo refused
  else echo client-error; fi
}
detail() { if [ "$(outcome "$1")" = refused ]; then refusal_text "$1"; else tail -1 "$D/$1.err" | cut -c1-200; fi; }
# refused:REASON when the refusal names REASON (a ContentResource.Reject), else the outcome.
refused_by() {
  if [ "$(outcome "$1")" = refused ] && refusal_text "$1" | grep -q "Reject.$2"; then echo "refused:$2"
  else echo "$(outcome "$1")"; fi
}
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -3 "$D/$1.err")" >&2; exit 1; }; }
invoke() {
  local name=$1 ws=$2 targets=$3
  jq -n --argjson t "$targets" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:$t}' >"$D/req/$name.json"
  # Proposal ids are prefixed `e-`: the sponsor's workspace already holds K12C's and K12T's.
  run "$name-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$name.json" --proposal-id "e-$name"
  if [ "$(cat "$D/$name-propose.rc")" != 0 ]; then cp "$D/$name-propose.rc" "$D/$name.rc"
    cp "$D/$name-propose.err" "$D/$name.err"; : >"$D/$name.out"; return; fi
  run "$name" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/e-$name/intent.json" --attempt "$ws/attempts/e-$name"
}
content() { jq -n --arg r "$1" --argjson a "$2" '[{name:$r,payload:{type:"content",actions:$a}}]'; }
delegate() { # NAME FROM-WS RESOURCE RECIPIENT-SUBJECT VERBS-JSON TO-WS LOCALNAME
  jq -n --arg n "$3" --arg r "$4" --argjson v "$5" \
    '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,recipient:$r,verbs:$v,maxCost:"50000"}' \
    >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$2" --request "$D/req/$1.json" --proposal-id "e-$1"; ok "$1-propose"
  run "$1-submit" "$MINI" workspace --action submit --dir "$2" \
    --intent "$2/proposals/e-$1/intent.json" --attempt "$2/attempts/e-$1"; ok "$1-submit"
  run "$1-publish" "$MINI" workspace --action publish-delegation --dir "$2" --proposal-id "e-$1" \
    --attempt "$2/attempts/e-$1"; ok "$1-publish"
  run "$1-import" "$MINI" workspace --action import --dir "$6" --name "$7" \
    --from-ref "$2/proposals/e-$1/recipient-reference.json"; ok "$1-import"
}
enroll() {
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
show() { run "$1" "$MINI" workspace --action doc-show --dir "$2" --name "$3"; }
# The live lines of a doc show: atoms by text, a transclusion as T.
lines_of() {
  jq -r '[.lines[] | select(.line != null) | if .kind == "embed" then "T" else .text end] | join("|")' "$D/$1.out"
}
root_revision() { jq -r .rootRevision "$D/$1.out"; }
section_revision() { jq -r --arg e "$2" '.lines[] | select(.element == $e) | .revision' "$D/$1.out"; }
read_view() { run "$1" "$MINI" workspace --action read --dir "$2" --name "$3"; }
atom() { jq -c --arg a "$2" '.cell.entries[] | select(.type == "atom" and .id == $a)' "$D/$1.out"; }
element_entry() { jq -c --arg a "$2" '.cell.entries[] | select(.type == "element" and .id == $a)' "$D/$1.out"; }
before_of() { atom "$1" "$2" | jq -c 'del(.type,.id,.canonical)'; }
edit_json() { # BEFORE-JSON ATOM PAYLOAD-HEX TOMBSTONE
  jq -n --argjson b "$1" --arg a "$2" --arg p "$3" --argjson t "$4" \
    '{type:"editAtom",atom:$a,before:$b,kind:{type:"text"},payload:$p,tombstone:$t}'
}

R_SUBJECT=$NEWCOMER_SUBJECT
E_SUBJECT=$(enroll ewriter); EW=$W/ewriter-workspace

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
for name in epaper ewall wpaper; do
  run "create-$name" "$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$name" --storage content \
    --predicate "$D/req/permit-all.json"; ok "create-$name"
done
for n in 1 2 3 4 5; do eval "WL$n=\$(hexof 'wall line $n')"; done
invoke a-writes-wall "$SPONSOR_WS" "$(content ewall "$(jq -n --arg l1 "$WL1" --arg l2 "$WL2" --arg l3 "$WL3" \
  --arg l4 "$WL4" --arg l5 "$WL5" '[
  {type:"createDocument",rootElement:"1",schema:"0"},
  {type:"createAtom",atom:"1001",kind:{type:"text"},payload:$l1},
  {type:"createAtom",atom:"1002",kind:{type:"text"},payload:$l2},
  {type:"createAtom",atom:"1003",kind:{type:"text"},payload:$l3},
  {type:"createAtom",atom:"1004",kind:{type:"text"},payload:$l4},
  {type:"createAtom",atom:"1005",kind:{type:"text"},payload:$l5},
  {type:"createRun",run:"2000",atoms:["1001","1002","1003","1004","1005"]}]')")"; ok a-writes-wall
delegate grant-r-epaper "$SPONSOR_WS" epaper "$R_SUBJECT" '["observe"]' "$NEWCOMER_WS" epaper
delegate grant-r-ewall "$SPONSOR_WS" ewall "$R_SUBJECT" '["observe"]' "$NEWCOMER_WS" ewall
delegate grant-e-wpaper "$SPONSOR_WS" wpaper "$E_SUBJECT" '["observe","mutate"]' "$EW" wpaper

# --- a document of five lines; a transclusion placed at line 3 ---
invoke a-writes-five "$SPONSOR_WS" "$(content epaper "$(jq -n \
  --arg p1 "$(hexof p1)" --arg p2 "$(hexof p2)" --arg p3 "$(hexof p3)" --arg p4 "$(hexof p4)" --arg p5 "$(hexof p5)" '[
  {type:"createDocument",rootElement:"1",schema:"0"},
  {type:"createAtom",atom:"3001",kind:{type:"text"},payload:$p1},
  {type:"createAtom",atom:"3002",kind:{type:"text"},payload:$p2},
  {type:"createAtom",atom:"3003",kind:{type:"text"},payload:$p3},
  {type:"createAtom",atom:"3004",kind:{type:"text"},payload:$p4},
  {type:"createAtom",atom:"3005",kind:{type:"text"},payload:$p5}]')")"
row a-writes-five installed "$(outcome a-writes-five)" "$(detail a-writes-five)"
show a-show-five "$SPONSOR_WS" epaper; ok a-show-five
row five-lines "p1|p2|p3|p4|p5" "$(lines_of a-show-five)" "A's doc show, the kernel's order"

run transclude-at-3 "$MINI" workspace --action transclude --dir "$SPONSOR_WS" --name epaper --source ewall \
  --from 1002 --to 1004 --mode snapshot --death keepTombstone --at 3
row transclude-at-3 installed "$(outcome transclude-at-3)" "$(detail transclude-at-3)"
T=$(grep -o 'workspace transclusion: [0-9]*' "$D/transclude-at-3.err" | tail -1 | cut -d' ' -f3)
show a-show-transcluded "$SPONSOR_WS" epaper; ok a-show-transcluded
row transclusion-at-line-3 "embed:$T" \
  "$(jq -r '.lines[] | select(.line == 3) | .kind + ":" + (.transclusion // "")' "$D/a-show-transcluded.out")" \
  "$(jq -r '.lines[] | select(.line == 3) | .text' "$D/a-show-transcluded.out" | head -1)"
row order-after-transclude "p1|p2|T|p3|p4|p5" "$(lines_of a-show-transcluded)" "one transaction: transclude + move"

# --- move, remove ---
run move-5-to-1 "$MINI" workspace --action doc-move --dir "$SPONSOR_WS" --name epaper --from 5 --to 1
row move-5-to-1 installed "$(outcome move-5-to-1)" "$(detail move-5-to-1)"
show a-show-moved "$SPONSOR_WS" epaper; ok a-show-moved
row order-after-move "p4|p1|p2|T|p3|p5" "$(lines_of a-show-moved)" "line 5 (p4) now line 1"

run remove-line-2 "$MINI" workspace --action doc-remove --dir "$SPONSOR_WS" --name epaper --line 2
row remove-line-2 installed "$(outcome remove-line-2)" "$(detail remove-line-2)"
show a-show-removed "$SPONSOR_WS" epaper; ok a-show-removed
row order-after-remove "p4|p2|T|p3|p5" "$(lines_of a-show-removed)" "p1 left the order"
read_view a-read-removed "$SPONSOR_WS" epaper; ok a-read-removed
row removed-atom-stays "present:detached" \
  "$( [ -n "$(atom a-read-removed 3001)" ] && echo present || echo absent):$(element_entry a-read-removed 3001 \
    | jq -r 'if .parent == null then "detached" else "under " + .parent end')" "atom 3001 stays, its element has no parent"

# --- 100 nested inserts at one spot: each between p2 and the one inserted before it ---
admitted=0
for k in $(seq 1 100); do
  run "insert-$k" "$MINI" workspace --action doc-insert --dir "$SPONSOR_WS" --name epaper --text "n$k" --at 3
  [ "$(outcome "insert-$k")" = installed ] && admitted=$((admitted + 1))
done
row hundred-nested-inserts 100/100 "$admitted/100" "$(detail insert-100)"
show a-show-hundred "$SPONSOR_WS" epaper; ok a-show-hundred
got=$(jq -r '[.lines[] | select(.line != null)] as $l
  | [($l[2] | .text), ($l[101] | .text), ($l[102] | if .kind == "embed" then "T" else .text end), ($l | length | tostring)]
  | join("|")' "$D/a-show-hundred.out")
row hundred-in-place "n100|n1|T|105" "$got" "lines 3, 102, 103 and the line count; no identifier space was split"

# --- sections: nest, then a cycle; a stale revision ---
invoke sections-create "$SPONSOR_WS" "$(content epaper '[{"type":"createContainer","element":"501"},{"type":"createContainer","element":"502"}]')"
show a-show-sections "$SPONSOR_WS" epaper; ok a-show-sections
r0=$(root_revision a-show-sections); s501=$(section_revision a-show-sections 501)
invoke sections-nest "$SPONSOR_WS" "$(content epaper "$(jq -n --arg r "$r0" --arg s "$s501" '[
  {type:"editElement",element:"1",revision:$r,op:{type:"remove",child:"502"}},
  {type:"editElement",element:"501",revision:$s,op:{type:"splice",index:"0",child:"502"}}]')")"
row sections-nest "installed installed" "$(outcome sections-create) $(outcome sections-nest)" "$(detail sections-nest)"
show a-show-nested "$SPONSOR_WS" epaper; ok a-show-nested
r1=$(root_revision a-show-nested); s502=$(section_revision a-show-nested 502)
invoke cycle-refused "$SPONSOR_WS" "$(content epaper "$(jq -n --arg r "$r1" --arg s "$s502" '[
  {type:"editElement",element:"1",revision:$r,op:{type:"remove",child:"501"}},
  {type:"editElement",element:"502",revision:$s,op:{type:"splice",index:"0",child:"501"}}]')")"
row cycle-refused refused:cycle "$(refused_by cycle-refused cycle)" "$(detail cycle-refused)"

show a-show-before-move "$SPONSOR_WS" epaper; ok a-show-before-move
stale=$(root_revision a-show-before-move)
first=$(jq -r '[.lines[] | select(.line != null)][0].element' "$D/a-show-before-move.out")
run a-moves-again "$MINI" workspace --action doc-move --dir "$SPONSOR_WS" --name epaper --from 1 --to 2; ok a-moves-again
invoke stale-element-refused "$SPONSOR_WS" "$(content epaper "$(jq -n --arg r "$stale" --arg c "$first" '[
  {type:"editElement",element:"1",revision:$r,op:{type:"move",child:$c,index:"3"}}]')")"
row stale-element-refused refused:staleElement "$(refused_by stale-element-refused staleElement)" \
  "$(detail stale-element-refused)"

# --- the reader sees the owner's order ---
show a-show-final "$SPONSOR_WS" epaper; ok a-show-final
show r-show-final "$NEWCOMER_WS" epaper; ok r-show-final
order() { jq -c '[.lines[] | {element, line, kind}]' "$D/$1.out"; }
row reader-order-equals-owner equal "$([ "$(order a-show-final)" = "$(order r-show-final)" ] && echo equal || echo differs)" \
  "R's own signed read; $(jq '[.lines[] | select(.line != null)] | length' "$D/r-show-final.out") lines"

# --- J12W, hand-equivalent: two writers, a line placed between two, a stale line refused by name ---
invoke w-writes-four "$SPONSOR_WS" "$(content wpaper "$(jq -n \
  --arg a "$(hexof one)" --arg b "$(hexof two)" --arg c "$(hexof three)" --arg d "$(hexof four)" '[
  {type:"createDocument",rootElement:"1",schema:"0"},
  {type:"createAtom",atom:"4001",kind:{type:"text"},payload:$a},
  {type:"createAtom",atom:"4002",kind:{type:"text"},payload:$b},
  {type:"createAtom",atom:"4003",kind:{type:"text"},payload:$c},
  {type:"createAtom",atom:"4004",kind:{type:"text"},payload:$d}]')")"
row w-writes-four installed "$(outcome w-writes-four)" "$(detail w-writes-four)"
read_view w-a-read "$SPONSOR_WS" wpaper; ok w-a-read
show w-a-show "$SPONSOR_WS" wpaper; ok w-a-show
invoke w-edit-and-insert "$SPONSOR_WS" "$(content wpaper "$(jq -n \
  --argjson e1 "$(edit_json "$(before_of w-a-read 4001)" 4001 "$(hexof "one'")" false)" \
  --argjson e3 "$(edit_json "$(before_of w-a-read 4003)" 4003 "$(hexof "three'")" false)" \
  --arg n "$(hexof new)" --arg r "$(root_revision w-a-show)" '[$e1, $e3,
  {type:"createAtom",atom:"4005",kind:{type:"text"},payload:$n},
  {type:"editElement",element:"1",revision:$r,op:{type:"move",child:"4005",index:"2"}}]')")"
row w-edit-and-insert installed "$(outcome w-edit-and-insert)" "$(detail w-edit-and-insert)"
show w-a-show2 "$SPONSOR_WS" wpaper; ok w-a-show2
row w-order "one'|two|new|three'|four" "$(lines_of w-a-show2)" "the inserted line in place"
read_view w-e-read "$EW" wpaper; ok w-e-read
edit_line_two_by_a=$(edit_json "$(before_of w-a-read 4002)" 4002 "$(hexof 'two, edited by A')" false)
invoke w-a-edits-2 "$SPONSOR_WS" "$(content wpaper "[$edit_line_two_by_a]")"
row w-a-edits-2 installed "$(outcome w-a-edits-2)" "$(detail w-a-edits-2)"
invoke w-e-stale-line "$EW" "$(content wpaper "[$(edit_json "$(before_of w-e-read 4002)" 4002 "$(hexof 'two, edited by E')" false)]")"
row w-e-stale-line refused:staleAtom "$(refused_by w-e-stale-line staleAtom)" "$(detail w-e-stale-line)"
show w-a-show3 "$SPONSOR_WS" wpaper; ok w-a-show3
row w-nothing-landed "two, edited by A" "$(jq -r '.lines[] | select(.line == 2) | .text' "$D/w-a-show3.out")" "line 2 after E's refused edit"
read_view w-e-read2 "$EW" wpaper; ok w-e-read2
invoke w-e-edits-4 "$EW" "$(content wpaper "[$(edit_json "$(before_of w-e-read2 4003)" 4003 "$(hexof "three', edited by E")" false)]")"
row w-e-edits-4 installed "$(outcome w-e-edits-4)" "$(detail w-e-edits-4)"
read_view w-a-read3 "$SPONSOR_WS" wpaper; ok w-a-read3
invoke w-strike-3 "$SPONSOR_WS" "$(content wpaper "[$(edit_json "$(before_of w-a-read3 4005)" 4005 "$(hexof new)" true)]")"
row w-strike-3 installed "$(outcome w-strike-3)" "$(detail w-strike-3)"
show w-a-show4 "$SPONSOR_WS" wpaper; ok w-a-show4
row w-numbering "4 live, 1 struck, numbered 1..4" "$(jq -r '"\([.lines[] | select(.line != null)] | length) live, \([.lines[] | select(.struck == true)] | length) struck, numbered \([.lines[] | select(.line != null) | .line] | if . == [1,2,3,4] then "1..4" else tostring end)"' "$D/w-a-show4.out")" \
  "$(lines_of w-a-show4)"

# --- restart and audit ---
pid=$(cat "$W/public/server.pid")
case "$(ps -o args= -p "$pid" 2>/dev/null)" in *" serve "*"--socket $SOCKET"*) ;; *) echo "server $pid is not ours" >&2; exit 1;; esac
kill -TERM "$pid"; for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-k12e.log" 2>&1 </dev/null &
echo $! >"$W/public/server.pid"
for i in $(seq 1 600); do grep -q serving "$W/public/serve-k12e.log" 2>/dev/null && [ -S "$SOCKET" ] && break; sleep 0.1; done
show a-show-restart "$SPONSOR_WS" epaper; ok a-show-restart
before=$(jq -c '[.lines[] | {element, line, kind, text}]' "$D/a-show-final.out")
after=$(jq -c '[.lines[] | {element, line, kind, text}]' "$D/a-show-restart.out")
row restart-identical identical "$([ "$before" = "$after" ] && echo identical || echo differs)" "A's doc show across a restart"

run audit "$HOST" "$CONFIG" audit
row audit re-admitted "$(grep -q "every signed ingress re-admitted" "$D/audit.out" && echo re-admitted || echo "rc=$(cat "$D/audit.rc")")" "$(head -1 "$D/audit.out"; tail -1 "$D/audit.err")"

cat "$rows" >&2
total=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $total element-tree rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$total/$total element-tree rows as expected: order is the tree's walk, a transclusion at line 3, 100 nested inserts placed, cycle and stale refused by name" >&2
echo "$rows"
