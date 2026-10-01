#!/usr/bin/env bash
# journey.d/j12h-history.sh — K-DOC-HISTORY: doc history / doc show --at / doc diff
# over the signed log, rendered by the Host (Lean) over the reader's own reads.
# Runs on the journey's fresh Store after J5 (the third key C exists).
#
# Parties: A = sponsor (owns `hist`), B = the newcomer (observe+mutate on hist,
# granted after h2), C = the third key (observe on hist, granted after h2).
# Five edits: h1 A creates the document and line 1001; h2 A appends 1002;
# h3 B edits 1001; h4 A appends 1003; h5 B edits 1002; h6 A moves 1003 to the
# top (an element-tree move: no atom changes, the order does). After each, A
# runs `doc-show` (current read) and the line table is saved: the control.
# Lines are the element tree's walk (view-document's order); changes are keyed
# by element (an atom's element is the atom's own id).
# Rows:
#   history-edits        A's history: rows at h1..h6, subjects A A B A B A   -> exact
#   history-atoms        each row's changes                               -> +1001 | +1002 | ~1001 | +1003 | ~1002 | moved 1001,1003
#   history-below        rows below h1 (the birth)                        -> 1
#   show-at-hN (N=1..6)  `doc-show --at hN` lines+root = saved control     -> equal
#   order-at-h6          the line order at h6                             -> 1003 1001 1002
#   diff-h2-h4           Lean diff h2→h4                                  -> ~1001 +1003
#   diff-agrees-show     jq diff (incl. moves) of the two --at tables = Lean diff -> equal
#   diff-h5-h6-moves     Lean diff h5→h6: the move's seams                 -> moved 1001, moved 1003
#   diff-moves-agree     jq diff of the --at h5 / h6 tables = Lean diff   -> equal
#   c-at-h2              C (granted after h2) --at h2                      -> refused (no-grant)
#   c-at-h3              C --at h3                                         -> read, = control h3
#   c-history-split      C's history: rows h1,h2 carry no content; h3..h6 do -> exact
#   restart-identical    stop+start the service; history and --at h4 again -> byte-identical
#   audit                Host audit re-admits every accepted record        -> re-admitted
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
TW=$W/third-workspace
mkdir -p "$D/req"
rows=$D/history-rows.tsv
: >"$rows"
bad=0

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -3 "$D/$1.err")" >&2; exit 1; }; }
row() { printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"; [ "$2" = "$3" ] || bad=$((bad + 1)); }
reason() { grep -o "encoded refusal: [0-9a-f]*" "$D/$1.err" | tail -1 | cut -d" " -f3 | xxd -r -p 2>/dev/null | tr -c "[:print:]" " "; }
hexof() { printf '%s' "$1" | xxd -p | tr -d '\n'; }
subject_of() { jq -r .subject "$1/workspace.json"; }
invoke() { # NAME WS ACTIONS-JSON -> prints the record's log height
  local name=$1 ws=$2 actions=$3
  jq -n --argjson a "$actions" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"hist",payload:{type:"content",actions:$a}}]}' \
    >"$D/req/$name.json"
  run "$name-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$name.json" --proposal-id "$name"; ok "$name-propose"
  run "$name" "$MINI" workspace --action submit --dir "$ws" --intent "$ws/proposals/$name/intent.json" --attempt "$ws/attempts/$name"; ok "$name"
  jq -e '.type == "confirmed"' "$ws/attempts/$name/outcome.json" >/dev/null || { echo "$name not confirmed" >&2; exit 1; }
  jq -r .acceptedCount "$ws/attempts/$name/outcome.json"
}
delegate() { # NAME RECIPIENT-SUBJECT VERBS-JSON TO-WS
  jq -n --arg r "$2" --argjson v "$3" \
    '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"hist",recipient:$r,verbs:$v,maxCost:"50000"}' >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/$1.json" --proposal-id "$1"; ok "$1-propose"
  run "$1-submit" "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/$1/intent.json" --attempt "$SPONSOR_WS/attempts/$1"; ok "$1-submit"
  run "$1-publish" "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id "$1" --attempt "$SPONSOR_WS/attempts/$1"; ok "$1-publish"
  run "$1-import" "$MINI" workspace --action import --dir "$4" --name hist --from-ref "$SPONSOR_WS/proposals/$1/recipient-reference.json"; ok "$1-import"
}
atom_before() { # READNAME ATOM -> editAtom's `before`
  jq -c --arg a "$2" '.cell.entries[] | select(.type == "atom" and .id == $a) | del(.type,.id,.canonical)' "$D/$1.out"
}
show() { run "$1" "$MINI" workspace --action doc-show --dir "$2" --name hist ${3:+--at "$3"} --format json; }
table() { jq -c '{root, lines}' "$D/$1.out"; }
kinds() { jq -c '[.[] | (if .type == "added" then "+" elif .type == "removed" then "-" elif .type == "moved" then "m" else "~" end) + .element]'; }
# The Lean diff and an independent jq diff of two `doc-show --at` tables, both
# keyed by element and projected to {type, element, before, after} (a line's
# revision; a move's predecessor among the lines on both sides).
lean_diff() { jq -c '[.changes[] | if .type == "moved" then {type, element, before, after}
  else {type, element, before: (.before.revision // null), after: (.after.revision // null)} end]
  | sort_by(.type, .element)' "$D/$1.out"; }
jq_diff() { jq -cn --slurpfile l "$D/$1.out" --slurpfile r "$D/$2.out" '
  def value: {kind, atom, payload, revision, createdBy, struck, transclusion};
  def pred($c; $k): ($c | index($k)) as $i | if $i == 0 then null else $c[$i - 1] end;
  ($l[0].lines | map({key: .element, value: .}) | from_entries) as $L |
  ($r[0].lines | map({key: .element, value: .}) | from_entries) as $R |
  ($l[0].lines | map(.element) | map(select($R[.] != null))) as $CL |
  ($r[0].lines | map(.element) | map(select($L[.] != null))) as $CR |
  ([$L | keys[] | select($R[.] == null) | {type: "removed", element: ., before: $L[.].revision, after: null}] +
   [$R | keys[] | select($L[.] == null) | {type: "added", element: ., before: null, after: $R[.].revision}] +
   [$L | keys[] | select($R[.] != null and ($L[.] | value) != ($R[.] | value)) |
     {type: "changed", element: ., before: $L[.].revision, after: $R[.].revision}] +
   [$CL[] | {type: "moved", element: ., before: pred($CL; .), after: pred($CR; .)} | select(.before != .after)])
  | sort_by(.type, .element)'; }

A=$(subject_of "$SPONSOR_WS"); B=$(subject_of "$NEWCOMER_WS"); C=$(subject_of "$TW")
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create-hist "$MINI" workspace --action create --dir "$SPONSOR_WS" --name hist --storage content --predicate "$D/req/permit-all.json"; ok create-hist
hist=$(jq -r .target "$SPONSOR_WS/refs/hist.json")

declare -A H
H[1]=$(invoke h-e1 "$SPONSOR_WS" "$(jq -n --arg p "$(hexof one)" '[
  {type:"createDocument",rootElement:"1",schema:"0"},
  {type:"createAtom",atom:"1001",kind:{type:"text"},payload:$p}]')")
show ctl-1 "$SPONSOR_WS"; ok ctl-1
H[2]=$(invoke h-e2 "$SPONSOR_WS" "$(jq -n --arg p "$(hexof two)" '[{type:"createAtom",atom:"1002",kind:{type:"text"},payload:$p}]')")
show ctl-2 "$SPONSOR_WS"; ok ctl-2
delegate h-grant-b "$B" '["observe","mutate"]' "$NEWCOMER_WS"
delegate h-grant-c "$C" '["observe"]' "$TW"
run b-read3 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name hist; ok b-read3
H[3]=$(invoke h-e3 "$NEWCOMER_WS" "$(jq -n --argjson b "$(atom_before b-read3 1001)" --arg p "$(hexof 'one, by B')" \
  '[{type:"editAtom",atom:"1001",before:$b,kind:{type:"text"},payload:$p,tombstone:false}]')")
show ctl-3 "$SPONSOR_WS"; ok ctl-3
H[4]=$(invoke h-e4 "$SPONSOR_WS" "$(jq -n --arg p "$(hexof three)" '[{type:"createAtom",atom:"1003",kind:{type:"text"},payload:$p}]')")
show ctl-4 "$SPONSOR_WS"; ok ctl-4
run b-read5 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name hist; ok b-read5
H[5]=$(invoke h-e5 "$NEWCOMER_WS" "$(jq -n --argjson b "$(atom_before b-read5 1002)" --arg p "$(hexof 'two, by B')" \
  '[{type:"editAtom",atom:"1002",before:$b,kind:{type:"text"},payload:$p,tombstone:false}]')")
show ctl-5 "$SPONSOR_WS"; ok ctl-5
H[6]=$(invoke h-e6 "$SPONSOR_WS" "$(jq -n --arg r "$(jq -r .rootRevision "$D/ctl-5.out")" \
  '[{type:"editElement",element:"1",revision:$r,op:{type:"move",child:"1003",index:"0"}}]')")
show ctl-6 "$SPONSOR_WS"; ok ctl-6

# Absolute heights: genesis height G = the current read's challenge height - the last log height.
# (the newest signed read of A's workspace is ctl-6's host read; doc-show's
# render attempts hold no challenge)
challenge=$(ls -t "$SPONSOR_WS"/attempts/*/challenge.json | head -1)
G=$(( $(jq -r .height "$challenge") - H[6] ))
[ "$G" -gt 0 ] || { echo "genesis height $G from $challenge is not positive" >&2; exit 1; }
for i in 1 2 3 4 5 6; do H[$i]=$((G + H[$i])); done
echo "genesis $G; edit heights ${H[1]} ${H[2]} ${H[3]} ${H[4]} ${H[5]} ${H[6]}; subjects A=$A B=$B C=$C" >&2

# history
run hist-a "$MINI" workspace --action doc-history --dir "$SPONSOR_WS" --name hist --format json; ok hist-a
want=$(jq -cn --arg a "$A" --arg b "$B" --argjson h "[\"${H[1]}\",\"${H[2]}\",\"${H[3]}\",\"${H[4]}\",\"${H[5]}\",\"${H[6]}\"]" \
  '[$h, [$a,$a,$b,$a,$b,$a]] | transpose | map({height: .[0], subject: .[1]})')
got=$(jq -c --argjson h1 "${H[1]}" '[.rows[] | select((.height|tonumber) >= $h1) | {height, subject}]' "$D/hist-a.out")
row history-edits "$want" "$got" "6 edits by two subjects"
got=$(jq -c --argjson h1 "${H[1]}" '[.rows[] | select((.height|tonumber) >= $h1) | .changes | [.[] | (if .type == "added" then "+" elif .type == "removed" then "-" elif .type == "moved" then "m" else "~" end) + .element]]' "$D/hist-a.out")
row history-atoms '[["+1001"],["+1002"],["~1001"],["+1003"],["~1002"],["m1001","m1003"]]' "$got" "changes per row, keyed by element"
revs=$(jq -c --argjson h "${H[3]}" '.rows[] | select((.height|tonumber) == $h) | .changes[0] | [.before.revision, .after.revision]' "$D/hist-a.out")
got=$(jq -c --argjson h1 "${H[1]}" '[.rows[] | select((.height|tonumber) < $h1)] | length' "$D/hist-a.out")
row history-below 1 "$got" "the birth row; h3 revision before→after $revs"

# show --at each height = the control saved right after that edit
for i in 1 2 3 4 5 6; do
  show at-$i "$SPONSOR_WS" "${H[$i]}"
  if [ "$(cat "$D/at-$i.rc")" = 0 ] && [ "$(table at-$i)" = "$(table ctl-$i)" ]; then g=equal; else g=differ; fi
  row show-at-h$i equal "$g" "height ${H[$i]}: $(jq -c '[.lines[] | .atom + "@" + .revision]' "$D/at-$i.out" 2>/dev/null | cut -c1-160)"
done

# diff h2 h4, and the differential against the two --at tables
run diff-24 "$MINI" workspace --action doc-diff --dir "$SPONSOR_WS" --name hist --from "${H[2]}" --to "${H[4]}" --format json; ok diff-24
got=$(jq -c '.changes' "$D/diff-24.out" | kinds)
row diff-h2-h4 '["~1001","+1003"]' "$got" "Lean diff ${H[2]}→${H[4]}"
row diff-agrees-show "$(lean_diff diff-24)" "$(jq_diff at-2 at-4)" "jq diff of show --at ${H[2]} / ${H[4]}"
row order-at-h6 "1003 1001 1002" "$(jq -r '[.lines[].element] | join(" ")' "$D/at-6.out")" "the element tree's walk at ${H[6]}"
run diff-56 "$MINI" workspace --action doc-diff --dir "$SPONSOR_WS" --name hist --from "${H[5]}" --to "${H[6]}" --format json; ok diff-56
row diff-h5-h6-moves '["m1001","m1003"]' "$(jq -c '.changes' "$D/diff-56.out" | kinds)" \
  "Lean diff ${H[5]}→${H[6]}: $(lean_diff diff-56 | cut -c1-200)"
row diff-moves-agree "$(lean_diff diff-56)" "$(jq_diff at-5 at-6)" "jq diff of show --at ${H[5]} / ${H[6]}"

# coverage at the asked height
show c-at-2 "$TW" "${H[2]}"
# atCovered refuses a grant that did not stand at h with the named reason no-grant
# (the Host's own decoding, `refused: no-grant: ...`), never a text to match.
if [ "$(cat "$D/c-at-2.rc")" != 0 ] && grep -q "refused: no-grant: " "$D/c-at-2.err"; then g=refused; else g="rc=$(cat "$D/c-at-2.rc")"; fi
row c-at-h2 refused "$g" "$(grep -o "refused: no-grant: [^;(]*" "$D/c-at-2.err" | head -1)"
show c-at-3 "$TW" "${H[3]}"
if [ "$(cat "$D/c-at-3.rc")" = 0 ] && [ "$(table c-at-3)" = "$(table ctl-3)" ]; then g=equal; else g=differ; fi
row c-at-h3 equal "$g" "C reads h3 = A's control at h3"
run hist-c "$MINI" workspace --action doc-history --dir "$TW" --name hist --format json; ok hist-c
got=$(jq -c --argjson h1 "${H[1]}" '[.rows[] | select((.height|tonumber) >= $h1) | (.after != null)]' "$D/hist-c.out")
row c-history-split '[false,false,true,true,true,true]' "$got" "C sees every row (current grant); content only from its grant height"

# restart: stop the service, start it again, and read the same history and --at
cp "$D/hist-a.out" "$D/hist-a.before"; cp "$D/at-4.out" "$D/at-4.before"
pid=$(cat "$W/public/server.pid")
case "$(ps -o args= -p "$pid")" in *" serve "*"--socket $SOCKET"*) ;; *) echo "pid $pid is not our server" >&2; exit 1;; esac
kill -TERM "$pid"; for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" >"$W/public/serve-k12h.log" 2>&1 </dev/null &
echo $! >"$W/public/server.pid"
for i in $(seq 1 600); do [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-k12h.log" && break; sleep 0.1; done
run hist-a "$MINI" workspace --action doc-history --dir "$SPONSOR_WS" --name hist --format json; ok hist-a
show at-4 "$SPONSOR_WS" "${H[4]}"; ok at-4
if cmp -s "$D/hist-a.out" "$D/hist-a.before" && cmp -s "$D/at-4.out" "$D/at-4.before"; then g=identical; else g=differ; fi
row restart-identical identical "$g" "server $pid -> $(cat "$W/public/server.pid")"

run audit "$HOST" "$CONFIG" audit
if [ "$(cat "$D/audit.rc")" = 0 ] && grep -q "re-admitted" "$D/audit.out" "$D/audit.err"; then g=re-admitted; else g=failed; fi
row audit re-admitted "$g" "$(grep -ho 'audited [0-9]* accepted records[^;]*' "$D/audit.out" "$D/audit.err" | head -1 | cut -c1-120)"

n=$(wc -l <"$rows")
echo "K12H: $((n - bad))/$n rows as expected" >&2
echo "$rows"
[ "$bad" = 0 ]
