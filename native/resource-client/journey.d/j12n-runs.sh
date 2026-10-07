#!/usr/bin/env bash
# journey.d/j12n-runs.sh — an appended line is range-transcludable (K-RUNS-RANGES),
# on the journey's fresh Store, after J5 (proposal ids are `rn-`).
#
# Parties: A = sponsor (owns `npaper`, the source, and `npage`, the host); R = the newcomer,
# observe on both: a reader who covers the source.
# npaper holds three lines n1..n3 in one run (9150). A then `doc append`s two lines through
# the document payload; each append is a createAtom plus an `insertRun` of the new atom at the
# end of every run that ends at the document's last line.
# Rows:
#   a-appends-1            A appends "line four"                                -> installed
#   run-grew               run 9150 holds four atoms, the last the new line     -> 4:true
#   a-transcludes-range    A transcludes (live) from line 3 to the appended line -> installed
#   appended-renders       R renders it over R's own read of npaper             -> live n3 n4, not revised
#   a-appends-2            A appends "line five"                                -> installed
#   run-grew-again         run 9150 holds five atoms, the last the new line     -> 5:true
#   range-ignores-later    the same transclusion after the second append        -> unchanged (n3 n4)
#   a-transcludes-new-only A transcludes (live) the second appended line alone  -> installed
#   new-only-renders       R renders it                                         -> live n5
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS NEWCOMER_WS
# NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Exit 0 = every row as
# expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
mkdir -p "$D/req"
rows=$D/runs-rows.tsv
: >"$rows"
bad=0

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
row() { printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"; [ "$2" = "$3" ] || bad=$((bad + 1)); }
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -3 "$D/$1.err")" >&2; exit 1; }; }
outcome() { if [ "$(cat "$D/$1.rc")" = 0 ]; then echo installed; else echo refused-or-error; fi; }
detail() { tail -1 "$D/$1.err" | cut -c1-200; }
hexof() { printf '%s' "$1" | xxd -p | tr -d '\n'; }
propose_submit() { # NAME WS REQUEST-FILE
  run "$1-propose" "$MINI" workspace --action propose --dir "$2" --request "$3" --proposal-id "rn-$1"
  if [ "$(cat "$D/$1-propose.rc")" != 0 ]; then cp "$D/$1-propose.rc" "$D/$1.rc"; cp "$D/$1-propose.err" "$D/$1.err"; return; fi
  run "$1" "$MINI" workspace --action submit --dir "$2" \
    --intent "$2/proposals/rn-$1/intent.json" --attempt "$2/attempts/rn-$1"
}
invoke() { # NAME WS RESOURCE ACTIONS-JSON
  jq -n --arg r "$3" --argjson a "$4" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$r,payload:{type:"content",actions:$a}}]}' >"$D/req/$1.json"
  propose_submit "$1" "$2" "$D/req/$1.json"
}
doc_append() { # NAME TEXT  (the document payload: what `doc append` sends)
  jq -n --arg t "$2" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"npaper",payload:{type:"document",actions:[{type:"append",text:$t}]}}]}' \
    >"$D/req/$1.json"
  propose_submit "$1" "$SPONSOR_WS" "$D/req/$1.json"
}
delegate() { # NAME FROM-WS RESOURCE RECIPIENT-SUBJECT VERBS-JSON TO-WS LOCALNAME
  jq -n --arg n "$3" --arg r "$4" --argjson v "$5" \
    '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,recipient:$r,verbs:$v,maxCost:"50000"}' >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$2" --request "$D/req/$1.json" --proposal-id "rn-$1"; ok "$1-propose"
  run "$1-submit" "$MINI" workspace --action submit --dir "$2" \
    --intent "$2/proposals/rn-$1/intent.json" --attempt "$2/attempts/rn-$1"; ok "$1-submit"
  run "$1-publish" "$MINI" workspace --action publish-delegation --dir "$2" --proposal-id "rn-$1" \
    --attempt "$2/attempts/rn-$1"; ok "$1-publish"
  run "$1-import" "$MINI" workspace --action import --dir "$6" --name "$7" \
    --from-ref "$2/proposals/rn-$1/recipient-reference.json"; ok "$1-import"
}
read_view() { run "$1" "$MINI" workspace --action read --dir "$2" --name "$3"; ok "$1"; }
run_shape() { # VIEW-NAME -> the number of atoms in run 9150
  jq -r '[.cell.entries[] | select(.type == "run" and .id == "9150")] | .[0] | (.atoms | length | tostring)' "$D/$1.out"
}
run_last() { jq -r '[.cell.entries[] | select(.type == "run" and .id == "9150")] | .[0].atoms[-1]' "$D/$1.out"; }
atom_of() { jq -r --arg p "$(hexof "$2")" '[.cell.entries[] | select(.type == "atom" and .payload == $p)] | .[0].id' "$D/$1.out"; }
show() { run "$1" "$MINI" workspace --action transclusions --dir "$2" --name npage; }
render() { # NAME ID -> "view:lines(hex, comma):revised"
  jq -r --arg id "$2" '.transclusions[] | select(.id == $id) | .render
    | .view + ":" + ((.lines // []) | join(",")) + ":" + ((.revised // "") | tostring)' "$D/$1.out"
}
transcluded_id() { grep -o 'workspace transclusion: [0-9]*' "$D/$1.err" | tail -1 | cut -d' ' -f3; }

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
for doc in npaper npage; do
  run "create-$doc" "$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$doc" --storage content \
    --predicate "$D/req/permit-all.json"; ok "create-$doc"
done
invoke a-writes "$SPONSOR_WS" npaper "$(jq -n --arg a "$(hexof 'line one')" --arg b "$(hexof 'line two')" \
  --arg c "$(hexof 'line three')" '[
  {type:"createDocument",rootElement:"9100",schema:"0"},
  {type:"createAtom",atom:"9101",kind:{type:"text"},payload:$a},
  {type:"createAtom",atom:"9102",kind:{type:"text"},payload:$b},
  {type:"createAtom",atom:"9103",kind:{type:"text"},payload:$c},
  {type:"createRun",run:"9150",atoms:["9101","9102","9103"]}]')"; ok a-writes
invoke a-writes-page "$SPONSOR_WS" npage '[{"type":"createDocument","rootElement":"9200","schema":"0"}]'; ok a-writes-page
delegate grant-r-paper "$SPONSOR_WS" npaper "$NEWCOMER_SUBJECT" '["observe"]' "$NEWCOMER_WS" npaper
delegate grant-r-page "$SPONSOR_WS" npage "$NEWCOMER_SUBJECT" '["observe"]' "$NEWCOMER_WS" npage

doc_append a-appends-1 "line four"
row a-appends-1 installed "$(outcome a-appends-1)" "$(detail a-appends-1)"
read_view a-read-1 "$SPONSOR_WS" npaper
N4=$(atom_of a-read-1 "line four")
row run-grew "4:true" "$(run_shape a-read-1):$([ "$(run_last a-read-1)" = "$N4" ] && echo true || echo false)" \
  "run 9150's atoms; the last is the appended line's atom $N4"

run a-transcludes-range "$MINI" workspace --action transclude --dir "$SPONSOR_WS" --name npage --source npaper \
  --from 9103 --to "$N4" --mode live --death keepTombstone
row a-transcludes-range installed "$(outcome a-transcludes-range)" "$(detail a-transcludes-range)"
T1=$(transcluded_id a-transcludes-range)
L3=$(hexof 'line three'); L4=$(hexof 'line four'); L5=$(hexof 'line five')
show r-after-1 "$NEWCOMER_WS"; ok r-after-1
row appended-renders "live:$L3,$L4:" "$(render r-after-1 "$T1")" "R renders the range 9103..$N4 over R's own read"

doc_append a-appends-2 "line five"
row a-appends-2 installed "$(outcome a-appends-2)" "$(detail a-appends-2)"
read_view a-read-2 "$SPONSOR_WS" npaper
N5=$(atom_of a-read-2 "line five")
row run-grew-again "5:true" "$(run_shape a-read-2):$([ "$(run_last a-read-2)" = "$N5" ] && echo true || echo false)" \
  "run 9150's atoms; the last is the second appended line's atom $N5"
show r-after-2 "$NEWCOMER_WS"; ok r-after-2
row range-ignores-later "live:$L3,$L4:" "$(render r-after-2 "$T1")" "the range ends after the first appended line; the second lies past it"

run a-transcludes-new-only "$MINI" workspace --action transclude --dir "$SPONSOR_WS" --name npage --source npaper \
  --from "$N5" --to "$N5" --mode live --death keepTombstone
row a-transcludes-new-only installed "$(outcome a-transcludes-new-only)" "$(detail a-transcludes-new-only)"
T2=$(transcluded_id a-transcludes-new-only)
show r-after-3 "$NEWCOMER_WS"; ok r-after-3
row new-only-renders "live:$L5:" "$(render r-after-3 "$T2")" "a range of the second appended line alone"

cat "$rows" >&2
total=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $total run-edit rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$total/$total run-edit rows as expected: doc append extends the run, the appended lines are named by ranges, an earlier range does not move" >&2
echo "$rows"
