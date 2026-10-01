#!/usr/bin/env bash
# journey.d/j12t-kernel.sh — range transclusion with disclosure at transclusion
# time (K-TRANSCLUDE), on the journey's fresh Store, after J5.
#
# Parties: A = sponsor (owns `wall`, the source, and `page`, the host);
# C = observe on wall, observe+mutate on page: the transcluder;
# R = the newcomer, observe on wall and on page: a reader who covers the source;
# D = observe on page only: a reader who does not;
# B = the third key, observe+mutate on page and nothing on wall: the outsider.
# wall holds five lines w1..w5 in one run. C transcludes w2..w4 into page three
# times: T1 snapshot (keepTombstone), T2 live (preferNext), T3 live (invalidate).
# Rows:
#   c-transcludes-snapshot    T1, with a read of wall in the same transaction -> installed
#   c-transcludes-live        T2 and T3                                       -> installed
#   page-records             page holds 3 transclusion records + 3 links    -> 3/3
#   page-holds-no-bytes      no line of wall appears in page's own view     -> absent
#   r-sees-inline             R renders T1 over R's own read of wall          -> snapshot w2 w3 w4
#   d-sees-placeholder        D renders every transclusion, holding no wall read -> unavailable x3
#   d-placeholder-text        the shape D sees                                -> [transclusion: 3 atoms of WALL, not readable by you]
#   b-cannot-transclude       B (no grant on wall) tries to transclude        -> refused (observation)
#   c-no-read-refused         C sends the transclude without the read target  -> refused sourceNotCovered
#   c-stale-opening-refused   C pins w3 at a revision wall does not hold       -> refused staleOpening
#   a-edits-inside            A edits w3                                      -> installed
#   inside-snapshot           T1 after the edit: read `at` its opening height -> snapshot w2 w3 w4, at H
#   inside-live               T2 after the edit                               -> live w2 w3' w4, revised
#   a-edits-outside           A edits w1                                      -> installed
#   outside-unchanged         T1 and T2 renderings after the outside edit     -> unchanged
#   a-deletes-endpoint        A tombstones w4 (both ranges' finish)           -> installed
#   death-invalidate          T3                                              -> invalidated
#   death-prefer-next         T2: the finish moves to w5                      -> live w2 w3' w5
#   death-snapshot-pinned     T1                                              -> snapshot w2 w3 w4
#   r-follows-live            R `follow`s T2 at the current height            -> live w2 w3' w5
#   d-follow-refused          D `follow`s T2                                  -> refused
#   restart-identical         stop and restart the service; R renders again   -> identical
#   audit                     Host audit re-admits every accepted record      -> re-admitted
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS NEWCOMER_WS
# NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Exit 0 = every row as
# expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
TW=$W/third-workspace
mkdir -p "$D/req"
rows=$D/transclusion-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

run() { # NAME cmd...
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
host_refused() {
  [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG\|host refused\|host returned refused\|refused" "$D/$1.err"
}
retained_outcome() { # NAME -> phase/detail of a retained refused outcome, if any
  local dir; dir=$(grep -o 'workspace attempt: .*' "$D/$1.err" | tail -1 | cut -d' ' -f3)
  [ -n "$dir" ] && [ -f "$dir/outcome.json" ] || return 0
  printf 'outcome %s phase %s: %s' "$(jq -r .type "$dir/outcome.json")" \
    "$(jq -r .phase "$dir/outcome.json" | xxd -r -p)" "$(jq -r .detail "$dir/outcome.json" | xxd -r -p)"
}
refusal_text() {
  { retained_outcome "$1"; echo; grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' '; tail -1 "$D/$1.err"; } | tr '\n' ' ' | cut -c1-300
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
read_view() { run "$1" "$MINI" workspace --action read --dir "$2" --name "$3"; }
atom() { jq -c --arg a "$2" '.cell.entries[] | select(.type == "atom" and .id == $a)' "$D/$1.out"; }
invoke() { # NAME WS TARGETS-JSON  (propose + submit)
  local name=$1 ws=$2 targets=$3
  jq -n --argjson t "$targets" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:$t}' >"$D/req/$name.json"
  run "$name-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$name.json" --proposal-id "$name"
  if [ "$(cat "$D/$name-propose.rc")" != 0 ]; then cp "$D/$name-propose.rc" "$D/$name.rc"
    cp "$D/$name-propose.err" "$D/$name.err"; : >"$D/$name.out"; return; fi
  run "$name" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/$name/intent.json" --attempt "$ws/attempts/$name"
}
content() { jq -n --arg r "$1" --argjson a "$2" '[{name:$r,payload:{type:"content",actions:$a}}]'; }
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
show() { run "$1" "$MINI" workspace --action transclusions --dir "$2" --name page; }
follow() { run "$1" "$MINI" workspace --action follow --dir "$2" --name page --transclusion "$3"; }
render() { # NAME ID -> "view:lines(hex, comma):revised[:at]"
  jq -r --arg id "$2" '.transclusions[] | select(.id == $id) | .render
    | .view + ":" + ((.lines // []) | join(",")) + ":" + ((.revised // "") | tostring)' "$D/$1.out"
}
transcluded_id() { grep -o 'workspace transclusion: [0-9]*' "$D/$1.err" | tail -1 | cut -d' ' -f3; }
edit_line() { # NAME N PAYLOAD-HEX TOMBSTONE
  read_view "$1-read" "$SPONSOR_WS" wall; ok "$1-read"
  local before; before=$(atom "$1-read" "$((1000 + $2))" | jq -c 'del(.type,.id,.canonical)')
  invoke "$1" "$SPONSOR_WS" "$(content wall "$(jq -n --argjson b "$before" --arg a "$((1000 + $2))" --arg p "$3" \
    --argjson t "$4" '[{type:"editAtom",atom:$a,before:$b,kind:{type:"text"},payload:$p,tombstone:$t}]')")"
}

R_SUBJECT=$NEWCOMER_SUBJECT
B_SUBJECT=$(jq -r .subject "$TW/workspace.json" 2>/dev/null || true)
[ -n "$B_SUBJECT" ] && [ "$B_SUBJECT" != null ] || B_SUBJECT=$(jq -r .subject "$JOURNEY_RUN/steps/J5/submit.out")
C_SUBJECT=$(enroll tcarol); CW=$W/tcarol-workspace
D_SUBJECT=$(enroll tdave); DW=$W/tdave-workspace

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create-wall "$MINI" workspace --action create --dir "$SPONSOR_WS" --name wall --storage content \
  --predicate "$D/req/permit-all.json"; ok create-wall
run create-page "$MINI" workspace --action create --dir "$SPONSOR_WS" --name page --storage content \
  --predicate "$D/req/permit-all.json"; ok create-page
wall=$(jq -r .target "$SPONSOR_WS/refs/wall.json")
for n in 1 2 3 4 5; do eval "L$n=\$(hexof 'wall line $n')"; done
L3b=$(hexof 'wall line 3, revised'); L1b=$(hexof 'wall line 1, revised')
invoke a-writes-wall "$SPONSOR_WS" "$(content wall "$(jq -n --arg l1 "$L1" --arg l2 "$L2" --arg l3 "$L3" \
  --arg l4 "$L4" --arg l5 "$L5" '[
  {type:"createDocument",rootElement:"1",schema:"0",body:{type:"runs",runs:["2000"]}},
  {type:"createAtom",atom:"1001",kind:{type:"text"},payload:$l1},
  {type:"createAtom",atom:"1002",kind:{type:"text"},payload:$l2},
  {type:"createAtom",atom:"1003",kind:{type:"text"},payload:$l3},
  {type:"createAtom",atom:"1004",kind:{type:"text"},payload:$l4},
  {type:"createAtom",atom:"1005",kind:{type:"text"},payload:$l5},
  {type:"createRun",run:"2000",atoms:["1001","1002","1003","1004","1005"]}]')")"; ok a-writes-wall
invoke a-writes-page "$SPONSOR_WS" "$(content page '[{"type":"createDocument","rootElement":"1","schema":"0","body":{"type":"runs","runs":[]}}]')"
ok a-writes-page

delegate grant-c-wall "$SPONSOR_WS" wall "$C_SUBJECT" '["observe"]' "$CW" wall
delegate grant-c-page "$SPONSOR_WS" page "$C_SUBJECT" '["observe","mutate"]' "$CW" page
delegate grant-r-wall "$SPONSOR_WS" wall "$R_SUBJECT" '["observe"]' "$NEWCOMER_WS" wall
delegate grant-r-page "$SPONSOR_WS" page "$R_SUBJECT" '["observe"]' "$NEWCOMER_WS" page
delegate grant-d-page "$SPONSOR_WS" page "$D_SUBJECT" '["observe"]' "$DW" page
delegate grant-b-page "$SPONSOR_WS" page "$B_SUBJECT" '["observe","mutate"]' "$TW" tpage
# D and B hold a reference naming wall, but only with their page capability.
run d-import-wall "$MINI" workspace --action import --dir "$DW" --name wall --kind object \
  --target "$wall" --observe-capability "$(jq -r .observeCapability "$DW/refs/page.json")"; ok d-import-wall
run b-import-wall "$MINI" workspace --action import --dir "$TW" --name twall --kind object \
  --target "$wall" --observe-capability "$(jq -r .observeCapability "$TW/refs/tpage.json")"; ok b-import-wall

# C transcludes w2..w4 three ways, each a two-target transaction (page + a read of wall).
run c-transcludes-snapshot "$MINI" workspace --action transclude --dir "$CW" --name page --source wall \
  --from 1002 --to 1004 --mode snapshot --death keepTombstone
row c-transcludes-snapshot installed "$(outcome c-transcludes-snapshot)" "$(detail c-transcludes-snapshot)"
T1=$(transcluded_id c-transcludes-snapshot)
run c-transcludes-live "$MINI" workspace --action transclude --dir "$CW" --name page --source wall \
  --from 1002 --to 1004 --mode live --death preferNext
T2=$(transcluded_id c-transcludes-live)
run c-transcludes-live-inv "$MINI" workspace --action transclude --dir "$CW" --name page --source wall \
  --from 1002 --to 1004 --mode live --death invalidate
T3=$(transcluded_id c-transcludes-live-inv)
row c-transcludes-live "installed installed" "$(outcome c-transcludes-live) $(outcome c-transcludes-live-inv)" \
  "T2=$T2 T3=$T3 $(detail c-transcludes-live-inv)"

read_view a-read-page "$SPONSOR_WS" page; ok a-read-page
nt=$(jq '[.cell.entries[] | select(.type == "transclusion")] | length' "$D/a-read-page.out")
nl=$(jq '[.cell.entries[] | select(.type == "link")] | length' "$D/a-read-page.out")
row page-records 3/3 "$nt/$nl" "transclusion records / links in page"
H=$(jq -r --arg id "$T1" '.cell.entries[] | select(.type == "transclusion" and .id == $id) | .opening.height' "$D/a-read-page.out")
leak=absent; for l in "$L2" "$L3" "$L4"; do grep -q "$l" "$D/a-read-page.out" && leak=present; done
row page-holds-no-bytes absent "$leak" "no wall line's bytes in page's own view; T1 opened at height $H"

show r-sees-inline "$NEWCOMER_WS"; ok r-sees-inline
row r-sees-inline "snapshot:$L2,$L3,$L4:" "$(render r-sees-inline "$T1")" "T1 over R's own read of wall"
show d-sees-placeholder "$DW"; ok d-sees-placeholder
row d-sees-placeholder "unavailable,unavailable,unavailable" \
  "$(jq -r '[.transclusions[].render.view] | join(",")' "$D/d-sees-placeholder.out")" "D holds no read of wall"
row d-placeholder-text "[transclusion: 3 atoms of $wall, not readable by you]" \
  "$(jq -r --arg id "$T1" '.transclusions[] | select(.id == $id) | .text' "$D/d-sees-placeholder.out")" "T1 as D sees it"

run b-cannot-transclude "$MINI" workspace --action transclude --dir "$TW" --name tpage --source twall \
  --from 1002 --to 1004 --mode snapshot
row b-cannot-transclude refused "$(outcome b-cannot-transclude)" "$(detail b-cannot-transclude)"

read_view c-read-wall "$CW" wall; ok c-read-wall
rev2=$(atom c-read-wall 1002 | jq -r .revision); rev3=$(atom c-read-wall 1003 | jq -r .revision)
rev4=$(atom c-read-wall 1004 | jq -r .revision)
request() { # PIN3-REVISION
  jq -n --arg w "$wall" --arg r2 "$rev2" --arg r3 "$1" --arg r4 "$rev4" '{source:$w,
    range:{start:{run:"2000",neighbor:"1002",bias:"before",death:"keepTombstone"},
           finish:{run:"2000",neighbor:"1004",bias:"after",death:"keepTombstone"}},
    mode:"snapshot",pins:[{atom:"1002",revision:$r2},{atom:"1003",revision:$r3},{atom:"1004",revision:$r4}]}'
}
invoke c-no-read-refused "$CW" "$(content page "$(jq -n --argjson q "$(request "$rev3")" \
  '[{type:"transclude",transclusion:"5001",link:"5002",request:$q}]')")"
row c-no-read-refused refused "$(outcome c-no-read-refused)" "$(detail c-no-read-refused)"
# Every wall line was written by one operation, so they share a revision: the
# forged pin names an operation that never wrote w3.
invoke c-stale-opening-refused "$CW" "$(jq -n --argjson q "$(request 1)" \
  '[{name:"page",payload:{type:"content",actions:[{type:"transclude",transclusion:"5003",link:"5004",request:$q}]}},
    {name:"wall",payload:{type:"read"}}]')"
row c-stale-opening-refused refused "$(outcome c-stale-opening-refused)" "$(detail c-stale-opening-refused)"

edit_line a-edits-inside 3 "$L3b" false
row a-edits-inside installed "$(outcome a-edits-inside)" "$(detail a-edits-inside)"
show r-after-inside "$NEWCOMER_WS"; ok r-after-inside
row inside-snapshot "snapshot:$L2,$L3,$L4::$H" "$(render r-after-inside "$T1"):$(jq -r --arg id "$T1" \
  '.transclusions[] | select(.id == $id) | .at // ""' "$D/r-after-inside.out")" "T1, re-read at its opening height"
row inside-live "live:$L2,$L3b,$L4:true" "$(render r-after-inside "$T2")" "T2 after the inside edit"

edit_line a-edits-outside 1 "$L1b" false
row a-edits-outside installed "$(outcome a-edits-outside)" "$(detail a-edits-outside)"
show r-after-outside "$NEWCOMER_WS"; ok r-after-outside
same=unchanged
for t in "$T1" "$T2" "$T3"; do
  [ "$(render r-after-inside "$t")" = "$(render r-after-outside "$t")" ] || same=changed
done
row outside-unchanged unchanged "$same" "T1 T2 T3 renderings before and after A's edit of w1"

edit_line a-deletes-endpoint 4 "$L4" true
row a-deletes-endpoint installed "$(outcome a-deletes-endpoint)" "$(detail a-deletes-endpoint)"
show r-after-death "$NEWCOMER_WS"; ok r-after-death
row death-invalidate "invalidated::" "$(render r-after-death "$T3")" "T3, finish dead under invalidate"
row death-prefer-next "live:$L2,$L3b,$L5:true" "$(render r-after-death "$T2")" "T2, finish moved to w5 under preferNext"
row death-snapshot-pinned "snapshot:$L2,$L3,$L4:" "$(render r-after-death "$T1")" "T1 after the endpoint died"

follow r-follows-live "$NEWCOMER_WS" "$T2"
row r-follows-live "live:$L2,$L3b,$L5:true" "$( [ "$(cat "$D/r-follows-live.rc")" = 0 ] && render r-follows-live "$T2")" \
  "R re-resolves T2 at the current height"
follow d-follow-refused "$DW" "$T2"
row d-follow-refused refused "$( [ "$(cat "$D/d-follow-refused.rc")" != 0 ] && grep -q 'follow refused' "$D/d-follow-refused.err" \
  && echo refused || echo "rc=$(cat "$D/d-follow-refused.rc")")" "$(tail -1 "$D/d-follow-refused.err" | cut -c1-200)"

# Restart: stop the journey's service and start it again on the same Store; R renders again.
pid=$(cat "$W/public/server.pid")
case "$(ps -o args= -p "$pid" 2>/dev/null)" in *" serve "*"--socket $SOCKET"*) ;; *) echo "server $pid is not ours" >&2; exit 1;; esac
kill -TERM "$pid"; for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-k12t.log" 2>&1 </dev/null &
echo $! >"$W/public/server.pid"
for i in $(seq 1 600); do grep -q serving "$W/public/serve-k12t.log" 2>/dev/null && [ -S "$SOCKET" ] && break; sleep 0.1; done
show r-after-restart "$NEWCOMER_WS"; ok r-after-restart
before=$(jq -c '[.transclusions[] | {id, render, at}]' "$D/r-after-death.out")
after=$(jq -c '[.transclusions[] | {id, render, at}]' "$D/r-after-restart.out")
row restart-identical identical "$([ "$before" = "$after" ] && echo identical || echo differs)" "R's three renderings across a restart"

run audit "$HOST" "$CONFIG" audit
row audit re-admitted "$(grep -q "every signed ingress re-admitted" "$D/audit.out" && echo re-admitted || echo "rc=$(cat "$D/audit.rc")")" "$(head -1 "$D/audit.out"; tail -1 "$D/audit.err")"

cat "$rows" >&2
total=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $total transclusion rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$total/$total transclusion rows as expected: disclosure checked at transclusion time, snapshot pinned (read at its height), live follows the range, endpoint death by policy, no bytes in the host" >&2
echo "$rows"
