#!/usr/bin/env bash
# journey.d/j12m.sh — marks on lines (K-MARKS), on the journey's fresh Store,
# after J5 (and after K12C/K12T/K12E/K12I when they ran: proposal ids are `m-`).
#
# Parties: A = sponsor (owns `mpaper`, four lines, and `mtarget`, one line);
# R = the newcomer, a reviewer holding observe+mutate on mpaper under mpaper's
# law "R writes no body record" (K-FIELDS' `fields = {annotations}` is not on
# this tree; the law is the same footprint: a mark is the annotations field).
# Rows:
#   a-bolds-line2          A: `mark --line 2 --kind bold`                    -> installed
#   a-links-line3          A: a link mark on line 3 to mtarget               -> installed
#   backlink-shows-mark    mtarget's doc-backlinks: mpaper's mark link, relation != 0 -> present
#   r-marks-line1          R (reviewer) marks line 1 italic                  -> installed
#   r-edits-line1          R edits line 1 (same grant; law: no body)         -> refused
#   rendered               doc-show lines 1..3                               -> _one_|**two**|[three](→ mtarget)
#   unknown-kind           `mark --kind underline`                           -> client-error:unknownKind
#   no-such-target         a mark on atom 999999 (no such line)              -> refused:noSuchTarget
#   a-edits-line2          A edits line 2                                    -> installed
#   stale-in-view          line 2's bold mark after the edit                 -> fresh=false, ~~**two'**~~
#   stale-mark-refused     a mark of line 2 at its old revision              -> refused:staleMark
#   a-remarks-line2        A marks line 2 bold again (the revision it reads) -> installed; fresh=1 stale=1; **two'**
#   r-unmarks-a-link       R unmarks A's link mark (neither author nor owner) -> refused:notMarkOwner
#   r-unmarks-own          R unmarks its own italic mark (author, not owner)  -> installed
#   a-unmarks-link         A unmarks its link mark                           -> installed
#   backlink-gone          mtarget's backlinks; lines 1..3 rendered          -> absent; one|**two'**|three
#   fifty-marks            A lays 50 marks on line 4 in one command          -> installed; 50 live marks
#   restart-identical      stop and restart the service; A's doc show        -> identical
#   audit                  Host audit re-admits every accepted record        -> re-admitted
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS NEWCOMER_WS
# NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Exit 0 = every row as
# expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
mkdir -p "$D/req"
rows=$D/mark-rows.tsv
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
refused_by() {
  if [ "$(outcome "$1")" = refused ] && refusal_text "$1" | grep -q "Reject.$2"; then echo "refused:$2"
  else echo "$(outcome "$1")"; fi
}
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -3 "$D/$1.err")" >&2; exit 1; }; }
invoke() { # NAME WS RESOURCE ACTIONS-JSON
  local name=$1 ws=$2 res=$3 actions=$4
  jq -n --arg r "$res" --argjson a "$actions" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$r,payload:{type:"content",actions:$a}}]}' \
    >"$D/req/$name.json"
  run "$name-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$name.json" --proposal-id "m-$name"
  if [ "$(cat "$D/$name-propose.rc")" != 0 ]; then cp "$D/$name-propose.rc" "$D/$name.rc"
    cp "$D/$name-propose.err" "$D/$name.err"; : >"$D/$name.out"; return; fi
  run "$name" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/m-$name/intent.json" --attempt "$ws/attempts/m-$name"
}
delegate() { # NAME FROM-WS RESOURCE RECIPIENT-SUBJECT VERBS-JSON TO-WS LOCALNAME
  jq -n --arg n "$3" --arg r "$4" --argjson v "$5" \
    '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,recipient:$r,verbs:$v,maxCost:"50000"}' \
    >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$2" --request "$D/req/$1.json" --proposal-id "m-$1"; ok "$1-propose"
  run "$1-submit" "$MINI" workspace --action submit --dir "$2" \
    --intent "$2/proposals/m-$1/intent.json" --attempt "$2/attempts/m-$1"; ok "$1-submit"
  run "$1-publish" "$MINI" workspace --action publish-delegation --dir "$2" --proposal-id "m-$1" \
    --attempt "$2/attempts/m-$1"; ok "$1-publish"
  run "$1-import" "$MINI" workspace --action import --dir "$6" --name "$7" \
    --from-ref "$2/proposals/m-$1/recipient-reference.json"; ok "$1-import"
}
hexof() { printf '%s' "$1" | xxd -p | tr -d '\n'; }
show() { run "$1" "$MINI" workspace --action doc-show --dir "$2" --name "$3" --format json; }
mark() { local name=$1 ws=$2; shift 2; run "$name" "$MINI" workspace --action mark --dir "$ws" --name mpaper "$@"; }
unmark() { local name=$1 ws=$2; shift 2; run "$name" "$MINI" workspace --action unmark --dir "$ws" --name mpaper "$@"; }
line() { jq -c --argjson n "$2" '.lines[] | select(.line == $n)' "$D/$1.out"; }
rendered_of() { jq -r '[.lines[] | select(.line != null and .line <= 3) | .rendered] | join("|")' "$D/$1.out"; }
read_view() { run "$1" "$MINI" workspace --action read --dir "$2" --name "$3"; }
atom() { jq -c --arg a "$2" '.cell.entries[] | select(.type == "atom" and .id == $a)' "$D/$1.out"; }
before_of() { atom "$1" "$2" | jq -c 'del(.type,.id,.canonical)'; }
edit_json() { # BEFORE-JSON ATOM PAYLOAD-HEX
  jq -n --argjson b "$1" --arg a "$2" --arg p "$3" \
    '[{type:"editAtom",atom:$a,before:$b,kind:{type:"text"},payload:$p,tombstone:false}]'
}
backlink_row() { grep " link $2 relation " "$D/$1.out" | head -1; }

R_SUBJECT=$NEWCOMER_SUBJECT

# mpaper's law: a mutation by R writes no body record (reads, delegations, installs pass).
jq -n --arg r "$R_SUBJECT" '{type:"any",predicates:[
  {type:"not",predicate:{type:"eq",slot:"request/verb",value:"2"}},
  {type:"not",predicate:{type:"eq",slot:"request/subject",value:$r}},
  {type:"eq",slot:"content/writes/body",value:"0"}]}' >"$D/req/mpaper-law.json"
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create-mpaper "$MINI" workspace --action create --dir "$SPONSOR_WS" --name mpaper --storage content \
  --predicate "$D/req/mpaper-law.json"; ok create-mpaper
run create-mtarget "$MINI" workspace --action create --dir "$SPONSOR_WS" --name mtarget --storage content \
  --predicate "$D/req/permit-all.json"; ok create-mtarget

invoke a-writes "$SPONSOR_WS" mpaper "$(jq -n --arg a "$(hexof one)" --arg b "$(hexof two)" \
  --arg c "$(hexof three)" --arg d "$(hexof four)" '[
  {type:"createDocument",rootElement:"6100",schema:"0"},
  {type:"createAtom",atom:"6101",kind:{type:"text"},payload:$a},
  {type:"createAtom",atom:"6102",kind:{type:"text"},payload:$b},
  {type:"createAtom",atom:"6103",kind:{type:"text"},payload:$c},
  {type:"createAtom",atom:"6104",kind:{type:"text"},payload:$d}]')"; ok a-writes
invoke a-writes-target "$SPONSOR_WS" mtarget "$(jq -n --arg a "$(hexof 'the target')" '[
  {type:"createDocument",rootElement:"6200",schema:"0"},
  {type:"createAtom",atom:"6201",kind:{type:"text"},payload:$a}]')"; ok a-writes-target
delegate grant-r "$SPONSOR_WS" mpaper "$R_SUBJECT" '["observe","mutate"]' "$NEWCOMER_WS" mpaper

# --- A: bold line 2, a link mark on line 3 -> mtarget's backlinks show it ---
mark a-bolds-line2 "$SPONSOR_WS" --line 2 --kind bold
row a-bolds-line2 installed "$(outcome a-bolds-line2)" "$(detail a-bolds-line2)"
mark a-links-line3 "$SPONSOR_WS" --line 3 --kind link --to mtarget
row a-links-line3 installed "$(outcome a-links-line3)" "$(detail a-links-line3)"
LINK=$(grep -o 'workspace mark link: [0-9]*' "$D/a-links-line3.err" | tail -1 | cut -d' ' -f4)
LINKMARK=$(grep -o 'workspace mark: [0-9]*' "$D/a-links-line3.err" | tail -1 | cut -d' ' -f3)
run backlinks1 "$MINI" workspace --action doc-backlinks --dir "$SPONSOR_WS" --name mtarget; ok backlinks1
b=$(backlink_row backlinks1 "$LINK"); rel=$(echo "$b" | awk '{print $5}')
row backlink-shows-mark present "$([ -n "$b" ] && [ "$(echo "$b" | awk '{print $1}')" = mpaper ] && [ -n "$rel" ] && [ "$rel" != 0 ] && echo present || echo absent)" \
  "row: $b"

# --- R, the reviewer: may mark, may not edit ---
mark r-marks-line1 "$NEWCOMER_WS" --line 1 --kind italic
row r-marks-line1 installed "$(outcome r-marks-line1)" "$(detail r-marks-line1)"
RMARK=$(grep -o 'workspace mark: [0-9]*' "$D/r-marks-line1.err" | tail -1 | cut -d' ' -f3)
read_view r-read1 "$NEWCOMER_WS" mpaper; ok r-read1
invoke r-edits-line1 "$NEWCOMER_WS" mpaper "$(edit_json "$(before_of r-read1 6101)" 6101 "$(hexof "one'")")"
row r-edits-line1 refused "$(outcome r-edits-line1)" "$(detail r-edits-line1); the same grant installed r-marks-line1"

show show1 "$SPONSOR_WS" mpaper; ok show1
row rendered "_one_|**two**|[three](→ mtarget)" "$(rendered_of show1)" "$(jq -r .text "$D/show1.out" | tr '\n' '/')"

# --- refusals by name ---
rev2=$(line show1 2 | jq -r .revision)
# An unknown kind is refused by name before anything is sent.  (The Host's
# draft parser refuses it too -- `unknownKind: ...` -- but on this tree a
# malformed draft still ends the shared session: cv 01a0f65d-f8a3, fixed on
# branch host-malformed 4c5c58a3; the Host-side row belongs after that merge.)
mark unknown-kind "$SPONSOR_WS" --line 2 --kind underline
row unknown-kind client-error:unknownKind \
  "$(outcome unknown-kind):$(grep -q unknownKind "$D/unknown-kind.err" && echo unknownKind || echo other)" \
  "$(tail -1 "$D/unknown-kind.err" | cut -c1-200)"
invoke no-such-target "$SPONSOR_WS" mpaper "$(jq -n --arg rv "$rev2" \
  '[{type:"mark",mark:"6302",target:{type:"atom",atom:"999999"},revision:$rv,kind:{type:"bold"}}]')"
row no-such-target refused:noSuchTarget "$(refused_by no-such-target noSuchTarget)" "$(detail no-such-target)"

# --- A edits line 2: the bold mark is stale, shown struck; a mark at the old revision is refused ---
read_view a-read1 "$SPONSOR_WS" mpaper; ok a-read1
invoke a-edits-line2 "$SPONSOR_WS" mpaper "$(edit_json "$(before_of a-read1 6102)" 6102 "$(hexof "two'")")"
row a-edits-line2 installed "$(outcome a-edits-line2)" "$(detail a-edits-line2)"
show show2 "$SPONSOR_WS" mpaper; ok show2
got="fresh=$(line show2 2 | jq -r '.marks[0].fresh'),$(line show2 2 | jq -r .rendered)"
row stale-in-view "fresh=false,~~**two'**~~" "$got" "line 2 marks: $(line show2 2 | jq -c '[.marks[] | {kind, fresh}]')"
invoke stale-mark-refused "$SPONSOR_WS" mpaper "$(jq -n --arg rv "$rev2" \
  '[{type:"mark",mark:"6303",target:{type:"atom",atom:"6102"},revision:$rv,kind:{type:"bold"}}]')"
row stale-mark-refused refused:staleMark "$(refused_by stale-mark-refused staleMark)" "$(detail stale-mark-refused)"
mark a-remarks-line2 "$SPONSOR_WS" --line 2 --kind bold
show show3 "$SPONSOR_WS" mpaper; ok show3
got="$(outcome a-remarks-line2);fresh=$(line show3 2 | jq '[.marks[] | select(.fresh)] | length') stale=$(line show3 2 | jq '[.marks[] | select(.fresh | not)] | length')"
got="$got;$(line show3 2 | jq -r .rendered)"
row a-remarks-line2 "installed;fresh=1 stale=1;**two'**" "$got" "a fresh mark of a kind outranks a stale one of it"

# --- unmark: author or owner only; the link goes with the mark ---
unmark r-unmarks-a-link "$NEWCOMER_WS" --mark "$LINKMARK"
row r-unmarks-a-link refused:notMarkOwner "$(refused_by r-unmarks-a-link notMarkOwner)" "$(detail r-unmarks-a-link)"
unmark r-unmarks-own "$NEWCOMER_WS" --mark "$RMARK"
row r-unmarks-own installed "$(outcome r-unmarks-own)" "$(detail r-unmarks-own)"
unmark a-unmarks-link "$SPONSOR_WS" --line 3 --kind link
row a-unmarks-link installed "$(outcome a-unmarks-link)" "$(detail a-unmarks-link)"
run backlinks2 "$MINI" workspace --action doc-backlinks --dir "$SPONSOR_WS" --name mtarget; ok backlinks2
show show4 "$SPONSOR_WS" mpaper; ok show4
got="$([ -z "$(backlink_row backlinks2 "$LINK")" ] && echo absent || echo present);$(rendered_of show4)"
row backlink-gone "absent;one|**two'**|three" "$got" \
  "$(tail -1 "$D/backlinks2.out"); line 2 $(line show4 2 | jq -r .rendered)"

# --- fifty marks on one line, one command ---
rev4=$(line show4 4 | jq -r .revision)
fifty=$(jq -n --arg rv "$rev4" '[range(0;50) | {type:"mark",mark:(6400 + . | tostring),
  target:{type:"atom",atom:"6104"},revision:$rv,kind:{type:(["bold","italic","code","heading"][. % 4])}}]')
invoke fifty-marks "$SPONSOR_WS" mpaper "$fifty"
show show5 "$SPONSOR_WS" mpaper; ok show5
row fifty-marks "installed;50;# **_\`four\`_**" "$(outcome fifty-marks);$(line show5 4 | jq '.marks | length');$(line show5 4 | jq -r .rendered)" \
  "$(detail fifty-marks)"

# --- restart and audit ---
pid=$(cat "$W/public/server.pid")
case "$(ps -o args= -p "$pid" 2>/dev/null)" in *" serve "*"--socket $SOCKET"*) ;; *) echo "server $pid is not ours" >&2; exit 1;; esac
kill -TERM "$pid"; for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-k12m.log" 2>&1 </dev/null &
echo $! >"$W/public/server.pid"
for i in $(seq 1 600); do grep -q serving "$W/public/serve-k12m.log" 2>/dev/null && [ -S "$SOCKET" ] && break; sleep 0.1; done
show show6 "$SPONSOR_WS" mpaper; ok show6
before=$(jq -c '[.lines[] | {element, line, kind, text, rendered, marks}]' "$D/show5.out")
after=$(jq -c '[.lines[] | {element, line, kind, text, rendered, marks}]' "$D/show6.out")
row restart-identical identical "$([ "$before" = "$after" ] && echo identical || echo differs)" "A's doc show, marks included, across a restart"

run audit "$HOST" "$CONFIG" audit
row audit re-admitted "$(grep -q "every signed ingress re-admitted" "$D/audit.out" && echo re-admitted || echo "rc=$(cat "$D/audit.rc")")" "$(head -1 "$D/audit.out"; tail -1 "$D/audit.err")"

cat "$rows" >&2
total=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $total mark rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$total/$total mark rows as expected: marks laid by revision, stale after edit and shown struck, a link mark is a backlink, a reviewer marks and cannot edit, unmark by author or owner only" >&2
echo "$rows"
