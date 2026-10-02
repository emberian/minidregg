#!/usr/bin/env bash
# journey.d/j12r.sh — the rendered document (P-DOC-RENDER), on the journey's
# fresh Store, after J5 (proposal ids are `rr-`).
#
# Parties: A = sponsor (owns `rpaper`, `rsrc` the transcluded source, and
# `rtarget` a link mark's target); R = the newcomer, observe+mutate on rpaper
# and nothing on rsrc: a reader who does not cover the transclusion's source.
# rpaper is built as: a heading, bold / italic / code lines, a link mark to
# rtarget, one struck line, a snapshot transclusion of rsrc lines 2..3 placed
# at line 6, and a line whose bold mark went stale when the line was edited.
# A annotates line 2; R annotates line 5.
# Rows:
#   golden            A's `doc-show` (text) vs journey.d/j12r.golden.txt, byte for byte,
#                     after substituting R's subject and the snapshot height  -> identical
#   raw-is-the-atoms  `--format raw` vs the live atoms' bytes, one per line  -> identical
#   json-rendered     `--format json` lines[].rendered agree with the text   -> agree
#   outline           `doc-outline`                                         -> "  1  Docuverse"
#   html              `--format html`: heading, strong, em, code, link, del, blockquote, aside -> all present
#   reader-placeholder R's doc-show line 6                                  -> [transclusion: 2 atoms of doc:<rsrc>, not readable by you]
#   reader-no-bytes   R's doc-show holds no line of rsrc                     -> absent
#   backlink-context  rtarget's doc-backlinks: the referencing line rendered -> "line 5: [see the target](→ rtarget)"
#   restart-identical stop and restart the service; A's doc-show             -> identical
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS NEWCOMER_WS
# NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Exit 0 = every row as
# expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$D/req"
rows=$D/render-rows.tsv
: >"$rows"
bad=0

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
row() { printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"; [ "$2" = "$3" ] || bad=$((bad + 1)); }
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -3 "$D/$1.err")" >&2; exit 1; }; }
invoke() { # NAME WS RESOURCE ACTIONS-JSON
  local name=$1 ws=$2 res=$3 actions=$4
  jq -n --arg r "$res" --argjson a "$actions" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$r,payload:{type:"content",actions:$a}}]}' \
    >"$D/req/$name.json"
  run "$name-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$name.json" --proposal-id "rr-$name"
  ok "$name-propose"
  run "$name" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/rr-$name/intent.json" --attempt "$ws/attempts/rr-$name"
}
delegate() { # NAME FROM-WS RESOURCE RECIPIENT-SUBJECT VERBS-JSON TO-WS LOCALNAME
  jq -n --arg n "$3" --arg r "$4" --argjson v "$5" \
    '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,recipient:$r,verbs:$v,maxCost:"50000"}' \
    >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$2" --request "$D/req/$1.json" --proposal-id "rr-$1"; ok "$1-propose"
  run "$1-submit" "$MINI" workspace --action submit --dir "$2" \
    --intent "$2/proposals/rr-$1/intent.json" --attempt "$2/attempts/rr-$1"; ok "$1-submit"
  run "$1-publish" "$MINI" workspace --action publish-delegation --dir "$2" --proposal-id "rr-$1" \
    --attempt "$2/attempts/rr-$1"; ok "$1-publish"
  run "$1-import" "$MINI" workspace --action import --dir "$6" --name "$7" \
    --from-ref "$2/proposals/rr-$1/recipient-reference.json"; ok "$1-import"
}
hexof() { printf '%s' "$1" | xxd -p | tr -d '\n'; }
show() { local name=$1 ws=$2; shift 2; run "$name" "$MINI" workspace --action doc-show --dir "$ws" --name rpaper "$@"; }
mark() { local name=$1; shift; run "$name" "$MINI" workspace --action mark --dir "$SPONSOR_WS" --name rpaper "$@"; ok "$name"; }
read_view() { run "$1" "$MINI" workspace --action read --dir "$2" --name "$3"; ok "$1"; }
atom() { jq -c --arg a "$2" '.cell.entries[] | select(.type == "atom" and .id == $a)' "$D/$1.out"; }
before_of() { atom "$1" "$2" | jq -c 'del(.type,.id,.canonical)'; }
edit() { # NAME ATOM PAYLOAD-HEX TOMBSTONE
  read_view "$1-read" "$SPONSOR_WS" rpaper
  invoke "$1" "$SPONSOR_WS" rpaper "$(jq -n --argjson b "$(before_of "$1-read" "$2")" --arg a "$2" --arg p "$3" \
    --argjson t "$4" '[{type:"editAtom",atom:$a,before:$b,kind:{type:"text"},payload:$p,tombstone:$t}]')"
  ok "$1"
}
annotate() { # NAME WS ATOM ID TEXT
  read_view "$1-read" "$2" rpaper
  invoke "$1" "$2" rpaper "$(jq -n --arg rv "$(atom "$1-read" "$3" | jq -r .revision)" --arg a "$3" --arg id "$4" \
    --arg b "$(hexof "$5")" '[{type:"annotate",annotation:$id,atom:$a,revision:$rv,body:$b}]')"
  ok "$1"
}

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
for doc in rpaper rsrc rtarget; do
  run "create-$doc" "$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$doc" --storage content \
    --predicate "$D/req/permit-all.json"; ok "create-$doc"
done
invoke a-writes-src "$SPONSOR_WS" rsrc "$(jq -n --arg a "$(hexof 'source one')" --arg b "$(hexof 'source two')" \
  --arg c "$(hexof 'source three')" --arg d "$(hexof 'source four')" '[
  {type:"createDocument",rootElement:"8200",schema:"0"},
  {type:"createAtom",atom:"8201",kind:{type:"text"},payload:$a},
  {type:"createAtom",atom:"8202",kind:{type:"text"},payload:$b},
  {type:"createAtom",atom:"8203",kind:{type:"text"},payload:$c},
  {type:"createAtom",atom:"8204",kind:{type:"text"},payload:$d},
  {type:"createRun",run:"8250",atoms:["8201","8202","8203","8204"]}]')"; ok a-writes-src
invoke a-writes-target "$SPONSOR_WS" rtarget "$(jq -n --arg a "$(hexof 'the target')" '[
  {type:"createDocument",rootElement:"8300",schema:"0"},
  {type:"createAtom",atom:"8301",kind:{type:"text"},payload:$a}]')"; ok a-writes-target
invoke a-writes "$SPONSOR_WS" rpaper "$(jq -n \
  --arg a "$(hexof 'Docuverse')" --arg b "$(hexof 'bold words')" --arg c "$(hexof 'slanted')" \
  --arg d "$(hexof 'mini serve')" --arg e "$(hexof 'see the target')" --arg f "$(hexof 'gone soon')" \
  --arg g "$(hexof 'will change')" '[
  {type:"createDocument",rootElement:"8100",schema:"0"},
  {type:"createAtom",atom:"8101",kind:{type:"text"},payload:$a},
  {type:"createAtom",atom:"8102",kind:{type:"text"},payload:$b},
  {type:"createAtom",atom:"8103",kind:{type:"text"},payload:$c},
  {type:"createAtom",atom:"8104",kind:{type:"text"},payload:$d},
  {type:"createAtom",atom:"8105",kind:{type:"text"},payload:$e},
  {type:"createAtom",atom:"8106",kind:{type:"text"},payload:$f},
  {type:"createAtom",atom:"8107",kind:{type:"text"},payload:$g}]')"; ok a-writes

mark mark-heading --line 1 --kind heading
mark mark-bold --line 2 --kind bold
mark mark-italic --line 3 --kind italic
mark mark-code --line 4 --kind code
mark mark-link --line 5 --kind link --to rtarget
mark mark-stale --line 7 --kind bold
annotate a-annotates-2 "$SPONSOR_WS" 8102 8401 'check this'
edit a-edits-7 8107 "$(hexof changed)" false
edit a-strikes-6 8106 "$(hexof 'gone soon')" true
run transclude "$MINI" workspace --action transclude --dir "$SPONSOR_WS" --name rpaper --source rsrc \
  --from 8202 --to 8203 --mode snapshot --death keepTombstone --at 6; ok transclude
delegate grant-r "$SPONSOR_WS" rpaper "$NEWCOMER_SUBJECT" '["observe","mutate"]' "$NEWCOMER_WS" rpaper
annotate r-annotates-5 "$NEWCOMER_WS" 8105 8402 'who wrote this?'

# --- A's rendering, byte for byte against the golden ---
show a-show "$SPONSOR_WS"; ok a-show
run a-transclusions "$MINI" workspace --action transclusions --dir "$SPONSOR_WS" --name rpaper; ok a-transclusions
H=$(jq -r '.transclusions[0].opening.height' "$D/a-transclusions.out")
sed -e "s/subject $NEWCOMER_SUBJECT /subject <R> /" -e "s/snapshot@$H⟩/snapshot@<H>⟩/" "$D/a-show.out" >"$D/a-show.normalized"
row golden identical "$(cmp -s "$D/a-show.normalized" "$HERE/j12r.golden.txt" && echo identical || echo differs)" \
  "diff: $(diff "$HERE/j12r.golden.txt" "$D/a-show.normalized" | tr '\n' '/' | cut -c1-400) (H=$H)"

# --- raw: the document's own live atoms, exactly ---
show a-raw "$SPONSOR_WS" --format raw; ok a-raw
printf 'Docuverse\nbold words\nslanted\nmini serve\nsee the target\nchanged\n' >"$D/expected.raw"
row raw-is-the-atoms identical "$(cmp -s "$D/a-raw.out" "$D/expected.raw" && echo identical || echo differs)" \
  "$(xxd -p "$D/a-raw.out" | tr -d '\n' | cut -c1-200)"

# --- json: the same rendering, as the struct ---
show a-json "$SPONSOR_WS" --format json; ok a-json
jq -j '.text' "$D/a-json.out" >"$D/a-json.text"
got=$( [ "$(jq -r '[.lines[] | .rendered] | join("|")' "$D/a-json.out")" = \
  "# Docuverse|**bold words**|_slanted_|\`mini serve\`|[see the target](→ rtarget)|~~gone soon~~|⟨from rsrc lines 2..3, snapshot@$H⟩|~~**changed**~~" ] \
  && cmp -s "$D/a-json.text" "$D/a-show.out" && echo agree || echo differ)
row json-rendered agree "$got" "$(jq -r '[.lines[] | .rendered] | join("|")' "$D/a-json.out" | cut -c1-300)"

# --- outline ---
run a-outline "$MINI" workspace --action doc-outline --dir "$SPONSOR_WS" --name rpaper; ok a-outline
row outline "  1  Docuverse" "$(cat "$D/a-outline.out")" "$(wc -l <"$D/a-outline.out") line(s)"

# --- html: the same structure ---
show a-html "$SPONSOR_WS" --format html; ok a-html
missing=""
for needle in 'role="heading" aria-level="1">Docuverse' '<strong>bold words</strong>' '<em>slanted</em>' \
  '<code>mini serve</code>' '<a class="link" data-target="rtarget">see the target</a>' \
  'data-struck="true" data-depth="1"><del>gone soon</del>' '<blockquote class="transclusion snapshot" data-source="rsrc">' \
  '<p class="quoted">source two</p>' '<aside class="annotation fresh" data-annotation=' 'data-fresh="true"><span class="author">you</span> <span class="body">check this</span></aside>' \
  '<s class="stale"><strong>changed</strong></s>'; do
  grep -qF "$needle" "$D/a-html.out" || missing="$missing [$needle]"
done
row html all-present "$([ -z "$missing" ] && echo all-present || echo missing)" "${missing:-every structure present}"

# --- R, who holds no read of rsrc ---
show r-show "$NEWCOMER_WS"; ok r-show
rsrc=$(jq -r .target "$SPONSOR_WS/refs/rsrc.json")
row reader-placeholder "  6  [transclusion: 2 atoms of doc:$rsrc, not readable by you]" "$(grep '^  6  ' "$D/r-show.out")" \
  "R's line 6"
row reader-no-bytes absent "$(grep -q 'source t' "$D/r-show.out" && echo present || echo absent)" "rsrc's lines in R's rendering"

# --- backlinks name the referencing line ---
run backlinks "$MINI" workspace --action doc-backlinks --dir "$SPONSOR_WS" --name rtarget; ok backlinks
row backlink-context "    line 5: [see the target](→ rtarget)" "$(grep '^    line ' "$D/backlinks.out")" \
  "$(head -2 "$D/backlinks.out" | tail -1 | cut -c1-200)"

# --- restart ---
pid=$(cat "$W/public/server.pid")
case "$(ps -o args= -p "$pid" 2>/dev/null)" in *" serve "*"--socket $SOCKET"*) ;; *) echo "server $pid is not ours" >&2; exit 1;; esac
kill -TERM "$pid"; for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-k12r.log" 2>&1 </dev/null &
echo $! >"$W/public/server.pid"
for i in $(seq 1 600); do grep -q serving "$W/public/serve-k12r.log" 2>/dev/null && [ -S "$SOCKET" ] && break; sleep 0.1; done
show a-show-restarted "$SPONSOR_WS"; ok a-show-restarted
row restart-identical identical "$(cmp -s "$D/a-show.out" "$D/a-show-restarted.out" && echo identical || echo differs)" \
  "A's doc show, byte for byte, across a restart"

cat "$rows" >&2
total=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $total render rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$total/$total render rows as expected: doc show matches the golden byte for byte, raw is the atoms, outline, html, a non-covering reader sees the placeholder, backlinks name their line, restart identical" >&2
echo "$rows"
