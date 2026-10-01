#!/usr/bin/env bash
# journey.d/jweb.sh — WEB-ENTRANCE + WEB-2: `mini web`, the read-only loopback
# hypertext face, on the docuverse braid. Runs after K12C (paper, notes, an
# annotation; carol and dave), K12T (wall, page with three transclusions; the
# readers tdave and the late joiner tlate) and K12H (hist, six edits, the third
# key granted after h2).
#
# Every page is a signed read under the serving workspace's own key. A document
# renders through the Host's view-document (the element tree's order,
# transclusions inline over the reader's own source reads); links and backlinks
# are the Host's link-index views; history, a page at a past height and a diff
# are K-DOC-HISTORY's `at`-height reads.
# Rows (expect -> got):
#   c-links-notes-to-paper   C adds a plain link notes -> paper             -> installed
#   a-creates-room           A creates lab, and labnote --in lab            -> installed
#   bind-any-refused         --listen 0.0.0.0:PORT                           -> refused (no listener)
#   bind-lan-refused         --listen <a non-loopback address>               -> refused
#   index-lists-refs         C's / lists C's references                      -> 2
#   doc-lines-match-show     C's /doc/paper rows = `doc-show` lines, in order -> equal
#   doc-text-match           every live line's text appears                  -> equal
#   page-context             subject + height on the page                    -> present
#   annotation-stale         R's annotation 7001 rendered fresh=false        -> false
#   backlinks-from-index     C's /doc/paper backlinks (the link index view)  -> notes:document
#   link-out                 C's /doc/notes links out (the links view)       -> 9101 -> paper
#   doc-page-reads           signed reads one /doc/notes view makes          -> 3 (page, links, backlinks)
#   page-order-equals-show   R's /doc/page element order = R's doc-show       -> equal
#   r-transclusions-inline   R's /doc/page renders                           -> invalidated live snapshot
#   r-snapshot-at-height     T1 shown as read at its opening height          -> present
#   late-joiner-placeholder  tlate's /doc/page renders                       -> invalidated live moved
#   d-placeholders           tdave's /doc/page                               -> unavailable x3
#   d-page-no-bytes          no wall bytes on tdave's page; R's page has them -> absent:present
#   transclusion-backlinks   R's /doc/wall backlinks of kind transclusion    -> 3 (page)
#   d-paper-refused          D's /doc/paper (a reference with no grant)      -> 403 refusal page
#   d-paper-no-bytes         no paper bytes on D's refusal page; C's has them -> absent:present
#   history-matches          A's /doc/hist/history rows = `doc-history` rows -> equal
#   history-split            the third key's history: content from its grant -> false false true true true true
#   at-page-equals-show      A's /at/H4/doc/hist order = `doc-show --at H4`  -> equal
#   at-refused               third key's /at/H2/doc/hist                     -> 403 refusal, did not cover
#   diff-moves               A's /doc/hist/diff/H5/H6                        -> moved 1001, moved 1003
#   foreign-host-refused     Host: evil.example:PORT                         -> 421
#   rebind-host-refused      Host: 127.0.0.1.nip.io:PORT                      -> 421
#   foreign-origin-refused   Origin: http://evil.example                     -> 403
#   post-refused             POST /TOKEN/doc/paper                           -> 405
#   wrong-secret             /WRONG/doc/paper                                -> 404
#   refused-requests-no-reads  signed reads made by the five refused requests -> 0
#   stream-501               /stream/notes (k-stream is not on this braid)   -> 501
#   board-fields             A's /board/shared                               -> fields >= 1
#   room-children            A's /room/lab lists labnote                     -> labnote
#   room-members             A's /room/lab members (the `who` view)          -> A present
#   lynx-dump                lynx -dump of C's /doc/paper (if lynx exists)   -> text
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
CW=$W/carol-workspace
DW=$W/dave-workspace
LW=$W/tlate-workspace
TDW=$W/tdave-workspace
TW=$W/third-workspace
mkdir -p "$D/req" "$D/pages"
rows=$D/web-rows.tsv
: >"$rows"
bad=0
PIDS=()
cleanup() { for pid in "${PIDS[@]}"; do kill "$pid" 2>/dev/null; wait "$pid" 2>/dev/null; done; }
trap cleanup EXIT

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -3 "$D/$1.err")" >&2; exit 1; }; }
row() { printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"; [ "$2" = "$3" ] || bad=$((bad + 1)); }
invoke() { # NAME WS RESOURCE ACTIONS-JSON
  jq -n --arg r "$3" --argjson a "$4" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$r,payload:{type:"content",actions:$a}}]}' >"$D/req/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$2" --request "$D/req/$1.json" --proposal-id "$1"
  [ "$(cat "$D/$1-propose.rc")" = 0 ] || { cp "$D/$1-propose.rc" "$D/$1.rc"; cp "$D/$1-propose.err" "$D/$1.err"; return; }
  run "$1" "$MINI" workspace --action submit --dir "$2" --intent "$2/proposals/$1/intent.json" --attempt "$2/attempts/$1"
}
rc_word() { [ "$(cat "$D/$1.rc")" = 0 ] && echo installed || echo "rc=$(cat "$D/$1.rc"): $(tail -1 "$D/$1.err" | cut -c1-160)"; }
attempts() { find "$1/attempts" -mindepth 1 -maxdepth 1 | wc -l; }
renders() { grep -o 'data-transclusion="[0-9]*" data-mode="[a-z]*" data-render="[a-z]*"' "$D/pages/$1" | grep -o 'render="[a-z]*"' | cut -d'"' -f2 | sort | tr '\n' ' ' | sed 's/ $//'; }
elements() { grep -o '<tr data-element="[0-9]*"' "$D/pages/$1" | cut -d'"' -f2 | tr '\n' ' ' | sed 's/ $//'; }
show_elements() { jq -r '[.lines[].element] | join(" ")' "$D/$1.out"; }

start() { # NAME WS -> sets URL_<NAME> and PORT_<NAME>
  "$MINI" web --dir "$2" --listen 127.0.0.1:0 >"$D/web-$1.out" 2>"$D/web-$1.err" &
  PIDS+=($!)
  local i url
  for i in $(seq 1 100); do
    url=$(grep -o 'http://127\.0\.0\.1:[0-9]*/[0-9a-f]*/' "$D/web-$1.out" 2>/dev/null | head -1)
    [ -n "$url" ] && break
    kill -0 "${PIDS[-1]}" 2>/dev/null || break
    sleep 0.1
  done
  [ -n "$url" ] || { echo "mini web $1 did not start: $(cat "$D/web-$1.err")" >&2; exit 1; }
  printf -v "URL_$1" '%s' "$url"
  printf -v "PORT_$1" '%s' "$(echo "$url" | sed 's|http://127.0.0.1:\([0-9]*\)/.*|\1|')"
}
get() { # FILE URL [curl args...] -> prints the HTTP status
  local file=$1 url=$2; shift 2
  curl -s --max-time 600 -o "$D/pages/$file" -w '%{http_code}' "$@" "$url"
}

paper=$(jq -r .target "$SPONSOR_WS/refs/paper.json")
A_SUBJECT=$(jq -r .subject "$SPONSOR_WS/workspace.json")
# K12H's absolute edit heights (its hook reports them).
read -r H1 H2 H3 H4 H5 H6 < <(sed -n 's/.*edit heights \([0-9 ]*\);.*/\1/p' "$JOURNEY_RUN/steps/K12H/hook.err" | head -1)
[ -n "${H6:-}" ] || { echo "K12H's edit heights not found in its hook.err" >&2; exit 1; }

# Setup: a plain link (C, notes -> paper), a room with one resource born in it
# (A), and D's reference to paper under no grant of its own.
invoke c-links-notes-to-paper "$CW" notes "$(jq -n --arg p "$paper" \
  '[{type:"link",link:"9101",source:null,target:{type:"document",id:$p},relation:"1"}]')"
row c-links-notes-to-paper installed "$(rc_word c-links-notes-to-paper)" "link 9101"
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create-lab "$MINI" workspace --action create --dir "$SPONSOR_WS" --name lab --storage content --predicate "$D/req/permit-all.json"
run create-labnote "$MINI" workspace --action create --dir "$SPONSOR_WS" --name labnote --storage content \
  --predicate "$D/req/permit-all.json" --in lab
row a-creates-room installed "$( [ "$(cat "$D/create-lab.rc")$(cat "$D/create-labnote.rc")" = 00 ] && echo installed || echo "lab rc=$(cat "$D/create-lab.rc") labnote rc=$(cat "$D/create-labnote.rc"): $(tail -1 "$D/create-labnote.err")")" "lab + labnote --in lab"
[ -f "$DW/refs/paper.json" ] || { run d-import-paper "$MINI" workspace --action import --dir "$DW" --name paper --kind object \
  --target "$paper" --observe-capability "$(jq -r .observeCapability "$DW/refs/notes.json")"; ok d-import-paper; }

# Bind refusals: nothing but 127.0.0.1.
run bind-any "$MINI" web --dir "$CW" --listen 0.0.0.0:28431
listening=$(ss -ltnH 'sport = :28431' 2>/dev/null | wc -l)
row bind-any-refused "refused:0" "$( [ "$(cat "$D/bind-any.rc")" != 0 ] && grep -q 'binds 127.0.0.1 only' "$D/bind-any.err" && echo refused || echo bound):$listening" "$(tail -1 "$D/bind-any.err")"
lan=$(hostname -I 2>/dev/null | awk '{print $1}'); lan=${lan:-10.0.0.1}
run bind-lan "$MINI" web --dir "$CW" --listen "$lan:28432"
row bind-lan-refused refused "$( [ "$(cat "$D/bind-lan.rc")" != 0 ] && grep -q 'binds 127.0.0.1 only' "$D/bind-lan.err" && echo refused || echo bound)" "$lan: $(tail -1 "$D/bind-lan.err")"

start C "$CW"; start DV "$DW"; start A "$SPONSOR_WS"; start R "$NEWCOMER_WS"; start L "$LW"; start TD "$TDW"; start T "$TW"
echo "servers: C=$URL_C D=$URL_DV A=$URL_A R=$URL_R L=$URL_L TD=$URL_TD T=$URL_T" >&2

code=$(get index.html "$URL_C")
row index-lists-refs "200:2" "$code:$(grep -o 'data-refs="[0-9]*"' "$D/pages/index.html" | grep -o '[0-9]*')" "C's references"

# A current document page.
code=$(get c-paper.html "${URL_C}doc/paper")
run c-show-paper "$MINI" workspace --action doc-show --dir "$CW" --name paper
want=$(jq -r '.lines[] | select(.kind == "atom") | "\(.element) \(.atom) \(.createdBy.subject) \(.revision)"' "$D/c-show-paper.out")
got=$(grep -o 'data-element="[0-9]*" data-kind="atom" data-line="[0-9-]*" data-atom="[0-9]*" data-creator="[0-9]*" data-revision="[0-9]*"' "$D/pages/c-paper.html" \
  | sed 's/ data-kind="atom" data-line="[0-9-]*"//; s/data-[a-z]*="\([0-9]*\)"/\1/g')
printf '%s\n' "$want" >"$D/lines-want.txt"; printf '%s\n' "$got" >"$D/lines-got.txt"
row doc-lines-match-show "200:equal" "$code:$([ -n "$want" ] && [ "$want" = "$got" ] && echo equal || echo differs)" "$(echo "$want" | wc -l) line(s): element atom creator revision, in the kernel's order"
missing=0
while IFS= read -r text; do grep -qF -- "$text" "$D/pages/c-paper.html" || missing=$((missing + 1)); done < <(jq -r '.lines[] | select(.kind == "atom" and .struck != true) | .text' "$D/c-show-paper.out")
row doc-text-match equal "$([ "$missing" = 0 ] && echo equal || echo "$missing missing")" "line text from the payload bytes"
subject=$(jq -r .subject "$CW/workspace.json")
row page-context present "$(grep -q "read as subject <span class=id>$subject</span> at height <span class=id data-height=\"[0-9]*\"" "$D/pages/c-paper.html" && echo present || echo absent)" "subject $subject, $(grep -o 'data-height="[0-9]*"' "$D/pages/c-paper.html")"
row annotation-stale false "$(grep -o 'data-annotation="7001" data-fresh="[a-z?]*"' "$D/pages/c-paper.html" | grep -o 'fresh="[a-z?]*"' | cut -d'"' -f2)" "R's annotation after A's edit"
row backlinks-from-index "notes:document" "$(grep -o 'data-backlink="[a-z0-9]*" data-kind="[a-z]*"' "$D/pages/c-paper.html" | sed 's/data-backlink="\([^"]*\)" data-kind="\([^"]*\)"/\1:\2/' | tr '\n' ' ' | sed 's/ $//')" "C's backlinks of paper, one signed index read"
before=$(attempts "$CW")
code=$(get c-notes.html "${URL_C}doc/notes")
reads=$(( $(attempts "$CW") - before ))
row link-out "200:present:paper" "$code:$(grep -q 'data-link="9101"' "$D/pages/c-notes.html" && echo present || echo absent):$(grep -o 'data-link="9101"[^>]*>[^<]*<span class=id>[0-9]*</span> -> <a href="[^"]*/doc/[a-z]*">' "$D/pages/c-notes.html" | grep -o '/doc/[a-z]*' | cut -d/ -f3)" "the links view"
row doc-page-reads 3 "$reads" "signed reads made by one /doc/notes view (notes holds no transclusion)"

# Transclusions inline (K12T's page), as three readers see them.
code=$(get r-page.html "${URL_R}doc/page")
run r-show-page "$MINI" workspace --action doc-show --dir "$NEWCOMER_WS" --name page
row page-order-equals-show "200:equal" "$code:$([ "$(elements r-page.html)" = "$(show_elements r-show-page)" ] && echo equal || echo differs)" "$(elements r-page.html)"
row r-transclusions-inline "invalidated live snapshot" "$(renders r-page.html)" "R covers wall and page"
row r-snapshot-at-height present "$(grep -q '\[snapshot at height [0-9]* of' "$D/pages/r-page.html" && echo present || echo absent)" "$(grep -o '\[snapshot at height [0-9]*' "$D/pages/r-page.html" | head -1)"
code=$(get l-page.html "${URL_L}doc/page")
row late-joiner-placeholder "200:invalidated live moved" "$code:$(renders l-page.html)" "$(grep -o 'its lines moved since height [0-9]*[^<]*' "$D/pages/l-page.html" | head -1)"
code=$(get td-page.html "${URL_TD}doc/page")
row d-placeholders "200:unavailable unavailable unavailable" "$code:$(renders td-page.html)" "$(grep -o '\[transclusion: [0-9]* atoms of [^]]*' "$D/pages/td-page.html" | head -1 | sed 's/<[^>]*>//g')"
row d-page-no-bytes "absent:present" "$(grep -q 'wall line' "$D/pages/td-page.html" && echo present || echo absent):$(grep -q 'wall line' "$D/pages/r-page.html" && echo present || echo absent)" "no wall bytes on tdave's page (control: R's page shows them)"
code=$(get r-wall.html "${URL_R}doc/wall")
row transclusion-backlinks "200:3" "$code:$(grep -c 'data-backlink="page" data-kind="transclusion"' "$D/pages/r-wall.html")" "page's three transclusion links count as backlinks of wall"

code=$(get d-paper.html "${URL_DV}doc/paper")
row d-paper-refused "403:refusal" "$code:$(grep -q 'data-refusal' "$D/pages/d-paper.html" && echo refusal || echo none)" "$(grep -o 'refused: [^<]*' "$D/pages/d-paper.html" | head -1)"
row d-paper-no-bytes "absent:present" "$(grep -q 'the second line' "$D/pages/d-paper.html" && echo present || echo absent):$(grep -q 'the second line' "$D/pages/c-paper.html" && echo present || echo absent)" "no paper bytes on D's refusal page (control: C's page shows them)"

# History, a page at a past height, and a diff (K12H's hist).
code=$(get a-history.html "${URL_A}doc/hist/history")
run a-doc-history "$MINI" workspace --action doc-history --dir "$SPONSOR_WS" --name hist
want=$(jq -r '[.rows[] | .height + ":" + (.subject // "-")] | join(" ")' "$D/a-doc-history.out")
got=$(grep -o 'data-row="[0-9]*" data-subject="[0-9-]*"' "$D/pages/a-history.html" | sed 's/data-row="\([0-9]*\)" data-subject="\([0-9-]*\)"/\1:\2/' | tr '\n' ' ' | sed 's/ $//')
row history-matches "200:equal" "$code:$([ -n "$want" ] && [ "$want" = "$got" ] && echo equal || echo differs)" "$got"
code=$(get t-history.html "${URL_T}doc/hist/history")
got=$(grep -o 'data-row="[0-9]*" data-subject="[0-9-]*" data-content="[a-z]*"' "$D/pages/t-history.html" \
  | awk -F'"' -v h1="$H1" '$2 >= h1 {print $6}' | tr '\n' ' ' | sed 's/ $//')
row history-split "200:false false true true true true" "$code:$got" "the third key, granted between h2 and h3"
code=$(get a-at-4.html "${URL_A}at/$H4/doc/hist")
run a-show-at-4 "$MINI" workspace --action doc-show --dir "$SPONSOR_WS" --name hist --at "$H4"
row at-page-equals-show "200:equal" "$code:$([ "$(elements a-at-4.html)" = "$(show_elements a-show-at-4)" ] && echo equal || echo differs)" "height $H4: $(elements a-at-4.html)"
code=$(get t-at-2.html "${URL_T}at/$H2/doc/hist")
row at-refused "403:did-not-cover" "$code:$(grep -q 'data-refusal.*did not cover' "$D/pages/t-at-2.html" && echo did-not-cover || echo other)" "$(grep -o 'history read refused[^<]*' "$D/pages/t-at-2.html" | head -1)"
code=$(get a-diff-56.html "${URL_A}doc/hist/diff/$H5/$H6")
row diff-moves "200:moved:1001 moved:1003" "$code:$(grep -o 'data-change="[a-z]*" data-element="[0-9]*"' "$D/pages/a-diff-56.html" | sed 's/data-change="\([a-z]*\)" data-element="\([0-9]*\)"/\1:\2/' | sort | tr '\n' ' ' | sed 's/ $//')" "height $H5 to $H6"

# The gate: refused before any read.
before=$(attempts "$CW")
code=$(get foreign.html "${URL_C}doc/paper" -H "Host: evil.example:$PORT_C")
row foreign-host-refused 421 "$code" "foreign Host"
code=$(get rebind.html "${URL_C}doc/paper" -H "Host: 127.0.0.1.nip.io:$PORT_C")
row rebind-host-refused 421 "$code" "DNS-rebinding name"
code=$(get origin.html "${URL_C}doc/paper" -H "Origin: http://evil.example")
row foreign-origin-refused 403 "$code" "$(grep -o 'Origin [^<]*' "$D/pages/origin.html" | head -1)"
code=$(get post.html "${URL_C}doc/paper" -X POST --data x=1)
row post-refused 405 "$code" "$(grep -o 'POST: [^<]*' "$D/pages/post.html" | head -1)"
code=$(get wrong.html "http://127.0.0.1:$PORT_C/00000000000000000000000000000000/doc/paper")
row wrong-secret 404 "$code" "path secret"
row refused-requests-no-reads 0 "$(( $(attempts "$CW") - before ))" "signed reads made while answering the five refused requests"
row stream-501 501 "$(get stream.html "${URL_C}stream/notes")" "$(grep -o 'streams are[^<]*' "$D/pages/stream.html" | cut -c1-100)"

code=$(get a-board.html "${URL_A}board/shared")
f=$(grep -o 'data-fields="[0-9]*"' "$D/pages/a-board.html" | grep -o '[0-9]*')
row board-fields "200:yes" "$code:$([ "${f:-0}" -ge 1 ] && echo yes || echo no)" "${f:-0} field(s) in shared"
code=$(get a-room.html "${URL_A}room/lab")
row room-children "200:labnote" "$code:$(grep -o 'data-child="[a-z0-9-]*"' "$D/pages/a-room.html" | cut -d'"' -f2 | tr '\n' ' ' | sed 's/ $//')" "born --in lab"
row room-members present "$(grep -q "data-member=\"$A_SUBJECT\"" "$D/pages/a-room.html" && echo present || echo absent)" "$(grep -o 'data-members="[0-9]*"' "$D/pages/a-room.html") $(grep -o 'data-members-refused>[^<]*' "$D/pages/a-room.html")"

if command -v lynx >/dev/null; then
  lynx -dump "${URL_C}doc/paper" >"$D/pages/c-paper.lynx.txt" 2>&1
  row lynx-dump text "$(grep -q 'the first line' "$D/pages/c-paper.lynx.txt" && echo text || echo none)" "lynx -dump"
else
  echo "lynx not installed: lynx row skipped" >&2
fi

cleanup; PIDS=()
cat "$rows" >&2
total=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $total web rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$total/$total web rows as expected: loopback-only, no write route, foreign Host/Origin refused before any read; pages in the kernel's order with transclusions inline; backlinks from the index; history, at-height and diff pages; refusals render as refusals" >&2
echo "$rows"
