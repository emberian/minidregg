#!/usr/bin/env bash
# journey.d/jweb.sh — WEB-ENTRANCE: `mini web`, the read-only loopback hypertext face,
# on the journey's fresh Store after K12C (which left paper, notes, quotes, an
# annotation, and carol/dave workspaces in the world).
#
# Parties: C = carol (observe paper; observe+mutate notes), D = dave (observe notes;
# a paper reference with no grant), A = the sponsor. Each runs its own `mini web`
# on 127.0.0.1:0 against its own workspace; every page is a signed read under that
# workspace's key.
# Rows (expect -> got):
#   c-links-notes-to-paper   C adds a plain link notes -> paper           -> installed
#   a-creates-room           A creates lab, and labnote --in lab          -> installed
#   bind-any-refused         --listen 0.0.0.0:PORT                         -> refused (no listener)
#   bind-lan-refused         --listen <a non-loopback address>             -> refused
#   index-lists-refs         C's / lists C's references                    -> 2
#   doc-lines-match-read     C's /doc/paper line table = `workspace read`  -> equal
#   doc-text-match           every line's text appears                     -> equal
#   page-context             subject + height on the page                  -> present
#   annotation-stale         R's annotation rendered fresh=false           -> false
#   backlink-quotes          /doc/paper backlinks from notes (quote+live+B's quote) -> 3
#   link-out                 /doc/notes lists link 9101                    -> present
#   quotes-render            C: 8001 stale, 8002 quoted (final bytes)      -> stale/quoted
#   d-paper-refused          D's /doc/paper                                -> 403 refusal page
#   d-quotes-unavailable     D's /doc/notes: 8001                          -> unavailable
#   foreign-host-refused     Host: evil.example:PORT                       -> 421, no signed read made
#   rebind-host-refused      Host: 127.0.0.1.nip.io:PORT                    -> 421
#   foreign-origin-refused   Origin: http://evil.example                   -> 403
#   post-refused             POST /TOKEN/doc/paper                         -> 405
#   wrong-secret             /WRONG/doc/paper                              -> 404, no signed read made
#   stream-501 / at-501      not on this tree                              -> 501
#   board-fields             A's /board/shared                             -> fields >= 1
#   room-children            A's /room/lab lists labnote                   -> labnote
#   lynx-dump                lynx -dump of C's /doc/paper (if lynx exists) -> text
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
CW=$W/carol-workspace
DW=$W/dave-workspace
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
  curl -s --max-time 300 -o "$D/pages/$file" -w '%{http_code}' "$@" "$url"
}

paper=$(jq -r .target "$SPONSOR_WS/refs/paper.json")

# Setup: a plain link (C, notes -> paper) and a room with one resource born in it (A).
invoke c-links-notes-to-paper "$CW" notes "$(jq -n --arg p "$paper" \
  '[{type:"link",link:"9101",source:null,target:{type:"document",id:$p},relation:"1"}]')"
row c-links-notes-to-paper installed "$(rc_word c-links-notes-to-paper)" "link 9101"
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create-lab "$MINI" workspace --action create --dir "$SPONSOR_WS" --name lab --storage content --predicate "$D/req/permit-all.json"
run create-labnote "$MINI" workspace --action create --dir "$SPONSOR_WS" --name labnote --storage content \
  --predicate "$D/req/permit-all.json" --in lab
row a-creates-room installed "$( [ "$(cat "$D/create-lab.rc")$(cat "$D/create-labnote.rc")" = 00 ] && echo installed || echo "lab rc=$(cat "$D/create-lab.rc") labnote rc=$(cat "$D/create-labnote.rc"): $(tail -1 "$D/create-labnote.err")")" "lab + labnote --in lab"

# Bind refusals: nothing but 127.0.0.1.
run bind-any "$MINI" web --dir "$CW" --listen 0.0.0.0:28431
listening=$(ss -ltnH 'sport = :28431' 2>/dev/null | wc -l)
row bind-any-refused "refused:0" "$( [ "$(cat "$D/bind-any.rc")" != 0 ] && grep -q 'binds 127.0.0.1 only' "$D/bind-any.err" && echo refused || echo bound):$listening" "$(tail -1 "$D/bind-any.err")"
lan=$(hostname -I 2>/dev/null | awk '{print $1}'); lan=${lan:-10.0.0.1}
run bind-lan "$MINI" web --dir "$CW" --listen "$lan:28432"
row bind-lan-refused refused "$( [ "$(cat "$D/bind-lan.rc")" != 0 ] && grep -q 'binds 127.0.0.1 only' "$D/bind-lan.err" && echo refused || echo bound)" "$lan: $(tail -1 "$D/bind-lan.err")"

start C "$CW"; start DV "$DW"; start A "$SPONSOR_WS"
echo "servers: C=$URL_C D=$URL_DV A=$URL_A" >&2

code=$(get index.html "$URL_C")
row index-lists-refs "200:2" "$code:$(grep -o 'data-refs="[0-9]*"' "$D/pages/index.html" | grep -o '[0-9]*')" "C's references"

code=$(get c-paper.html "${URL_C}doc/paper")
run c-read-paper "$MINI" workspace --action read --dir "$CW" --name paper
want=$(jq -r '[.cell.entries[] | select(.type == "atom")] | sort_by([(.id | length), .id]) | .[] | "\(.id) \(.createdBy.subject) \(.revision)"' "$D/c-read-paper.out")
got=$(grep -o 'data-atom="[0-9]*" data-creator="[0-9]*" data-revision="[0-9]*"' "$D/pages/c-paper.html" | sed 's/data-[a-z]*="\([0-9]*\)"/\1/g')
printf '%s\n' "$want" >"$D/lines-want.txt"; printf '%s\n' "$got" >"$D/lines-got.txt"
row doc-lines-match-read "200:equal" "$code:$([ -n "$want" ] && [ "$want" = "$got" ] && echo equal || echo differs)" "$(echo "$want" | wc -l) line(s): atom creator revision"
missing=0
while IFS= read -r text; do grep -qF -- "$text" "$D/pages/c-paper.html" || missing=$((missing + 1)); done < <(jq -r '.cell.entries[] | select(.type == "atom") | .payload' "$D/c-read-paper.out" | while read -r h; do printf '%s' "$h" | xxd -r -p; echo; done)
row doc-text-match equal "$([ "$missing" = 0 ] && echo equal || echo "$missing missing")" "line text from the payload bytes"
subject=$(jq -r .subject "$CW/workspace.json")
row page-context present "$(grep -q "read as subject <span class=id>$subject</span> at height <span class=id data-height=\"[0-9]*\"" "$D/pages/c-paper.html" && echo present || echo absent)" "subject $subject, $(grep -o 'data-height="[0-9]*"' "$D/pages/c-paper.html")"
row annotation-stale false "$(grep -o 'data-annotation="7001" data-fresh="[a-z?]*"' "$D/pages/c-paper.html" | grep -o 'fresh="[a-z?]*"' | cut -d'"' -f2)" "R's annotation after A's edit"
n=$(grep -c 'data-backlink="notes"' "$D/pages/c-paper.html")
row backlink-quotes 3 "$n" "$(grep -o 'data-backlink="notes" data-kind="[a-z]*"' "$D/pages/c-paper.html" | cut -d'"' -f4 | sort | uniq -c | tr -s ' \n' ' ')"

code=$(get c-notes.html "${URL_C}doc/notes")
row link-out "200:present" "$code:$(grep -q 'data-link="9101"' "$D/pages/c-notes.html" && echo present || echo absent)" "$(grep -o 'data-link="9101">[^<]*' "$D/pages/c-notes.html" | head -1)"
q1=$(grep -o 'data-quote="8001" data-mode="[a-z]*" data-render="[a-z]*"' "$D/pages/c-notes.html" | grep -o 'render="[a-z]*"' | cut -d'"' -f2)
q2=$(grep -o 'data-quote="8002" data-mode="[a-z]*" data-render="[a-z]*"' "$D/pages/c-notes.html" | grep -o 'render="[a-z]*"' | cut -d'"' -f2)
final=$(grep -c 'the second line, final' "$D/pages/c-notes.html")
row quotes-render "stale/quoted/1" "$q1/$q2/$final" "snapshot 8001, live 8002 with the final bytes"

code=$(get d-paper.html "${URL_DV}doc/paper")
row d-paper-refused "403:refusal" "$code:$(grep -q 'data-refusal' "$D/pages/d-paper.html" && echo refusal || echo none)" "$(grep -o 'refused: [^<]*' "$D/pages/d-paper.html" | head -1)"
row d-paper-no-bytes absent "$(grep -q 'the second line' "$D/pages/d-paper.html" && echo present || echo absent)" "no paper bytes on D's refusal page"
code=$(get d-notes.html "${URL_DV}doc/notes")
row d-quotes-unavailable "200:unavailable" "$code:$(grep -o 'data-quote="8001" data-mode="[a-z]*" data-render="[a-z]*"' "$D/pages/d-notes.html" | grep -o 'render="[a-z]*"' | cut -d'"' -f2)" "D holds no paper read"
row d-notes-no-bytes absent "$(grep -q 'the second line' "$D/pages/d-notes.html" && echo present || echo absent)" "no paper bytes on D's notes page"

before=$(attempts "$CW")
code=$(get foreign.html "${URL_C}doc/paper" -H "Host: evil.example:$PORT_C")
row foreign-host-refused "421:0" "$code:$(( $(attempts "$CW") - before ))" "new signed reads made: $(( $(attempts "$CW") - before ))"
code=$(get rebind.html "${URL_C}doc/paper" -H "Host: 127.0.0.1.nip.io:$PORT_C")
row rebind-host-refused 421 "$code" "DNS-rebinding name"
code=$(get origin.html "${URL_C}doc/paper" -H "Origin: http://evil.example")
row foreign-origin-refused 403 "$code" "$(grep -o 'Origin [^<]*' "$D/pages/origin.html" | head -1)"
code=$(get post.html "${URL_C}doc/paper" -X POST --data x=1)
row post-refused 405 "$code" "$(grep -o 'POST: [^<]*' "$D/pages/post.html" | head -1)"
before=$(attempts "$CW")
code=$(get wrong.html "http://127.0.0.1:$PORT_C/00000000000000000000000000000000/doc/paper")
row wrong-secret "404:0" "$code:$(( $(attempts "$CW") - before ))" "path secret"
row stream-501 501 "$(get stream.html "${URL_C}stream/notes")" "$(grep -o 'streams are[^<]*' "$D/pages/stream.html" | cut -c1-80)"
row at-501 501 "$(get at.html "${URL_C}at/5/doc/paper")" "$(grep -o 'a read at a past[^<]*' "$D/pages/at.html" | cut -c1-80)"

code=$(get a-board.html "${URL_A}board/shared")
f=$(grep -o 'data-fields="[0-9]*"' "$D/pages/a-board.html" | grep -o '[0-9]*')
row board-fields "200:yes" "$code:$([ "${f:-0}" -ge 1 ] && echo yes || echo no)" "${f:-0} field(s) in shared"
code=$(get a-room.html "${URL_A}room/lab")
row room-children "200:labnote" "$code:$(grep -o 'data-child="[a-z0-9-]*"' "$D/pages/a-room.html" | cut -d'"' -f2 | tr '\n' ' ' | sed 's/ $//')" "born --in lab"

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
echo "$total/$total web rows as expected: loopback-only, no write route, foreign Host/Origin refused before any read, line table = signed read, backlinks, quotes, refusals render as refusals" >&2
echo "$rows"
