#!/usr/bin/env bash
# deploy/demo-seed/seed.sh: make the demo world lived-in, using only the verbs a member types.
# Runs ON THE DEMO BOX as root, once, after genesis, after the public reader and the seed members
# are enrolled and `mini apps bootstrap` has run, before the door opens. See README.md.
#
# Every line below is one member's shell line, handed to the same forced command ssh and the
# Discord runner use (mini-shell-ssh), as that member's own account. Nothing writes the Store any
# other way. Idempotent: each step looks for its object first (a document by `doc show`, an
# attempt by its id in `history all`, a room by `chat rooms`, ...). One line per step on stdout:
#   seed: ok|skip|FAIL  <what>
set -uo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
D=$here/data
unset MINI_ROOT
# The box's own paths (C, NODE, S, LIB, TENANT_GROUP), exactly as mini-session-run reads them.
. /usr/local/lib/mini/infra/lib.sh
[ "$(id -u)" = 0 ] || { echo "seed: must run as root" >&2; exit 2; }
[ "${TENANCY:-}" = split ] || { echo "seed: only under split tenancy" >&2; exit 2; }

BOX=${SEED_HOST:-box}      # the house member: the sponsor/box account
SAGE=${SEED_GUEST:-sage}   # the second seed member (the frame enrols it; README)
PUBLIC=$(cat /etc/mini/public-subject 2>/dev/null) || { echo "seed: /etc/mini/public-subject is missing (the public reader is not enrolled)" >&2; exit 2; }
BUDGET=${SEED_HERMES_BUDGET:-100}
# The publication grant's per-read cost ceiling: the file the web body's Publish form reads too.
PUBMAX=$(tr -d '[:space:]' <"$here/public-read-max-cost") || { echo "seed: public-read-max-cost is missing" >&2; exit 2; }
FAILS=0
OUT=; ERR=; RC=0
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT

say_() { printf 'seed: %s  %s\n' "$1" "$2"; }
ok_()   { say_ ok "$1"; }
skip_() { say_ skip "$1"; }
fail_() { say_ FAIL "$1"; FAILS=$((FAILS + 1)); }
# errtail_: the part of $ERR that names the failure, bounded to 400 bytes: the `error:` line and a
# `template ... stopped at line ...` line when present, then the last three non-empty lines (warnings
# and paths come first and used to fill a head cut).
errtail_() {
  { grep -E '^(error:|template .* stopped at line)' <<<"$ERR" | head -3
    grep -v '^[[:space:]]*$' <<<"$ERR" | tail -3; } | awk '!seen[$0]++' | tr '\n' '|' | head -c 400
}

# as MEMBER LINE [TIMEOUT]: one shell line as the member's own account; sets OUT, ERR, RC.
as() {
  local m=$1 line=$2 limit=${3:-120}
  [[ $line != *[[:cntrl:]]* ]] && [ "${#line}" -le 4000 ] || { OUT=; ERR="line too long or has a control character"; RC=2; return 2; }
  timeout --kill-after=5 "$limit" \
    setpriv --reuid="mini-s-$m" --regid="$TENANT_GROUP" --init-groups --reset-env -- \
    env -i PATH=/usr/bin:/bin LANG=C.UTF-8 SSH_ORIGINAL_COMMAND="$line" \
    "$LIB/mini-shell-ssh" "$C/bin/mini" "$C/bin/minidregg-host" "$NODE/deployment/pinned-config.json" \
    "$NODE/public/mini.sock" "$S/$m/workspace" "$S/$m" </dev/null >"$T/out" 2>"$T/err"
  RC=$?; OUT=$(cat "$T/out"); ERR=$(cat "$T/err")
  # timeout(1) exits 124 (137 after --kill-after): name it, it is not a failure of the line itself.
  case $RC in 124|137) ERR="error: TIMEOUT rc=$RC after ${limit}s running: ${line:0:100}"$'\n'"$ERR" ;; esac
  return $RC
}
# stage MEMBER FILE <stdin: contents>: a file under the member's HOME/requests (what @FILE names).
stage() {
  install -d -m 0700 -o "mini-s-$1" -g "$TENANT_GROUP" "$S/$1/requests"
  install -m 0600 -o "mini-s-$1" -g "$TENANT_GROUP" /dev/stdin "$S/$1/requests/$2"
}
# have MEMBER ID: the member already made attempt ID (admitted, refused or undecided).
have() { as "$1" "history all" && grep -qE "^attempt[[:space:]]+$2[[:space:]]" <<<"$OUT"; }
# do_ MEMBER ID LINE...: skip when the attempt id exists; else run the proposing line, then `submit ID`.
propose_submit() { # MEMBER ID LINE
  have "$1" "$2" && return 0
  as "$1" "$3" && as "$1" "submit $2"
}

# --- 0. who is who
as "$BOX" whoami && BOXS=$(jq -r '.subject // empty' <<<"$OUT")
as "$SAGE" whoami && SAGES=$(jq -r '.subject // empty' <<<"$OUT")
if [ -z "${BOXS:-}" ] || [ -z "${SAGES:-}" ]; then
  fail_ "members: $BOX and $SAGE must be enrolled and initialised (whoami shows no subject); nothing seeded"; exit 1
fi
ok_ "members: $BOX=$BOXS $SAGE=$SAGES public=$PUBLIC"

# --- 1. documents: build a document from a one-paragraph-per-line file, publish it to the public reader
# (the grant's MAX-COST is a per-read ceiling: every read costs its encoded intent's length, so 0 covers no read)
doc_build() { # MEMBER NAME FILE
  local m=$1 n=$2 f=$3 i=0 l id fail=0
  as "$m" "doc show $n" || as "$m" "doc new $n draft" || { fail_ "doc $n: doc new: $(errtail_)"; return 1; }
  while IFS= read -r l || [ -n "$l" ]; do
    [ -n "$l" ] || continue
    i=$((i + 1)); id="$n-a$i"
    have "$m" "$id" && continue
    printf '%s\n' "$l" | stage "$m" "$id.txt"
    as "$m" "doc append $id $n @$id.txt" && as "$m" "submit $id" || { fail=1; fail_ "doc $n line $i: $(errtail_)"; break; }
  done <"$f"
  [ "$fail" = 0 ] && ok_ "doc $n: $i lines"
}
publish_public() { # MEMBER REF
  # pubr-: the first publications (id pub-) carried MAX-COST 0, which covers no read; a world that holds
  # them is published again under this id, and the public reader's import replaces the dead reference.
  local id="pubr-$2"
  if have "$1" "$id"; then skip_ "publish $2 to the public reader: done"; return 0; fi
  as "$1" "delegate $id $2 $PUBLIC observe $PUBMAX" && as "$1" "submit $id" && as "$1" "publish $id" \
    && ok_ "publish $2 to the public reader" || fail_ "publish $2: $(errtail_)"
}
for d in what-is-mini a-refusal-explains-itself the-lost-reply the-lamplighters-note house-rules field-notes; do
  doc_build "$BOX" "$d" "$D/docs/$d.txt"
done

# --- 2. the lobby: a room, two members, signed posts
if as "$BOX" "chat rooms" && grep -qw lobby <<<"$OUT"; then skip_ "room lobby exists"
elif as "$BOX" "chat new lobby"; then ok_ "room lobby founded by $BOX"
else fail_ "chat new lobby: $(errtail_)"; fi
if as "$SAGE" "chat rooms" && grep -qw lobby <<<"$OUT"; then skip_ "$SAGE already in lobby"
elif as "$BOX" "chat invite lobby $SAGES $SAGE"; then
  join=$(grep '^chat join lobby ' <<<"$OUT" | tail -1)
  if [ -n "$join" ] && as "$SAGE" "$join"; then ok_ "$SAGE joined lobby"; else fail_ "$SAGE joining lobby: ${join:-no join line printed}: $(errtail_)"; fi
else fail_ "chat invite lobby: $(errtail_)"; fi
post() { # MEMBER TEXT
  as "$1" "tail -n 200"; if grep -qF -- "${2:0:48}" <<<"$OUT"; then skip_ "post by $1 already there"; return; fi
  as "$1" "say $2" && ok_ "post by $1: ${2:0:48}" || fail_ "say by $1: $(errtail_)"
}
while IFS= read -r l; do [ -n "$l" ] && post "$BOX" "$l"; done <"$D/lobby/box-posts.txt"
while IFS= read -r l; do [ -n "$l" ] && post "$SAGE" "$l"; done <"$D/lobby/sage-posts.txt"

# --- 3. Hermes into the lobby, and its introduction
if as "$BOX" "read lobby-hermes-librarian"; then skip_ "Hermes already summoned into lobby"
elif as "$BOX" "summon lobby as librarian --budget $BUDGET" 600; then ok_ "Hermes summoned into lobby as librarian, budget $BUDGET"
else fail_ "summon lobby: $(errtail_)"; fi
post "$BOX" "$(cat "$D/lobby/hermes-intro.txt")"
publish_public "$BOX" lobby

# --- 4. the story table, its law, a first scene
# `story new` is skipped once the story exists; `story seal` is idempotent (an already sealed table writes
# nothing), so it runs every time and a seal that failed on an earlier pass is finished on this one.
if as "$BOX" "story list" && grep -qw tale <<<"$OUT"; then skip_ "story tale exists"
else
  as "$BOX" "story new tale --from tale --gm $SAGES" 600 || fail_ "story new: $(errtail_)"
fi
if as "$BOX" "story list" && grep -qw tale <<<"$OUT"; then
  as "$BOX" "story seal tale" 600 \
    && ok_ "story tale installed under the sealed law, GM $SAGE" || fail_ "story seal: $(errtail_)"
fi
if as "$SAGE" "story list" && grep -qw tale <<<"$OUT"; then skip_ "$SAGE already in story tale"
elif as "$BOX" "story invite tale $SAGES gm"; then
  inv=$(sed -n 's/^story join tale //p' <<<"$OUT" | tail -1)
  if [ -n "$inv" ]; then
    printf '%s\n' "$inv" | stage "$SAGE" tale-invite.json
    as "$SAGE" "story join tale @tale-invite.json" && ok_ "$SAGE joined tale as GM" || fail_ "story join: $(errtail_)"
  else fail_ "story invite printed no join line"; fi
else fail_ "story invite: $(errtail_)"; fi
as "$SAGE" "story enter tale" >/dev/null
opening=$(cat "$D/lobby/story-opening.txt")
if as "$SAGE" "look" && grep -qF "lamp upstairs" <<<"$OUT"; then skip_ "first scene already narrated"
else as "$SAGE" "narrate '$opening'" && ok_ "first scene narrated by the GM" || fail_ "narrate: $(errtail_)"; fi

# --- 5. one Objective Bend program, one run
# done = the object has an activity record (a made cell alone is not a run: `bend show` says "no activity record")
if as "$BOX" "bend show lobby-tally" && ! grep -q "no activity record" <<<"$OUT"; then skip_ "bend object lobby-tally already runs tally"
else
  src=${TALLY_SRC:-$C/world/activity/Tally.obend}; [ -f "$src" ] || src=$here/../../world/activity/Tally.obend
  if [ -f "$src" ]; then
    stage "$BOX" Tally.obend <"$src"
    { as "$BOX" "bend lookup tally" && grep -qi admitted <<<"$OUT"; } || as "$BOX" "bend publish tally @Tally.obend --entry tally" 600
    # the object cell first: the shell verb that makes a member-owned content cell (bend never makes one)
    if [ "$RC" = 0 ] && { as "$BOX" "refs" && grep -qw lobby-tally <<<"$OUT" || as "$BOX" "create lobby-tally content open"; } \
       && as "$BOX" "bend run tally lobby-tally" 600; then ok_ "bend tally published and run on lobby-tally"
    else fail_ "bend: $(errtail_)"; fi
  else fail_ "bend: Tally.obend not found (TALLY_SRC)"; fi
fi

# --- 6. a delegation: one grant that covers, one that does not, one visible refusal
grant() { # OWNER NAME RECIPIENT-SUBJECT VERBS TO-MEMBER
  local id="g-$2-$5"
  if have "$1" "$id"; then skip_ "grant $2 -> $5: done"; return 0; fi
  as "$1" "delegate $id $2 $3 $4 50000" && as "$1" "submit $id" && as "$1" "publish $id" && as "$1" "export $id" || { fail_ "grant $2: $(errtail_)"; return 1; }
  printf '%s\n' "$OUT" | stage "$5" "$2.ref.json"
  as "$5" "import $2 @$2.ref.json" && ok_ "grant $2 ($4) from $1 to $5" || fail_ "import $2 by $5: $(errtail_)"
}
grant "$BOX" field-notes "$SAGES" observe,mutate "$SAGE"
grant "$BOX" house-rules "$SAGES" observe "$SAGE"
printf '%s\n' "sage's first field note, inside the grant." | stage "$SAGE" note1.txt
if have "$SAGE" sage-note; then skip_ "sage's in-grant note: done"
elif as "$SAGE" "doc append sage-note field-notes @note1.txt" && as "$SAGE" "submit sage-note"; then ok_ "sage appended to field-notes (inside the grant)"
else fail_ "sage-note: $(errtail_)"; fi
printf '%s\n' "sage tries to edit the house rules." | stage "$SAGE" overstep.txt
if have "$SAGE" sage-overstep; then skip_ "sage's refused attempt on house-rules: done"
elif as "$SAGE" "doc append sage-overstep house-rules @overstep.txt"; then
  as "$SAGE" "submit sage-overstep"
  if [ "$RC" = 3 ]; then ok_ "sage's attempt outside the grant was refused (receipted)"; else fail_ "sage-overstep: expected a refusal (exit 3), got $RC: $(errtail_)"; fi
else fail_ "doc append sage-overstep: $(errtail_)"; fi

# --- 7. featured apps as grains, each with a little real content
app_id() { # NAME -> appId (exact name from the catalogue)
  as "$BOX" "apps search --json" 300 && jq -r --arg n "$1" '[.apps[]? | select(.name == $n)][0].appId // empty' <<<"$OUT"
}
grain_of() { # NAME -> grain id (a<N>) among the box member's grains
  as "$BOX" "apps list --json" && jq -r --arg n "$(tr '[:upper:]' '[:lower:]' <<<"$1")" \
    '[.. | objects | select(has("grain")) | select((tostring | ascii_downcase) | contains($n))][0].grain // empty' <<<"$OUT"
}
# open GRAIN: sets ORIGIN and a cookie jar $T/jar-GRAIN, by the bootstrap token `apps open` prints once.
open_grain() {
  as "$BOX" "apps open $1 --json" 900 || { as "$BOX" "apps start $1 --json" 900; as "$BOX" "apps open $1 --json" 900; } || return 1
  ORIGIN=$(jq -r .origin <<<"$OUT"); local tok; tok=$(jq -r .bootstrapToken <<<"$OUT")
  [ -n "$ORIGIN" ] && [ "$ORIGIN" != null ] || return 1
  curl -sS --max-time 900 -c "$T/jar-$1" -o /dev/null -w '%{http_code}' --data-urlencode "token=$tok" "$ORIGIN/__mini/bootstrap" | grep -qE '^(200|30[0-9])$'
}
web() { # GRAIN METHOD PATH [curl args]: one request on the grain's private origin as the box member
  local g=$1 mth=$2 p=$3; shift 3
  curl -sS --max-time 900 -b "$T/jar-$g" -H "Origin: $ORIGIN" -X "$mth" -o "$T/body" -w '%{http_code}' "$@" "$ORIGIN$p"
}
install_app() { # NAME -> GRAIN in $G
  G=$(grain_of "$1")
  if [ -n "$G" ]; then skip_ "app $1 already installed as $G"; return 0; fi
  local id; id=$(app_id "$1"); [ -n "$id" ] || { fail_ "app $1: not in the catalogue (apps search)"; return 1; }
  as "$BOX" "apps install $id" 1800 || { fail_ "apps install $1: $(errtail_)"; return 1; }
  G=$(grain_of "$1"); [ -n "$G" ] && ok_ "app $1 installed as $G" || { fail_ "app $1: installed but no grain id in apps list"; return 1; }
}
DECK_URL=
if install_app EtherCalc; then
  if open_grain "$G"; then
    c=$(web "$G" PUT /_/lobby-tally -H 'Content-Type: text/csv' --data-binary @"$D/apps/calc.csv")
    case $c in 20*) ok_ "EtherCalc sheet lobby-tally written ($c)";; *) fail_ "EtherCalc write: HTTP $c";; esac
  else fail_ "EtherCalc: could not open $G"; fi
fi
if install_app Etherpad; then
  if open_grain "$G"; then
    # The Sandstorm package disables /api completely. Its pad UI imports a multipart `file` here;
    # a .txt upload becomes the pad's text, and the matching export proves the write.
    c=$(web "$G" POST /p/welcome/import -F "file=@$D/apps/pad-welcome.txt;filename=welcome.txt;type=text/plain")
    if [ "$c" = 200 ] && jq -e '.code == 0' "$T/body" >/dev/null 2>&1; then
      c=$(web "$G" GET /p/welcome/export/txt)
      if [ "$c" = 200 ] && grep -Fq 'Welcome to the pad. Type here' "$T/body"; then ok_ "Etherpad pad welcome imported and read back"
      else fail_ "Etherpad import readback: HTTP $c"; fi
    else fail_ "Etherpad pad import: HTTP $c $(tail -c 400 "$T/body" | tr '\n' ' ')"; fi
  else fail_ "Etherpad: could not open $G"; fi
fi
# The featured deck app is our reveal.js package (apps/interfaces/revealjs.json, app vku2z...): the grain keeps one
# deck at /var/deck.md and its web root renders it. deck.replace is PUT /deck.md (204); deck.read is GET /deck.md.
DECK_APP="reveal.js markdown decks"
if install_app "$DECK_APP"; then
  if open_grain "$G"; then
    www=$(sed -E 's#^(https?://[^./]+)\.#\1-www.#' <<<"$ORIGIN")
    c=$(web "$G" PUT /deck.md -H 'Content-Type: text/markdown' --data-binary @"$D/apps/slides/slides.md")
    if [ "$c" = 204 ] || [ "$c" = 200 ]; then
      c=$(web "$G" GET /deck.md)
      if [ "$c" = 200 ] && grep -Fq '# Mini, in four slides' "$T/body"; then
        c=$(curl -sS --max-time 120 -o "$T/deck" -w '%{http_code}' "$www/")
        if [ "$c" = 200 ]; then DECK_URL=$www; ok_ "reveal.js deck written, read back and published at $www"
        else fail_ "reveal.js public deck page: HTTP $c"; fi
      else fail_ "reveal.js deck readback: HTTP $c"; fi
    else fail_ "reveal.js deck write: HTTP $c"; fi
  else fail_ "reveal.js: could not open $G"; fi
fi
# a deck already published by an earlier run
if [ -z "$DECK_URL" ] && G=$(grain_of "reveal.js") && [ -n "$G" ]; then
  as "$BOX" "apps status $G --json" && o=$(jq -r '.. | .origin? // empty' <<<"$OUT" | head -1)
  if [ -n "${o:-}" ]; then w=$(sed -E 's#^(https?://[^./]+)\.#\1-www.#' <<<"$o")
    c=$(curl -sS --max-time 60 -o "$T/deck" -w '%{http_code}' "$w/") && [ "$c" = 200 ] && DECK_URL=$w; fi
fi

# --- 8. the welcome document (last: it links everything and names the deck), then the public front page
doc_build "$BOX" welcome "$D/docs/welcome.txt"
for t in what-is-mini a-refusal-explains-itself the-lost-reply the-lamplighters-note house-rules field-notes; do
  propose_submit "$BOX" "welcome-link-$t" "doc link welcome-link-$t welcome $t" || fail_ "link welcome -> $t: $(errtail_)"
done
ok_ "welcome links checked"
if as "$BOX" "doc transclusions welcome" && grep -qi 'what-is-mini\|live' <<<"$OUT"; then skip_ "welcome transclusion exists"
else
  as "$BOX" "doc range what-is-mini 2 4" && as "$BOX" "doc transclude welcome what-is-mini 2 4 live" \
    && ok_ "welcome transcludes what-is-mini lines 2..4 live" || fail_ "transclusion: $(errtail_)"
fi
if [ -n "$DECK_URL" ]; then
  if have "$BOX" welcome-deck; then skip_ "welcome names the deck: done"
  else
    printf 'This deck was published by a member'"'"'s app; open it without an account: %s\n' "$DECK_URL" | stage "$BOX" welcome-deck.txt
    as "$BOX" "doc append welcome-deck welcome @welcome-deck.txt" && as "$BOX" "submit welcome-deck" \
      && ok_ "welcome names the deck at $DECK_URL" || fail_ "welcome deck line: $(errtail_)"
  fi
fi
for d in welcome what-is-mini a-refusal-explains-itself the-lost-reply the-lamplighters-note house-rules field-notes; do publish_public "$BOX" "$d"; done

if [ "$FAILS" = 0 ]; then echo "seed: done, no failures"; else echo "seed: done, $FAILS FAIL line(s); re-run to resume (steps already done are skipped)"; fi
[ "$FAILS" = 0 ]
