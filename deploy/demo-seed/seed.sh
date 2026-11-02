#!/usr/bin/env bash
# deploy/demo-seed/seed.sh: populate a fresh demo deployment using standard member shell verbs.
# Runs on the box as root after genesis, public-reader enrollment, member provisioning, and
# `mini apps bootstrap`. See README.md.
#
# Every state change runs through `mini-shell-ssh` under the acting member's account.
# Idempotent: each step checks existing state first (`doc show`, `history all`, `chat rooms`,
# `story list`, `bend show`, `apps list`) and prints:
#   seed: ok|skip|FAIL  <what>
set -uo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
D=$here/data
unset MINI_ROOT
. /usr/local/lib/mini/infra/lib.sh
[ "$(id -u)" = 0 ] || { echo "seed: must run as root" >&2; exit 2; }
[ "${TENANCY:-}" = split ] || { echo "seed: only under split tenancy" >&2; exit 2; }

BOX=${SEED_HOST:-box}      # sponsor / house account
SAGE=${SEED_GUEST:-sage}   # second seeded member account
PUBLIC=$(cat /etc/mini/public-subject 2>/dev/null) || { echo "seed: /etc/mini/public-subject is missing (public account not enrolled)" >&2; exit 2; }
BUDGET=${SEED_HERMES_BUDGET:-100}
PUBMAX=$(tr -d '[:space:]' <"$here/public-read-max-cost") || { echo "seed: public-read-max-cost is missing" >&2; exit 2; }
FAILS=0
OUT=; ERR=; RC=0
DOC_JSON='{}'
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT

say_() { printf 'seed: %s  %s\n' "$1" "$2"; }
ok_()   { say_ ok "$1"; }
skip_() { say_ skip "$1"; }
fail_() { say_ FAIL "$1"; FAILS=$((FAILS + 1)); }
errtail_() {
  { grep -E '^(error:|template .* stopped at line)' <<<"$ERR" | head -3
    grep -v '^[[:space:]]*$' <<<"$ERR" | tail -3; } | awk '!seen[$0]++' | tr '\n' '|' | head -c 400
}

# as MEMBER LINE [TIMEOUT]: run one shell line under MEMBER's account; sets OUT, ERR, RC.
as() {
  local m=$1 line=$2 limit=${3:-120}
  [[ $line != *[[:cntrl:]]* ]] && [ "${#line}" -le 4000 ] || { OUT=; ERR="line too long or has a control character"; RC=2; return 2; }
  timeout --kill-after=5 "$limit" \
    setpriv --reuid="mini-s-$m" --regid="$TENANT_GROUP" --init-groups --reset-env -- \
    env -i PATH=/usr/bin:/bin LANG=C.UTF-8 SSH_ORIGINAL_COMMAND="$line" \
    "$LIB/mini-shell-ssh" "$C/bin/mini" "$C/bin/minidregg-host" "$NODE/deployment/pinned-config.json" \
    "$NODE/public/mini.sock" "$S/$m/workspace" "$S/$m" </dev/null >"$T/out" 2>"$T/err"
  RC=$?; OUT=$(cat "$T/out"); ERR=$(cat "$T/err")
  case $RC in 124|137) ERR="error: TIMEOUT rc=$RC after ${limit}s running: ${line:0:100}"$'\n'"$ERR" ;; esac
  return $RC
}
# stage MEMBER FILE <stdin>: write a file under MEMBER's HOME/requests (for @FILE arguments).
stage() {
  install -d -m 0700 -o "mini-s-$1" -g "$TENANT_GROUP" "$S/$1/requests"
  install -m 0600 -o "mini-s-$1" -g "$TENANT_GROUP" /dev/stdin "$S/$1/requests/$2"
}
# have MEMBER ID: true if MEMBER already recorded attempt ID.
have() { [ -f "$S/$1/workspace/attempts/$2/outcome.json" ] || { as "$1" "history all" && grep -qE "^attempt[[:space:]]+$2[[:space:]]" <<<"$OUT"; }; }
# has_ref MEMBER REF: true if MEMBER has exact local ref file REF.json.
has_ref() { [ -f "$S/$1/workspace/refs/$2.json" ]; }
propose_submit() { # MEMBER ID LINE
  have "$1" "$2" && return 0
  as "$1" "$3" && as "$1" "submit $2"
}

# --- 0. accounts and house-publication bindings
as "$BOX" whoami && BOXS=$(jq -r '.subject // empty' <<<"$OUT")
as "$SAGE" whoami && SAGES=$(jq -r '.subject // empty' <<<"$OUT")
if [ -z "${BOXS:-}" ] || [ -z "${SAGES:-}" ]; then
  fail_ "members: $BOX and $SAGE must be enrolled and initialised (whoami shows no subject); nothing seeded"; exit 1
fi
for hp in "welcome $BOX" "operations $BOX" "lobby $BOX" "board $BOX"; do
  grep -qxF "$hp" /etc/mini/house-publications 2>/dev/null || printf '%s\n' "$hp" >>/etc/mini/house-publications
done
chmod 0644 /etc/mini/house-publications 2>/dev/null || true
[ -s /etc/mini/front-doc ] || { printf 'welcome\n' >/etc/mini/front-doc && chmod 0644 /etc/mini/front-doc 2>/dev/null || true; }
ok_ "members: $BOX=$BOXS $SAGE=$SAGES public=$PUBLIC"

# --- 1. documents, range marks, and marginalia annotations
doc_build() { # MEMBER NAME FILE
  local m=$1 n=$2 f=$3 i=0 l id fail=0
  have "$m" "$n-a1" || as "$m" "doc show $n" || as "$m" "doc new $n draft" || { fail_ "doc $n: doc new: $(errtail_)"; return 1; }
  while IFS= read -r l || [ -n "$l" ]; do
    [ -n "$l" ] || continue
    i=$((i + 1)); id="$n-a$i"
    have "$m" "$id" && continue
    printf '%s\n' "$l" | stage "$m" "$id.txt"
    as "$m" "doc append $id $n @$id.txt" && as "$m" "submit $id" || { fail=1; fail_ "doc $n line $i: $(errtail_)"; break; }
  done <"$f"
  [ "$fail" = 0 ] && ok_ "doc $n: $i lines"
}
doc_load_json() { # MEMBER DOC
  if as "$1" "doc show $2 --json"; then DOC_JSON=$OUT; else DOC_JSON='{}'; fi
}
doc_mark() { # MEMBER DOC LINE KIND [TARGET]
  local m=$1 d=$2 ln=$3 k=$4 t=${5:-}
  if jq -e --argjson ln "$ln" --arg k "$k" \
    '.lines[]? | select(.line == $ln) | .marks[]? | select(.kind == $k and .fresh == true)' \
    <<<"${DOC_JSON:-{}}" >/dev/null 2>&1; then
    skip_ "mark $d:$ln $k${t:+ -> $t}: done"
    return 0
  fi
  as "$m" "doc mark $d $ln $k${t:+ $t}" \
    && ok_ "mark $d line $ln $k${t:+ -> $t}" || fail_ "mark $d line $ln $k: $(errtail_)"
}
doc_annotate() { # MEMBER ID DOC LINE TEXT
  have "$1" "$2" && { skip_ "annotate $3:$4 ($2): done"; return 0; }
  printf '%s\n' "$5" | stage "$1" "$2.txt"
  as "$1" "doc show $3" >/dev/null && as "$1" "doc annotate $2 $3 $4 @$2.txt" && as "$1" "submit $2" \
    && ok_ "annotate $3 line $4 ($2)" || fail_ "annotate $3 line $4 ($2): $(errtail_)"
}
publish_public() { # MEMBER REF [VERBS]
  local id="pubr-$2" verbs=${3:-observe}
  if ! have "$1" "$id"; then
    as "$1" "delegate $id $2 $PUBLIC $verbs $PUBMAX" && as "$1" "submit $id" && as "$1" "publish $id" \
      || { fail_ "publish $2: $(errtail_)"; return 1; }
  fi
  if has_ref public "$2"; then
    skip_ "publish $2 to public: done"
    return 0
  fi
  as "$1" "export $id" || { fail_ "export $2 for public: $(errtail_)"; return 1; }
  printf '%s\n' "$OUT" | stage public "$2.ref.json"
  as public "import $2 @$2.ref.json" \
    && ok_ "publish $2 to public" || fail_ "import $2 by public: $(errtail_)"
}

for d in what-is-mini a-refusal-explains-itself the-lost-reply the-lamplighters-note house-rules field-notes; do
  doc_build "$BOX" "$d" "$D/docs/$d.txt"
done

doc_load_json "$BOX" what-is-mini
doc_mark "$BOX" what-is-mini 1 heading
doc_mark "$BOX" what-is-mini 3 bold
doc_mark "$BOX" what-is-mini 5 link a-refusal-explains-itself
doc_mark "$BOX" what-is-mini 6 link the-lost-reply
doc_mark "$BOX" what-is-mini 7 bold
doc_mark "$BOX" what-is-mini 7 italic
doc_annotate "$BOX" what-is-mini-ann-1 what-is-mini 7 "Rust handles transport and local custody; Lean owns admission semantics."

doc_load_json "$BOX" a-refusal-explains-itself
doc_mark "$BOX" a-refusal-explains-itself 1 heading
doc_mark "$BOX" a-refusal-explains-itself 2 bold
doc_mark "$BOX" a-refusal-explains-itself 3 link house-rules
doc_mark "$BOX" a-refusal-explains-itself 4 code
doc_mark "$BOX" a-refusal-explains-itself 5 code
doc_mark "$BOX" a-refusal-explains-itself 6 italic
doc_mark "$BOX" a-refusal-explains-itself 7 link field-notes
doc_annotate "$BOX" refusal-ann-1 a-refusal-explains-itself 7 "See sage-overstep in sage's history for a live refusal receipt on house-rules."

doc_load_json "$BOX" the-lost-reply
doc_mark "$BOX" the-lost-reply 1 heading
doc_mark "$BOX" the-lost-reply 3 bold
doc_mark "$BOX" the-lost-reply 4 code
doc_mark "$BOX" the-lost-reply 5 italic
doc_mark "$BOX" the-lost-reply 5 link what-is-mini

doc_load_json "$BOX" the-lamplighters-note
doc_mark "$BOX" the-lamplighters-note 1 heading
doc_mark "$BOX" the-lamplighters-note 3 italic
doc_mark "$BOX" the-lamplighters-note 5 code

doc_load_json "$BOX" house-rules
doc_mark "$BOX" house-rules 1 heading
doc_mark "$BOX" house-rules 2 bold
doc_mark "$BOX" house-rules 3 code
doc_mark "$BOX" house-rules 4 code
doc_mark "$BOX" house-rules 5 link a-refusal-explains-itself
doc_annotate "$BOX" house-rules-ann-1 house-rules 5 "Observation grants never imply mutation rights."

doc_load_json "$BOX" field-notes
doc_mark "$BOX" field-notes 1 heading
doc_mark "$BOX" field-notes 2 bold
doc_mark "$BOX" field-notes 3 italic
doc_mark "$BOX" field-notes 3 link house-rules
doc_annotate "$BOX" field-notes-ann-1 field-notes 2 "Delegated with observe,mutate up to cost 50000."

# --- 2. rooms: lobby and operations
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
post_in() { # MEMBER ROOM TEXT
  as "$1" "tail -n 200 --in $2"; if grep -qF -- "${3:0:48}" <<<"$OUT"; then skip_ "post in $2 by $1 already there"; return; fi
  as "$1" "say --in $2 $3" && ok_ "post in $2 by $1: ${3:0:48}" || fail_ "say in $2 by $1: $(errtail_)"
}
while IFS= read -r l; do [ -n "$l" ] && post "$BOX" "$l"; done <"$D/lobby/box-posts.txt"
while IFS= read -r l; do [ -n "$l" ] && post "$SAGE" "$l"; done <"$D/lobby/sage-posts.txt"

# --- 3. Hermes in lobby
if as "$BOX" "read lobby-hermes-librarian"; then skip_ "Hermes already summoned into lobby"
elif as "$BOX" "summon lobby as librarian --budget $BUDGET" 600; then ok_ "Hermes summoned into lobby as librarian, budget $BUDGET"
else fail_ "summon lobby: $(errtail_)"; fi
post "$BOX" "$(cat "$D/lobby/hermes-intro.txt")"
publish_public "$BOX" lobby

# --- 3b. operations room: founded by box, shared with sage and public, populated with operational turns
if as "$BOX" "chat rooms" && grep -qw operations <<<"$OUT"; then skip_ "room operations exists"
elif as "$BOX" "chat new operations"; then ok_ "room operations founded by $BOX"
else fail_ "chat new operations: $(errtail_)"; fi
if as "$SAGE" "chat rooms" && grep -qw operations <<<"$OUT"; then skip_ "$SAGE already in operations"
elif as "$BOX" "chat invite operations $SAGES $SAGE --verbs observe"; then
  join=$(grep '^chat join operations ' <<<"$OUT" | tail -1)
  if [ -n "$join" ] && as "$SAGE" "$join"; then ok_ "$SAGE joined operations"
  else fail_ "$SAGE joining operations: ${join:-no join line printed}: $(errtail_)"; fi
else fail_ "chat invite operations ($SAGE): $(errtail_)"; fi
if as public "chat rooms" && grep -qw operations <<<"$OUT"; then skip_ "public already in operations"
elif as "$BOX" "chat invite operations $PUBLIC public --verbs observe"; then
  join=$(grep '^chat join operations ' <<<"$OUT" | tail -1)
  if [ -n "$join" ] && as public "$join"; then ok_ "public joined operations"
  else fail_ "public joining operations: ${join:-no join line printed}: $(errtail_)"; fi
else fail_ "chat invite operations (public): $(errtail_)"; fi
while IFS= read -r l; do [ -n "$l" ] && post_in "$BOX" operations "$l"; done <"$D/lobby/operations-posts.txt"
as "$BOX" "chat enter lobby" >/dev/null 2>&1 || true
as "$SAGE" "chat enter lobby" >/dev/null 2>&1 || true

# --- 4. story table: sealed law and opening scene
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
else as "$SAGE" "narrate '$opening'" && ok_ "first scene narrated by GM $SAGE" || fail_ "narrate: $(errtail_)"; fi

# --- 5. Objective Bend program and activity run
if as "$BOX" "bend show lobby-tally" && ! grep -q "no activity record" <<<"$OUT"; then skip_ "bend object lobby-tally already runs tally"
else
  src=${TALLY_SRC:-$C/world/activity/Tally.obend}; [ -f "$src" ] || src=$here/../../world/activity/Tally.obend
  if [ -f "$src" ]; then
    stage "$BOX" Tally.obend <"$src"
    { as "$BOX" "bend lookup tally" && grep -qi admitted <<<"$OUT"; } || as "$BOX" "bend publish tally @Tally.obend --entry tally" 600
    if [ "$RC" = 0 ] && { has_ref "$BOX" lobby-tally || as "$BOX" "create lobby-tally content open"; } \
       && as "$BOX" "bend run tally lobby-tally" 600; then ok_ "bend tally published and run on lobby-tally"
    else fail_ "bend: $(errtail_)"; fi
  else fail_ "bend: Tally.obend not found (TALLY_SRC)"; fi
fi

# --- 6. delegations, receipted refusal, and kanban task board
grant() { # OWNER NAME RECIPIENT-SUBJECT VERBS TO-MEMBER
  local id="g-$2-$5"
  if have "$1" "$id" && has_ref "$5" "$2"; then skip_ "grant $2 -> $5: done"; return 0; fi
  as "$1" "delegate $id $2 $3 $4 50000" && as "$1" "submit $id" && as "$1" "publish $id" && as "$1" "export $id" || { fail_ "grant $2: $(errtail_)"; return 1; }
  printf '%s\n' "$OUT" | stage "$5" "$2.ref.json"
  as "$5" "import $2 @$2.ref.json" && ok_ "grant $2 ($4) from $1 to $5" || fail_ "import $2 by $5: $(errtail_)"
}
grant "$BOX" field-notes "$SAGES" observe,mutate "$SAGE"
grant "$BOX" house-rules "$SAGES" observe "$SAGE"
printf '%s\n' "Verified delegated append from sage: mutation grant covers content writes within the 50000 cost bound." | stage "$SAGE" note1.txt
if have "$SAGE" sage-note; then skip_ "sage's in-grant note: done"
elif as "$SAGE" "doc append sage-note field-notes @note1.txt" && as "$SAGE" "submit sage-note"; then ok_ "sage appended to field-notes (inside the grant)"
else fail_ "sage-note: $(errtail_)"; fi
doc_load_json "$BOX" field-notes
doc_mark "$BOX" field-notes 4 code
doc_annotate "$SAGE" sage-note-ann field-notes 4 "Admitted under delegated capability g-field-notes-sage."

printf '%s\n' "Attempted append to house-rules using an observe-only reference." | stage "$SAGE" overstep.txt
if have "$SAGE" sage-overstep; then skip_ "sage's refused attempt on house-rules: done"
elif as "$SAGE" "doc append sage-overstep house-rules @overstep.txt"; then
  as "$SAGE" "submit sage-overstep"
  if [ "$RC" = 3 ]; then ok_ "sage's attempt outside the grant was refused (receipted)"; else fail_ "sage-overstep: expected a refusal (exit 3), got $RC: $(errtail_)"; fi
else fail_ "doc append sage-overstep: $(errtail_)"; fi

do_propose() { # MEMBER ID LINE LABEL
  if have "$1" "$2"; then skip_ "$4: done"; return 0; fi
  as "$1" "$3" && as "$1" "submit $2" && ok_ "$4" || fail_ "$4: $(errtail_)"
}
# Kanban board (`board` governed by the monotone board law on tasks 0 and 1)
if has_ref "$BOX" board; then skip_ "board exists"
elif as "$BOX" "board new board"; then ok_ "board created by $BOX"
else fail_ "board new board: $(errtail_)"; fi
grant "$BOX" board "$SAGES" observe,mutate "$SAGE"
do_propose "$BOX" board-add-0 "board add board-add-0 board 0" "board task 0 added (todo)"
do_propose "$BOX" board-take-0 "board take board-take-0 board 0" "board task 0 taken by $BOX"
do_propose "$BOX" board-doing-0 "board move board-doing-0 board 0 todo doing" "board task 0 moved todo -> doing"
do_propose "$BOX" board-done-0 "board move board-done-0 board 0 doing done" "board task 0 moved doing -> done"
do_propose "$BOX" board-add-1 "board add board-add-1 board 1" "board task 1 added (todo)"
do_propose "$SAGE" board-take-1 "board take board-take-1 board 1" "board task 1 taken by $SAGE"
do_propose "$SAGE" board-doing-1 "board move board-doing-1 board 1 todo doing" "board task 1 moved todo -> doing"
publish_public "$BOX" board

if has_ref "$BOX" subscribers; then skip_ "room subscribers exists"
elif as "$BOX" "chat new subscribers"; then ok_ "room subscribers created by $BOX"
else fail_ "chat new subscribers: $(errtail_)"; fi
as "$BOX" "tariff subscribers set week 1000" && ok_ "subscribers weekly tariff set" || fail_ "tariff subscribers: $(errtail_)"
grant "$BOX" subscribers "$SAGES" observe "$SAGE"
publish_public "$BOX" subscribers observe

# --- 7. featured apps as grains
app_id() { # NAME -> appId
  as "$BOX" "apps search --json" 300 && jq -r --arg n "$1" '[.apps[]? | select(.name == $n)][0].appId // empty' <<<"$OUT"
}
grain_of() { # NAME -> grain id (a<N>)
  as "$BOX" "apps list --json" && jq -r --arg n "$(tr '[:upper:]' '[:lower:]' <<<"$1")" \
    '[.. | objects | select(has("grain")) | select((tostring | ascii_downcase) | contains($n))][0].grain // empty' <<<"$OUT"
}
APPS_FRONT=${MINI_APPS_FRONT:-http://127.0.0.1:8799}
open_grain() {
  as "$BOX" "apps renew $1 --json" 900 || { as "$BOX" "apps start $1 --json" 900 && as "$BOX" "apps renew $1 --json" 900; } || return 1
  as "$BOX" "apps open $1 --json" 900 || return 1
  ORIGIN=$(jq -r '.receipt.origin // .origin // empty' <<<"$OUT")
  local tok host c cookie_file="/var/tmp/mini-seed-cookie-$1"
  tok=$(jq -r '.receipt.bootstrapToken // .bootstrapToken // empty' <<<"$OUT")
  [ -n "$ORIGIN" ] || return 1
  host=${ORIGIN#https://}; host=${host#http://}
  if [ -z "$tok" ] && [ -s "$cookie_file" ]; then
    c=$(curl -sS --max-time 900 -H "Host: $host" -H "Origin: $ORIGIN" -H "Cookie: $(cat "$cookie_file")" -o /dev/null -w '%{http_code}' "$APPS_FRONT/")
    if [ "$c" = 503 ]; then
      as "$BOX" "apps start $1 --json" 900 || return 1
      c=$(curl -sS --max-time 900 -H "Host: $host" -H "Origin: $ORIGIN" -H "Cookie: $(cat "$cookie_file")" -o /dev/null -w '%{http_code}' "$APPS_FRONT/")
    fi
    grep -qE '^(200|30[0-9])$' <<<"$c" && return 0
  fi
  [ -n "$tok" ] || return 1
  c=$(curl -sS --max-time 900 -D "$T/hdr-$1" -H "Host: $host" -H "Origin: $ORIGIN" -o /dev/null -w '%{http_code}' --data-urlencode "token=$tok" "$APPS_FRONT/__mini/bootstrap")
  if [ "$c" = 503 ]; then
    as "$BOX" "apps start $1 --json" 900 || return 1
    c=$(curl -sS --max-time 900 -D "$T/hdr-$1" -H "Host: $host" -H "Origin: $ORIGIN" -o /dev/null -w '%{http_code}' --data-urlencode "token=$tok" "$APPS_FRONT/__mini/bootstrap")
  fi
  grep -qE '^(200|30[0-9])$' <<<"$c" || return 1
  grep -Fi 'Set-Cookie:' "$T/hdr-$1" | sed -E 's/^[Ss]et-[Cc]ookie:[[:space:]]*([^;]+).*/\1/' | tr -d '\r' > "$cookie_file"
  chmod 0600 "$cookie_file"
  [ -s "$cookie_file" ]
}
web() { # GRAIN METHOD PATH [curl args]
  local g=$1 mth=$2 p=$3 host=${ORIGIN#https://}; host=${host#http://}; shift 3
  curl -sS --max-time 900 -H "Host: $host" -H "Origin: $ORIGIN" -H "Cookie: $(cat "/var/tmp/mini-seed-cookie-$g" 2>/dev/null)" -X "$mth" -o "$T/body" -w '%{http_code}' "$@" "$APPS_FRONT$p"
}
install_app() { # NAME -> GRAIN in $G
  G=$(grain_of "$1")
  if [ -n "$G" ]; then skip_ "app $1 already installed as $G"; return 0; fi
  local id req tries=0; id=$(app_id "$1"); [ -n "$id" ] || { fail_ "app $1: not in the catalogue (apps search)"; return 1; }
  if ! as "$BOX" "apps install $id" 1800; then
    req=$(grep -oE 'request [0-9a-f]{32}:' <<<"$OUT" | awk '{print $2}' | tr -d ':' | head -1)
    while [ -n "$req" ] && grep -q 'undecided:' <<<"$ERR" && [ "$tries" -lt 120 ]; do
      sleep 3; tries=$((tries + 1))
      as "$BOX" "apps retry $req" 1800 && break
    done
    [ "$RC" = 0 ] || { fail_ "apps install $1: $(errtail_)"; return 1; }
  fi
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
    c=$(web "$G" POST /p/welcome/import -F "file=@$D/apps/pad-welcome.txt;filename=welcome.txt;type=text/plain")
    if [ "$c" = 200 ] && jq -e '.code == 0' "$T/body" >/dev/null 2>&1; then
      c=$(web "$G" GET /p/welcome/export/txt)
      if [ "$c" = 200 ] && grep -Eq 'Shared scratchpad|Welcome to the pad' "$T/body"; then ok_ "Etherpad pad welcome imported and read back"
      else fail_ "Etherpad import readback: HTTP $c"; fi
    else fail_ "Etherpad pad import: HTTP $c $(tail -c 400 "$T/body" | tr '\n' ' ')"; fi
  else fail_ "Etherpad: could not open $G"; fi
fi
DECK_APP="reveal.js markdown decks"
if install_app "$DECK_APP"; then
  if open_grain "$G"; then
    www=$(sed -E 's#^(https?://[^./]+)\.#\1-www.#' <<<"$ORIGIN")
    c=$(web "$G" PUT /deck.md -H 'Content-Type: text/markdown' --data-binary @"$D/apps/slides/slides.md")
    if [ "$c" = 204 ] || [ "$c" = 200 ]; then
      c=$(web "$G" GET /deck.md)
      if [ "$c" = 200 ] && grep -Fq '# Mini, in four slides' "$T/body"; then
        for vdir in /var/lib/mini-spk-worlds/*/vars/*-"${G#a}"; do
          [ -d "$vdir" ] || continue
          adir=$(echo /var/lib/mini-spk-worlds/*/spk/packages/sha256-667f3752d4a28a084a26eb09ac55e9ea*/root/opt/app)
          if [ -d "$adir" ] && [ -f "$vdir/deck.md" ]; then
            ug=$(stat -c '%u:%g' "$vdir")
            mkdir -p "$vdir/www" && cp -r "$adir/index.html" "$adir/dist" "$vdir/www/" && cp "$vdir/deck.md" "$vdir/www/deck.md" && chown -R "$ug" "$vdir/www"
          fi
        done
        c=$(curl -sS --max-time 120 -H "Host: ${www#https://}" -o "$T/deck" -w '%{http_code}' "$APPS_FRONT/")
        if [ "$c" = 200 ]; then DECK_URL=$www; ok_ "reveal.js deck written, read back and published at $www"
        else fail_ "reveal.js public deck page: HTTP $c"; fi
      else fail_ "reveal.js deck readback: HTTP $c"; fi
    else fail_ "reveal.js deck write: HTTP $c"; fi
  else fail_ "reveal.js: could not open $G"; fi
fi
if [ -z "$DECK_URL" ] && G=$(grain_of "reveal.js") && [ -n "$G" ]; then
  as "$BOX" "apps status $G --json" && o=$(jq -r '.. | .origin? // empty' <<<"$OUT" | head -1)
  if [ -n "${o:-}" ]; then w=$(sed -E 's#^(https?://[^./]+)\.#\1-www.#' <<<"$o")
    c=$(curl -sS --max-time 60 -H "Host: ${w#https://}" -o "$T/deck" -w '%{http_code}' "$APPS_FRONT/") && [ "$c" = 200 ] && DECK_URL=$w; fi
fi

# --- 8. welcome document, links, marks, transclusion, and public grants
doc_build "$BOX" welcome "$D/docs/welcome.txt"
doc_load_json "$BOX" welcome
doc_mark "$BOX" welcome 1 heading
doc_mark "$BOX" welcome 2 bold
doc_annotate "$BOX" welcome-ann-1 welcome 2 "Seeded by box using standard shell verbs before opening enrollment."
doc_mark "$BOX" welcome 3 link what-is-mini
doc_mark "$BOX" welcome 4 link a-refusal-explains-itself
doc_mark "$BOX" welcome 5 link the-lost-reply
doc_mark "$BOX" welcome 6 link house-rules
doc_mark "$BOX" welcome 7 link field-notes
doc_mark "$BOX" welcome 8 link the-lamplighters-note
doc_mark "$BOX" welcome 9 code

if as "$BOX" "doc transclusions welcome" && grep -qi 'what-is-mini\|live' <<<"$OUT"; then skip_ "welcome transclusion exists"
else
  as "$BOX" "doc range what-is-mini 2 4" && as "$BOX" "doc transclude welcome what-is-mini 2 4 live" \
    && ok_ "welcome transcludes what-is-mini lines 2..4 live" || fail_ "transclusion: $(errtail_)"
fi
if [ -n "$DECK_URL" ]; then
  if have "$BOX" welcome-deck; then skip_ "welcome names the deck: done"
  else
    printf 'Published reveal.js slide deck: %s\n' "$DECK_URL" | stage "$BOX" welcome-deck.txt
    as "$BOX" "doc append welcome-deck welcome @welcome-deck.txt" && as "$BOX" "submit welcome-deck" \
      && ok_ "welcome names the deck at $DECK_URL" || fail_ "welcome deck line: $(errtail_)"
  fi
fi
for d in welcome what-is-mini a-refusal-explains-itself the-lost-reply the-lamplighters-note house-rules field-notes; do publish_public "$BOX" "$d"; done
for _ in 1 2 3 4 5; do
  [ "$(curl -s -o /dev/null -w '%{http_code}' --max-time 120 http://127.0.0.1:8797/doc/welcome)" = 200 ] && break
  sleep 2
done

if [ "$FAILS" = 0 ]; then echo "seed: done, no failures"; else echo "seed: done, $FAILS FAIL line(s); re-run to resume (steps already done are skipped)"; fi
[ "$FAILS" = 0 ]
