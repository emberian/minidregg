#!/usr/bin/env bash
# journey.d/jweb-frontend.sh — J-WEB-FRONTEND: the Mini web front end end to end
# (docs/WEB-FRONTEND-2026-10-27.md): the root helper (here in --dev, as this user), the keyless
# gateway, the member's body and shell behind it.
#
#   as a journey hook (JWF)     journey.sh exports MINI HOST CONFIG SOCKET NEWCOMER_WS NEWCOMER_SUBJECT
#                               JOURNEY_STEP_DIR; carol (K12C's docuverse author) is the member when her
#                               workspace exists, else the newcomer (whose spine workspace cannot birth a
#                               document: the three document rows then say why).
#   jweb-frontend.sh --dry      the same, from the environment (MINI HOST CONFIG SOCKET WS SUBJECT STEP_DIR);
#                               for a Mac with a running journey world.
#   jweb-frontend.sh --box NAME ON THE DEMO BOX, as root: the real helper and gateway units; writes a login
#                               record for the hosted account NAME as the door would, then the same rows
#                               against the gateway on loopback with the public Origin.
#
# Rows (expect -> got):
#   login-confirm      GET /login/CODE shows the one-shot confirm form (no cookie yet)      -> 200, form
#   login              POST /login exchanges the code for a cookie; the code is spent        -> 303 + cookie; second POST refused
#   stage-member       GET / with the cookie: the member's workspace (its subject on the page) -> 200
#   csrf-refused       POST /doc/new with a wrong csrf token                                 -> 403
#   origin-refused     POST with a foreign Origin                                            -> 403
#   term-open          POST /term makes a terminal; GET /term/ID has the WebSocket address    -> 303, data-ws
#   term-whoami        over the WebSocket, `whoami` prints the member's subject              -> present
#   doc-new            POST /doc/new (law note) through the form                             -> admitted
#   doc-append         POST /doc/NAME/append through the form                               -> admitted; the page shows the text
#   receipt            GET /receipts/ID shows the attempt's decoded outcome                  -> 200, outcome admitted
#   parity             every verb x subcommand leaf in `help` has a route, a no-JS form, and its
#                      placeholder-filled form plans through the shell (/verb/NAME/dry)          -> none missing, 0 refusals
#   parity-redproof    a verb the shell lacks has no face                                          -> 404
#   publish / public-read-published / public-front-doc / public-read-unpublished / unpublish / public-read-revoked
#   / public-house-name-reserved (a member's `operations` is handed over as operations-MEMBER, never the box's room)
#                      the member publishes a document to a second member (the public reader); an anonymous GET
#                      reads its text (200) and the front page shows it; an unpublished document is refused;
#                      after Unpublish the Host refuses the visitor (403)
#   verb-index         /verb lists the catalog                                                       -> 200
#   verb-run           POST /verb/whoami through the derived form                                    -> answered, the subject
#   tour               GET /tour: twelve steps with the real forms                                      -> 200, 12
#   tour-step          POST /tour/4 (`can` through the tour's form) lands an outcome under the step   -> outcome
#   export-*           POST /export, ready, download (attachment, streamed), deleted on the box, untar: the
#                      document's text and the manifest's height and world root equal the live page's  -> PASS
#   hermes-tools-*     /room/ROOM/resident on a room this member founds: what Hermes may do (hermes/tools bits
#                      1/2/4/8, hermes/compute), the founder's grant form; grant files+oracle (admitted, 9), revoke
#                      the oracle (admitted, 1); the same form on a document is refused, never admitted
#   bend-*             /bend lists this workspace's programs and reads any activity; /bend/await draws the shell's
#                      `bend await` (phase, slot, decider, deadline); an answer to a slot this member does not
#                      decide, through the derived `bend answer` form, is refused
#   story-page-*       /story shows the invitation where the door hands one (HOME/requests/NAME-invite.json) with
#                      the derived `story join` form filled in; the front page says it waits; an invitation
#                      addressed to someone else has no form and its join is refused; story-join posts the
#                      /story page's own form; after it the story is held as player
#   tour-chromium      jtour.mjs: login, /tour, step 4 (`can DOC`) through the pane, a terminal prompt (needs Playwright) -> answered, elapsed
#   logout             POST /logout clears the cookie; the old cookie no longer opens /term   -> 303; 401
#   public-reader      GET / without a session answers (the public body, or a named refusal) -> 200|502, "public reader"
#   J-COLD-READ        the public reader's first visit after idle (demo-dry 2026-10-28: 504 at the gateway's 120 s).
#     cold-read-consent   the public body's consent provider ends (box: mini-consent@public stopped, as its idle
#                         exit does; dev: the reader's resident stopped by its PID file); anonymous GET / through
#                         the gateway, whose own deadline is 120 s                              -> 200 within it
#     cold-read-body      the public body ended too (box: its scope; dev: the pid the helper recorded), the first
#                         visit after a start                                                     -> 200 within it
#     warm-at-start       the helper warms the public body before any visitor (dev: the helper restarted by its
#                         PID file; box: its journal since it started) -> "public reader warmed ... 200", then GET / 200
# Output: one row per check (`PASS|FAIL<TAB>row<TAB>detail`), then `J-WEB-FRONTEND PASS n/n` or
# `... FAIL k/n` as the last line of stdout and stderr. Exit 0 only on PASS. Every process this script
# starts is stopped by the PID in its PID file, and only that.
set -uo pipefail
umask 077
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
mode=${1:-hook}
rows=0 fails=0
row() {
  rows=$((rows + 1))
  if [ "$2" = 1 ]; then printf 'PASS\t%s\t%s\n' "$1" "$3"
  else
    fails=$((fails + 1)); printf 'FAIL\t%s\t%s\n' "$1" "$3"
    # Keep the complete refusal, not only the headline (which can be uniform).
    printf '%s' "${page:-}" >"$R/$1-failed.html"
  fi
}
verdict() { local v="J-WEB-FRONTEND PASS $rows/$rows"; [ "$fails" = 0 ] || v="J-WEB-FRONTEND FAIL $fails/$rows"; echo "$v"; echo "$v" >&2; [ "$fails" = 0 ]; }
unconfigured() { echo "UNCONFIGURED: $*" >&2; exit 5; }
PIDS=()
stop() { for f in "${PIDS[@]}"; do [ -f "$f" ] && kill "$(cat "$f")" 2>/dev/null; rm -f "$f"; done; }
trap stop EXIT

free_port() { python3 -I -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])'; }
token() { head -c 32 /dev/urandom | base64 | tr '+/' '-_' | tr -d '=\n'; }
sha256() { printf '%s' "$1" | (shasum -a 256 2>/dev/null || sha256sum) | cut -c1-64; }

case $mode in
hook|--dry)
  if [ "$mode" = hook ]; then
    D=${JOURNEY_STEP_DIR:?}; WS=${NEWCOMER_WS:?}; SUBJECT=${NEWCOMER_SUBJECT:?}
  else
    D=${STEP_DIR:?STEP_DIR}; WS=${WS:?WS}; SUBJECT=${SUBJECT:?SUBJECT}
  fi
  : "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
  # The document rows birth a document, which the spine's newcomer cannot (no birth context). JWF
  # provisions its own member `jwf` from the sponsor's shell, the way the docuverse provisions its
  # authors (K12C): keygen, enroll plan/seal/submit, provision, the birth context, init.
if [ -n "${SPONSOR_WS:-}" ] && [ -f "$SPONSOR_WS/workspace.json" ]; then
    # The member's HOME must be short: the client's resident consent socket lives under
    # HOME/.mini/consent-anchors/ and a Unix socket path is bounded (sun_path). Stable per step
    # directory, so a run on a box that keeps its world finds the member it provisioned before.
    M=${XDG_RUNTIME_DIR:-/tmp}/jwf-m-$(printf '%s' "$D" | cksum | cut -c1-8); mkdir -p -m 700 "$M/home/requests" "$M/home/provision" "$M/sponsor-home/keys" "$M/sponsor-home/requests"
    # The member dir is tmpfs: it goes with the step on every exit path, unless JWF_KEEP_MEMBER=1 keeps it
    # for a box whose world outlives the run (then the next run reuses the member it holds).
    [ "${JWF_KEEP_MEMBER:-0}" = 1 ] || { JWF_MEMBER_DIR=$M; trap 'stop; rm -rf "$JWF_MEMBER_DIR"' EXIT; }
    mline() { # WORKSPACE HOME LINE -> stdout; rc in $?
      "$MINI" shell --socket "$SOCKET" --workspace "$1" --home "$2" --host "$HOST" --config "$CONFIG" --line "$3" 2>"$M/last.err"
    }
    pinned=$(jq -r '.socket // empty' "$SPONSOR_WS/workspace.json" 2>/dev/null); [ -z "$pinned" ] || SOCKET=$pinned
    # provision_jwf [DIR]: enrol and initialise one member whose HOME is DIR/home (default $M); a second
    # call with another DIR makes the public reader (a distinct subject), see PUBREAD below.
    provision_jwf() {
      local P=${1:-$M}; mkdir -p -m 700 "$P/home/requests" "$P/home/provision"
      # A fresh account name each time a member is provisioned: a world that outlives the step
      # (a box kept between runs) already holds the earlier ones.
      local NAME; NAME=jwf-$(date +%s | tail -c 6)$$$([ "$P" = "$M" ] || echo p); printf '%s\n' "$NAME" >"$P/name"
      mline "$WS" "$P/home" "keygen mini.key" >/dev/null || return 1
      install -m 0600 "$P/home/keys/mini.key" "$M/sponsor-home/keys/$NAME.key" || return 1
      mline "$SPONSOR_WS" "$M/sponsor-home" "enroll plan $NAME $NAME.key $(xxd -p -c 256 "$P/home/keys/mini.key.next.pub") $(xxd -p -c 256 "$P/home/keys/mini.key.next.cosign")" >/dev/null || return 1
      mline "$SPONSOR_WS" "$M/sponsor-home" "enroll seal $NAME" >/dev/null || return 1
      mline "$SPONSOR_WS" "$M/sponsor-home" "enroll submit $NAME" >"$P/submit.out" || return 1
      rm -f "$M/sponsor-home/keys/$NAME.key"
      local subject; subject=$(jq -r '.subject // empty' "$P/submit.out"); [ -n "$subject" ] || return 1
      printf '%s\n' '{"type":"all","predicates":[]}' >"$P/permit-all.json"
      "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "$NAME" --holder "$subject" --funding 1000 --account-predicate "$P/permit-all.json" --factory-ref factory >"$P/provision.out" 2>"$P/provision.err" || return 1
      install -m 0600 "$SPONSOR_WS/provisions/$NAME/birth-context.json" "$P/home/provision/birth-context.json" || return 1
      mline "$P/home/workspace" "$P/home" "init mini.key $subject" >/dev/null || return 1
      [ "$P" = "$M" ] || return 0
      # The door's last enrolment step for a stranger who ticked "contribute my data for research":
      # the member's research-consent fact, as the member (door::research_consent_lines(true)).
      for l in "create research-consent declared open 1" "invoke research-consent-0 research-consent create 1 1" "submit research-consent-0"; do
        mline "$M/home/workspace" "$M/home" "$l" >/dev/null || return 1
      done
      : >"$M/provisioned-this-run"
    }
    # A member an earlier run of this step provisioned (JWF_KEEP_MEMBER=1 on a box that keeps its world) is reused.
    [ -f "$M/home/workspace/workspace.json" ] || provision_jwf || true
    if [ -f "$M/home/workspace/workspace.json" ] && [ "$(jq -r '.birthContext != null' "$M/home/workspace/workspace.json")" = true ]; then
      JSUBJ=$(jq -r .subject "$M/home/workspace/workspace.json")
      WS=$M/home/workspace; SUBJECT=$JSUBJ; JWF_HOME=$M/home
      echo "jwf: provisioned member $(cat "$M/name" 2>/dev/null || echo jwf) as subject $JSUBJ" >&2
    else
      echo "jwf: could not provision its own member ($(tail -1 "$M/last.err" 2>/dev/null; tail -1 "$M/provision.err" 2>/dev/null)); using the newcomer" >&2
    fi
    # PUBREAD: the public reader is a second member (a distinct subject) with its own workspace, as
    # on the box ("the hosted member public"); the member publishes to ITS subject, and the front
    # page is the member's published document. Without it the public body is the member itself.
    if [ "$WS" = "$M/home/workspace" ]; then
      PUBP=$M/pub
      [ -f "$PUBP/home/workspace/workspace.json" ] || { mkdir -p -m 700 "$PUBP"; provision_jwf "$PUBP" || true; }
      if [ -f "$PUBP/home/workspace/workspace.json" ] && [ "$(jq -r '.birthContext != null' "$PUBP/home/workspace/workspace.json")" = true ]; then
        PUBREAD_SUBJECT=$(jq -r .subject "$PUBP/home/workspace/workspace.json"); PUBREAD_WS=$PUBP/home/workspace; PUBREAD_HOME=$PUBP/home
      else
        echo "jwf: could not provision the public reader ($(tail -1 "$M/last.err" 2>/dev/null; tail -1 "$PUBP/provision.err" 2>/dev/null)); the public rows will say so" >&2
      fi
    fi
  fi
  BIN=$(dirname "$MINI")
  GATEWAY=${MINI_WEB_BIN:-$BIN/mini-web}; HELPER=${MINI_WEB_SPAWN_BIN:-$BIN/mini-web-spawn}
  [ -x "$GATEWAY" ] && [ -x "$HELPER" ] || unconfigured "no mini-web / mini-web-spawn beside $MINI (cargo build -p minidregg-mini-web -p minidregg-mini-web-spawn), or set MINI_WEB_BIN / MINI_WEB_SPAWN_BIN"
  WRAPPER=$REPO/deploy/shell/mini-shell-ssh
  [ -x "$WRAPPER" ] || unconfigured "no $WRAPPER"
  # A workspace that pins its Host's socket must be addressed by that exact path.
  pinned=$(jq -r '.socket // empty' "$WS/workspace.json" 2>/dev/null); [ -z "$pinned" ] || SOCKET=$pinned
  R=$D/jwf; mkdir -p "$R/state" "$R/home" "$R/pubhome"
  DOC="jwf$(od -An -N3 -tu4 /dev/urandom | tr -d ' ' | cut -c1-6)"; DOC2=${DOC}x
  # Unix sockets need a short path (sun_path); the step directory can be long.
  RUNDIR=$(mktemp -d "${XDG_RUNTIME_DIR:-/tmp}/jwf.XXXXXX"); trap 'stop; rm -rf "$RUNDIR" ${JWF_MEMBER_DIR:+"$JWF_MEMBER_DIR"}' EXIT
  HOMEDIR=${JWF_HOME:-$R/home}
  jq -n --arg mini "$MINI" --arg host "$HOST" --arg config "$CONFIG" --arg socket "$SOCKET" --arg wrapper "$WRAPPER" \
    --arg aws "$WS" --arg ahome "$HOMEDIR" --arg pws "${PUBREAD_WS:-$WS}" --arg phome "${PUBREAD_HOME:-$R/pubhome}" \
    --arg psub "${PUBREAD_SUBJECT:-}" --arg front "$DOC" \
    '{mini:$mini,host:$host,config:$config,socket:$socket,wrapper:$wrapper,
      sessions:{alice:{workspace:$aws,home:$ahome}}, public:{workspace:$pws,home:$phome}}
     + (if $psub == "" then {} else {publicSubject:$psub,frontDoc:$front,housePublications:{($front):"alice"}} end)' >"$R/dev.json"
  HSOCK=$RUNDIR/spawn.sock
  start_helper() { nohup "$HELPER" --dev "$R/dev.json" --socket "$HSOCK" --state "$R/state" --run "$RUNDIR" >>"$R/helper.log" 2>&1 & echo $! >"$R/helper.pid"; }
  start_helper; PIDS+=("$R/helper.pid")
  PORT=$(free_port); ORIGIN=http://127.0.0.1:$PORT
  nohup "$GATEWAY" --listen "127.0.0.1:$PORT" --helper "$HSOCK" --origin "$ORIGIN" --shutdown "the end of this journey" >"$R/gateway.log" 2>&1 &
  echo $! >"$R/gateway.pid"; PIDS+=("$R/gateway.pid")
  for _ in $(seq 1 50); do curl -s -m 1 "$ORIGIN/healthz" >/dev/null 2>&1 && [ -S "$HSOCK" ] && break; sleep 0.1; done
  CODE=$(token)
  printf '{"name":"alice","expires":%d}\n' "$(( $(date +%s) + 3600 ))" >"$R/state/logins/$(sha256 "$CODE").json"
  COOKIE_NAME=mini_session
  ;;
--box)
  NAME=${2:?usage: jweb-frontend.sh --box NAME}
  [ "$(id -u)" = 0 ] || { echo "jweb-frontend --box runs as root on the box" >&2; exit 2; }
  id -u "mini-s-$NAME" >/dev/null 2>&1 || unconfigured "no hosted account mini-s-$NAME"
  D=$(mktemp -d /tmp/jwf.XXXXXX); R=$D
  SUBJECT=$(jq -r .subject "/var/lib/mini/sessions/$NAME/workspace/workspace.json")
  PORT=${MINI_WEB_PORT:-8797}; ORIGIN=${MINI_WEB_ORIGIN:-https://demo.dregg.online}
  CODE=$(token)
  mkdir -p /var/lib/mini-web-spawn/logins
  printf '{"name":"%s","expires":%d}\n' "$NAME" "$(( $(date +%s) + 3600 ))" >"/var/lib/mini-web-spawn/logins/$(sha256 "$CODE").json"
  chmod 600 "/var/lib/mini-web-spawn/logins/$(sha256 "$CODE").json"
  COOKIE_NAME=__Host-mini_session
  ;;
*) echo "usage: jweb-frontend.sh [--dry | --box NAME]" >&2; exit 2 ;;
esac

BASE=http://127.0.0.1:$PORT
JAR=$R/jar
# curl talks to the loopback gateway; the browser's Origin and fetch-site headers are supplied as a browser would.
req() { # METHOD PATH [curl args...] -> body on stdout; status via st (a file: req runs in a subshell), headers in $R/h
  local method=$1 path=$2; shift 2
  curl -s -o "$R/body" -D "$R/h" -w '%{http_code}' -X "$method" -b "$JAR" -c "$JAR" -H "Origin: $ORIGIN" -H 'Sec-Fetch-Site: same-origin' "$@" "$BASE$path" >"$R/status"
  cat "$R/body"
}
st() { cat "$R/status" 2>/dev/null; }
csrf_of() { grep -o 'name="csrf" value="[^"]*"' "$R/body" | head -1 | sed 's/.*value="//; s/"$//'; }

page=$(req GET "/login/$CODE")
row login-confirm "$([ "$(st)" = 200 ] && grep -q 'action="/login"' <<<"$page" && echo 1 || echo 0)" "$(st)"
req POST /login --data-urlencode "code=$CODE" >/dev/null
has_cookie=$(grep -c "$COOKIE_NAME" "$JAR" || true)
req POST /login --data-urlencode "code=$CODE" -b /dev/null -c /dev/null >"$R/second"
row login "$([ "$has_cookie" -ge 1 ] && [ "$(st)" = 403 ] && echo 1 || echo 0)" "cookie=$has_cookie second=$(st)"
page=$(req GET /)
row stage-member "$([ "$(st)" = 200 ] && grep -q "$SUBJECT\|alice\|mini-s-" <<<"$page" && ! grep -q 'public reader' <<<"$page" && echo 1 || echo 0)" "$(st)"
CSRF=$(csrf_of)
req POST /doc/new --data-urlencode "csrf=nope" --data-urlencode "name=x" --data-urlencode "law=note" >/dev/null
row csrf-refused "$([ "$(st)" = 403 ] && echo 1 || echo 0)" "$(st)"
evil=$(curl -s -o /dev/null -w '%{http_code}' -X POST -b "$JAR" -H 'Origin: https://evil.example' --data-urlencode "csrf=$CSRF" --data-urlencode "name=x" --data-urlencode "law=note" "$BASE/doc/new")
row origin-refused "$([ "$evil" = 403 ] && echo 1 || echo 0)" "$evil"
req POST /term --data-urlencode "csrf=$CSRF" --data-urlencode cols=100 --data-urlencode rows=30 >/dev/null
TERM_PATH=$(grep -i '^location:' "$R/h" | awk '{print $2}' | tr -d '\r')
page=$(req GET "$TERM_PATH")
WSPATH=$(grep -o 'data-ws="[^"]*"' <<<"$page" | head -1 | sed 's/data-ws="//; s/"$//')
row term-open "$([ -n "$WSPATH" ] && echo 1 || echo 0)" "${TERM_PATH:-none} ws=${WSPATH:-none}"
COOKIE_VALUE=$(awk -v n="$COOKIE_NAME" '$6==n {print $7}' "$JAR" | tail -1)
out=$(python3 -I "$HERE/jweb-frontend-ws.py" "127.0.0.1" "$PORT" "$WSPATH" "$ORIGIN" "$COOKIE_NAME=$COOKIE_VALUE" "$SUBJECT" 2>"$R/ws.err"); ws_rc=$?
row term-whoami "$([ "$ws_rc" = 0 ] && echo 1 || echo 0)" "$(tail -c 200 <<<"$out" | tr '\n' ' ' | cut -c1-160) $(tail -1 "$R/ws.err")"
[ -n "${DOC:-}" ] || DOC="jwf$(od -An -N3 -tu4 /dev/urandom | tr -d ' ' | cut -c1-6)"
page=$(req POST /doc/new --data-urlencode "csrf=$CSRF" --data-urlencode "name=$DOC" --data-urlencode "law=note")
printf '%s\n' "$page" >"$R/doc-new.html"
row doc-new "$(grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o 'class="headline">[^<]*' <<<"$page" | head -1 | cut -c18-120)"
TEXT="hello from the browser $(date +%s)"
page=$(req POST "/doc/$DOC/append" --data-urlencode "csrf=$CSRF" --data-urlencode "text=$TEXT")
RID=$(grep -o '/receipts/w-[0-9a-f]*' <<<"$page" | head -1 | cut -d/ -f3)
docpage=$(req GET "/doc/$DOC")
row doc-append "$(grep -q 'outcome admitted' <<<"$page" && grep -q "$TEXT" <<<"$docpage" && echo 1 || echo 0)" "$(st) receipt=${RID:-none} $(grep -o 'class="headline">[^<]*' <<<"$page" | head -1 | cut -c18-120)"
page=$(req GET "/receipts/${RID:-none}")
row receipt "$([ "$(st)" = 200 ] && grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st)"
# The receipt's anchor: the sealed call's digest and the Host's confirmation point, labelled as a
# point and not as a proof (A10's inclusion opening is pending).
row receipt-anchor "$(grep -qE 'sha256 [0-9a-f]{64}' <<<"$page" && grep -q 'acceptedCount' <<<"$page" && grep -q 'inclusion proof pending' <<<"$page" && echo 1 || echo 0)" "$(grep -o 'acceptedCount [0-9?]*' <<<"$page" | head -1) $(grep -o 'worldRoot [0-9?]*' <<<"$page" | head -1)"
# Publication, end to end (lane/un-public-read): the member publishes DOC to the public reader (a second
# member with its own subject), the helper hands the reference over, and an ANONYMOUS visitor reads
# the text (200) on /doc/DOC and on the front page; an unpublished document (DOC2) is refused; after
# Unpublish the Host refuses the visitor again (403 no-grant). A grant whose cost ceiling is 0 covers no
# read, which is how every published document once answered 403.
anon() { curl -s -o "$R/anon.body" -w '%{http_code}' -m 60 "$BASE$1"; }
if [ "$mode" = --box ]; then
  printf 'UNCONFIGURED\tpublication\tthe box has its own public reader; seed.sh and the rehearsal check /welcome anonymously\n'
elif [ -z "${PUBREAD_SUBJECT:-}" ]; then
  row public-reader-member "0" "no second member could be provisioned (needs SPONSOR_WS): the publication rows cannot run"
else
  req POST /doc/new --data-urlencode "csrf=$CSRF" --data-urlencode "name=$DOC2" --data-urlencode "law=note" >/dev/null
  TEXT2="never published $(date +%s)"
  req POST "/doc/$DOC2/append" --data-urlencode "csrf=$CSRF" --data-urlencode "text=$TEXT2" >/dev/null
  page=$(req POST "/doc/$DOC/publish" --data-urlencode "csrf=$CSRF")
  row publish "$(grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o 'class="headline">[^<]*' <<<"$page" | head -1 | cut -c18-120)"
  # The helper's sweep runs every 60 s; the public body imports at its next render of / or /doc.
  pstatus=0; for _ in $(seq 1 24); do anon / >/dev/null; pstatus=$(anon "/doc/$DOC"); [ "$pstatus" = 200 ] && break; sleep 5; done
  row public-read-published "$([ "$pstatus" = 200 ] && grep -q "$TEXT" "$R/anon.body" && echo 1 || echo 0)" "anonymous GET /doc/$DOC -> $pstatus $(grep -o 'data-refusal>[^<]*' "$R/anon.body" | head -1 | cut -c1-140)"
  fstatus=$(anon /)
  row public-front-doc "$([ "$fstatus" = 200 ] && grep -q "$TEXT" "$R/anon.body" && echo 1 || echo 0)" "anonymous GET / -> $fstatus"
  ustatus=$(anon "/doc/$DOC2")
  row public-read-unpublished "$([ "$ustatus" != 200 ] && ! grep -q "$TEXT2" "$R/anon.body" && echo 1 || echo 0)" "anonymous GET /doc/$DOC2 -> $ustatus"
  page=$(req POST "/doc/$DOC/unpublish" --data-urlencode "csrf=$CSRF")
  row unpublish "$(grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o 'class="headline">[^<]*' <<<"$page" | head -1 | cut -c18-120)"
  rstatus=$(anon "/doc/$DOC")
  row public-read-revoked "$([ "$rstatus" = 403 ] && ! grep -q "$TEXT" "$R/anon.body" && echo 1 || echo 0)" "anonymous GET /doc/$DOC after unpublish -> $rstatus"
  # Published again (a new grant for the same document): the public reader replaces its dead reference
  # and the same name reads again (a re-run of the seed on a world that holds an older publication).
  page=$(req POST "/doc/$DOC/publish" --data-urlencode "csrf=$CSRF")
  pstatus=0; for _ in $(seq 1 24); do anon / >/dev/null; pstatus=$(anon "/doc/$DOC"); [ "$pstatus" = 200 ] && break; sleep 5; done
  row public-republish "$(grep -q 'outcome admitted' <<<"$page" && [ "$pstatus" = 200 ] && grep -q "$TEXT" "$R/anon.body" && echo 1 || echo 0)" "republish then anonymous GET /doc/$DOC -> $pstatus"
  # A house name is the operator's to give (/etc/mini/house-publications; here frontDoc is alice's and
  # `operations` is nobody's): alice's own document named `operations` reaches the public reader as
  # operations-alice, and the public index's operations room does not show it as the box's.
  req POST /doc/new --data-urlencode "csrf=$CSRF" --data-urlencode "name=operations" --data-urlencode "law=note" >/dev/null
  TEXT3="squatted operations $(date +%s)"
  req POST /doc/operations/append --data-urlencode "csrf=$CSRF" --data-urlencode "text=$TEXT3" >/dev/null
  page=$(req POST /doc/operations/publish --data-urlencode "csrf=$CSRF")
  qstatus=0; for _ in $(seq 1 24); do anon /doc >/dev/null; qstatus=$(anon /doc/operations-alice); [ "$qstatus" = 200 ] && break; sleep 5; done
  qread=$(grep -c "$TEXT3" "$R/anon.body")
  istatus=$(anon /doc)
  row public-house-name-reserved "$([ "$qstatus" = 200 ] && [ "$qread" -gt 0 ] && [ "$istatus" = 200 ] && ! grep -q "$TEXT3" "$R/anon.body" && echo 1 || echo 0)" \
    "member-published operations: GET /doc/operations-alice -> $qstatus (text $qread); GET /doc -> $istatus, operations room shows it: $(grep -c "$TEXT3" "$R/anon.body")"
fi
# Research consent (ember's ruling): the door wrote the member's fact at enrolment (ticked: CC0);
# /export shows it with the sentence; the member flips it there (a write on their own cell); the
# export's manifest carries the value the world holds.
page=$(req GET /export)
if [ -f "${M:-/nonexistent}/provisioned-this-run" ]; then
  row consent-enrol "$(grep -q 'field 1): <strong>contributed for research (CC0)' <<<"$page" && grep -q 'Data is not retained after' <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o 'field 1): <strong>[^<]*' <<<"$page" | sed 's/.*<strong>//')"
else
  row consent-enrol "$(grep -qE 'field 1\): <strong>(contributed for research \(CC0\)|not contributed)' <<<"$page" && echo 1 || echo 0)" "reused member: $(grep -o 'field 1): <strong>[^<]*' <<<"$page" | sed 's/.*<strong>//')"
fi
rm -f "${M:-/nonexistent}/provisioned-this-run"
if grep -q 'field 1): <strong>contributed for research (CC0)' <<<"$page"; then CWANT=none; CARGS=(); else CWANT=cc0; CARGS=(--data-urlencode "choice=cc0"); fi
page=$(req POST /export/consent --data-urlencode "csrf=$CSRF" "${CARGS[@]}")
cflip=$(grep -o 'class="headline">[^<]*' <<<"$page" | head -1 | cut -c18-120)
page=$(req GET /export)
want_text=$([ "$CWANT" = cc0 ] && echo 'contributed for research (CC0)' || echo 'not contributed')
row consent-flip "$(grep -q "field 1): <strong>$want_text" <<<"$page" && echo 1 || echo 0)" "to $CWANT: $cflip"
# The subscriber tier's page: what it buys (from the provider table, when the box has the row),
# the policy line marked for ember, the price and window from the room, the two forms.
page=$(req GET /subscribe)
row subscribe-page "$([ "$(st)" = 200 ] && grep -q 'action="/subscribe/pay"' <<<"$page" && grep -q 'action="/subscribe/join"' <<<"$page" && grep -q 'Data is not retained after' <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o 'model calls a day' <<<"$page" | head -1)"
# Export my world (the 11 November shutdown): start, wait until it is ready, read the document page
# (its stamp carries the read's height and world root), download (streamed through the gateway,
# then deleted on the box), untar: the document's text and the manifest's root are the live world's.
page=$(req POST /export --data-urlencode "csrf=$CSRF")
XNAME=$(grep -o 'Preparing <code>world-[0-9]*' <<<"$page" | sed 's/.*<code>//' | head -1)
row export-start "$([ -n "$XNAME" ] && echo 1 || echo 0)" "$(st) ${XNAME:-no name}"
xready=0; xstart=$(date +%s)
# The export reads every document the member holds (one signed read each): its time is published
# in the row, and the wait is generous (JWF_EXPORT_WAIT_S, 900).
for i in $(seq 1 $(( ${JWF_EXPORT_WAIT_S:-900} / 5 ))); do
  page=$(req GET /export); grep -q "action=\"/export/$XNAME/download\"" <<<"$page" && { xready=1; break; }
  grep -q "<code>$XNAME</code> ended without an archive" <<<"$page" && break
  sleep 5
done
row export-ready "$xready" "$(st) after $(( $(date +%s) - xstart )) s, $(ls "$M/home/workspace/refs" 2>/dev/null | wc -l | tr -d ' ') references $(grep -o "<code>$XNAME</code> ended without an archive: <code>[^<]*" <<<"$page" | sed 's/.*<code>//' | cut -c1-160)"
docpage=$(req GET "/doc/$DOC")
LIVE_H=$(grep -o 'data-height="[0-9]*"' <<<"$docpage" | head -1 | grep -o '[0-9]*')
LIVE_W=$(grep -o 'data-world-root="[^"]*"' <<<"$docpage" | head -1 | sed 's/.*="//; s/"$//')
XCSRF=$(csrf_of)
curl -s -o "$R/export.tar" -D "$R/xh" -w '%{http_code}' -X POST -b "$JAR" -c "$JAR" -H "Origin: $ORIGIN" -H 'Sec-Fetch-Site: same-origin' \
  --data-urlencode "csrf=${XCSRF:-$CSRF}" "$BASE/export/$XNAME/download" >"$R/status"
xtype=$(grep -i '^content-type:' "$R/xh" | tr -d '\r' | cut -d' ' -f2)
row export-download "$([ "$(st)" = 200 ] && [ "$xtype" = application/x-tar ] && [ -s "$R/export.tar" ] && echo 1 || echo 0)" "$(st) $xtype $(wc -c <"$R/export.tar" | tr -d ' ') bytes"
page=$(req GET /export)
row export-deleted "$(grep -q "/export/$XNAME/download" <<<"$page" && echo 0 || echo 1)" "the box keeps no copy once downloaded"
rm -rf "$R/export"; mkdir -p "$R/export"; tar -xf "$R/export.tar" -C "$R/export" 2>"$R/export.err"
XM="$R/export/mini-export/manifest.json"
row export-document "$([ -f "$XM" ] && grep -qF "$TEXT" "$R/export/mini-export/documents/$DOC.txt" 2>/dev/null && echo 1 || echo 0)" "$(head -c 200 "$R/export.err") documents=$(jq '.documents|length' "$XM" 2>/dev/null) attempts=$(jq '.attempts|length' "$XM" 2>/dev/null)"
XH=$(jq -r '.height // ""' "$XM" 2>/dev/null); XW=$(jq -r '.worldRoot // ""' "$XM" 2>/dev/null)
row export-consent "$([ "$(jq -r '.researchConsent // ""' "$XM" 2>/dev/null)" = "$CWANT" ] && echo 1 || echo 0)" "manifest $(jq -r '.researchConsent // "absent"' "$XM" 2>/dev/null), the world $CWANT"
row export-root "$([ -n "$XW" ] && [ "$XW" = "$LIVE_W" ] && [ "$XH" = "$LIVE_H" ] && echo 1 || echo 0)" "manifest height $XH root $(cut -c1-16 <<<"$XW") | live height $LIVE_H root $(cut -c1-16 <<<"$LIVE_W")"
# The private-room shape of `room invite` (parity's one world leaf): this member founds a private
# room; the sponsor, as invitee, signs its key declaration into HOME/requests/decl.json.
shell_as_member() { "$MINI" shell --socket "$SOCKET" --workspace "$WS" --home "${HOMEDIR:-$R/home}" --host "$HOST" --config "$CONFIG" --line "$1" 2>"$R/shell.err"; }
if [ -n "${SPONSOR_WS:-}" ] && [ -f "$SPONSOR_WS/workspace.json" ]; then
  PRIV="priv$(od -An -N3 -tu4 /dev/urandom | tr -d ' ' | cut -c1-6)"
  # A private room's keys live in the member's encrypted key cache, under a passphrase the member
  # holds (FRIENDS.md); the journey's member holds one for this step.
  MINI_KEYCACHE_PASSPHRASE=jwf-cache-pass shell_as_member "room new $PRIV --private" >"$R/priv.out"; priv_rc=$?
  if [ "$priv_rc" = 0 ] && [ -f "$WS/refs/$PRIV.json" ]; then
    rid=$(jq -r .target "$WS/refs/$PRIV.json"); kid=$(jq -r .private.keys "$WS/refs/$PRIV.json")
    fk=$(od -An -tx1 -v "${HOMEDIR:-$R/home}/keys/mini.key.pub" | tr -d ' \n')
    ke=$("$MINI" key-status --workspace "$SPONSOR_WS" 2>/dev/null | jq -r .keyEpoch)
    "$MINI" workspace --action room-key --op recipient-record --dir "$SPONSOR_WS" --room-id "$rid" --keys-cell "$kid" --key-epoch "$ke" --founder-key "$fk" >"${HOMEDIR:-$R/home}/requests/decl.json" 2>"$R/decl.err"; decl_rc=$?
  else decl_rc=1; fi
  row private-room "$([ "$priv_rc" = 0 ] && [ "${decl_rc:-1}" = 0 ] && jq -e '.type == "minidregg-signed-room-recipient-v3"' "${HOMEDIR:-$R/home}/requests/decl.json" >/dev/null 2>&1 && echo 1 || echo 0)" "room new $PRIV --private rc=$priv_rc; declaration rc=${decl_rc:-1} $(tail -1 "$R/shell.err" 2>/dev/null | cut -c1-100) $(tail -1 "$R/decl.err" 2>/dev/null | cut -c1-100)"
fi
headline() { grep -o 'class="headline">[^<]*' <<<"$1" | head -1 | cut -c18-160; }
# What Hermes may do in a room (the room's hermes/tools and hermes/compute, docs/HERMES-TOOLS-2026-10-27.md
# §3, §5): this member founds a room; its resident page draws the grant and gives the founder the form;
# each change is the `tariff ROOM set` leaf's outcome.
HT="ht$(od -An -N3 -tu4 /dev/urandom | tr -d ' ' | cut -c1-6)"
page=$(req POST /room/new --data-urlencode "csrf=$CSRF" --data-urlencode "name=$HT" --data-urlencode "law=open")
ht_new=$(headline "$page")
page=$(req GET "/room/$HT/resident")
row hermes-tools-none "$([ "$(st)" = 200 ] && grep -q 'data-hermes-tools="0"' <<<"$page" && grep -q "action=\"/room/$HT/hermes-tools\"" <<<"$page" && echo 1 || echo 0)" "$(st) room new: $ht_new; $(grep -o 'data-hermes-tools="[0-9]*"' <<<"$page" | head -1)"
page=$(req POST "/room/$HT/hermes-tools" --data-urlencode "csrf=$CSRF" --data-urlencode "tool1=on" --data-urlencode "tool8=on" --data-urlencode "compute=0" --data-urlencode "was-tools=0" --data-urlencode "was-compute=0")
ht_grant=$(headline "$page")
page2=$(req GET "/room/$HT/resident")
row hermes-tools-grant "$(grep -q 'outcome admitted' <<<"$page" && grep -q "tariff $HT set hermes/tools 9" <<<"$page" && grep -q 'data-hermes-tools="9"' <<<"$page2" && grep -q 'data-tool="oracle" data-granted="true"' <<<"$page2" && echo 1 || echo 0)" "$ht_grant; then $(grep -o 'data-hermes-tools="[0-9]*"' <<<"$page2" | head -1)"
page=$(req POST "/room/$HT/hermes-tools" --data-urlencode "csrf=$CSRF" --data-urlencode "tool1=on" --data-urlencode "compute=0" --data-urlencode "was-tools=9" --data-urlencode "was-compute=0")
ht_revoke=$(headline "$page")
page2=$(req GET "/room/$HT/resident")
row hermes-tools-revoke "$(grep -q 'outcome admitted' <<<"$page" && grep -q 'data-hermes-tools="1"' <<<"$page2" && grep -q 'data-tool="oracle" data-granted="false"' <<<"$page2" && grep -q 'data-tool="files" data-granted="true"' <<<"$page2" && echo 1 || echo 0)" "$ht_revoke; then $(grep -o 'data-hermes-tools="[0-9]*"' <<<"$page2" | head -1)"
# A document is not a room: the same grant on it is refused (by the client or the Host), never admitted.
page=$(req POST "/room/$DOC/hermes-tools" --data-urlencode "csrf=$CSRF" --data-urlencode "tool8=on" --data-urlencode "was-tools=0" --data-urlencode "was-compute=0")
row hermes-tools-refused "$(grep -qE 'outcome (refused|error)' <<<"$page" && ! grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st) $(headline "$page")"
# Programs (/bend): the workspace's bend registry and any activity read through `bend await`; an answer
# to a slot this member does not decide (here: a slot no program opened) is refused through the
# derived `bend answer` form.
page=$(req GET /bend)
row bend-programs "$([ "$(st)" = 200 ] && grep -q 'action="/bend/await"' <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -c 'data-object=' <<<"$page") programs"
HT_CELL=$(jq -r '.target // empty' "$WS/refs/$HT.json" 2>/dev/null)
page=$(req GET "/bend/await?object=${HT_CELL:-1}&transaction=1")
row bend-await-read "$({ [ "$(st)" = 200 ] && grep -q 'data-phase="none"' <<<"$page"; } || { [ "$(st)" = 403 ] && grep -qE 'outcome (refused|error)' <<<"$page"; } && echo 1 || echo 0)" "$(st) object ${HT_CELL:-1}: $(grep -o 'data-phase="[^"]*"' <<<"$page" | head -1) $(headline "$page")"
vb=$(req GET /verb/bend)
a=$(tr -d '\n' <<<"$vb" | awk -v lit="<code>bend answer</code>" 'BEGIN{RS="</form>"} index($0, lit) {match($0,/name="alt" value="[0-9]+"/); print substr($0,RSTART+18,RLENGTH-19); exit}')
set -- $(tr -d '\n' <<<"$vb" | awk -v lit="<code>bend answer</code>" 'BEGIN{RS="</form>"} index($0, lit) {while (match($0,/name="a[0-9]+"/)) {print substr($0,RSTART+6,RLENGTH-7); $0=substr($0,RSTART+RLENGTH)}; exit}' | tr '\n' ' ')
page=$(req POST /verb/bend --data-urlencode "csrf=$CSRF" --data-urlencode "alt=${a:-6}" --data-urlencode "${1:-a2}=1" --data-urlencode "${2:-a3}={\"reply\": {\"tag\": \"natural\", \"value\": \"7\"}}")
row bend-answer-refused "$(grep -q 'outcome refused' <<<"$page" && echo 1 || echo 0)" "$(st) alt=${a:-?} $(headline "$page")"
# Parity (docs/DEMO-EXPERIENCE-2026-10-27.md §1a): every verb the shell's `help` lists has a form at
# /verb/NAME in the body; a verb with no face is red by name.
help=$("$MINI" shell --socket "$SOCKET" --workspace "$WS" --home "${HOMEDIR:-$R/home}" --host "$HOST" --config "$CONFIG" --line help 2>/dev/null)
# PARITY: every verb x subcommand leaf
# the shell's `help` lists (each usage alternative's leading literal words) has a route and a no-JS
# form in the body; a leaf without one is red by name.
verbs=$(awk '/^  [a-z][a-z-]* / {print $1}' <<<"$help" | sort -u)
missing=""; count=0; leaves=0
# The usage words below are split unquoted; a bracketed flag such as [--json] is a glob that matches a
# one-letter file in the working directory (a file named j turned `apps list [--json]` into `apps list j`).
set -f
for v in $verbs; do
  count=$((count + 1))
  page=$(req GET "/verb/$v")
  if [ "$(st)" != 200 ] || ! grep -q "action=\"/verb/$v\"" <<<"$page"; then missing="$missing $v"; continue; fi
  usage=$(awk -v v="$v" '$1==v && /^  [a-z]/ {sub(/^  [a-z-]+ +/, ""); print; exit}' <<<"$help")
  while IFS= read -r alt; do
    lits=""; for w in $alt; do case $w in [a-z]*) [[ $w =~ ^[a-z/-]+$ ]] && lits="$lits $w" || break;; *) break;; esac; done
    lits=${lits# }; [ -n "$lits" ] || continue
    leaves=$((leaves + 1))
    grep -qF "<h2><code>$lits</code></h2>" <<<"$page" || missing="$missing $v($lits)"
  done < <(sed 's/ | /\n/g' <<<"$usage")
done
set +f
# PARITY = every leaf has a route and a no-JS form (above) AND its placeholder-filled form assembles
# to a line the shell's planner accepts (`/verb/NAME/dry`: the real parser and plan builder, no Host).
mkdir -p "${HOMEDIR:-$R/home}/requests" "${HOMEDIR:-$R/home}/keys"; printf 'hello\n' >"${HOMEDIR:-$R/home}/requests/x.txt"; printf '{}\n' >"${HOMEDIR:-$R/home}/requests/x.json"; printf 'k\n' >"${HOMEDIR:-$R/home}/keys/x.txt"
dry_leaves=0; dry_errors=0; dry_bad=""; dry_world=0; dry_world_names=""
mkdir -p "$R/dry"
for v in $verbs; do
  page=$(req GET "/verb/$v/dry")
  printf '%s\n' "$page" >"$R/dry/$v.html"
  l=$(grep -o 'data-leaves="[0-9]*"' <<<"$page" | grep -o '[0-9]*'); e=$(grep -o 'data-errors="[0-9]*"' <<<"$page" | grep -o '[0-9]*')
  w=$(grep -o 'data-world="[0-9]*"' <<<"$page" | grep -o '[0-9]*')
  dry_leaves=$((dry_leaves + ${l:-0})); dry_errors=$((dry_errors + ${e:-0})); dry_world=$((dry_world + ${w:-0}))
  [ "${e:-1}" = 0 ] || dry_bad="$dry_bad $v($(grep -o '<tr class="usage"><td><code>[^<]*' <<<"$page" | sed 's/.*<code>//' | tr '\n' ',' | cut -c1-80))"
  [ "${w:-0}" = 0 ] || dry_world_names="$dry_world_names $v($(grep -o '<tr class="world"><td><code>[^<]*' <<<"$page" | sed 's/.*<code>//' | tr '\n' ',' | cut -c1-80))"
done
# A `world` leaf parsed but this workspace could not plan it (an open room given a private room's
# declaration): not a form/parser disagreement; it is named, and its outcome is a spine row's.
row parity "$([ "$count" -gt 40 ] && [ "$leaves" -gt 100 ] && [ -z "$missing" ] && [ "$dry_errors" = 0 ] && [ "$dry_leaves" -ge "$leaves" ] && echo 1 || echo 0)" "$count verbs, $leaves leaves in help, $dry_leaves dry-run leaves, $dry_errors usage refusals, $dry_world world refusals; without a face:${missing:- none}; usage:${dry_bad:- none}; world:${dry_world_names:- none}"
# Red-proof: a verb the shell does not have must have no face (the check can go red).
req GET /verb/no-such-verb-x >/dev/null
row parity-redproof "$([ "$(st)" = 404 ] && echo 1 || echo 0)" "$(st) for a verb the shell lacks"
page=$(req GET /verb)
row verb-index "$([ "$(st)" = 200 ] && grep -q '/verb/delegate' <<<"$page" && echo 1 || echo 0)" "$(st)"
page=$(req POST /verb/whoami --data-urlencode "csrf=$CSRF" --data-urlencode "alt=0")
row verb-run "$(grep -q 'outcome answered' <<<"$page" && grep -q "$SUBJECT" <<<"$page" && echo 1 || echo 0)" "$(st) whoami through the derived form answers (a local verb, never admitted)"
# The tour (DEMO-EXPERIENCE §1): twelve steps whose forms are the real forms; step 4's `can` runs
# through /tour/4 and its outcome lands under the step.
page=$(req GET /tour)
row tour "$([ "$(st)" = 200 ] && [ "$(grep -c 'class="step"' <<<"$page")" = 12 ] && grep -q 'action="/tour/4"' <<<"$page" && echo 1 || echo 0)" "$(st) steps=$(grep -c 'class="step"' <<<"$page")"
# `can DOC`, one reference: bare `can` dry-runs every grant the member holds (op 130 each) and on a
# used workspace outlasts the gateway's two minutes, and the body answers one request at a time.
page=$(req POST /tour/4 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=can" --data-urlencode "alt=0" --data-urlencode "a1=$DOC")
# `can` is a read (op 130 dry-runs, never submits): its outcome class is `answered`, never a
# world transition; a Host that lacks op 130 answers it undecided, which is red here by design.
row tour-step "$(grep -q 'id="step-4"' <<<"$page" && grep -q 'step-outcome' <<<"$page" && grep -q 'outcome answered' <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o 'class="headline">[^<]*' <<<"$page" | head -1 | cut -c18-100)"
# The tour's lost reply (DEMO-EXPERIENCE A11): the append form with `lose this reply once` comes
# back undecided with its retained attempt; the retry shows the decided outcome; one line landed.
alt=$(tr -d '\n' <<<"$page" | awk 'BEGIN{RS="</form>"} /name="lose"/ {match($0,/name="alt" value="[0-9]+"/); print substr($0,RSTART+18,RLENGTH-19); exit}')
fields=$(tr -d '\n' <<<"$page" | awk 'BEGIN{RS="</form>"} /name="lose"/ {while (match($0,/name="a[0-9]+"/)) {print substr($0,RSTART+6,RLENGTH-7); $0=substr($0,RSTART+RLENGTH)}; exit}' | tr '\n' ' ')
set -- $fields; F_ID=${1:-a2}; F_NAME=${2:-a3}; F_TEXT=${3:-a4}
LOSE_ID="w-$(od -An -N6 -tx1 /dev/urandom | tr -d ' \n')"; LOSE_TEXT="lost once $(date +%s)"
page=$(req POST /tour/3 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=doc" --data-urlencode "alt=${alt:-0}" --data-urlencode "$F_ID=$LOSE_ID" --data-urlencode "$F_NAME=$DOC" --data-urlencode "$F_TEXT=$LOSE_TEXT" --data-urlencode "submit=on" --data-urlencode "lose=on")
row tour-lose "$(grep -q 'outcome undecided' <<<"$page" && grep -q "/receipts/$LOSE_ID" <<<"$page" && echo 1 || echo 0)" "$(st) alt=${alt:-?} fields=$F_ID,$F_NAME,$F_TEXT $(grep -o 'class="headline">[^<]*' <<<"$page" | head -1 | cut -c18-140)"
page=$(req POST "/receipts/$LOSE_ID/retry" --data-urlencode "csrf=$CSRF")
docpage=$(req GET "/doc/$DOC")
row tour-lose-retry "$(grep -q 'outcome admitted' <<<"$page" && [ "$(grep -c "$LOSE_TEXT" <<<"$docpage")" = 1 ] && echo 1 || echo 0)" "$(st) lines=$(grep -c "$LOSE_TEXT" <<<"$docpage") $(grep -o 'class="headline">[^<]*' <<<"$page" | head -1 | cut -c18-120)"
# The tour's refusal and the write its law admits (step 4): editing a line of the note through
# the editor (the pinned read, then the save) is refused by the note's law (`content/atom-edits
# == 0`); `can --any` on the note answers the law and one write it admits (as slot witnesses: the
# shell line to paste is lawsat's to print); the append, the write the law admits, is admitted.
pre_of() { python3 -I -c 'import sys,re,html; page=re.sub(r"<section class=\"ops.*?</section>", "", sys.stdin.read(), flags=re.S); m=re.search(r"<pre>(.*?)</pre>", page, re.S); print(html.unescape(m.group(1)) if m else "")'; }
page=$(req GET "/doc/$DOC/edit")
EDIT_URL=$(grep -o 'action="/doc/[^"]*/edit/[^"/]*"' <<<"$page" | head -1 | sed 's/action="//; s/"$//')
NEWTEXT=$(python3 -I -c 'import sys,re,html; m=re.search(r"<textarea name=text[^>]*>\n?(.*?)</textarea>", sys.stdin.read(), re.S); t=html.unescape(m.group(1)) if m else ""; lines=t.split("\n"); lines[0]="edited: " + lines[0] if lines else ["edited"]; print("\n".join(lines))' <<<"$page")
page=$(req POST "${EDIT_URL:-/doc/$DOC/edit/none}" --data-urlencode "csrf=$CSRF" --data-urlencode "text=$NEWTEXT")
row tour-refused "$(grep -q 'data-save-status="refused"' <<<"$page" && echo 1 || echo 0)" "$(st) ${EDIT_URL:-no editor form} $(grep -o 'data-save-status="[a-z]*"[^>]*>[^<]*' <<<"$page" | head -1 | cut -c1-160)"
page=$(req POST /tour/4 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=can" --data-urlencode "alt=0" --data-urlencode "a1=$DOC" --data-urlencode "a3=on")
can_text=$(pre_of <<<"$page")
# The line `can --any` composed from the grammar leaf of the witnessed verb (`doc append ID DOC
# 'hello'`), offered as "paste and submit", is submitted and admitted.
paste_line=$(grep -A1 '^ *paste:' <<<"$can_text" | tail -1 | sed 's/^ *//')
page2=$(req POST /paste --data-urlencode "csrf=$CSRF" --data-urlencode "line=$paste_line")
row tour-can-any "$(grep -q 'outcome answered' <<<"$page" && grep -q 'law version' <<<"$can_text" && grep -q 'action="/paste"' <<<"$page" && [ -n "$paste_line" ] && grep -q 'outcome admitted' <<<"$page2" && echo 1 || echo 0)" "$(st) can --any $DOC: $(tr '\n' ' ' <<<"$can_text" | cut -c1-160) | paste=${paste_line:-none}: $(grep -o 'class="headline">[^<]*' <<<"$page2" | head -1 | cut -c18-60)"
# A tour form's alternative index and its field names, by the form's literals (its <h2><code>).
alt_of() { tr -d '\n' <<<"$1" | awk -v lit="<code>$2</code>" 'BEGIN{RS="</form>"} index($0, lit) {match($0,/name="alt" value="[0-9]+"/); print substr($0,RSTART+18,RLENGTH-19); exit}'; }
fields_of() { tr -d '\n' <<<"$1" | awk -v lit="<code>$2</code>" 'BEGIN{RS="</form>"} index($0, lit) {while (match($0,/name="a[0-9]+"/)) {print substr($0,RSTART+6,RLENGTH-7); $0=substr($0,RSTART+RLENGTH)}; exit}' | tr '\n' ' '; }
tour=$(req GET /tour)
# Door 12, "changes the rules" (DEMO-EXPERIENCE A7): a law on the member's own document that
# refuses their append but admits installs (so it stays changeable). `law check` first (a read:
# answered, a write exists in principle); install (admitted); the append refused with the clause;
# the revised law admitted; the append admitted.
RULES="rules$(od -An -N3 -tu4 /dev/urandom | tr -d ' ' | cut -c1-6)"
req POST /doc/new --data-urlencode "csrf=$CSRF" --data-urlencode "name=$RULES" --data-urlencode "law=note" >/dev/null
STRICT='any [ not (verb == write), slot "content/payload-bytes/after" <= 0 ]'
LOOSE='any [ not (verb == write), slot "content/payload-bytes/after" <= 16384 ]'
a=$(alt_of "$tour" "law check"); set -- $(fields_of "$tour" "law check"); F_LAW=${1:-a2}
page=$(req POST /tour/12 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=law" --data-urlencode "alt=${a:-0}" --data-urlencode "$F_LAW=$STRICT")
row rules-check "$(grep -q 'id="step-12"' <<<"$page" && grep -q 'outcome answered' <<<"$page" && echo 1 || echo 0)" "$(st) alt=${a:-?} $(headline "$page") $(pre_of <<<"$page" | tr '\n' ' ' | cut -c1-120)"
a=$(alt_of "$tour" "law"); set -- $(fields_of "$tour" "law"); F_ID=${1:-a1}; F_REF=${2:-a2}; F_LAW=${3:-a3}
LID="w-$(od -An -N6 -tx1 /dev/urandom | tr -d ' \n')"
page=$(req POST /tour/12 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=law" --data-urlencode "alt=${a:-0}" --data-urlencode "$F_ID=$LID" --data-urlencode "$F_REF=$RULES" --data-urlencode "$F_LAW=$STRICT" --data-urlencode "submit=on")
row rules-install "$(grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st) alt=${a:-?} fields=$F_ID,$F_REF,$F_LAW $(headline "$page")"
page=$(req POST "/doc/$RULES/append" --data-urlencode "csrf=$CSRF" --data-urlencode "text=under the strict law")
row rules-refused "$(grep -q 'outcome refused' <<<"$page" && grep -q '<mark class="clause">' <<<"$page" && echo 1 || echo 0)" "$(st) $(headline "$page")"
LID2="w-$(od -An -N6 -tx1 /dev/urandom | tr -d ' \n')"
page=$(req POST /tour/12 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=law" --data-urlencode "alt=${a:-0}" --data-urlencode "$F_ID=$LID2" --data-urlencode "$F_REF=$RULES" --data-urlencode "$F_LAW=$LOOSE" --data-urlencode "submit=on")
row rules-revised "$(grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st) $(headline "$page")"
page=$(req POST "/doc/$RULES/append" --data-urlencode "csrf=$CSRF" --data-urlencode "text=under the revised law")
row rules-admitted "$(grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st) $(headline "$page")"
# The tour runs no shell itself: its purse meter fills in after the page (data-load).
page=$(req GET /tour)
row tour-purse-later "$(grep -q 'data-load="/purse/meter"' <<<"$page" && echo 1 || echo 0)" "$(st)"
page=$(req GET /purse/meter)
row purse-meter "$(grep -q '<meter ' <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o 'class="n">[0-9]*' <<<"$page" | head -1)"
# Door 11, the story (A7): the built-in tale; the member is author and, invited by themself,
# player; one legal move admitted; the impossible move refused beside the theorem's name.
TALE="tale$(od -An -N3 -tu4 /dev/urandom | tr -d ' ' | cut -c1-6)"
a=$(alt_of "$tour" "story new"); set -- $(fields_of "$tour" "story new"); F_NAME=${1:-a2}; F_FROM=${2:-a3}
page=$(req POST /tour/11 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=story" --data-urlencode "alt=${a:-0}" --data-urlencode "$F_NAME=$TALE" --data-urlencode "$F_FROM=tale")
# The tale's template is nineteen transitions (minutes on a used world): past the body's 100 s the
# page answers undecided ("still deciding") and the shell runs on to its decision; the seal is then
# retried, as a member would, until the story exists (at most six minutes).
ok=0; grep -q 'outcome admitted' <<<"$page" && ok=1; grep -q 'still deciding' <<<"$page" && ok=1
row story-new "$ok" "$(st) alt=${a:-?} fields=$F_NAME,$F_FROM $(headline "$page") $(pre_of <<<"$page" | head -2 | tr '\n' ' ' | cut -c1-100)"
a=$(alt_of "$tour" "story seal"); set -- $(fields_of "$tour" "story seal"); F_NAME=${1:-a2}
for i in $(seq 1 24); do
  page=$(req POST /tour/11 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=story" --data-urlencode "alt=${a:-0}" --data-urlencode "$F_NAME=$TALE")
  grep -q 'has no story' <<<"$page" || break
  sleep 15
done
row story-seal "$(grep -q 'outcome admitted' <<<"$page" && echo 1 || echo 0)" "$(st) $(headline "$page")"
a=$(alt_of "$tour" "story invite"); set -- $(fields_of "$tour" "story invite"); F_NAME=${1:-a2}; F_SUBJ=${2:-a3}
page=$(req POST /tour/11 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=story" --data-urlencode "alt=${a:-0}" --data-urlencode "$F_NAME=$TALE" --data-urlencode "$F_SUBJ=$SUBJECT" --data-urlencode "submit=on")
INVITE=$(pre_of <<<"$page" | sed -n "s/^story join $TALE //p" | head -1)
row story-invite "$(grep -q 'outcome admitted' <<<"$page" && [ -n "$INVITE" ] && echo 1 || echo 0)" "$(st) $(headline "$page") invitation=$(cut -c1-60 <<<"$INVITE")"
# Stories (/story): the invitation where the door hands one (HOME/requests/NAME-invite.json) is shown
# with the derived `story join` form filled in (the member founded the tale, so it holds it as author
# and the player's invitation still waits); the front page says it waits. An invitation addressed to
# someone else is listed without a form, and its join is refused by the shell.
HM=${HOMEDIR:-$R/home}; mkdir -p "$HM/requests"
[ -n "$INVITE" ] && printf '%s\n' "$INVITE" >"$HM/requests/$TALE-invite.json"
[ -n "$INVITE" ] && jq -c '.grant.recipient = "1"' <<<"$INVITE" >"$HM/requests/$TALE-other.json" 2>/dev/null
page=$(req GET /story); printf '%s' "$page" >"$R/story.html"
row story-page-invited "$([ "$(st)" = 200 ] && grep -q "data-story=\"$TALE\" data-file=\"$TALE-invite.json\" data-to-me=\"true\"" <<<"$page" && grep -q "value=\"@$TALE-invite.json\"" <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o 'data-story="[^"]*" data-file="[^"]*" data-to-me="[a-z]*"' <<<"$page" | tr '\n' ' ' | cut -c1-200)"
front=$(req GET /)
row story-front-notice "$(grep -q 'data-invited="[1-9]' <<<"$front" && grep -q "<code>$TALE</code>" <<<"$front" && echo 1 || echo 0)" "$(st) $(grep -o 'data-invited="[0-9]*"' <<<"$front" | head -1)"
# The /story page's form for one invitation, its fields as the page filled them (name=value lines).
story_form() { python3 -I - "$R/story.html" "$1" <<'PY'
import sys, re, html
page, mark = open(sys.argv[1]).read(), sys.argv[2]
for art in page.split("</article>"):
    art = art[art.rfind("<article"):]
    if mark in art:
        m = re.search(r"<form[^>]*>(.*?)</form>", art, re.S)
        for tag in re.findall(r"<(?:input|textarea)[^>]*>", m.group(1) if m else ""):
            n, v = re.search(r'name="([^"]*)"', tag), re.search(r'value="([^"]*)"', tag)
            if n and 'type="checkbox"' not in tag:
                print(n.group(1) + "=" + html.unescape(v.group(1) if v else ""))
        break
PY
}
other_form=$(story_form "data-file=\"$TALE-other.json\"")
o_alt=$(story_form "data-file=\"$TALE-invite.json\"" | sed -n 's/^alt=//p')
page=$(req POST /verb/story --data-urlencode "csrf=$CSRF" --data-urlencode "alt=${o_alt:-3}" --data-urlencode "a2=$TALE" --data-urlencode "a3=@$TALE-other.json")
row story-join-refused "$([ -z "$other_form" ] && grep -q "data-file=\"$TALE-other.json\" data-to-me=\"false\"" "$R/story.html" && grep -qE 'outcome (refused|error)' <<<"$page" && grep -q 'not addressed to you' <<<"$page" && echo 1 || echo 0)" "$(st) form for another's invitation: ${other_form:-none}; $(headline "$page")"
rm -f "$HM/requests/$TALE-other.json"
# The join, through the /story page's own filled form (the place the stranger's invitation is shown).
args=(); while IFS= read -r kv; do [ -n "$kv" ] && args+=(--data-urlencode "$kv"); done < <(story_form "data-file=\"$TALE-invite.json\"")
page=$(req POST /verb/story --data-urlencode "csrf=$CSRF" "${args[@]}")
row story-join "$(grep -q 'outcome answered' <<<"$page" && grep -q 'joined' <<<"$page" && echo 1 || echo 0)" "$(st) fields=${#args[@]} $(headline "$page") $(pre_of <<<"$page" | head -1 | cut -c1-100)"
page=$(req GET /story)
row story-page-joined "$(grep -q "<tr data-story=\"$TALE\"><td><code>$TALE</code>" <<<"$page" && ! grep -q "data-file=\"$TALE-invite.json\"" <<<"$page" && echo 1 || echo 0)" "$(st) $(grep -o "<tr data-story=\"$TALE\">.\{0,120\}" <<<"$page" | head -1 | sed 's/<[^>]*>/ /g')"
page=$(req POST /tour/11 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=go" --data-urlencode "alt=0" --data-urlencode "a1=north")
row story-move "$(grep -q 'outcome admitted' <<<"$page" && grep -q 'anteroom' <<<"$page" && echo 1 || echo 0)" "$(st) $(headline "$page") $(pre_of <<<"$page" | head -1 | cut -c1-100)"
page=$(req POST /tour/11 --data-urlencode "csrf=$CSRF" --data-urlencode "verb=go" --data-urlencode "alt=0" --data-urlencode "a1=north")
# The theorem's name is also static tour copy: a rate refusal must not pass
# this row merely because that copy is present. Require the actual law clause.
printf '%s' "$page" >"$R/story-refused.html"
row story-refused "$(grep -q 'outcome refused' <<<"$page" && pre_of <<<"$page" | grep -q 'law-denied:' && grep -q 'sealed_story_scene_monotone' <<<"$page" && grep -q "proved for the built-in tale" <<<"$page" && echo 1 || echo 0)" "$(st) $(headline "$page")"
# A used workspace: ~40 more grants (one document each). The Grants page answers at once and
# judges one grant per request (never a 504); one judge answers; a bare `can` through the form
# ends within the body's deadline, as the whole answer or as the named notice, never a 504.
for i in $(seq -w 1 40); do req POST /doc/new --data-urlencode "csrf=$CSRF" --data-urlencode "name=zz-grant-$i" --data-urlencode "law=note" >/dev/null; done
page=$(req GET /grants)
n_load=$(grep -o 'data-load="/grants/judge/' <<<"$page" | wc -l | tr -d ' ')
row grants-many "$([ "$(st)" = 200 ] && [ "$n_load" -ge 40 ] && echo 1 || echo 0)" "$(st) $n_load grants listed, each judged on its own"
page=$(req GET "/grants/judge/$DOC")
row grants-judge "$([ "$(st)" = 200 ] && grep -q 'held:' <<<"$page" && echo 1 || echo 0)" "$(st) $(pre_of <<<"$page" | head -1 | cut -c1-100)"
page=$(req POST /verb/can --data-urlencode "csrf=$CSRF" --data-urlencode "alt=0")
row can-bare "$([ "$(st)" != 504 ] && [ "$(st)" != 502 ] && { grep -q 'outcome answered' <<<"$page" || grep -q 'grants judged within' <<<"$page"; } && echo 1 || echo 0)" "$(st) $(headline "$page") $(grep -o '[0-9]* of [0-9]* grants judged[^<]*' <<<"$page" | head -1)"
# The same, headless through Chromium (jtour.mjs), with a second one-time code; needs Playwright.
PW=${PLAYWRIGHT_DIR:-$HOME/tools/playwright/node_modules}
if [ -f "$PW/playwright/index.mjs" ] && command -v node >/dev/null && [ "$mode" != --box ]; then
  CODE2=$(token); printf '{"name":"alice","expires":%d}\n' "$(( $(date +%s) + 3600 ))" >"$R/state/logins/$(sha256 "$CODE2").json"
  out=$(PLAYWRIGHT_DIR=$PW node "$HERE/jtour.mjs" "$BASE" "$CODE2" "$SUBJECT" "$DOC" 2>"$R/jtour.err"); rc=$?
  row tour-chromium "$([ "$rc" = 0 ] && echo 1 || echo 0)" "$out $(tail -1 "$R/jtour.err" | cut -c1-120)"
else
  printf 'UNCONFIGURED\ttour-chromium\tno Playwright at %s (PLAYWRIGHT_DIR), or --box\n' "$PW"
fi
req POST /logout --data-urlencode "csrf=$CSRF" >/dev/null
logout_status=$(st)
after=$(curl -s -o /dev/null -w '%{http_code}' -H "Cookie: $COOKIE_NAME=$COOKIE_VALUE" "$BASE/term")
row logout "$([ "$logout_status" = 303 ] && [ "$after" = 401 ] && echo 1 || echo 0)" "logout=$logout_status then /term=$after"
pub=$(curl -s -o "$R/body" -w '%{http_code}' "$BASE/")
row public-reader "$(grep -q 'public reader' "$R/body" && echo 1 || echo 0)" "$pub $(grep -o 'class="headline">[^<]*' "$R/body" | head -1 | cut -c18-120)"
# J-COLD-READ: the first visit after the public reader went cold answers within the gateway's own
# deadline (proxy::BODY_TIMEOUT, 120 s; curl waits past it so a 504 is the gateway's). On the box the
# public member's consent worker idles out and its next start replays the Store (demo-dry 2026-10-28,
# 349e59ef1: 23 s on an idle box, 504 under load); in dev the reader's consent is its resident provider,
# stopped here by its PID file, and the body reconnects to a new one. The front document is the
# published DOC in dev (its TEXT on the page); on the box, the operator's.
cold_get() { # -> "STATUS SECONDS"; the page in $R/anon.body
  curl -s -o "$R/anon.body" -w '%{http_code} %{time_total}' -m 150 "$BASE/"
}
cold_ok() { # "STATUS SECONDS" -> 1|0: 200 within 120 s, with the front document when dev published one
  local status=${1%% *} secs=${1##* }
  [ "$status" = 200 ] && awk -v s="$secs" 'BEGIN { exit !(s < 120) }' && { [ "$mode" = --box ] || [ -z "${PUBREAD_SUBJECT:-}" ] || grep -q "$TEXT" "$R/anon.body"; } && echo 1 || echo 0
}
gone() { # PID: wait up to 30 s for it to exit (a zombie has exited: a resident's parent, the body, never reaps it)
  for _ in $(seq 1 300); do
    kill -0 "$1" 2>/dev/null || return 0
    case $(ps -o stat= -p "$1" 2>/dev/null) in Z*) return 0 ;; esac
    sleep 0.1
  done; return 1
}
stop_reader_residents() { # dev: the public reader's resident consent (r-) and codec (c-) providers, by their PID files
  local f pid kinds=${1:-r}
  for k in $kinds; do
    for f in "${PUBREAD_HOME:-/nonexistent}"/.mini/consent-anchors/"$k"-*.pid; do
      [ -f "$f" ] || continue
      pid=$(cat "$f"); kill "$pid" 2>/dev/null && gone "$pid"
    done
  done
}
if [ "$mode" = --box ]; then
  systemctl stop mini-consent@public.service
  got=$(cold_get)
  row cold-read-consent "$(cold_ok "$got")" "mini-consent@public stopped, then anonymous GET / -> $got"
  systemctl stop mini-web-body-public.scope mini-consent@public.service 2>/dev/null
  got=$(cold_get)
  row cold-read-body "$(cold_ok "$got")" "public body and mini-consent@public stopped, then anonymous GET / -> $got"
  since=$(systemctl show -p ActiveEnterTimestamp --value mini-web-spawn.service)
  warmed=$(journalctl -u mini-web-spawn.service --since "$since" -o cat 2>/dev/null | grep 'public reader warmed' | tail -1)
  got=$(cold_get)
  row warm-at-start "$([ -n "$warmed" ] && grep -q ': HTTP/1.1 200 ' <<<"$warmed" && [ "$(cold_ok "$got")" = 1 ] && echo 1 || echo 0)" "${warmed:-no warming line since the helper started ($since)}; GET / -> $got"
elif [ -z "${PUBREAD_SUBJECT:-}" ]; then
  row cold-read "0" "no public reader member (needs SPONSOR_WS): the cold rows cannot run"
else
  cold_get >/dev/null   # the body and its provider are warm before the provider ends
  stop_reader_residents r
  got=$(cold_get)
  row cold-read-consent "$(cold_ok "$got")" "the reader's resident consent stopped by its PID file, then anonymous GET / -> $got"
  bpid=$(jq -r '.bodyPid // empty' "$R/state/sessions/public.json" 2>/dev/null)
  [ -z "$bpid" ] || { kill "$bpid" 2>/dev/null; gone "$bpid"; }
  stop_reader_residents "r c"
  got=$(cold_get)
  row cold-read-body "$(cold_ok "$got")" "public body ${bpid:-none} and the reader's residents stopped, then anonymous GET / -> $got"
  # The helper restarted by its PID file, every body it started first by the pid it recorded (a fresh
  # helper ends an earlier helper's bodies only on Linux), the reader's residents too: it must warm the
  # public body itself, before any visitor.
  for f in "$R"/state/sessions/*.json; do
    bpid=$(jq -r '.bodyPid // empty' "$f" 2>/dev/null); [ -z "$bpid" ] || { kill "$bpid" 2>/dev/null; gone "$bpid"; }
  done
  hpid=$(cat "$R/helper.pid"); kill "$hpid" 2>/dev/null; gone "$hpid"
  stop_reader_residents "r c"
  mark=$(wc -l <"$R/helper.log")
  start_helper
  warmed=""
  for _ in $(seq 1 300); do   # a warming that failed is sent again at the helper's next sweeps
    warmed=$(tail -n +"$((mark + 1))" "$R/helper.log" | grep -E 'public reader (not )?warmed' | tail -1)
    grep -q 'public reader warmed' <<<"$warmed" && break; sleep 1
  done
  got=$(cold_get)
  row warm-at-start "$(grep -q 'public reader warmed.*: HTTP/1.1 200 ' <<<"$warmed" && [ "$(cold_ok "$got")" = 1 ] && echo 1 || echo 0)" "${warmed:-the restarted helper logged no warming within 300 s}; then GET / -> $got"
fi
verdict
