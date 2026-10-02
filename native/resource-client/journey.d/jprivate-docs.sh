#!/usr/bin/env bash
# Private document composition on the SAME Store as JPRIV1. Run after its
# alice/carl fixtures (or provide PD_OWNER_WS/HOME and PD_MEMBER_WS/HOME).
# This never provisions a test encryption shortcut: room invite distributes
# the actual epoch key and every document action uses ordinary signed admission.
set -eu
umask 077
: "${JOURNEY_STEP_DIR:?}" "${JOURNEY_WORLD:?}" "${JOURNEY_RUN:?}"
: "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
SD=$JOURNEY_STEP_DIR
FIXTURE=${PD_FIXTURE_DIR:-$JOURNEY_RUN/steps/JPRIV1}
OWNER_WS=${PD_OWNER_WS:-$FIXTURE/w/alice}
MEMBER_WS=${PD_MEMBER_WS:-$FIXTURE/w/carl}
OWNER_HOME=${PD_OWNER_HOME:-$FIXTURE/h/alice}
MEMBER_HOME=${PD_MEMBER_HOME:-$FIXTURE/h/carl}
OWNER_PASS=${PD_OWNER_PASS:-cache-pass-alice}
MEMBER_PASS=${PD_MEMBER_PASS:-cache-pass-carl}
for file in "$OWNER_WS/workspace.json" "$MEMBER_WS/workspace.json"; do
  [ -f "$file" ] || { echo "JPRIVATE-DOCS prerequisite missing: $file (run JPRIV1 first)" >&2; exit 1; }
done
mkdir -p "$SD/log" "$OWNER_HOME/requests" "$MEMBER_HOME/requests"
TABLE=$SD/jprivate-docs.tsv
printf 'row\tcheck\tresult\n' >"$TABLE"
N=0
ROOM=pd-room
DOC=pd-paper

fail() { printf '%s\t%s\tFAIL\n' "$N" "$*" >>"$TABLE"; echo "JPRIVATE-DOCS: $* ($TABLE)" >&2; exit 1; }
check() { local label=$1; shift; N=$((N + 1)); "$@" || fail "$label"; printf '%s\t%s\tok\n' "$N" "$label" >>"$TABLE"; }
run_as() {
  local who=$1; shift
  if [ "$who" = owner ]; then MINI_KEYCACHE_PASSPHRASE=$OWNER_PASS "$@"
  else MINI_KEYCACHE_PASSPHRASE=$MEMBER_PASS "$@"; fi
}
line() {
  local who=$1 text=$2 ws home
  if [ "$who" = owner ]; then ws=$OWNER_WS; home=$OWNER_HOME
  else ws=$MEMBER_WS; home=$MEMBER_HOME; fi
  N=$((N + 1)); OUT=$SD/log/$N.out; ERR=$SD/log/$N.err
  printf '%s\n' "$text" >"$SD/log/$N.line"
  set +e
  run_as "$who" "$MINI" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$ws" --home "$home" --line "$text" >"$OUT" 2>"$ERR"
  RC=$?
  set -e
}
ok() { line "$1" "$2"; [ "$RC" = 0 ] || fail "$1: $2: $(tail -1 "$ERR")"; printf '%s\t%s: %s\tok\n' "$N" "$1" "$2" >>"$TABLE"; }
refused() {
  local reason=$3
  line "$1" "$2"
  [ "$RC" != 0 ] && grep -Eq "$reason" "$ERR" || fail "$1: $2 should refuse $reason (rc $RC)"
  printf '%s\t%s: %s refused %s\tok\n' "$N" "$1" "$2" "$reason" >>"$TABLE"
}
pull() { ok "$1" "doc pull $DOC"; cp "$OUT" "$2"; }
handoff() {
  ok owner "submit $1"; ok owner "publish $1"; ok owner "export $1"
  local ref; ref=$(cat "$OUT")
  cp "$ref" "$SD/$1-reference.json"
  ok member "import $2 $ref"
}

MEMBER=$(jq -r .subject "$MEMBER_WS/workspace.json")
ok member whoami
ENC=$(jq -er .encryptionKey "$OUT")
ok owner "room new $ROOM --private"
ok owner "room invite pd-invite $ROOM $MEMBER $ENC --verbs observe,place,append,mutate"
handoff pd-invite "$ROOM"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/document-law.json"
check 'birth a real document inside the private room' run_as owner "$MINI" workspace --socket "$SOCKET" \
  --action doc-new --dir "$OWNER_WS" --name "$DOC" --predicate "$SD/document-law.json" --in "$ROOM"
check 'birth reference retains its private room' jq -e --arg room "$ROOM" '.sealedIn == $room' "$OWNER_WS/refs/$DOC.json"
ok owner "delegate pd-share $DOC $MEMBER observe,mutate 50000"
handoff pd-share "$DOC"
# The imported reference must carry the private-room hint. A fallback from
# already sealed content is a refusal, never permission to publish plaintext.
check 'member reference retains its private room' jq -e --arg room "$ROOM" '.sealedIn == $room' "$MEMBER_WS/refs/$DOC.json"

# The recipient holds a second real room key. Changing the routing hint to
# that audience must fail at signed ancestry, before a reference is installed.
ok owner "room new pd-other --private"
ok owner "room invite pd-other-invite pd-other $MEMBER $ENC --verbs observe,place,append,mutate"
handoff pd-other-invite pd-other
OTHER_ROOM=$(jq -er .target "$MEMBER_WS/refs/pd-other.json")
jq --arg room "$OTHER_ROOM" '.sealedRoom = $room' "$SD/pd-share-reference.json" >"$SD/cross-room-reference.json"
refused member "import pd-cross-room $SD/cross-room-reference.json" 'signed room history does not establish'
check 'cross-room refusal installs no document reference' test ! -e "$MEMBER_WS/refs/pd-cross-room.json"

check 'birth a second private document for room discovery' run_as owner "$MINI" workspace --socket "$SOCKET" \
  --action doc-new --dir "$OWNER_WS" --name pd-discovered --predicate "$SD/document-law.json" --in "$ROOM"
ok owner 'doc pull pd-discovered'
ok owner 'doc append pd-discovery-body pd-discovered PRIVATE-DOCS-discovered'
ok owner 'submit pd-discovery-body'
DISCOVERED=$(jq -er .target "$OWNER_WS/refs/pd-discovered.json")
DISCOVERED_NAME=$ROOM-cell-$DISCOVERED
ok member "room ls $ROOM --import"
check 'discovered child retains verified private context' jq -e --arg room "$ROOM" '.sealedIn == $room' "$MEMBER_WS/refs/$DISCOVERED_NAME.json"
ok member "doc pull $DISCOVERED_NAME"
check 'discovered private document opens through the ordinary reader' grep -Fx 'PRIVATE-DOCS-discovered' "$OUT"

pull owner "$OWNER_HOME/requests/pd-edit.md"
printf 'PRIVATE-DOCS unique first\nPRIVATE-DOCS unique second\n' >"$OWNER_HOME/requests/pd-edit.md"
ok owner "doc push pd-seed $DOC @pd-edit.md"
ok owner "doc insert $DOC 2 PRIVATE-DOCS-inserted"
ok owner "doc move $DOC 3 1"
pull owner "$SD/owner-current.txt"
pull member "$MEMBER_HOME/requests/pd-edit.md"
check 'member opens exactly the same placed document' cmp "$SD/owner-current.txt" "$MEMBER_HOME/requests/pd-edit.md"
ok owner "doc edit pd-edit $DOC 1 PRIVATE-DOCS-revised"
ok owner 'submit pd-edit'
sed -i '1s/.*/PRIVATE-DOCS-stale-member/' "$MEMBER_HOME/requests/pd-edit.md"
refused member "doc push pd-stale $DOC @pd-edit.md" 'stale-line|staleAtom'
pull member "$MEMBER_HOME/requests/pd-edit.md"
sed -i '2s/.*/PRIVATE-DOCS-member-edit/' "$MEMBER_HOME/requests/pd-edit.md"
ok member "doc push pd-member $DOC @pd-edit.md"
ok owner "doc remove $DOC 3"
pull owner "$SD/before-reopen.txt"

check 'signed commands and Store contain no private document plaintext or its hex' \
  python3 - "$JOURNEY_WORLD" "$OWNER_WS/proposals" "$MEMBER_WS/proposals" <<'PY'
import pathlib, sys
needle = b'PRIVATE-DOCS'
for root in map(pathlib.Path, sys.argv[1:]):
    for path in root.rglob('*'):
        if not path.is_file(): continue
        # Requests are private client drafts. Only submitted intent commands
        # and the Store tree are checked here; retained opened reads are local.
        if root.name == 'proposals' and path.name != 'intent.json': continue
        data = path.read_bytes()
        if needle in data or needle.hex().encode() in data:
            raise SystemExit(f'private plaintext found in {path}')
PY

# Restart only the exact journey-owned service whose pid and socket agree.
PID=$(cat "$JOURNEY_WORLD/public/server.pid")
ARGS=$(ps -o args= -p "$PID")
case "$ARGS" in *" serve "*"--socket $SOCKET"*) ;; *) fail 'server pid is not this journey service';; esac
CHILDREN=$(pgrep -P "$PID" || true)
kill -TERM "$PID"
for _ in $(seq 1 300); do kill -0 "$PID" 2>/dev/null || break; sleep 0.1; done
kill -0 "$PID" 2>/dev/null && fail 'journey service did not stop'
for child in $CHILDREN; do
  for _ in $(seq 1 300); do kill -0 "$child" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$child" 2>/dev/null && fail 'journey Host child did not stop'
done
set +e
"$HOST" "$CONFIG" audit >"$SD/audit.out" 2>"$SD/audit.err"
AUDIT=$?
set -e
# Restore service even when the audit refutes the candidate.
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$JOURNEY_WORLD/public/serve-private-docs.log" 2>&1 </dev/null &
echo "$!" >"$JOURNEY_WORLD/public/server.pid"
echo "started server $! (private docs reopen)" >>"$JOURNEY_RUN/services.log"
[ "$AUDIT" = 0 ] || fail 'cold audit refused'
READY=0
for _ in $(seq 1 600); do
  line owner "doc pull $DOC"
  if [ "$RC" = 0 ]; then READY=1; break; fi
  sleep 0.1
done
[ "$READY" = 1 ] || fail 'reopened document unavailable'
check 'private document is byte-identical after cold reopen' cmp "$SD/before-reopen.txt" "$OUT"

ok owner "revoke pd-revoke $DOC $MEMBER"
ok owner 'submit pd-revoke'
refused member "doc pull $DOC" 'revoked|no-grant|undisclosed'
refused member "doc insert $DOC 1 PRIVATE-DOCS-forbidden" 'revoked|no-grant|undisclosed'
pull owner "$SD/after-revoke.txt"
check 'revoked member changed nothing' cmp "$SD/before-reopen.txt" "$SD/after-revoke.txt"
echo "$TABLE"
echo "JPRIVATE-DOCS: $N rows passed; real room keys, ciphertext guards, placement, stale edit, revoke and cold reopen" >&2
