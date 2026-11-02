#!/usr/bin/env bash
# J-DOOR: a stranger joins through the self-serve door (deploy/door/README.md).
#
#   jdoor.sh --dry BIN-DIR     anywhere: the unprivileged half end to end over HTTP. BIN-DIR holds a
#                              built mini-door (cargo build -p minidregg-discord-entrance --bin mini-door).
#                              Starts the form on a free loopback port in a scratch tree, GETs /join,
#                              POSTs a join, checks the queued file is exactly the schema, checks the
#                              per-source limit and the status page; the processor's decisions are its
#                              unit tests (mini-door-process tests), not this script.
#   jdoor.sh --box             ON A SPLIT-TENANCY SCRATCH BOX, as root, with the door installed
#                              (deploy/door/infra/INSTALL.md): signup through the real form, one
#                              processor pass, ssh login as mini-s-NAME, a first write, and the custody
#                              row (no file outside the member's home holds the member's key bytes).
#
# Output: one row per check on stdout (`PASS|FAIL<TAB>row<TAB>detail`), then `J-DOOR PASS n/n` or
# `J-DOOR FAIL k/n` as the last line of stdout and stderr. Exit 0 only on PASS. A process this script
# starts is stopped by the PID in its PID file, and only that.
set -uo pipefail
umask 077
mode=${1:-}
rows=0 fails=0
row() {  # NAME OK DETAIL
  rows=$((rows + 1))
  if [ "$2" = 1 ]; then printf 'PASS\t%s\t%s\n' "$1" "$3"; else fails=$((fails + 1)); printf 'FAIL\t%s\t%s\n' "$1" "$3"; fi
}
verdict() {
  local v="J-DOOR PASS $rows/$rows"
  [ "$fails" = 0 ] || v="J-DOOR FAIL $fails/$rows"
  echo "$v"; echo "$v" >&2
  [ "$fails" = 0 ]
}
ok() { if "$@" >/dev/null 2>&1; then echo 1; else echo 0; fi; }

KEYDIR=$(mktemp -d "${TMPDIR:-/tmp}/jdoor-key.XXXXXX")
ssh-keygen -q -t ed25519 -N '' -C jdoor -f "$KEYDIR/id" || { echo "jdoor: ssh-keygen failed" >&2; exit 2; }
PUB=$(cat "$KEYDIR/id.pub")
NAME="jd$(od -An -N3 -tu4 /dev/urandom | tr -d ' ' | cut -c1-6)"

post_join() {  # BASE ROUTE -> response body on stdout
  curl -sS -m 10 -H 'X-Real-IP: 203.0.113.77' --data-urlencode "name=$NAME" --data-urlencode "key=$PUB" \
    --data-urlencode "route=$2" --data-urlencode "discord=on" "$1/join"
}

case $mode in
--dry)
  BIN=${2:?usage: jdoor.sh --dry BIN-DIR}
  [ -x "$BIN/mini-door" ] || { echo "jdoor: no $BIN/mini-door" >&2; exit 2; }
  W=$(mktemp -d "${TMPDIR:-/tmp}/jdoor-dry.XXXXXX")
  mkdir -p "$W/queue" "$W/status"
  printf '{"type":"minidregg-door-state-v1","free":true,"freeReason":null,"paid":false}\n' >"$W/status/door-state.json"
  PORT=$(python3 -I -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])')
  MINI_DOOR_LISTEN=127.0.0.1:$PORT MINI_DOOR_QUEUE=$W/queue MINI_DOOR_STATUS=$W/status \
    nohup "$BIN/mini-door" >"$W/door.log" 2>&1 &
  echo $! >"$W/door.pid"
  stop() { [ -f "$W/door.pid" ] && kill "$(cat "$W/door.pid")" 2>/dev/null; rm -f "$W/door.pid"; }
  trap stop EXIT
  BASE=http://127.0.0.1:$PORT
  for _ in $(seq 1 50); do curl -s -m 1 "$BASE/healthz" >/dev/null && break; sleep 0.1; done
  page=$(curl -sS -m 5 "$BASE/join")
  row "the form says everything is world-readable" "$(ok grep -q 'world-readable' <<<"$page")" "GET /join"
  resp=$(post_join "$BASE" free)
  id=$(grep -oE '/join/status/[0-9a-f]{32}' <<<"$resp" | head -n1 | cut -d/ -f4)
  row "a join POST answers with its bearer status URL" "$([ -n "$id" ] && echo 1 || echo 0)" "${id:-none}"
  q="$W/queue/join-$id.json"
  row "exactly one request file, named by kind and id" "$([ -f "$q" ] && [ "$(ls "$W/queue" | wc -l | tr -d ' ')" = 1 ] && echo 1 || echo 0)" "$(ls "$W/queue" | tr '\n' ' ')"
  schema=$(python3 -I - "$q" "$NAME" "$PUB" <<'PY'
import json, sys
v = json.load(open(sys.argv[1]))
want = {"type", "kind", "id", "at", "name", "sshKey", "discord", "route"}
assert set(v) == want, sorted(v)
assert v["type"] == "minidregg-door-request-v1" and v["kind"] == "join" and v["route"] == "free"
assert v["name"] == sys.argv[2] and v["discord"] is True
assert v["sshKey"] == " ".join(sys.argv[3].split()[:2]), "the comment is dropped"
print("ok")
PY
)
  row "the queued request is exactly the processor's schema (comment dropped)" "$([ "$schema" = ok ] && echo 1 || echo 0)" "$schema"
  mode_bits=$(stat -c %a "$q" 2>/dev/null || stat -f %Lp "$q")
  row "the request file is 0600" "$([ "$mode_bits" = 600 ] && echo 1 || echo 0)" "$mode_bits"
  st=$(curl -sS -m 5 "$BASE/join/status/$id")
  row "the status page shows the request queued" "$(ok grep -q 'queued' <<<"$st")" "GET /join/status/ID"
  bad=$(curl -sS -m 5 -o /dev/null -w '%{http_code}' -H 'X-Real-IP: 203.0.113.78' --data-urlencode "name=ember" \
    --data-urlencode "key=$PUB" --data-urlencode "route=free" "$BASE/join")
  row "a reserved name is refused and queues nothing" "$([ "$bad" = 400 ] && [ "$(ls "$W/queue" | wc -l | tr -d ' ')" = 1 ] && echo 1 || echo 0)" "HTTP $bad"
  codes=""
  for n in 1 2 3; do
    NAME="jd-limit$n"
    codes+="$(curl -sS -m 5 -o /dev/null -w '%{http_code}' -H 'X-Real-IP: 198.51.100.9' --data-urlencode "name=$NAME" \
      --data-urlencode "key=$PUB" --data-urlencode "route=free" "$BASE/join") "
  done
  codes+=$(curl -sS -m 5 -o /dev/null -w '%{http_code}' -H 'X-Real-IP: 198.51.100.9' --data-urlencode "name=jd-limit4" \
      --data-urlencode "key=$PUB" --data-urlencode "route=free" "$BASE/join")
  row "a fourth POST from one source within the hour is refused" "$([ "$codes" = "200 200 200 429" ] && echo 1 || echo 0)" "$codes"
  stop
  rm -rf "$W"
  ;;
--box)
  [ "$(id -u)" = 0 ] || { echo "jdoor: --box runs as root on the box" >&2; exit 2; }
  [ "$(tr -d '[:space:]' </etc/mini/tenancy 2>/dev/null)" = split ] || { echo "jdoor: UNCONFIGURED — not a split-tenancy box" >&2; exit 2; }
  [ -f /etc/mini/door.json ] || { echo "jdoor: UNCONFIGURED — no /etc/mini/door.json" >&2; exit 2; }
  BASE=http://127.0.0.1:8796
  curl -sf -m 2 "$BASE/healthz" >/dev/null || BASE=http://127.0.0.1:8795
  row "the form answers on loopback" "$(ok curl -sf -m 5 "$BASE/healthz")" "$BASE/healthz"
  resp=$(post_join "$BASE" free)
  id=$(grep -oE '/join/status/[0-9a-f]{32}' <<<"$resp" | head -n1 | cut -d/ -f4)
  row "signup through the real form" "$([ -n "$id" ] && echo 1 || echo 0)" "name $NAME id ${id:-none}"
  phase=none
  for _ in $(seq 1 40); do
    /var/lib/mini/candidate/current/bin/mini-door-process 2>>"$KEYDIR/process.log" || true
    phase=$(jq -r '.phase // "none"' "/var/lib/mini-door-status/$id.json" 2>/dev/null || echo none)
    case $phase in enrolled|refused) break ;; esac
    sleep 15
  done
  row "the processor enrols the hosted account" "$([ "$phase" = enrolled ] && echo 1 || echo 0)" \
    "$phase: $(jq -r '.detail // ""' "/var/lib/mini-door-status/$id.json" 2>/dev/null)"
  row "the account and its key file exist" "$(ok id "mini-s-$NAME")" "$(id "mini-s-$NAME" 2>&1)"
  SSH=(ssh -i "$KEYDIR/id" -o IdentitiesOnly=yes -o StrictHostKeyChecking=accept-new -o UserKnownHostsFile="$KEYDIR/known" -o BatchMode=yes)
  who=$("${SSH[@]}" "mini-s-$NAME@127.0.0.1" whoami 2>&1); rc=$?
  row "ssh login as mini-s-NAME runs mini shell" "$([ "$rc" = 0 ] && echo 1 || echo 0)" "$(head -c 160 <<<"$who" | tr '\n' ' ')"
  out=$("${SSH[@]}" "mini-s-$NAME@127.0.0.1" "doc new jdoor-note note" 2>&1); rc=$?
  row "the first write is admitted" "$([ "$rc" = 0 ] && echo 1 || echo 0)" "$(head -c 160 <<<"$out" | tr '\n' ' ')"
  code=$(jq -r '.linkCode // empty' "/var/lib/mini-door-status/$id.json")
  row "a Discord link code was issued" "$([ -n "$code" ] && echo 1 || echo 0)" "${code:-none}"
  custody=$(python3 -I - "/var/lib/mini/sessions/$NAME" <<'PY'
import os, sys
home = os.path.realpath(sys.argv[1])
secret = open(os.path.join(home, "keys", "mini.key"), "rb").read()
assert len(secret) == 32
roots = ["/var/lib/mini", "/etc/mini", "/var/lib/mini-door", "/var/lib/mini-door-status",
         "/var/lib/mini-door-process", "/var/lib/mini-discord", "/var/lib/mini-core", "/tmp", "/var/tmp"]
found = []
for root in roots:
    for d, dirs, files in os.walk(root, followlinks=False):
        if os.path.realpath(d).startswith(home + os.sep) or os.path.realpath(d) == home:
            dirs[:] = []
            continue
        for f in files:
            p = os.path.join(d, f)
            try:
                if not os.path.isfile(p) or os.path.islink(p) or os.path.getsize(p) > 256 << 20:
                    continue
                with open(p, "rb") as h:
                    if secret in h.read():
                        found.append(p)
            except OSError:
                pass
print("none" if not found else " ".join(found[:5]))
PY
)
  row "custody: no file outside the member's home holds the member's key" "$([ "$custody" = none ] && echo 1 || echo 0)" "$custody"
  echo "jdoor: the test account mini-s-$NAME stays on this scratch box (its data); its key is $KEYDIR/id" >&2
  ;;
*)
  echo "usage: jdoor.sh --dry BIN-DIR | --box" >&2
  exit 64
  ;;
esac
[ "$mode" = --box ] || rm -rf "$KEYDIR"
verdict
