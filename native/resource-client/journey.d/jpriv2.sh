#!/usr/bin/env bash
# J-PRIV-2 hook for native/resource-client/journey.sh: a participant whose key
# never touches the box. Two machine roles on one host:
#   BOX     the journey's live Store (JOURNEY_WORLD) plus a private sshd whose
#           authorized_keys holds one hosted-shell key (the sponsor, mode=shell)
#           and one proxy key (the friend, mode=proxy);
#   LAPTOP  the friend's own directory: their Mini key, workspace, attempts and
#           ssh key. The friend's `mini` reaches the Host only as
#           `mini --remote box ...` through ssh and deploy/shell/mini-socket-proxy.
# The sponsor acts only through the hosted shell (`ssh sponsor-box 'VERB'`),
# which is the unchanged M4 path. Files crossing between the roles are the
# sponsor's printed offer/welcome and the friend's printed public key and
# possession signature: what two people would paste to each other.
#
# Passes when every row holds; rows are in $JOURNEY_STEP_DIR/steps.tsv.
# Last stdout line: steps.tsv. Last stderr line: the detail.
# Env beyond the hook contract: JPRIV2_PORT (default 22424).
set -uo pipefail
umask 077
D=$JOURNEY_STEP_DIR
PORT=${JPRIV2_PORT:-22424}
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
DEPLOY=$HERE/../../deploy/shell
SSHD=$(command -v sshd || echo /usr/sbin/sshd)
BOX=$D/box
LAPTOP=$D/laptop
SPONSOR_TERM=$D/sponsor-terminal
LOG=$D/log
TABLE=$D/steps.tsv
mkdir -m 700 "$BOX" "$BOX/bin" "$BOX/sshd" "$BOX/homes" "$BOX/homes/sponsor" "$LAPTOP" "$LAPTOP/.ssh" \
  "$LAPTOP/bin" "$SPONSOR_TERM" "$LOG"
printf 'n\twho\twhat\texpect\texit\tverdict\tnote\n' >"$TABLE"
N=0 FAILS=0 SSHD_PID= LAST=
die() { echo "J-PRIV-2: $*" >&2; exit 1; }
if ss -ltn 2>/dev/null | awk '{print $4}' | grep -q ":$PORT\$"; then die "port $PORT in use"; fi

row() { # who what expect exit verdict note
  N=$((N + 1))
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$@" >>"$TABLE"
  [[ $5 == ok ]] || FAILS=$((FAILS + 1))
  printf '%3s %-8s %-72.72s exp=%-3s got=%-3s %s %s\n' "$N" "$@" >&2
}
run() { # who what expect command...   (stdout -> $LOG/N.out, LAST=that file)
  local who=$1 what=$2 expect=$3 rc note err=$LOG/$((N + 1)).err; shift 3
  "$@" >"$LOG/$((N + 1)).out" 2>"$err"; rc=$?
  LAST=$LOG/$((N + 1)).out
  note=$(grep -m1 -E '^(refused|error|undecided|usage|mini|proxy)' "$err" | cut -c1-140)
  if [[ $rc == "$expect" || ( $expect == nz && $rc != 0 ) ]]; then row "$who" "$what" "$expect" "$rc" ok "$note"
  else row "$who" "$what" "$expect" "$rc" FAIL "$note | $(tail -1 "$err" | cut -c1-200)"; fi
}
check() { # who what command...
  local who=$1 what=$2; shift 2
  if "$@" >>"$LOG/checks.txt" 2>&1; then row "$who" "$what" - - ok ""; else row "$who" "$what" - - FAIL "check failed"; fi
}

# ------------------------------------------------------------------ the box
install -m 0500 "$MINI" "$BOX/bin/mini"
install -m 0500 "$DEPLOY/mini-shell-ssh" "$BOX/bin/mini-shell-ssh"
install -m 0500 "$DEPLOY/mini-socket-proxy" "$BOX/bin/mini-socket-proxy"
ssh-keygen -q -t ed25519 -N '' -C jpriv2-sponsor -f "$SPONSOR_TERM/id_ed25519" || die keygen
ssh-keygen -q -t ed25519 -N '' -C jpriv2-friend -f "$LAPTOP/.ssh/id_ed25519" || die keygen
# The friend's ssh PUBLIC key is the only thing of theirs the operator installs.
cp "$LAPTOP/.ssh/id_ed25519.pub" "$BOX/friend-ssh.pub"
{
  "$DEPLOY/render-shell-key" "$BOX/bin/mini-shell-ssh" "$BOX/bin/mini" "$HOST" "$CONFIG" "$SOCKET" \
    "$SPONSOR_WS" "$BOX/homes/sponsor" "$SPONSOR_TERM/id_ed25519.pub" || die "render sponsor"
  "$DEPLOY/render-shell-key" mode=proxy "$BOX/bin/mini-socket-proxy" "$BOX/bin/mini" "$SOCKET" \
    "$BOX/friend-ssh.pub" || die "render friend"
} >"$BOX/sshd/authorized_keys"
ssh-keygen -q -t ed25519 -N '' -f "$BOX/sshd/host_ed25519" || die keygen
cat >"$BOX/sshd/sshd_config" <<EOF
Port $PORT
ListenAddress 127.0.0.1
HostKey $BOX/sshd/host_ed25519
AuthorizedKeysFile $BOX/sshd/authorized_keys
PidFile $BOX/sshd/sshd.pid
AllowUsers $USER
PubkeyAuthentication yes
PasswordAuthentication no
KbdInteractiveAuthentication no
UsePAM no
StrictModes no
PermitTTY yes
X11Forwarding no
AllowTcpForwarding no
AllowStreamLocalForwarding no
AllowAgentForwarding no
PermitTunnel no
PermitUserEnvironment no
LogLevel VERBOSE
EOF
stop_sshd() {
  [[ -n $SSHD_PID ]] || return 0
  local cmd
  cmd=$(tr '\0' ' ' 2>/dev/null <"/proc/$SSHD_PID/cmdline") || { SSHD_PID=; return 0; }
  [[ $cmd == *"$BOX/sshd/sshd_config"* ]] || { echo "pid $SSHD_PID is not our sshd" >&2; return 1; }
  kill -TERM "$SSHD_PID"
  for _ in $(seq 1 100); do kill -0 "$SSHD_PID" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$SSHD_PID" 2>/dev/null && return 1
  echo "stopped sshd $SSHD_PID" >>"$LOG/cleanup.txt"; SSHD_PID=
}
trap 'stop_sshd' EXIT
setsid "$SSHD" -f "$BOX/sshd/sshd_config" -D -e >"$BOX/sshd/sshd.log" 2>&1 </dev/null &
SSHD_PID=$!
for _ in $(seq 1 100); do
  ss -ltn | awk '{print $4}' | grep -q "127.0.0.1:$PORT\$" && break
  kill -0 "$SSHD_PID" 2>/dev/null || die "sshd exited: $(tail -3 "$BOX/sshd/sshd.log")"
  sleep 0.1
done
KNOWN="[127.0.0.1]:$PORT $(cut -d' ' -f1-2 "$BOX/sshd/host_ed25519.pub")"
for who in laptop sponsor; do
  if [[ $who == laptop ]]; then dir=$LAPTOP/.ssh alias=box; else dir=$SPONSOR_TERM alias=sponsor-box; fi
  echo "$KNOWN" >"$dir/known_hosts"
  cat >"$dir/config" <<EOF
Host $alias
  HostName 127.0.0.1
  Port $PORT
  User $USER
  IdentityFile $dir/id_ed25519
  IdentitiesOnly yes
  UserKnownHostsFile $dir/known_hosts
  StrictHostKeyChecking yes
  BatchMode yes
  LogLevel ERROR
EOF
done
# The friend's ssh: their own ssh config, as ~/.ssh/config would be on a laptop.
printf '#!/bin/sh\nexec ssh -F %s "$@"\n' "$LAPTOP/.ssh/config" >"$LAPTOP/bin/ssh"
chmod 0700 "$LAPTOP/bin/ssh"
sponsor() { ssh -F "$SPONSOR_TERM/config" sponsor-box "$1"; }
friend_ssh() { ssh -F "$LAPTOP/.ssh/config" box "$@"; }
FMINI=$LAPTOP/bin/mini                 # the friend's own copy of the client
install -m 0500 "$MINI" "$FMINI"
# The friend's laptop holds its own Host image (its local pure-codec authority,
# MINI_LOCAL_HOST, run as the storeless `codec` loop, and the portable
# `join --welcome --verifier`), its own consent provider and credential
# verifier, and a consent config naming only laptop paths and NO Store. A remote
# member cannot replay the box's history, so it signs through thin consent
# (MINI_THIN_CONSENT=1). Any frame that admits a Store fails loudly on the
# absent one; nothing on the laptop reads a box file.
install -m 0500 "$HOST" "$LAPTOP/bin/minidregg-host"
install -m 0500 "$(dirname "$HOST")/minidregg-client-consent" "$LAPTOP/bin/minidregg-client-consent"
install -m 0500 "$VERIFIER" "$LAPTOP/bin/minidregg-credential-signature-verifier"
jq --arg none "$LAPTOP/no-store" --arg verifier "$LAPTOP/bin/minidregg-credential-signature-verifier" \
  '.storageRoot = $none | .storageBinary = $none | .signatureBinary = $verifier | .checkpointKey = null' \
  "$CONFIG" >"$LAPTOP/consent.json" || die "laptop consent config"
fmini() {
  MINI_SSH=$LAPTOP/bin/ssh MINI_THIN_CONSENT=1 MINI_LOCAL_HOST=$LAPTOP/bin/minidregg-host \
    MINI_CONSENT_HOST=$LAPTOP/bin/minidregg-client-consent MINI_CONSENT_CONFIG=$LAPTOP/consent.json \
    MINI_CONSENT_ANCHOR_DIR=$LAPTOP/.consent-anchors "$FMINI" "$@"
}
ME=$LAPTOP/.mini
FKEY=$ME/friend.key
FROOT=$ME/box
FWS=$FROOT/workspace
FHOME=$ME/home
fshell() { fmini --remote box shell --workspace "$FWS" --home "$FHOME" --line "$1"; }
row operator "box: sshd on 127.0.0.1:$PORT; authorized_keys = sponsor mode=shell + friend mode=proxy" - - ok "$(cut -c1-60 <<<"$(sed -n 2p "$BOX/sshd/authorized_keys")")"
check operator "laptop consent config: no Store, no box or build path (thin consent only)" \
  bash -c "[[ ! -e '$LAPTOP/no-store' ]] && ! grep -qF -e '$BOX' -e '$JOURNEY_WORLD' -e '$(dirname "$HOST")' -e '$(dirname "$VERIFIER")' '$LAPTOP/consent.json'"
check operator "authorized_keys line 2 is restrict,command=\"…/mini-socket-proxy …\" (no pty)" \
  bash -c "sed -n 2p '$BOX/sshd/authorized_keys' | grep -qE '^restrict,command=\"$BOX/bin/mini-socket-proxy $BOX/bin/mini $SOCKET\" ssh-ed25519 '"

# ------------------------------------------------------------------ enrollment
run friend "join --key: keygen on the laptop" 0 fmini join --key "$FKEY"
PUB=$(sed -n 1p "$LAST"); NEXT=$(sed -n 2p "$LAST"); COSIGN=$(sed -n 3p "$LAST")
check friend "printed public key is 64 hex and the key file is on the laptop" bash -c "[[ '$PUB' =~ ^[0-9a-f]{64}\$ && -f '$FKEY' ]]"
check friend "join --key printed the next key's public half too (K-PREROTATE), and it is not the key" bash -c "[[ '$NEXT' =~ ^[0-9a-f]{64}\$ && '$NEXT' != '$PUB' ]]"
check friend "join --key printed the next key's co-signature as a third line (FIX-IDENTITY)" bash -c "[[ '$COSIGN' =~ ^[0-9a-f]{128}\$ ]]"
run sponsor "hosted shell: enroll plan friend <public key hex> <next public key hex> <co-signature hex>" 0 sponsor "enroll plan friend $PUB $NEXT $COSIGN"
run sponsor "hosted shell: enroll offer friend (the offer the friend receives)" 0 sponsor "enroll offer friend"
cp "$LAST" "$LAPTOP/offer.json"
check sponsor "offer carries the Plan, the command, config and Host digest; no secret" \
  jq -e --arg p "$PUB" '.type == "minidregg-participant-join-offer-v1" and .publicKey == $p and (.plan.possessionHeader | length > 0) and (.hostSha256 | length == 64)' "$LAPTOP/offer.json"
FSUBJ=$(jq -r .subject "$LAPTOP/offer.json")
run friend "join --remote box --sponsor-plan: Host re-decodes the offer, friend signs possession" 0 \
  fmini --remote box join --key "$FKEY" --sponsor-plan "$LAPTOP/offer.json" --dir "$FROOT"
SIG=$(jq -r .possessionSignature "$LAST")
run sponsor "hosted shell: enroll seal friend <signature hex>" 0 sponsor "enroll seal friend $SIG"
run sponsor "hosted shell: enroll submit friend" 0 sponsor "enroll submit friend"
check sponsor "admitted: subject $FSUBJ, the friend's public key, no key path" \
  jq -e --arg p "$PUB" --arg s "$FSUBJ" '.authority == "admitted-key-only" and .publicKey == $p and .subject == $s and .keyPath == null' "$LAST"
run sponsor "hosted shell: provision friend $FSUBJ 1000 all[]" 0 sponsor "provision friend $FSUBJ 1000 {\"type\":\"all\",\"predicates\":[]}"
run sponsor "hosted shell: enroll welcome friend" 0 sponsor "enroll welcome friend"
cp "$LAST" "$LAPTOP/welcome.json"
run friend "join --remote box --welcome: remote workspace on the laptop" 0 \
  fmini --remote box join --key "$FKEY" --welcome "$LAPTOP/welcome.json" --dir "$FROOT" \
  --verifier "$LAPTOP/bin/minidregg-host"
check friend "workspace pins socket ssh:box, no Host image, the Host digest, the laptop key" \
  jq -e --arg k "$FKEY" '.socket == "ssh:box" and .host == null and (.hostSha256 | length == 64) and .key == $k' "$FWS/workspace.json"

# ------------------------------------------------------------------ use
run friend "create notes declared all[] (remote shell)" 0 fshell 'create notes declared {"type":"all","predicates":[]}'
run friend "invoke first-write notes create 2 1" 0 fshell 'invoke first-write notes create 2 1'
run friend "submit first-write" 0 fshell 'submit first-write'
check friend "write installed" jq -e '.type == "confirmed" and .confirmation == "installed"' "$LAST"
run friend "read notes (CLI: mini --remote box workspace --action read)" 0 \
  fmini --remote box workspace --action read --dir "$FWS" --name notes

check friend "read back field 2 = 1" bash -c "[[ \$(jq -r '[.. | objects | select(.key?.field? == \"2\") | .value][0]' '$LAST') == 1 ]]"
run friend "delegate grant-sponsor notes $SPONSOR_SUBJECT observe 50000" 0 fshell "delegate grant-sponsor notes $SPONSOR_SUBJECT observe 50000"
run friend "submit grant-sponsor" 0 fshell 'submit grant-sponsor'
run friend "publish grant-sponsor" 0 fshell 'publish grant-sponsor'
run friend "export grant-sponsor" 0 fshell 'export grant-sponsor'
REF=$(jq -c . "$LAST")
run sponsor "hosted shell: import friend-notes <reference>" 0 sponsor "import friend-notes $REF"
run sponsor "hosted shell: read friend-notes (the delegated grant)" 0 sponsor "read friend-notes"
check sponsor "sponsor reads the friend's field 2 = 1 through the delegation" \
  bash -c "[[ \$(jq -r '[.. | objects | select(.key?.field? == \"2\") | .value][0]' '$LAST') == 1 ]]"

# ------------------------------------------------------------------ custody
BOXROOTS=("$JOURNEY_WORLD" "$BOX")
find "${BOXROOTS[@]}" -name '*.key' | xargs -n1 basename | sort >"$D/keys-on-box.txt"
row operator "find BOX -name '*.key' | xargs -n1 basename: $(tr '\n' ' ' <"$D/keys-on-box.txt")" - - ok ""
check operator "no friend key file on the box" bash -c "! grep -qx 'friend.key' '$D/keys-on-box.txt'"
check operator "control: hosted keys ARE listed (sponsor.key, newcomer.key)" \
  bash -c "grep -qx sponsor.key '$D/keys-on-box.txt' && grep -qx newcomer.key '$D/keys-on-box.txt'"
python3 - "$FKEY" "$JOURNEY_WORLD/sponsor.key" "$D/seed-scan.json" "${BOXROOTS[@]}" <<'PY'
import json, os, sys
friend, sponsor, out, roots = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
def forms(seed):
    return [seed, seed.hex().encode(), seed.hex().upper().encode()]
fs, ss = open(friend, "rb").read(), open(sponsor, "rb").read()
counts = {"friendSeed": 0, "sponsorSeed": 0, "files": 0}
hits = {"friendSeed": [], "sponsorSeed": []}
for root in roots:
    for d, _, names in os.walk(root):
        for n in names:
            p = os.path.join(d, n)
            if not os.path.isfile(p) or os.path.islink(p):
                continue
            try:
                b = open(p, "rb").read()
            except OSError:
                continue
            counts["files"] += 1
            for label, seed in (("friendSeed", fs), ("sponsorSeed", ss)):
                if any(f in b for f in forms(seed)):
                    counts[label] += 1
                    hits[label].append(p)
json.dump({"counts": counts, "hits": hits}, open(out, "w"), indent=1)
PY
row operator "seed scan of every box file: $(jq -c .counts "$D/seed-scan.json")" - - ok ""
check operator "the friend's secret seed (raw or hex) is in no box file" jq -e '.counts.friendSeed == 0' "$D/seed-scan.json"
check operator "control: the sponsor's hosted seed IS found by the same scan" jq -e '.counts.sponsorSeed >= 1' "$D/seed-scan.json"

# ------------------------------------------------------------------ refusals
python3 - "$CONFIG" "$(jq -r .hostSha256 "$FWS/workspace.json")" "$FWS/attempts/first-write/call.bin" "$D" <<'PY'
import struct, sys
config, host, call, d = open(sys.argv[1], "rb").read(), bytes.fromhex(sys.argv[2]), open(sys.argv[3], "rb").read(), sys.argv[4]
def envelope(cfg, pin, request):
    body = bytes([2]) + struct.pack("<I", len(cfg)) + cfg + pin + request
    return struct.pack("<I", len(body)) + body
tampered = bytearray(call); tampered[len(call) // 2] ^= 0x01
frames = {
    "tampered-call": envelope(config, host, bytes([2]) + bytes(tampered)),
    "wrong-config": envelope(config.replace(b"}", b' }', 1), host, bytes([0])),
    "operator-op": envelope(config, host, bytes([22, 1])),
    "wrong-host-pin": envelope(config, bytes(32), bytes([0])),
    "exact-call": envelope(config, host, bytes([2]) + call),
}
for name, frame in frames.items():
    open(f"{d}/frame-{name}.bin", "wb").write(frame)
PY
reply_of() { python3 -c '
import struct, sys
b = open(sys.argv[1], "rb").read()
if len(b) < 5: print(f"no-reply bytes={len(b)}"); sys.exit()
n = struct.unpack("<I", b[:4])[0]; f = b[4:4+n]
tail = f[1:].decode("utf-8", "replace") if f[0] == 254 else f[1:].hex()[:40]
print(f"byte={f[0]} {tail}")' "$1"; }
proxy_case() { # name expect-exit
  local name=$1 expect=$2
  run friend "raw frame over the proxy: $name" "$expect" friend_ssh <"$D/frame-$name.bin"
  row friend "  reply to $name: $(reply_of "$LAST")" - - ok ""
}
run friend "stray bytes (an HTTP request line) on the proxy pipe" nz bash -c "printf 'GET / HTTP/1.0\r\n\r\n' | ssh -F '$LAPTOP/.ssh/config' box"
check friend "  no reply byte came back; the proxy said why on stderr" \
  bash -c "[[ ! -s '$LAST' ]] && grep -q 'proxy: not a socket frame' '$LOG/$N.err'"
run friend "ssh box 'cat /etc/passwd' (a command on a proxy key)" 64 friend_ssh 'cat /etc/passwd'
check friend "  nothing ran: no output" bash -c "[[ ! -s '$LAST' ]]"
proxy_case wrong-config nz
check friend "  proxy refused config pin before the socket" bash -c "grep -q 'proxy: config pin mismatch' '$LOG/$((N - 1)).err'"
proxy_case operator-op nz
check friend "  proxy refused an operator-socket operation" bash -c "grep -q 'proxy: operation unavailable on selected socket' '$LOG/$((N - 1)).err'"
proxy_case wrong-host-pin 0
check friend "  the socket refused the Host pin (254)" bash -c "reply=\$(python3 -c 'import sys;b=open(sys.argv[1],\"rb\").read();print(b[4])' '$LOG/$((N - 1)).out'); [[ \$reply == 254 ]]"
proxy_case tampered-call 0
TAMPERED_REPLY=$LOG/$((N - 1)).out
proxy_case exact-call 0
EXACT_REPLY=$LOG/$((N - 1)).out
# The Host decodes its own two outcomes (op 8, kind outcome), asked over the
# same proxy in one session of two frames.
python3 - "$CONFIG" "$(jq -r .hostSha256 "$FWS/workspace.json")" "$TAMPERED_REPLY" "$EXACT_REPLY" >"$D/frame-inspect.bin" <<'PY'
import struct, sys
config, host = open(sys.argv[1], "rb").read(), bytes.fromhex(sys.argv[2])
out = sys.stdout.buffer
for path in sys.argv[3:5]:
    b = open(path, "rb").read(); n = struct.unpack("<I", b[:4])[0]; frame = b[4:4 + n]
    assert frame[0] == 2, frame[:1]
    request = bytes([8]) + struct.pack("<H", 7) + b"outcome" + frame[1:]
    body = bytes([2]) + struct.pack("<I", len(config)) + config + host + request
    out.write(struct.pack("<I", len(body)) + body)
PY
run friend "Host decodes both outcomes (two op-8 frames, one proxy session)" 0 friend_ssh <"$D/frame-inspect.bin"
python3 - "$LAST" "$D/decoded-tampered.json" "$D/decoded-exact.json" <<'PY'
import json, struct, sys
b = open(sys.argv[1], "rb").read()
for out in sys.argv[2:4]:
    n = struct.unpack("<I", b[:4])[0]; frame = b[4:4 + n]; b = b[4 + n:]
    assert frame[0] == 8, frame[:1]
    json.dump(json.loads(frame[1:]), open(out, "w"), indent=1)
PY
row friend "  tampered-call outcome: $(jq -c '{type, reason: (.reason // .refusal // .detail // null)}' "$D/decoded-tampered.json" | cut -c1-150)" - - ok ""
check friend "  the Host refused the tampered signed call" jq -e '.type == "refused"' "$D/decoded-tampered.json"
row friend "  exact-call outcome: $(jq -c '{type, confirmation, acceptedCount}' "$D/decoded-exact.json")" - - ok ""
check friend "  control: the untampered call on the same raw path is confirmed, replayed (no new effect)" \
  jq -e '.type == "confirmed" and .confirmation == "replayed"' "$D/decoded-exact.json"
run friend "after the refusals: read notes still answers field 2 = 1" 0 fshell 'read notes'
check friend "  field 2 = 1" bash -c "[[ \$(jq -r '[.. | objects | select(.key?.field? == \"2\") | .value][0]' '$LAST') == 1 ]]"
run friend "keygen over --remote is refused (not a participant Host command)" nz fmini --remote box keygen --secret "$ME/x.key" --public "$ME/x.pub"
run sponsor "hosted shell unchanged: whoami" 0 sponsor whoami
check sponsor "  sponsor session is subject $SPONSOR_SUBJECT" jq -e --arg s "$SPONSOR_SUBJECT" '.subject == $s' "$LAST"

stop_sshd || die "could not stop sshd"
row operator "stop sshd" - - ok ""
trap - EXIT
echo "$TABLE"
if [[ $FAILS -ne 0 ]]; then echo "$FAILS of $N rows failed; first: $(awk -F'\t' '$6 == "FAIL" {print $1": "$3; exit}' "$TABLE")" >&2; exit 1; fi
echo "$N rows ok: friend $FSUBJ enrolled from its own key, created/wrote/read/delegated over the proxy; no friend key or seed on the box; 6 proxy/Host refusals" >&2
