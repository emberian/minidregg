#!/usr/bin/env bash
# The ssh:DEST operator route end to end: the SDK's ssh client -> a REAL unprivileged sshd (127.0.0.1,
# a high port, a throwaway host key, a throwaway client key) -> the forced command
# `deploy/shell/mini-socket-proxy` (`mini socket-proxy`) -> a REAL scratch Store's public socket served by
# the candidate's Host. Nothing leaves this machine's loopback; no key from anywhere else is read.
#
#   native/mini-sdk/tests/ssh-e2e.sh ART_DIR [RUN_DIR]
#
# ART_DIR is a candidate directory (scripts/pipeline/fetch-artifacts <tip> DEST: run.sh, manifest.json,
# genesis-params.example.json, bin/mini). RUN_DIR (default: a fresh dir under $TMPDIR; it must be short
# enough for a unix socket) receives the Store, the keys and the logs; the keys are deleted on exit,
# the logs kept. Runs tests/ssh_e2e.rs with the addresses it prepared and fails if any test fails.
# Cleanup kills only the sshd this script started (by pid, after checking its command line) and stops
# the Store through run.sh.
set -euo pipefail
umask 077
ART=$(cd "${1:?usage: ssh-e2e.sh ART_DIR [RUN_DIR]}" && pwd -P)
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
RUN=${2:-$(mktemp -d "${TMPDIR:-/tmp}/sdk-ssh-e2e.XXXXXX")}
mkdir -p "$RUN"; RUN=$(cd "$RUN" && pwd -P)
STORE=$RUN/store LOG=$RUN/log KEYS=$RUN/keys
mkdir -m 700 "$LOG" "$KEYS"
SSHD=$(command -v sshd || echo /usr/sbin/sshd)
SSHD_PID=
die() { echo "ssh-e2e: $*" >&2; exit 1; }
cleanup() {
  local status=$?
  if [[ -n $SSHD_PID ]] && [[ $(tr '\0' ' ' 2>/dev/null <"/proc/$SSHD_PID/cmdline") == *"$RUN/sshd_config"* ]]; then
    kill -TERM "$SSHD_PID" && echo "stopped sshd $SSHD_PID" >>"$LOG/cleanup.txt"
  fi
  "$ART/run.sh" stop --state "$STORE" >>"$LOG/cleanup.txt" 2>&1 || true
  rm -rf "$KEYS" "$RUN/client" "$RUN/host_ed25519" "$RUN/host_ed25519.pub" "$RUN/host_wrong" "$RUN/host_wrong.pub" "$STORE/keys"
  echo "ssh-e2e: keys deleted; logs in $LOG" >&2
  exit "$status"
}
trap cleanup EXIT

# --- the scratch Store, served by the candidate's Host --------------------------------------------
"$ART/run.sh" init --manifest "$ART/manifest.json" --params "$ART/genesis-params.example.json" --state "$STORE" >"$LOG/init.log" 2>&1 \
  || die "run.sh init failed (see $LOG/init.log)"
"$ART/run.sh" start --state "$STORE" >"$LOG/start.log" 2>&1 || die "run.sh start failed (see $LOG/start.log)"
SOCKET=$STORE/public/mini.sock
for _ in $(seq 1 100); do [[ -S $SOCKET ]] && break; sleep 0.1; done
[[ -S $SOCKET ]] || die "the Store never bound $SOCKET"

# --- throwaway keys: sshd host key, a second host key to plant, the client's key ------------------
ssh-keygen -q -t ed25519 -N '' -C e2e-host -f "$RUN/host_ed25519"
ssh-keygen -q -t ed25519 -N '' -C e2e-planted -f "$RUN/host_wrong"
mkdir -m 700 "$RUN/client"
ssh-keygen -q -t ed25519 -N '' -C e2e-member -f "$RUN/client/id_ed25519"

# --- sshd: unprivileged, loopback, high port, the member's key may run only the byte proxy --------
PORT=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])')
"$REPO/deploy/shell/render-shell-key" mode=proxy "$REPO/deploy/shell/mini-socket-proxy" "$ART/bin/mini" "$SOCKET" \
  "$RUN/client/id_ed25519.pub" >"$RUN/authorized_keys"
cat >"$RUN/sshd_config" <<SSHD_CONFIG
Port $PORT
ListenAddress 127.0.0.1
HostKey $RUN/host_ed25519
AuthorizedKeysFile $RUN/authorized_keys
PidFile $RUN/sshd.pid
AllowUsers $(id -un)
PubkeyAuthentication yes
PasswordAuthentication no
KbdInteractiveAuthentication no
UsePAM no
StrictModes no
PermitTTY no
X11Forwarding no
AllowTcpForwarding no
AllowStreamLocalForwarding no
AllowAgentForwarding no
PermitTunnel no
PermitUserEnvironment no
LogLevel VERBOSE
SSHD_CONFIG
setsid "$SSHD" -f "$RUN/sshd_config" -D -e >"$LOG/sshd.log" 2>&1 </dev/null &
SSHD_PID=$!
for _ in $(seq 1 100); do
  (exec 3<>"/dev/tcp/127.0.0.1/$PORT") 2>/dev/null && break
  kill -0 "$SSHD_PID" 2>/dev/null || die "sshd exited: $(tail -3 "$LOG/sshd.log")"
  sleep 0.1
done

# --- the member's ssh configurations: the right host key, a planted one, and none -----------------
hostkey() { cut -d' ' -f1-2 "$1"; }
printf '[127.0.0.1]:%s %s\n' "$PORT" "$(hostkey "$RUN/host_ed25519.pub")" >"$RUN/known_hosts_good"
printf '[127.0.0.1]:%s %s\n' "$PORT" "$(hostkey "$RUN/host_wrong.pub")" >"$RUN/known_hosts_wrong"
: >"$RUN/known_hosts_empty"
for kind in good wrong empty; do
  cat >"$RUN/ssh_config_$kind" <<SSH_CONFIG
Host mini-box
  HostName 127.0.0.1
  Port $PORT
  User $(id -un)
  IdentityFile $RUN/client/id_ed25519
  IdentitiesOnly yes
  UserKnownHostsFile $RUN/known_hosts_$kind
  GlobalKnownHostsFile /dev/null
SSH_CONFIG
done
# The same host without the member's identity: the unauthorised-key test supplies its own.
grep -v '^  IdentityFile ' "$RUN/ssh_config_good" >"$RUN/ssh_config_nokey"

# --- the tests ---------------------------------------------------------------------------------------
export MINI_SDK_E2E_ALIAS=mini-box MINI_SDK_E2E_SOCKET=$SOCKET MINI_SDK_E2E_CONFIG=$STORE/public/mini.config
export MINI_SDK_E2E_SSH_CONFIG_GOOD=$RUN/ssh_config_good MINI_SDK_E2E_SSH_CONFIG_WRONG=$RUN/ssh_config_wrong
export MINI_SDK_E2E_SSH_CONFIG_EMPTY=$RUN/ssh_config_empty MINI_SDK_E2E_SSH_CONFIG_NOKEY=$RUN/ssh_config_nokey MINI_SDK_E2E_SSHD_LOG=$LOG/sshd.log
export MINI_SDK_E2E_KNOWN_HOSTS_EMPTY=$RUN/known_hosts_empty
export PATH=$HOME/.cargo/bin:$PATH
cd "$REPO/native/mini-sdk"
cargo test --offline --features native --test ssh_e2e -- --ignored --test-threads=1 --nocapture 2>&1 | tee "$LOG/ssh-e2e.log"
[[ ${PIPESTATUS[0]} == 0 ]] || die "ssh_e2e tests failed (see $LOG/ssh-e2e.log)"
grep -q '^test result: ok. [1-9][0-9]* passed; 0 failed' "$LOG/ssh-e2e.log" || die "no passing result in $LOG/ssh-e2e.log"
echo "ssh-e2e: PASS ($(grep -c 'Accepted publickey' "$LOG/sshd.log") publickey logins accepted by sshd; evidence in $LOG)" >&2
