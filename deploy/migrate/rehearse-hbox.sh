#!/usr/bin/env bash
# deploy/migrate/rehearse-hbox.sh — the world migration's rehearsal frame on hbox (user hbox, sudo).
#
# A copy of the demo's state (Store, /etc/mini, sessions with the members' hosted keys, the door's and the
# lobby's trees, the serving candidate) lives under W=/ci/migrate/demo. W is 0700 and SECRET (every hosted
# key is in it); `clean` removes it, and the accounts and mountpoints this script made.
#
# Every command runs as root in a private mount namespace in which the copy is bind-mounted twice: at the
# box's own absolute paths (/var/lib/mini, /etc/mini, /usr/local/lib/mini, /var/lib/mini-door*,
# /var/lib/mini-apps, /var/lib/mini-web-spawn), because the Store's pinned config and every workspace
# recorded those, and under MINI_ROOT=W/mr, the infra scripts' sandbox prefix (lib.sh: nothing calls
# systemctl, as_mini is a subshell; `MINI_ROOT=/` gives `//etc/mini`, which their resolved-path checks
# refuse). The Store's account is root here (mini-core on the box); every hosted member runs as its own
# account mini-s-NAME in group mini-sessions, as on the box (split tenancy): the delegated consent worker
# refuses a controller of its own uid, and seed.sh and world-migrate switch to mini-s-NAME themselves.
#
#   rehearse-hbox.sh mountpoints        sudo: mountpoints, the mini-s-NAME accounts and the group (once)
#   rehearse-hbox.sh tenant             ownership as on the box: the Store root's, each home its member's
#   rehearse-hbox.sh ns CMD...          run CMD as root inside the frame
#   rehearse-hbox.sh store-start        the Store (store-entry.sh) and its public relay; PID files in W/run
#   rehearse-hbox.sh consent-start [NAME...]  each member's delegated consent worker (mini-consent@NAME)
#   rehearse-hbox.sh store-stop         stop every process above by its PID file
#   rehearse-hbox.sh clean              store-stop; remove W, the accounts and the mountpoints it made
set -euo pipefail
W=${W:-/ci/migrate}
DEMO=$W/demo
RUN=$W/run
MR=$W/mr
MEM=${REHEARSE_MEM:-24G}
GROUP=mini-sessions
POINTS=(var/lib/mini etc/mini usr/local/lib/mini var/lib/mini-door var/lib/mini-door-process var/lib/mini-door-status var/lib/mini-apps var/lib/mini-web-spawn)

ns() {
  local binds="" p
  for p in "${POINTS[@]}"; do
    [ -d "$DEMO/$p" ] || continue
    binds+="mount --rbind '$DEMO/$p' '/$p' && mount --rbind '$DEMO/$p' '$MR/$p' && "
  done
  sudo systemd-run --scope --quiet -p MemoryMax="$MEM" -p CPUWeight=20 \
    unshare --mount --propagation private -- bash -c "$binds exec \"\$@\"" ns \
    env -i PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin LANG=C.UTF-8 HOME=/root TMPDIR=/tmp \
      MINI_ROOT="$MR" "$@"
}

members() { sudo find "$DEMO/var/lib/mini/sessions" -mindepth 3 -maxdepth 3 -path '*/keys/mini.key.pub' | awk -F/ '{print $(NF-2)}' | sort; }

case ${1:-} in
mountpoints)
  install -d -m 0700 "$RUN"
  for p in "${POINTS[@]}"; do
    [ -e "/$p" ] || { sudo install -d -m 0755 "/$p"; echo "/$p" >>"$W/mountpoints.created"; }
    install -d "$MR/$p"
  done
  getent group "$GROUP" >/dev/null || { sudo groupadd --system "$GROUP"; echo "group $GROUP" >>"$W/accounts.created"; }
  for n in $(members); do
    id "mini-s-$n" >/dev/null 2>&1 && continue
    sudo useradd --system --no-create-home --shell /usr/sbin/nologin -g "$GROUP" "mini-s-$n"; echo "user mini-s-$n" >>"$W/accounts.created"
  done
  "$0" tenant ;;
tenant)
  sudo chown -R root:root "$DEMO/var/lib/mini" "$DEMO/etc/mini" "$DEMO/usr/local/lib/mini" "$DEMO"/var/lib/mini-*
  for d in "$DEMO/var/lib/mini" "$DEMO/var/lib/mini/store" "$DEMO/var/lib/mini/store/node" "$DEMO/var/lib/mini/store/node/deployment" "$DEMO/var/lib/mini/store/node/public" "$DEMO/var/lib/mini/sessions"; do
    sudo test -d "$d" && sudo chgrp "$GROUP" "$d" && sudo chmod 0710 "$d"
  done
  sudo chmod 0755 "$DEMO/var/lib/mini/candidate" "$DEMO/usr/local/lib/mini" "$DEMO/etc/mini"
  ! sudo test -f "$DEMO/var/lib/mini/store/node/deployment/pinned-config.json" || sudo chmod 0644 "$DEMO/var/lib/mini/store/node/deployment/pinned-config.json"
  for n in $(members); do
    id "mini-s-$n" >/dev/null 2>&1 || continue
    sudo chown -R "mini-s-$n:$GROUP" "$DEMO/var/lib/mini/sessions/$n"; sudo chmod 0700 "$DEMO/var/lib/mini/sessions/$n"
  done ;;
ns) shift; ns "$@" ;;
store-start)
  install -d -m 0700 "$RUN"
  for x in store relay; do
    if [ -s "$RUN/$x.pid" ] && kill -0 "$(cat "$RUN/$x.pid")" 2>/dev/null; then echo "$x already running ($(cat "$RUN/$x.pid"))"; continue; fi
    case $x in
      store) cmd='exec "$MINI_ROOT/usr/local/lib/mini/infra/store-entry.sh"' ;;
      # public-ingress.sh's split-tenancy branch (its socket group), with the frame's lib.sh
      relay) cmd='. "$MINI_ROOT/usr/local/lib/mini/infra/lib.sh"; CANDIDATE_PROG=relay; candidate_serving_state
        install -d -m 0710 -g mini-sessions "$NODE/public"; install -d -m 0700 "$NODE/tmp"; export TMPDIR=$NODE/tmp; rm -f "$NODE/public/mini.sock"
        exec "$MINI" serve-public-proxy --socket "$NODE/public/mini.sock" --upstream "$NODE/operator/mini.sock" --config "$CONFIG" --socket-gid "$(getent group mini-sessions | cut -d: -f3)"' ;;
    esac
    : >"$RUN/$x.log"
    nohup "$0" ns bash -c "$cmd" >>"$RUN/$x.log" 2>&1 &
    echo $! >"$RUN/$x.pid"; echo "$x started (pid $(cat "$RUN/$x.pid"), log $RUN/$x.log)"
    if [ $x = store ]; then   # the relay needs the operator socket answering, not merely present
      for i in $(seq 900); do grep -q '^mini: serving' "$RUN/store.log" && break; kill -0 "$(cat "$RUN/store.pid")" || break; sleep 1; done
      grep -q '^mini: serving' "$RUN/store.log" || { echo "store did not serve:"; tail -n 5 "$RUN/store.log"; exit 1; }
    else
      for i in $(seq 60); do grep -q '^mini: serving public proxy' "$RUN/relay.log" && break; sleep 1; done
    fi
  done ;;
consent-start)
  shift
  [ $# -gt 0 ] || set -- $(members)
  for n in "$@"; do
    x=consent-$n
    if [ -s "$RUN/$x.pid" ] && kill -0 "$(cat "$RUN/$x.pid")" 2>/dev/null; then continue; fi
    : >"$RUN/$x.log"
    nohup "$0" ns /usr/local/lib/mini/migrate/rehearse-consent.sh "$n" root "mini-s-$n" >>"$RUN/$x.log" 2>&1 &
    echo $! >"$RUN/$x.pid"; echo "$x started (pid $(cat "$RUN/$x.pid"))"
  done ;;
store-stop)
  # Each PID file names this script's own process; its child is sudo, which relays the signal into the scope.
  for f in "$RUN"/consent-*.pid "$RUN/relay.pid" "$RUN/store.pid"; do
    [ -s "$f" ] || continue
    pid=$(cat "$f")
    if kill -0 "$pid" 2>/dev/null; then
      kids=$(pgrep -P "$pid" || true)
      kill "$pid" 2>/dev/null || true
      for k in $kids; do sudo kill "$k" 2>/dev/null || true; done
      for i in $(seq 60); do kill -0 "$pid" 2>/dev/null || break; sleep 1; done
    fi
    rm -f "$f"; echo "$(basename "$f" .pid) stopped"
  done
  # The codec/consent residents clients daemonised (c-*.pid, r-*.pid beside their anchors), as ship.sh's
  # stop_resident_pidfile: each only while /proc says it is a `mini ...-resident`, its children with it.
  while IFS= read -r f; do
    pid=$(sudo cat "$f" 2>/dev/null) || continue
    [[ $pid =~ ^[0-9]+$ ]] && sudo test -r "/proc/$pid/cmdline" || continue
    sudo tr '\0' ' ' <"/proc/$pid/cmdline" | grep -qE '^/var/lib/mini/candidate/[^ ]+/bin/mini [a-z-]+-resident ' || continue
    kids=$(pgrep -P "$pid" || true)
    sudo kill "$pid" $kids 2>/dev/null || true
    echo "resident $pid stopped ($(basename "$f"))"
  done < <(sudo find "$DEMO/var/lib/mini" -xdev \( -name 'c-*.pid' -o -name 'r-*.pid' \) -type f) ;;
clean)
  "$0" store-stop || true
  created=$(cat "$W/mountpoints.created" 2>/dev/null || true)
  accounts=$(cat "$W/accounts.created" 2>/dev/null || true)
  sudo rm -rf --one-file-system "$W"
  for p in $created; do sudo rmdir "$p" 2>/dev/null || true; done
  while read -r kind name; do
    [ "$kind" = user ] && [ -n "$name" ] && sudo userdel "$name"
  done <<<"$accounts"
  ! grep -q "^group $GROUP" <<<"$accounts" || sudo groupdel "$GROUP" 2>/dev/null || true
  echo "removed $W" ;;
*) sed -n '2,24p' "$0" >&2; exit 64 ;;
esac
