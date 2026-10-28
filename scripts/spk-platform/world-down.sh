#!/bin/bash
# world-down.sh RUN_ROOT: remove the standing world world-up.sh made, with the same checked
# cleanup two-world-journey.sh performs at exit (residents and the broker stopped and journaled,
# volumes unmounted and destroyed through the fixed-verb helper, the root registry and sudoers
# rule removed by the installer, removal asserted). Every process it stops is one it can name
# by unit; nothing is killed by pattern.
set -uo pipefail
[[ $# == 1 && -f $1/WORLD.env && -f $1/root-setup.log ]] || { echo "usage: $0 RUN_ROOT (with WORLD.env)" >&2; exit 2; }
run=$1
# shellcheck disable=SC1091
. "$run/WORLD.env"
op_uid=$(id -u)
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
units=/run/user/$op_uid/systemd/user
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
installer=$repo/deploy/spk-host/install-user-world
rc=0
if [[ -f $CONFIG ]]; then
  BIN="$BIN" GRAINS_ROOT="$GRAINS_ROOT" BROKER_SOCKET="$BROKER_SOCKET" "$here/grain-journey.sh" stop-services "$RUN" >>"$run/cleanup-services.log" 2>&1 || rc=1
fi
"$here/stop-residents.sh" "$RUN" >>"$run/cleanup-services.log" 2>&1 || rc=1
: >"$run/residents-$STORE.log"
while read -r unit; do
  [[ -n $unit ]] || continue
  journalctl --user --no-pager -u "$unit" >>"$run/residents-$STORE.log" || rc=1
  systemctl --user stop "$unit" || rc=1
done < <(systemctl --user list-units --all --plain --no-legend "mini-spk-s$STORE-a*.service" "mini-spk-supervisor@$STORE-*.service" "mini-spk-supervisor-s$STORE@*.service" | awk '{print $1}')
if systemctl --user is-active "mini-spk-broker@$STORE.service" >/dev/null; then systemctl --user stop "mini-spk-broker@$STORE.service" || rc=1; fi
journalctl --user --no-pager -u "mini-spk-broker@$STORE.service" >"$run/broker-$STORE.log" || rc=1
for request in "$GRAINS_ROOT/broker"/volume-*.json; do
  [[ -f $request ]] || continue
  for verb in unmount destroy; do
    payload=$(jq -c --arg verb "$verb" '.verb=$verb' "$request")
    sudo -n -- "$HELPER" "$payload" >>"$run/volume-helper.log" 2>&1 || rc=1
  done
done
if [[ -f /etc/mini-spk-volumes/$STORE.json ]]; then sudo -n -- "$installer" remove "$STORE" "$HELPER" >>"$run/root-cleanup.log" 2>&1 || rc=1; fi
rm -f "$units/mini-spk-broker@$STORE.service"
while read -r unit; do [[ -z $unit ]] || rm -f "$units/$unit"; done < <(find "$units" -maxdepth 1 -type f \( -name "*s$STORE*" -o -name "mini-spk-supervisor@$STORE-*.service" \) -printf '%f\n')
systemctl --user daemon-reload
[[ ! -e /etc/sudoers.d/mini-spk-$STORE && ! -e /etc/mini-spk-volumes/$STORE.json && ! -e $HELPER ]] || rc=1
printf 'WORLD DOWN store=%s removal_assertions=%s\n' "$STORE" "$rc" | tee -a "$run/result.log"
exit $rc
