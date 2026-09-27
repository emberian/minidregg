#!/usr/bin/env bash
# Isolated systemd lifecycle check for the shared attestation handoff directory.
# Runs no SPK app and touches no production /run/minidregg path.
set -euo pipefail

name=mini-spk-volume-handoff-check-20260927
handoff=/run/$name
first=mini-spk-handoff-check-a-20260927
second=mini-spk-handoff-check-b-20260927
[[ ! -e $handoff && ! -L $handoff ]] || { echo 'test handoff already exists' >&2; exit 1; }

cleanup() {
  systemctl stop "$first.service" "$second.service" >/dev/null 2>&1 || true
  systemctl reset-failed "$first.service" "$second.service" >/dev/null 2>&1 || true
  if [[ -d $handoff && ! -L $handoff ]]; then
    rm -f -- "$handoff/first.witness" "$handoff/second.witness"
    rmdir -- "$handoff"
  fi
}
trap cleanup EXIT

systemd-run --no-block --unit="$first" --property=Type=oneshot \
  --property="RuntimeDirectory=$name" --property=RuntimeDirectoryMode=0755 \
  --property=RuntimeDirectoryPreserve=yes \
  /bin/sh -c "printf first > '$handoff/first.witness'; sleep 3" >/dev/null
sleep 0.5
systemd-run --no-block --unit="$second" --property=Type=oneshot \
  --property="RuntimeDirectory=$name" --property=RuntimeDirectoryMode=0755 \
  --property=RuntimeDirectoryPreserve=yes \
  /bin/sh -c "printf second > '$handoff/second.witness'; sleep 6" >/dev/null

for _ in {1..80}; do
  if [[ $(systemctl show -P ActiveState "$first.service") == inactive ]]; then break; fi
  sleep 0.1
done
[[ $(systemctl show -P ActiveState "$first.service") == inactive ]]
[[ $(systemctl show -P ActiveState "$second.service") == activating ]]
[[ $(cat "$handoff/first.witness") == first ]]
[[ $(cat "$handoff/second.witness") == second ]]
echo 'after first oneshot stopped: both witnesses retained while second runs'

for _ in {1..80}; do
  if [[ $(systemctl show -P ActiveState "$second.service") == inactive ]]; then break; fi
  sleep 0.1
done
[[ $(systemctl show -P ActiveState "$second.service") == inactive ]]
[[ $(cat "$handoff/first.witness") == first ]]
[[ $(cat "$handoff/second.witness") == second ]]
echo 'after both oneshots stopped: both witnesses retained'
echo "first unit result: $(systemctl show -P Result "$first.service")"
echo "second unit result: $(systemctl show -P Result "$second.service")"
