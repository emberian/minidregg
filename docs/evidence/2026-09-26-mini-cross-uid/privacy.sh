#!/bin/sh
set -eu
provision=/tmp/mini-cross-account-signed-20260926-r1
for spec in 'nobody daemon' 'daemon nobody'; do
  set -- $spec
  who=$1 other=$2
  if sudo -n -u "$who" cat "/tmp/mini-cross-task-$other-20260926/key" >/dev/null 2>&1; then echo "FAIL: $who read $other key"; exit 1; fi
  if sudo -n -u "$who" cat "$provision/tool.key" >/dev/null 2>&1; then echo "FAIL: $who read operator tool key"; exit 1; fi
  if sudo -n -u "$who" cat "$provision/deployment/pinned-config.json" >/dev/null 2>&1; then echo "FAIL: $who read private config"; exit 1; fi
  if sudo -n -u "$who" ls "$provision/store" >/dev/null 2>&1; then echo "FAIL: $who traversed Store"; exit 1; fi
  if sudo -n -u "$who" cat "/tmp/mini-cross-front-$other-signed-20260926/host.json" >/dev/null 2>&1; then echo "FAIL: $who read $other public config"; exit 1; fi
  if ! sudo -n -u "$who" cat "/tmp/mini-cross-front-$who-signed-20260926/host.json" >/dev/null; then echo "FAIL: $who cannot read own public config"; exit 1; fi
  echo "PASS: $who own public config readable; other key/config and operator config/Store denied"
done
stat -c '%n %U:%G %a' /tmp/mini-cross-account-signed-20260926-r1 /tmp/mini-cross-uid-gate-20260926/private /tmp/mini-cross-front-nobody-signed-20260926 /tmp/mini-cross-front-daemon-signed-20260926 /tmp/mini-cross-task-nobody-20260926 /tmp/mini-cross-task-daemon-20260926
getfacl -cp /tmp/mini-cross-front-nobody-signed-20260926 /tmp/mini-cross-front-daemon-signed-20260926
