#!/usr/bin/env bash
# v12 schedule (W4/P4096/T1s/G2/N64, every-eight read-only lookups, all-cover and native-delayed
# poles) with the three relays on host B. Foreground; tee d. An ICMP RTT sample runs alongside
# for the cross-host latency distribution.
set -euo pipefail
. "$(dirname "$0")/env.sh"
sha256sum "$MINI_NEW" "$HOST" "$0" "$RC/cohort-native-tcp.py" | tee $L/logs/v13-two-host.inputs.sha256
ping -c 300 -i 0.2 -q $REMOTE_IP > $L/logs/rtt-before.txt 2>&1
( ping -D -i 0.2 -c 420 $REMOTE_IP > $L/logs/rtt-during.txt 2>&1 ) &
PING=$!
python3 $RC/cohort-native-tcp.py --mini $MINI_NEW --fixture $LOOKUP --native-socket $SOCKET \
  --evidence $L/evidence/v13-two-host --epochs 64 --processing-slots 2 --native-workload every-eight \
  --topology two-host --bind-ip $LAN_IP --remote $REMOTE --remote-ip $REMOTE_IP \
  --remote-dir $REMOTE_BASE/v13 --startup-s 120 2>&1 | tee $L/logs/v13-two-host.log
kill $PING 2>/dev/null || true
