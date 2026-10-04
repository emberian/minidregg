#!/usr/bin/env bash
# A NEW signed content write carried exactly once through the cohort into the scratch plain
# Host (the value is a random 19-digit canonical decimal: the scalar field takes nothing else), the first reply lost to the 2 s delay and recovered by reserved repair fetch.
# P=32768 carries the signed-call envelope.
set -euo pipefail
. "$(dirname "$0")/env.sh"
TOPO=${TOPO:-single}
sha256sum "$MINI_NEW" "$HOST" "$0" "$RC/cohort-native-tcp.py" "$RC/cohort-scratch-world.py" | tee $L/logs/new-effect.inputs.sha256
python3 $RC/cohort-scratch-world.py prepare --root $WORLD --out $EFFECT --value "${VALUE:-$(python3 -c "import secrets;print(secrets.randbelow(10**18)+10**18)")}"
EXTRA=()
if [ "$TOPO" = two-host ]; then
  EXTRA=(--topology two-host --bind-ip $LAN_IP --remote $REMOTE --remote-ip $REMOTE_IP --remote-dir $REMOTE_BASE/effect --startup-s 120)
fi
python3 $RC/cohort-native-tcp.py --mini $MINI_NEW --fixture $EFFECT --native-socket $SOCKET \
  --evidence $L/evidence/new-effect --epochs 16 --processing-slots 2 --native-workload single \
  --payload-bytes 32768 --real-clients 1 --expect capture \
  --member-keys "$WORLD/sponsor.key:$WORLD/sponsor.pub" "${EXTRA[@]}" 2>&1 | tee $L/logs/new-effect.log
python3 $RC/cohort-scratch-world.py verify --root $WORLD --fixture $EFFECT --evidence $L/evidence/new-effect \
  2>&1 | tee $L/logs/new-effect-verify.log
