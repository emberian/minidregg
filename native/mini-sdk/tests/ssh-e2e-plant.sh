#!/usr/bin/env bash
# The ssh:DEST end-to-end gate must go red when the forced command does not reach the Host.
#
#   native/mini-sdk/tests/ssh-e2e-plant.sh ART_DIR RUN_DIR
#
# Copies the candidate ART_DIR to RUN_DIR/art and replaces its `bin/mini` with a wrapper that runs the real
# binary for every verb except `socket-proxy`; that verb (the sshd forced command) exits without splicing
# the bytes to the Host's public socket. Then runs ssh-e2e.sh on that candidate. Exit 0 only
# when ssh-e2e.sh FAILS and its log names the failed DESCRIBE test (a gate that cannot go red is no gate);
# exit 1 when the planted fault went unseen; exit 2 on a harness error.
set -euo pipefail
ART=$(cd "${1:?usage: ssh-e2e-plant.sh ART_DIR RUN_DIR}" && pwd -P)
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
RUN=${2:?usage: ssh-e2e-plant.sh ART_DIR RUN_DIR}
mkdir -p "$RUN"; RUN=$(cd "$RUN" && pwd -P)
PLANTED=$RUN/art
[[ ! -e $PLANTED ]] || { echo "ssh-e2e-plant: $PLANTED exists" >&2; exit 2; }
cp -a "$ART" "$PLANTED"
chmod -R u+w "$PLANTED"
mv "$PLANTED/bin/mini" "$PLANTED/bin/mini.real"
cat >"$PLANTED/bin/mini" <<WRAPPER
#!/bin/sh
if [ "\$1" = socket-proxy ]; then
  echo "planted fault: the forced command never reaches the Host" >&2
  exit 1
fi
exec "$PLANTED/bin/mini.real" "\$@"
WRAPPER
chmod 755 "$PLANTED/bin/mini"
set +e
# bounded: with the planted proxy a hung peer must not hang the gate
timeout -k 5 150 "$HERE/ssh-e2e.sh" "$PLANTED" "$RUN/e2e" >"$RUN/ssh-e2e.out" 2>"$RUN/ssh-e2e.err"
rc=$?
set -e
LOG=$RUN/e2e/log/ssh-e2e.log
if [[ $rc != 0 ]] && grep -q 'ssh_carries_describe_to_the_host_and_equals_the_unix_socket_over_one_session' "$LOG" 2>/dev/null \
   && grep -Eq 'FAILED|panicked' "$LOG"; then
  echo "ssh-e2e-plant: RED as planted (ssh-e2e.sh exit $rc; the DESCRIBE test failed: $LOG)" >&2
  exit 0
fi
echo "ssh-e2e-plant: the planted fault was NOT seen (ssh-e2e.sh exit $rc; see $RUN/ssh-e2e.err and $LOG)" >&2
exit 1
