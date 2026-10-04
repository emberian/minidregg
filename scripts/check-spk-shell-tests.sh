#!/usr/bin/env bash
# check-spk-shell-tests.sh — every deploy/spk-host/tests/*.sh, as one gate.
# The SPK broker's shell paths (prepared-custody ingest, inbox staging recovery,
# the untrusted /var image import of 6904304a) are tested by shell scripts that
# run unprivileged. Each must exit 0 AND print a final line starting with PASS.
# A skip (exit 77, e.g. e2fsprogs absent) is RED here: a runner that cannot run
# a test is not a runner that passed it. A new test file enters by existing.
set -uo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root" || exit 2
logs=$root/build-logs/spk-shell; mkdir -p "$logs"
red=0 n=0
for test in deploy/spk-host/tests/*.sh; do
  n=$((n + 1)); name=$(basename "$test" .sh); log=$logs/$name.log
  bash "$test" >"$log" 2>&1; rc=$?
  if [ "$rc" = 0 ] && tail -1 "$log" | grep -q '^PASS'; then
    echo "spk-shell: ok: $name"
  else
    echo "spk-shell: RED: $name: exit $rc; $(tail -1 "$log" | cut -c1-200) ($log)"; red=$((red + 1))
  fi
done
[ "$n" -gt 0 ] || { echo "spk-shell: RED: no test found"; exit 1; }
if [ "$red" != 0 ]; then echo "spk-shell: FAIL: $red of $n red"; exit 1; fi
echo "spk-shell: PASS ($n tests)"
