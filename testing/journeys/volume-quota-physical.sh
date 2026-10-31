#!/usr/bin/env bash
# Physical receiver for the project-quota volume directory (deploy/spk-host/VOLUMES.md).
# Root only, on a disposable file-backed ext4 made here: the LOOP DEVICE IS THE TEST RIG's
# (a real prjquota filesystem to run against), never the volume mechanism under test.
# usage: volume-quota-physical.sh TEST_ELF SHA256 [TEST_FILTER...]
set -euo pipefail
[ "$(id -u)" = 0 ] || { echo "root disposable receiver required" >&2; exit 2; }
(( $# >= 2 )) || { echo "usage: receiver TEST_ELF SHA256 [filter...]" >&2; exit 2; }
test_binary=$1 expected_sha=$2
shift 2
[[ $expected_sha =~ ^[0-9a-f]{64}$ ]] || exit 2
id=$(date +%s)-$$
mnt=/var/lib/mini-spk-volume-test-$id
img=/var/lib/mini-spk-volume-test-$id.img
pidfile=$mnt.pid
[ ! -e "$mnt" ] && [ ! -e "$img" ] || { echo "fresh owned paths already exist" >&2; exit 2; }
umask 022
cleanup() {
  if /usr/bin/mountpoint -q "$mnt"; then /usr/bin/umount "$mnt" || true; fi
  rmdir "$mnt" 2>/dev/null || true
  rm -f -- "$img"
}
trap cleanup EXIT
install -m 700 "$test_binary" "$img.elf"
[ "$(sha256sum "$img.elf" | cut -d ' ' -f 1)" = "$expected_sha" ] || { rm -f "$img.elf"; echo "test ELF source changed" >&2; exit 2; }
truncate -s 512M "$img"
/usr/sbin/mkfs.ext4 -q -F -O quota,project -E quotatype=prjquota "$img"
install -d -m 755 "$mnt"
/usr/bin/mount -o loop,prjquota "$img" "$mnt"
install -d -m 755 -o root -g root "$mnt/world"
install -d -m 700 -o root -g root "$mnt/world/volume-custody"
MINI_VOLUME_QUOTA_ROOT=$mnt/world /usr/bin/timeout 600 "$img.elf" --ignored --test-threads=1 "$@" 2>&1 | tee "$mnt.log"
rc=${PIPESTATUS[0]}
rm -f "$img.elf"
# Teardown assertions: the filesystem holds no volume, conf or witness after the tests.
left=$(find "$mnt/world" \( -name '*.conf' -o -name '*.witness' \) 2>/dev/null | wc -l)
echo "REMAINING registrations/witnesses: $left"
exit "$rc"
