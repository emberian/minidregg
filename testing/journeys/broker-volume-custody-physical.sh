#!/usr/bin/env bash
# Explicit root-only disposable filesystem receiving; never an app/world volume.
set -euo pipefail
[ "$(id -u)" = 0 ] || { echo "root disposable receiver required" >&2; exit 2; }
[ "$#" = 3 ] || { echo "usage: receiver TEST_ELF SHA256 FRESH_ROOT" >&2; exit 2; }
test_binary=$1
expected_sha=$2
fixture_root=$3
[[ "$expected_sha" =~ ^[0-9a-f]{64}$ ]] || exit 2
[[ "$fixture_root" =~ ^/var/lib/mini-spk-custody-receiving-[a-z0-9-]+$ ]] || exit 2
[ ! -e "$fixture_root" ] && [ ! -L "$fixture_root" ] || { echo "fresh owned root already exists" >&2; exit 2; }
umask 077
mkdir -m 700 "$fixture_root"
# Root-owned private destination; hash readback precedes any execution.
install -m 700 "$test_binary" "$fixture_root/test-elf"
actual_sha=$(sha256sum "$fixture_root/test-elf" | cut -d ' ' -f 1)
[ "$actual_sha" = "$expected_sha" ] || { echo "test ELF source changed" >&2; exit 2; }
name=1111111111111111-990010
mkdir -m 700 "$fixture_root/volumes" "$fixture_root/vars" "$fixture_root/vars/$name" "$fixture_root/broker"
truncate -s 32M "$fixture_root/volumes/$name.ext4"
printf 'app_uid=64010\nsize_mib=32\n' > "$fixture_root/volumes/$name.conf"
/usr/sbin/mkfs.ext4 -q -F "$fixture_root/volumes/$name.ext4"
cleanup() {
  # Cleanup cannot turn a failed production recovery into a PASS.
  if /usr/bin/mountpoint -q "$fixture_root/vars/$name"; then
    /usr/sbin/fsfreeze -u "$fixture_root/vars/$name" 2>/dev/null || true
    /usr/bin/umount "$fixture_root/vars/$name" || true
  fi
}
trap cleanup EXIT
/usr/bin/mount -o loop,nodev,nosuid,noexec "$fixture_root/volumes/$name.ext4" "$fixture_root/vars/$name"
MINI_VOLUME_CUSTODY_RECEIVING_ROOT="$fixture_root" /usr/bin/timeout 20 "$fixture_root/test-elf" \
  --exact broker::volume_custody::tests::volume_custody_physical_process_death_reconciles_exact_mount \
  --ignored --nocapture > "$fixture_root/receiving.log" 2>&1
cat "$fixture_root/receiving.log"
# Production receiver must have removed exactly its pending obligation.
[ ! -e "$fixture_root/broker/freezes/$name.json" ]
[ -f "$fixture_root/vars/$name/after-recovery" ]
[ ! -e "$fixture_root/grains-backup.json" ]
echo "PHYSICAL-CUSTODY-RECEIVING: PASS (exact SIGKILL freeze recovery; partial copy never complete)"
