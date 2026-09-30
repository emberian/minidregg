#!/usr/bin/env bash
# Run the sandbox-floor probe as an app inside a resident sandbox, through the
# production PreparedResident::prepare + spawn_gate::spawn_bounded path, as root.
#
#   sandbox-floor-audit.sh TEST_ELF PROBE_ELF BWRAP EVIDENCE_DIR [APP_UID APP_GID]
#
# TEST_ELF is the spk-host lib test executable (`cargo test --lib --no-run`), PROBE_ELF
# the built `spk-sandbox-probe`. The script builds a throwaway image (the probe plus the
# shared objects `ldd` names, at their own paths), mounts a 16 MiB tmpfs owned by the app
# UID as the separate /var, runs the two root-only tests in transient system units, and
# removes everything it created. Evidence: the unit transcripts and hashes.
set -euo pipefail

[ $# -ge 4 ] || { echo "usage: $0 TEST_ELF PROBE_ELF BWRAP EVIDENCE_DIR [APP_UID APP_GID]" >&2; exit 2; }
TEST_ELF=$(realpath "$1")
PROBE_ELF=$(realpath "$2")
BWRAP=$3
EVIDENCE=$4
APP_UID=${5:-65534}
APP_GID=${6:-65534}
[ "$APP_UID" != 0 ] && [ "$APP_GID" != 0 ] || { echo "app UID/GID must not be 0" >&2; exit 2; }
mkdir -p "$EVIDENCE"

STAMP=$(date -u +%Y%m%dT%H%M%SZ)
DIR=/run/spk-sandbox-floor-audit-$STAMP
UNIT=spk-sandbox-floor-audit-$STAMP

cleanup() {
  sudo -n umount "$DIR/var" 2>/dev/null || true
  sudo -n rm -rf --one-file-system "$DIR"
}
trap cleanup EXIT

sudo -n install -d -o root -g root -m 0755 "$DIR" "$DIR/image" "$DIR/var"
for mountpoint in var tmp proc dev; do
  sudo -n install -d -o root -g root -m 0755 "$DIR/image/$mountpoint"
done
sudo -n install -o root -g root -m 0555 "$PROBE_ELF" "$DIR/image/spk-sandbox-probe"
# Dynamic loader and libraries at the paths the ELF names.
ldd "$PROBE_ELF" | grep -oE '/[^ ]+' | sort -u | while read -r lib; do
  sudo -n install -D -o root -g root -m 0555 "$(realpath "$lib")" "$DIR/image$lib"
done
sudo -n mount -t tmpfs -o "size=16m,mode=0700,uid=$APP_UID,gid=$APP_GID,nosuid,nodev" \
  spk-audit-var "$DIR/var"

BWRAP_SHA=$(sha256sum "$BWRAP" | cut -d' ' -f1)
{
  echo "stamp=$STAMP"
  echo "host=$(hostname) kernel=$(uname -r)"
  echo "bwrap=$BWRAP sha256=$BWRAP_SHA version=$("$BWRAP" --version)"
  echo "bwrap_package=$(dpkg-query -W -f='${Package} ${Version}' bubblewrap 2>/dev/null || echo unknown)"
  echo "test_elf_sha256=$(sha256sum "$TEST_ELF" | cut -d' ' -f1)"
  echo "probe_sha256=$(sha256sum "$PROBE_ELF" | cut -d' ' -f1)"
  echo "app_uid=$APP_UID app_gid=$APP_GID"
  echo "image_files:"
  (cd "$DIR/image" && sudo -n find . -type f -exec sha256sum {} +) | sort -k2
  echo "var_mount=$(findmnt -no SOURCE,FSTYPE,OPTIONS "$DIR/var")"
  echo "unprivileged_userns_clone=$(cat /proc/sys/kernel/unprivileged_userns_clone 2>/dev/null || echo absent)"
  echo "apparmor_restrict_unprivileged_userns=$(cat /proc/sys/kernel/apparmor_restrict_unprivileged_userns 2>/dev/null || echo absent)"
} > "$EVIDENCE/environment.txt"

run() {
  local name=$1 test=$2
  set +e
  sudo -n systemd-run --system --unit="$UNIT-$name" --wait --pipe --collect \
    -p MemoryMax=256M -p TasksMax=64 -p RuntimeMaxSec=120 -p KillMode=control-group \
    --setenv=SPK_AUDIT_DIR="$DIR" --setenv=SPK_AUDIT_BWRAP="$BWRAP" \
    --setenv=SPK_AUDIT_BWRAP_SHA256="$BWRAP_SHA" \
    --setenv=SPK_AUDIT_UID="$APP_UID" --setenv=SPK_AUDIT_GID="$APP_GID" \
    -- "$TEST_ELF" --ignored --exact "$test" --nocapture --test-threads=1 \
    > "$EVIDENCE/$name.transcript" 2>&1
  local status=$?
  set -e
  echo "$name unit=$UNIT-$name test=$test exit=$status" | tee -a "$EVIDENCE/results.txt"
  sudo -n cat "$DIR/app-output-$name.log" > "$EVIDENCE/app-output-$name.log" 2>/dev/null || true
  return $status
}

: > "$EVIDENCE/results.txt"
floor=0; control=0
run floor resident_launch::tests::root_probe_holds_inside_resident_sandbox || floor=$?
run pre-floor resident_launch::tests::root_probe_breaches_under_pre_floor_arguments || control=$?
[ "$floor" = 0 ] && [ "$control" = 0 ]
