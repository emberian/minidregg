#!/usr/bin/env bash
# Build the OwnTracks Recorder SPK on dregg-forge (root, x86_64). Idempotent.
set -euo pipefail
# Run in a private mount namespace: the smoke rootfs's /proc mount cannot leak to, or be unmounted by,
# anything else, and it vanishes with this process.
if [[ ${1:-} != --private-mount-namespace ]]; then
  exec unshare --mount --propagation private bash "$0" --private-mount-namespace
fi
BASE=/srv/spk-build/owntracks
RECIPE="$BASE/recipe"; WORK="$BASE/work"; BUNDLE="$BASE/package"; ROOTFS="$BUNDLE/rootfs"; BUILDROOT="$WORK/buildroot"
OUT="$BASE/out"; LOGS="$BASE/logs"
SPK=/var/lib/spk-fresh/tools/spk
INCLUDE=/var/lib/spk-fresh/tools/sandstorm-308/usr/include
BRIDGE=/var/lib/spk-fresh/tools/sandstorm-308/bin/sandstorm-http-bridge
KEYRING="$BASE/owntracks.key"
SRC_SHA=ba4d72ef3d9d61801f208c06fbd2a28250069107
SRC_SHA256=662a786d3298a5700f874c6e053c767890ba189ba798714ea6314810fcfab8a3
SRC_URL="https://codeload.github.com/mnutt/owntracks-recorder/tar.gz/$SRC_SHA"
PACKAGES=(bash coreutils libcurl4t64 libconfig11 ca-certificates)
BUILD_PACKAGES=(build-essential libcurl4-openssl-dev libconfig-dev pkg-config)
[[ $(id -u) -eq 0 && -x $SPK && -s $KEYRING && $(stat -c %a "$KEYRING") == 600 ]]
APP_ID=$(cat "$BASE/app-id")
mkdir -p "$WORK" "$BUNDLE" "$OUT" "$LOGS"
curl -fL --retry 3 -o "$WORK/src.tar.gz" "$SRC_URL"
printf '%s  %s\n' "$SRC_SHA256" "$WORK/src.tar.gz" | sha256sum -c -
rm -rf "$WORK/src"; mkdir -p "$WORK/src"
tar -xzf "$WORK/src.tar.gz" -C "$WORK/src" --strip-components=1
(cd "$WORK/src" && patch -p1 < "$RECIPE/patches/0001-sandstorm-identity-one-storage-name.patch")

debootstrap() { command debootstrap --variant=minbase trixie "$1" http://deb.debian.org/debian; }
prep_root() { # ROOT PACKAGE...
  local root=$1; shift
  printf '#!/bin/sh\nexit 101\n' > "$root/usr/sbin/policy-rc.d"; chmod 755 "$root/usr/sbin/policy-rc.d"
  cp /etc/resolv.conf "$root/etc/resolv.conf"
  chroot "$root" /usr/bin/env DEBIAN_FRONTEND=noninteractive apt-get update
  chroot "$root" /usr/bin/env DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends "$@"
  chroot "$root" /usr/bin/dpkg-query -W -f='${Package}=${Version}\n' > "$LOGS/$(basename "$root")-debian-package-versions.txt"
  rm -f "$root/usr/sbin/policy-rc.d" "$root/etc/resolv.conf"
}
# The compiler lives in a throwaway build root; the package carries only the binaries and their runtime libraries.
rm -rf "$BUILDROOT"; debootstrap "$BUILDROOT"
prep_root "$BUILDROOT" "${BUILD_PACKAGES[@]}"
mkdir -p "$BUILDROOT/src"; cp -a "$WORK/src/." "$BUILDROOT/src/"
# The 2016 sources do not pass -Werror under gcc 14 (format-truncation notes in storage.c); warnings stay on.
chroot "$BUILDROOT" /bin/bash -c 'cd /src && cp .sandstorm/config.mk . && sed -i "s/ -Werror//" Makefile && make' 2>&1 | tee "$LOGS/make.log"

rm -rf "$ROOTFS"; debootstrap "$ROOTFS"
prep_root "$ROOTFS" "${PACKAGES[@]}"
rm -rf "$ROOTFS/var/lib/apt/lists" "$ROOTFS/var/cache/apt"/* "$ROOTFS/usr/share/doc" "$ROOTFS/usr/share/man" \
  "$ROOTFS/usr/share/info" "$ROOTFS/usr/share/locale"
mkdir -p "$ROOTFS/opt/app"
install -m 755 "$BUILDROOT/src/ot-recorder" "$BUILDROOT/src/ocat" "$ROOTFS/opt/app/"
cp -a "$WORK/src/docroot" "$ROOTFS/opt/app/docroot"
cp "$RECIPE/launcher.sh" "$ROOTFS/opt/app/"; chmod 755 "$ROOTFS/opt/app/launcher.sh"
cp -a "$BRIDGE" "$ROOTFS/sandstorm-http-bridge"
printf '%s\n' "$SRC_SHA" > "$ROOTFS/opt/app/UPSTREAM_COMMIT"
# smoke in a chroot as the grain user
mkdir -p "$ROOTFS/var" "$ROOTFS/tmp" "$ROOTFS/dev" "$ROOTFS/proc"; chmod 1777 "$ROOTFS/tmp"
chown -R 65534:65534 "$ROOTFS/var"
# /dev is a few mknod'd nodes INSIDE the rootfs; the host's /dev is never bind-mounted. Only /proc is a
# mount. Nothing under $ROOTFS is removed unless findmnt shows no mount left beneath it.
assert_no_mounts() {
  if findmnt -rn -o TARGET | grep -F "$ROOTFS/" >&2; then
    echo "FATAL: mounts remain under $ROOTFS; refusing to remove anything" >&2; exit 1
  fi
}
cleanup() {
  if [[ -f $BASE/smoke.pid ]]; then
    kill -TERM -- "-$(cat "$BASE/smoke.pid")" 2>/dev/null || true
    for _ in $(seq 1 50); do kill -0 -- "-$(cat "$BASE/smoke.pid")" 2>/dev/null || break; sleep 0.2; done
    rm -f "$BASE/smoke.pid"
  fi
  if findmnt -rn "$ROOTFS/proc" >/dev/null; then
    umount "$ROOTFS/proc" || { echo "FATAL: cannot unmount $ROOTFS/proc" >&2; exit 1; }
  fi
}
trap cleanup EXIT
mkdir -p "$ROOTFS/dev"
for node in null:1:3 zero:1:5 full:1:7 random:1:8 urandom:1:9; do
  IFS=: read -r n maj min <<<"$node"
  [[ -c $ROOTFS/dev/$n ]] || mknod -m 666 "$ROOTFS/dev/$n" c "$maj" "$min"
done
mount -t proc proc "$ROOTFS/proc"
setsid chroot --userspec=65534:65534 "$ROOTFS" /usr/bin/env -i PATH=/usr/local/bin:/usr/bin:/bin HOME=/var TMPDIR=/var/tmp /bin/bash /opt/app/launcher.sh > "$LOGS/smoke.log" 2>&1 &
echo $! > "$BASE/smoke.pid"
sleep 2
python3 -I "$RECIPE/smoke.py" http://127.0.0.1:8000 | tee "$OUT/smoke.json"
cleanup; trap - EXIT
assert_no_mounts
rm -rf "$ROOTFS/var" "$ROOTFS/tmp" "$ROOTFS/dev" "$ROOTFS/proc"; mkdir -p "$ROOTFS/var" "$ROOTFS/tmp"; chmod 1777 "$ROOTFS/tmp"
find "$ROOTFS" -name __pycache__ -prune -exec rm -rf {} +
printf '%s\n' sandstorm-manifest sandstorm-http-bridge-config sandstorm-http-bridge > "$BUNDLE/sandstorm-files.list"
sed "s/OWNTRACKS_APP_ID/$APP_ID/" "$RECIPE/sandstorm-pkgdef.capnp" > "$BUNDLE/sandstorm-pkgdef.capnp"
cp "$RECIPE/description.md" "$RECIPE/changelog.md" "$RECIPE/version.txt" "$BUNDLE/"
cp "$WORK/src/.sandstorm/logo.svg" "$WORK/src/.sandstorm/notices.txt" "$BUNDLE/"
( cd "$BUNDLE" && "$SPK" pack -I"$INCLUDE" -k"$KEYRING" -p"sandstorm-pkgdef.capnp:pkgdef" "$OUT/owntracks.spk" )
"$SPK" verify --details "$OUT/owntracks.spk" | tee "$LOGS/verify-details.txt"
sha256sum "$OUT/owntracks.spk" | tee "$OUT/owntracks.spk.sha256"
date -u +%Y-%m-%dT%H:%M:%SZ > "$OUT/build-date-utc.txt"
