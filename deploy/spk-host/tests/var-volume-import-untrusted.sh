#!/usr/bin/env bash
# The import path of spk-var-volume never mounts operator bytes: it runs the
# production import_untrusted_tree (e2fsprogs in userspace) against a crafted
# image and checks what crosses into the destination. Unprivileged: the
# production reader drop (setpriv to the app uid) is replaced by the caller's
# own uid, which is what the drop produces for the app.
set -euo pipefail
source_file=$(cd -- "$(dirname -- "$0")/.." && pwd)/spk-var-volume
for tool in /usr/sbin/mkfs.ext4 /usr/sbin/debugfs /usr/sbin/e2fsck /usr/sbin/blkid; do
  [[ -x $tool ]] || { echo "SKIP: $tool absent"; exit 77; }
done
scratch=$(mktemp -d /tmp/mini-spk-var-import-XXXXXXXX)
trap 'rm -rf -- "$scratch"' EXIT
eval "$(sed -n '/^import_untrusted_tree() {/,/^}/p' "$source_file")"
untrusted_reader=(env)
# Exactly one mount in the script, of the image it made itself.
[[ $(grep -c '/usr/bin/mount ' "$source_file") == 1 ]]
grep -q -- '/usr/bin/mount -t ext4 -o loop,nosuid,nodev,noatime -- "$image" "$target"' "$source_file"
mkdir -m 700 "$scratch/src" "$scratch/src/sub" "$scratch/stage" "$scratch/dest"
printf 'kept' > "$scratch/src/sub/data"
printf 'setuid' > "$scratch/src/suid"; chmod 4755 "$scratch/src/suid"
ln -s /etc/shadow "$scratch/src/escape"
mkfifo "$scratch/src/fifo"
fallocate -l 64M "$scratch/stage/untrusted.ext4"
/usr/sbin/mkfs.ext4 -q -F -d "$scratch/src" "$scratch/stage/untrusted.ext4"
import_untrusted_tree "$scratch/stage" "$scratch/dest" "$scratch/log"
[[ $(cat "$scratch/dest/sub/data") == kept ]]
[[ -L $scratch/dest/escape && $(readlink "$scratch/dest/escape") == /etc/shadow ]]
[[ ! -e $scratch/dest/fifo && ! -L $scratch/dest/fifo ]]
[[ $(stat -c '%u' "$scratch/dest/sub/data") == "$(id -u)" ]]
# A damaged image is refused before anything is copied.
mkdir -m 700 "$scratch/bad" "$scratch/bad-dest"
cp "$scratch/stage/untrusted.ext4" "$scratch/bad/untrusted.ext4"
dd if=/dev/zero of="$scratch/bad/untrusted.ext4" bs=1024 seek=1 count=1 conv=notrunc status=none
if import_untrusted_tree "$scratch/bad" "$scratch/bad-dest" "$scratch/bad-log"; then
  echo 'damaged import image was accepted' >&2; exit 1
fi
[[ -z $(ls -A "$scratch/bad-dest") ]]
echo 'PASS: import parsed in userspace only; tree copied; symlink kept unfollowed; fifo dropped; damaged image refused before copy'
