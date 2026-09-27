#!/usr/bin/env bash
# Fresh resource, one private mount namespace, two simultaneous create callers.
set -euo pipefail

scratch=/tank/chreatures/mini-spk-var-race-20260927
source_script=/tank/chreatures/spk-var-volume-source-20260927
[[ ! -e $scratch ]] || { echo 'race fixture already exists; no replay' >&2; exit 1; }
[[ ! -e /var/lib/minidregg && ! -e /etc/minidregg && ! -e /run/minidregg ]] || {
  echo 'host mountpoint already exists; refusing fixture' >&2; exit 1;
}
sudo install -d -o root -g root -m 700 -- "$scratch"
sudo install -d -o root -g root -m 755 -- "$scratch/var-spk" "$scratch/etc-minidregg" "$scratch/run-minidregg"
sudo install -d -o root -g root -m 700 -- "$scratch/etc-minidregg/spk"
sudo install -d -o root -g root -m 700 -- "$scratch/etc-minidregg/spk/volumes"
sudo install -d -o root -g root -m 700 -- "$scratch/var-spk/images"
sudo install -d -o root -g root -m 711 -- "$scratch/var-spk/vars"
sudo install -o root -g root -m 755 -- "$source_script" "$scratch/spk-var-volume"
sudo install -d -o root -g root -m 755 /var/lib/minidregg /var/lib/minidregg/spk /etc/minidregg /run/minidregg
cleanup_mountpoints() {
  sudo rmdir /var/lib/minidregg/spk /var/lib/minidregg /etc/minidregg /run/minidregg
}
trap cleanup_mountpoints EXIT

sudo unshare -m --propagation private /bin/bash -s <<'INNER'
set -euo pipefail
scratch=/tank/chreatures/mini-spk-var-race-20260927
script=$scratch/spk-var-volume
resource=991026
mount --bind "$scratch/var-spk" /var/lib/minidregg/spk
mount --bind "$scratch/etc-minidregg" /etc/minidregg
mount --bind "$scratch/run-minidregg" /run/minidregg
printf 'deployment_id=%064d\nhost_id=%064d\n' 3 4 > /etc/minidregg/spk/host-identity
chmod 600 /etc/minidregg/spk/host-identity

set +e
"$script" create "$resource" 65534 64 eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee \
  > "$scratch/creator-a.log" 2>&1 &
pid_a=$!
"$script" create "$resource" 65534 64 eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee \
  > "$scratch/creator-b.log" 2>&1 &
pid_b=$!
wait "$pid_a"; result_a=$?
wait "$pid_b"; result_b=$?
set -e
if ! { [[ $result_a == 0 && $result_b != 0 ]] || [[ $result_b == 0 && $result_a != 0 ]]; }; then
  echo "expected one creator and one refusal, got $result_a/$result_b" >&2
  exit 1
fi
echo "creator results: $result_a/$result_b"
[[ $(stat -c '%u:%a:%s:%h' "/var/lib/minidregg/spk/images/$resource.ext4") == '0:600:67108864:1' ]]
[[ $(stat -c '%u:%a:%h' "/etc/minidregg/spk/volumes/$resource.conf") == '0:600:1' ]]
"$script" attest "$resource"
echo 'winner image UUID:'
/usr/sbin/blkid -p -s UUID -o value -- "/var/lib/minidregg/spk/images/$resource.ext4"
echo 'losing creator refusal:'
if [[ $result_a == 0 ]]; then cat "$scratch/creator-b.log"; else cat "$scratch/creator-a.log"; fi

umount "/var/lib/minidregg/spk/vars/$resource"
umount /var/lib/minidregg/spk
umount /etc/minidregg
umount /run/minidregg
INNER
echo 'race fixture retained privately; no application process ran'
