#!/usr/bin/env bash
set -euo pipefail
source_file=$(cd -- "$(dirname -- "$0")/.." && pwd)/spk-stage-prepared-inbox
scratch=$(mktemp -d /tmp/mini-spk-inbox-recovery-XXXXXXXX)
trap 'rm -rf -- "$scratch"' EXIT
# Execute the exact production recovery function in a private scratch inbox.
eval "$(sed -n '/^recover_existing_inbox() {/,/^}/p' "$source_file")"
owner=$(id -u)
mkdir -m 700 "$scratch/inbox"
printf 'verified signed bytes' > "$scratch/inbox/.prepared.0001"
chmod 600 "$scratch/inbox/.prepared.0001"
expected=$(sha256sum "$scratch/inbox/.prepared.0001" | cut -d ' ' -f 1)
ln "$scratch/inbox/.prepared.0001" "$scratch/inbox/gitweb.spk"
[[ $(stat -c '%h' "$scratch/inbox/gitweb.spk") == 2 ]]
recover_existing_inbox "$scratch/inbox/gitweb.spk" "$scratch/inbox" "$owner" "$expected"
[[ ! -e $scratch/inbox/.prepared.0001 &&
   $(stat -c '%h' "$scratch/inbox/gitweb.spk") == 1 ]]
recover_existing_inbox "$scratch/inbox/gitweb.spk" "$scratch/inbox" "$owner" "$expected"
if recover_existing_inbox "$scratch/inbox/gitweb.spk" "$scratch/inbox" "$owner" \
    0000000000000000000000000000000000000000000000000000000000000000; then
  echo 'wrong digest was accepted' >&2; exit 1
fi
printf 'other bytes' > "$scratch/inbox/other"
chmod 600 "$scratch/inbox/other"
rm "$scratch/inbox/gitweb.spk"
ln "$scratch/inbox/other" "$scratch/inbox/gitweb.spk"
other_digest=$(sha256sum "$scratch/inbox/other" | cut -d ' ' -f 1)
if recover_existing_inbox "$scratch/inbox/gitweb.spk" "$scratch/inbox" "$owner" "$other_digest"; then
  echo 'unexplained second hardlink was accepted' >&2; exit 1
fi
echo 'PASS: exact ln crash recovered; ordinary inode and digest checked; unrelated link refused'
