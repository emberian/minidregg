#!/usr/bin/env bash
# relay-base.sh TIP SRC_HOST DST_HOST [SRC_DIR] : copy the gated warm tree at TIP from SRC_HOST:SRC_DIR
# (default /srv/warm-base/src) into DST_HOST:/srv/warm-base (src swapped in by rename, FROZEN rewritten),
# relayed through this Mac (tar|zstd; the boxes have no keys for each other). .lake/packages is NOT sent:
# the receiver hardlinks its own (same lake-manifest). Then mk-lane --verify on the receiver (0 compiled).
set -euo pipefail
T=$1 SH=$2 DH=$3 SD=${4:-/srv/warm-base/src}
ssh $SH "cd $SD && [ \$(git rev-parse HEAD) = $T ] && [ -z \"\$(git status --porcelain --untracked-files=no)\" ] && git diff --quiet $T -- lake-manifest.json lean-toolchain"
ssh $DH "set -e; W=/srv/warm-base; old=\$(sed -n 's/^tip=//p' \$W/FROZEN); [ \"\$old\" != $T ]; git -C \$W/src diff --quiet \$old $T -- lake-manifest.json lean-toolchain 2>/dev/null || git -C \$W/src fetch -q https://github.com/emberian/minidregg.git $T; git -C \$W/src diff --quiet \$old $T -- lake-manifest.json lean-toolchain || { echo manifest changed: cold path needed; exit 9; }; rm -rf \$W/src.new; mkdir -p \$W/src.new/.lake; cp -al \$W/src/.lake/packages \$W/src.new/.lake/packages"
s=$(date +%s)
ssh $SH "tar -C $SD --exclude=./.lake/packages -cf - . | zstd -3 -T8 -q -c" | ssh $DH "zstd -d -q -c | tar -C /srv/warm-base/src.new -xf -"
echo "relay: $(( $(date +%s) - s ))s"
ssh $DH "set -e; W=/srv/warm-base; T=$T; old=\$(sed -n 's/^tip=//p' \$W/FROZEN); cd \$W/src.new; [ \$(git rev-parse HEAD) = \$T ]; [ -z \"\$(git status --porcelain --untracked-files=no)\" ]; git remote set-url base \$W/src 2>/dev/null || true
echo \"advancing \$old -> \$T (copy from $SH:$SD) \$(date -Is)\" > \$W/NOT-READY.txt
mv \$W/src \$W/src.prev-\${old:0:8}; mv \$W/src.new \$W/src
printf 'tip=%s\nfrozen_at=%s\nbuilt_in=$SH:$SD (copied by relay; .lake/packages hardlinked from prev)\nprev=%s (kept at %s)\nrule=read-only base; lanes come from /srv/warm-base/mk-lane.sh <lane>; never build in /srv/warm-base/src\n' \$T \"\$(date -Is)\" \$old \$W/src.prev-\${old:0:8} > \$W/FROZEN.new; mv -f \$W/FROZEN.new \$W/FROZEN; rm -f \$W/NOT-READY.txt
p=mk-verify-\${T:0:8}; timeout 550 \$W/mk-lane.sh --verify \$p 2>&1 | tail -1; rm -rf /srv/lanes/\$p"
