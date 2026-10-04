#!/usr/bin/env bash
# relay-persvati.sh TIP : copy burst-gate's frozen base tree (TIP) into the persvati base by a
# low-priority tar|zstd relay through this Mac (no rebuild on persvati), swap src in, update
# FROZEN and mk-lane.sh TIP=, then mk-lane --verify (0 compiled). .lake/packages: persvati's own,
# hardlinked from the previous src (same lake-manifest).
set -euo pipefail
T=$1; B=/home/ember/workbox/claude-lanes/persvati-base
ssh ember@67.213.124.13 "cd /srv/warm-base/src && [ \$(git rev-parse HEAD) = $T ]"
ssh persvati "set -e; cd $B; old=\$(git -C src rev-parse HEAD); git -C src fetch -q origin; git -C src diff --quiet \$old $T -- lake-manifest.json lean-toolchain || { echo manifest changed; exit 9; }; rm -rf src.new; mkdir -p src.new/.lake; cp -al src/.lake/packages src.new/.lake/packages"
s=$(date +%s)
ssh ember@67.213.124.13 "nice -n 19 tar -C /srv/warm-base/src --exclude=./.lake/packages -cf - . | zstd -3 -T4 -q -c" | ssh persvati "zstd -d -q -c | nice -n 19 ionice -c3 tar -C $B/src.new -xf -"
echo "relay $(( $(date +%s) - s ))s"
ssh persvati "set -e; cd $B; T=$T; old=\$(git -C src rev-parse HEAD); [ \$(git -C src.new rev-parse HEAD) = \$T ]; [ -z \"\$(git -C src.new status --porcelain --untracked-files=no)\" ]
git -C src.new remote remove base 2>/dev/null || true; git -C src.new remote remove github 2>/dev/null || true; git -C src.new remote set-url origin https://github.com/emberian/minidregg.git 2>/dev/null || git -C src.new remote add origin https://github.com/emberian/minidregg.git
mv FROZEN FROZEN.prev; echo \"ADVANCING \$old -> \$T by copy from burst-gate \$(date -Is)\" > ADVANCING.txt
mv src src.prev-\${old:0:8}; mv src.new src
sed \"s/^TIP=.*/TIP=\$T/\" mk-lane.sh > mk-lane.sh.new && chmod +x mk-lane.sh.new && mv -f mk-lane.sh.new mk-lane.sh
printf 'tip=%s\nfrozen=%s\ngreen_log=burst-gate:/srv/warm-base/logs (copied by relay, not rebuilt)\nprev=%s kept at %s\n' \$T \$(date -Is) \$old $B/src.prev-\${old:0:8} > FROZEN; rm -f ADVANCING.txt FROZEN.prev
cd /home/ember/workbox/claude-lanes && nice -n 10 ./persvati-base/mk-lane.sh --verify mk-verify-\${T:0:8} 2>&1 | tail -1; rm -rf /home/ember/workbox/claude-lanes/mk-verify-\${T:0:8}"
