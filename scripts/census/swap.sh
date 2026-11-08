#!/usr/bin/env bash
# scripts/census/swap.sh WORLD DIR: before and after on the SAME scratch world. Installs
# DIR/minidregg-host, DIR/mini and (when present) DIR/minidregg-client-consent in place in WORLD's
# published candidate (the originals kept once under WORLD/base-bins; DIR=base puts them back),
# rewrites the changed digests (SHA256SUMS, manifest, provenance, the Store's state.json, and every
# live workspace pin of the Host image) and restarts the Store. A scratch-world device only: a real
# world changes its Host image through the re-genesis (docs/WORLD-MIGRATION.md), never this.
set -euo pipefail
W=$1; D=$2; R=$W/root/var/lib/mini; C=$(readlink -f $R/candidate/current); K=$W/base-bins; S=$R/store/node
mkdir -p $K; for f in minidregg-host mini minidregg-client-consent; do [ -e $K/$f ] || cp $C/bin/$f $K/; done
[ "$D" = base ] && D=$K
chmod -R u+w $C
put() { local f=$1 b=$2 old new; old=$(sha256sum "$C/$f" | cut -d" " -f1); install -m 0555 "$b" "$C/$f"; new=$(sha256sum "$C/$f" | cut -d" " -f1)
  [ "$old" = "$new" ] && return 0
  sed -i "s/$old/$new/g" $C/SHA256SUMS $C/manifest.json $C/provenance.json $S/state.json; echo "$f $old -> $new"; }
HOLD=$(sha256sum $C/bin/minidregg-host | cut -d" " -f1)
put bin/minidregg-host $D/minidregg-host
HNEW=$(sha256sum $C/bin/minidregg-host | cut -d" " -f1)
if [ "$HOLD" != "$HNEW" ]; then
  grep -rl "$HOLD" $R/sessions $S --include=*.json 2>/dev/null | grep -v /attempts/ | while read -r p; do sed -i "s/$HOLD/$HNEW/g" "$p"; done
fi
put bin/clients/x86_64-unknown-linux-gnu/minidregg-host $D/minidregg-host
put bin/mini $D/mini
put bin/clients/x86_64-unknown-linux-gnu/mini $D/mini
if [ -e $D/minidregg-client-consent ]; then
  put bin/minidregg-client-consent $D/minidregg-client-consent
  put bin/clients/x86_64-unknown-linux-gnu/minidregg-client-consent $D/minidregg-client-consent
fi
pold=$(grep "  provenance.json$" $C/SHA256SUMS | cut -d" " -f1); pnew=$(sha256sum $C/provenance.json | cut -d" " -f1)
[ "$pold" = "$pnew" ] || { sed -i "s/$pold/$pnew/g" $C/SHA256SUMS $C/manifest.json $S/state.json; echo "provenance.json $pold -> $pnew"; }
(cd $C && sha256sum --quiet -c SHA256SUMS && echo sums-ok)
$W/restart.sh
