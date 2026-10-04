#!/bin/bash
# grow-world.sh TAG BINDIR SRCTREE FIELDS: a fresh scratch world w/grow-TAG on BINDIR's binaries
# (minidregg-host, mini, store, verifier, minidregg-client-consent beside mini) with a declared
# cell `lab` holding FIELDS. Grow it with growth-levels.sh TAG BINDIR LEVEL...
set -uo pipefail
L=${L:-/srv/lanes/schema-v2-2}
TAG=$1 B=$2 SRCTREE=$3 FIELDS=$4
HOST=$B/minidregg-host MINI=$B/mini STORE=$B/minidregg-link-sqlite-store VERIFIER=$B/minidregg-credential-signature-verifier
WORLD=$L/w/grow-$TAG OUT=$L/evidence/grow-$TAG SOCK=$L/w/g-$TAG.sock
mkdir -p $OUT $L/w; chmod 700 $L/w
sha256sum $HOST $MINI $STORE $VERIFIER $B/minidregg-client-consent > $OUT/binaries.sha256
sh $SRCTREE/native/resource-client/newparticipant-acceptance.sh $HOST $MINI $STORE $VERIFIER $WORLD $SOCK > $OUT/bootstrap.out 2> $OUT/bootstrap.err || { echo bootstrap-failed > $OUT/state; exit 1; }
WS=$WORLD/sponsor
printf "%s\n" "{\"type\":\"all\",\"predicates\":[]}" > $OUT/permit-all.json
/usr/bin/time -f "create %e s" -o $OUT/create.time $MINI workspace --action create --dir $WS --name lab --storage declared --predicate $OUT/permit-all.json --fields "$FIELDS" > $OUT/create.out 2> $OUT/create.err || { echo create-failed > $OUT/state; exit 1; }
echo created > $OUT/state
