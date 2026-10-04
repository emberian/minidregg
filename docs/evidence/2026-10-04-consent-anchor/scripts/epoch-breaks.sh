#!/bin/bash
# epoch-breaks.sh: one executed refusal per Store-epoch break. Copies the (stopped) fork world's Store,
# rewrites ONE component of the epoch label inside its seed blob (same length), and opens it with this
# lane's Host. Each must refuse naming exactly that component, before the head anchor is consulted.
set -uo pipefail
L=${L:-/srv/lanes/schema-v2-2}; B=$L/bin-mine; E=$L/evidence/epoch; W=$L/w/fork
C=$(jq -r .config $W/handoff.json)
mkdir -p $E; chmod 700 $E
run() { # NAME FROM TO
  local d=$E/break-$1; rm -rf $d; mkdir -p $d; chmod 700 $d
  cp -a $W/store $W/store.head-anchor $d/
  python3 - "$d/store/forward-link.sqlite3" "$2" "$3" <<'PY'
import sqlite3, sys
db, old, new = sys.argv[1], sys.argv[2].encode(), sys.argv[3].encode()
assert len(old) == len(new)
c = sqlite3.connect(db); (seed,) = c.execute("SELECT bytes FROM durable_seed WHERE slot=1").fetchone()
assert seed.count(old) == 1, (old, seed[:120]); c.execute("UPDATE durable_seed SET bytes=? WHERE slot=1", (seed.replace(old, new),)); c.commit()
PY
  jq --arg s $d/store '.storageRoot=$s' $C > $d/config.json; chmod 600 $d/config.json
  ( $B/minidregg-host $d/config.json presence-index; echo "exit $?" ) > $d/open.txt 2>&1
  echo "== $1 ($2 -> $3)"; cat $d/open.txt
}
{
run control "LOG-TAG/v2" "LOG-TAG/v2"
run state-key "state-key/tagged-v4" "state-key/tagged-v3"
run schema-refs "schema-refs/v5" "schema-refs/v4"
run log-tags "LOG-TAG/v2" "LOG-TAG/v1"
echo "== main-born Store (seed frame v1, from persvati rooms-main-v1-1 at main 36fca3ac binaries)"
cat $E/main-world-tip-host.txt
} 2>&1 | tee $E/epoch-breaks.txt
