#!/usr/bin/env bash
# JAUDIT (KN2-STORE-OPEN, `mini store audit`): the Store re-derived from genesis, on the journey's
# live Store, after its last write.
#
#   clean       `mini store audit` exits 0 and prints both lines: the store audit line (records,
#               chain, tags, accumulator, spent map, checkpoints, head root) and then the
#               `audited N accepted records` line of the existing audit
#   usage       the Host's store-audit arm refuses a stray option with exit 2
#   control     a COPY of the Store, untouched, audits clean (the copy procedure moves nothing)
#   planted     in another COPY one byte of a NON-HEAD durable_log record is flipped; the byte is
#               asserted changed BEFORE the verdict is read; `mini store audit` exits 1, stderr is
#               `store audit refused: ...` and names that height, and the second (re-admission)
#               audit never ran behind the refused store
#
# Hook contract: journey.sh exports MINI HOST CONFIG SOCKET JOURNEY_WORLD JOURNEY_STEP_DIR.
# Last stdout line = artifact; last stderr line = detail.
set -u
umask 077
D=$JOURNEY_STEP_DIR/jstoreaudit
mkdir -p -m 700 "$D"
T=$D/jstoreaudit.tsv; : >"$T"
N=0; BAD=0
row() {  # row CHECK EXPECTED OBSERVED OK(0/1)
  N=$((N + 1))
  if [ "$4" = 1 ]; then printf 'PASS\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"
  else printf 'FAIL\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"; BAD=$((BAD + 1)); fi
}
audit() {  # audit NAME CONFIG : mini store audit, rc and streams kept
  "$MINI" store audit --host "$HOST" --config "$2" >"$D/$1.out" 2>"$D/$1.err"
  echo $? >"$D/$1.rc"
}
rc() { cat "$D/$1.rc"; }

# clean, on the live Store.
audit clean "$CONFIG"
row "mini store audit on the journey Store" "exit 0, store audit line then audited line" \
  "exit=$(rc clean) $(head -1 "$D/clean.out" | cut -c1-90) | $(tail -n +2 "$D/clean.out" | head -1 | cut -c1-70)" \
  "$([ "$(rc clean)" = 0 ] && head -1 "$D/clean.out" | grep -q '^store audit: [0-9][0-9]* records; chain, tags, accumulator (' \
      && sed -n 2p "$D/clean.out" | grep -q '^audited [0-9][0-9]* accepted records: ' && echo 1 || echo 0)"

# usage: exit 2, nothing on stdout.
"$HOST" "$CONFIG" store-audit --bogus >"$D/usage.out" 2>"$D/usage.err"; echo $? >"$D/usage.rc"
row "store-audit with a stray option" "exit 2, no stdout, usage on stderr" \
  "exit=$(rc usage) stdout=$(wc -c <"$D/usage.out") $(head -1 "$D/usage.err")" \
  "$([ "$(rc usage)" = 2 ] && [ ! -s "$D/usage.out" ] && grep -q '^usage: store-audit' "$D/usage.err" && echo 1 || echo 0)"

# Two copies of the Store: control and planted.
ROOT=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["storageRoot"])' "$CONFIG")
copy() {
  mkdir -m 700 "$D/$1"
  cp -a "$ROOT" "$D/$1/store"
  [ -e "$ROOT.head-anchor" ] && cp -a "$ROOT.head-anchor" "$D/$1/store.head-anchor"
  python3 - "$CONFIG" "$D/$1/store" "$D/$1/config.json" <<'PY'
import json, os, sys
c = json.load(open(sys.argv[1])); c["storageRoot"] = sys.argv[2]
fd = os.open(sys.argv[3], os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
os.write(fd, json.dumps(c).encode()); os.close(fd)
PY
}
copy control; copy planted
audit control "$D/control/config.json"
row "an untouched copy of the Store" "exit 0 and the same store audit line" \
  "exit=$(rc control) $(head -1 "$D/control.out" | cut -c1-60)" \
  "$([ "$(rc control)" = 0 ] && [ "$(head -1 "$D/control.out")" = "$(head -1 "$D/clean.out")" ] && echo 1 || echo 0)"

python3 - "$D/planted/store/forward-link.sqlite3" >"$D/planted/mutation.txt" 2>"$D/planted/mutation.err" <<'PY'
import sqlite3, sys
db = sqlite3.connect(sys.argv[1])
top = db.execute("select max(height) from durable_log").fetchone()[0]
height = max(1, top // 2)
if not (1 <= height < top):
    sys.exit(f"no non-head record: top {top}")
before = db.execute("select record from durable_log where height = ?", (height,)).fetchone()[0]
index = len(before) // 2
after = bytearray(before); after[index] ^= 0x01
db.execute("update durable_log set record = ? where height = ?", (bytes(after), height))
db.commit()
stored = db.execute("select record from durable_log where height = ?", (height,)).fetchone()[0]
assert stored != before and len(stored) == len(before), "mutation did not take"
print(f"{height} {index} {top}")
PY
mrc=$?
read -r MH MI MTOP <"$D/planted/mutation.txt" || :
row "the planted fault took: one byte of a non-head record changed" "exit 0, height < head" \
  "rc=$mrc height=${MH:-?} byte=${MI:-?} head=${MTOP:-?} $(head -1 "$D/planted/mutation.err")" \
  "$([ "$mrc" = 0 ] && [ -n "${MH:-}" ] && [ "$MH" -lt "$MTOP" ] && echo 1 || echo 0)"
if [ "$mrc" = 0 ]; then
  audit planted "$D/planted/config.json"
  row "mini store audit on the planted copy" "exit 1; stderr store audit refused naming height $MH; no re-admission line" \
    "exit=$(rc planted) stdout=$(wc -c <"$D/planted.out")B $(tail -1 "$D/planted.err" | cut -c1-140)" \
    "$([ "$(rc planted)" = 1 ] && grep -q '^store audit refused: ' "$D/planted.err" \
        && grep -qE "(^|[^0-9])$MH([^0-9]|\$)" "$D/planted.err" && ! grep -q '^audited ' "$D/planted.out" && echo 1 || echo 0)"
fi

echo "$T"
if [ "$BAD" = 0 ]; then
  echo "JAUDIT: $N/$N checks; $(head -1 "$D/clean.out" | cut -c1-80); planted height $MH refused: $(tail -1 "$D/planted.err" | cut -c1-100)" >&2
  exit 0
fi
echo "JAUDIT: $BAD of $N checks failed (see $T)" >&2
exit 1
