#!/usr/bin/env bash
# Replace only an E-written scratch Store's recorded epoch with F's current
# epoch. The same journey must fail a clean-refusal expectation, or report the
# finding that all historical values/receipts survived without this epoch gate.
# Usage: plant-hostupgrade-reinterpret.sh CAND_E CAND_F NEW_OUT
set -euo pipefail
umask 077
if [ "${1:-}" = --rewrite ]; then
  [ "$#" = 4 ] || exit 2
  python3 - "$2" "$3" "$4" <<'PY'
import pathlib, sqlite3, sys
store, target, evidence = map(pathlib.Path, sys.argv[1:])
db = sqlite3.connect(store / 'forward-link.sqlite3')
before = db.execute('select bytes from durable_seed where slot=1').fetchone()[0]
def frame(b):
    end = b.index(255); size = sum(x * 255**i for i, x in enumerate(b[:end]))
    start = end + 1
    assert size > 18 and len(b) >= start + size
    f = b[start:start+size]; prefix = b'DREGG.DURABLE.SEED\x02'
    assert f.startswith(prefix), 'not a labelled v2 durable seed'
    return f[len(prefix):], b[start+size:]
def nat(n):
    out = bytearray()
    while n:
        out.append(n % 255); n //= 255
    return bytes(out) + b'\xff'
old, suffix = frame(before); new = target.read_bytes().rstrip(b'\n')
(evidence / 'epoch-before.txt').write_bytes(old + b'\n')
if old == new:
    db.close()
    sys.exit('plant precondition: epochs identical')
f = b'DREGG.DURABLE.SEED\x02' + new
after = nat(len(f)) + f + suffix
# No other logical Store data changes; SQLite page metadata is physical custody.
tables = [r[0] for r in db.execute("select name from sqlite_master where type='table' and name != 'durable_seed' order by name")]
def content():
    return {t: db.execute('select * from "' + t.replace('"','""') + '"').fetchall() for t in tables}
untouched = content()
db.execute('update durable_seed set bytes=? where slot=1', (after,)); db.commit()
stored = db.execute('select bytes from durable_seed where slot=1').fetchone()[0]
actual, rest = frame(stored)
assert stored != before and actual == new and rest == suffix
assert content() == untouched, 'mutation touched another table'
db.close()
(evidence / 'epoch-after.txt').write_bytes(actual + b'\n')
(evidence / 'mutation.txt').write_text('MUTATION ASSERTED before != after; after == F current epoch; seed payload and other tables unchanged\n')
PY
  exit 0
fi
if [ "$#" != 3 ]; then echo "usage: $0 CAND_E CAND_F NEW_OUT" >&2; exit 2; fi
ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
E=$(realpath "$1") F=$(realpath "$2") OUT=$(realpath -m "$3")
[ ! -e "$OUT" ] || { echo "plant: evidence exists: $OUT" >&2; exit 2; }
mkdir -p -m 700 "$OUT"
TMP=$(mktemp -d /tmp/hup.XXXXXX)
trap 'rm -rf -- "$TMP"' EXIT
jq '.clock.genesisNow = 1790000000 | .clock.maxStepSeconds = 300' "$F/genesis-params.example.json" >"$TMP/params.json"
"$F/run.sh" init --manifest "$F/manifest.json" --params "$TMP/params.json" --state "$TMP/f" >"$OUT/f-init.out" 2>"$OUT/f-init.err"
python3 - "$TMP/f/store/forward-link.sqlite3" >"$OUT/f-current-epoch.txt" <<'PY'
import sqlite3, sys
with sqlite3.connect('file:' + sys.argv[1] + '?mode=ro', uri=True) as db:
    b = db.execute('select bytes from durable_seed where slot=1').fetchone()[0]
end = b.index(255); size = sum(x * 255**i for i, x in enumerate(b[:end]))
f = b[end+1:end+1+size]; prefix = b'DREGG.DURABLE.SEED\x02'
assert f.startswith(prefix)
print(f[len(prefix):].decode('ascii'))
PY
# Mutation belongs to this plant. Inject one invocation into a TEMPORARY driver,
# after N's clean stop/audit and before the N1 transition and refusal hash.
python3 - "$ROOT" "$TMP/jhostupgrade.sh" "$OUT" <<'PY'
import pathlib, shlex, sys
root, dest, out = map(pathlib.Path, sys.argv[1:])
text = (root / 'native/resource-client/journey.d/jhostupgrade.sh').read_text()
operator = 'OPERATOR=$(CDPATH=\'\' cd -- "$(dirname -- "$0")/../../../deploy/candidate" && pwd)/run.sh'
assert text.count(operator) == 1
text = text.replace(operator, 'OPERATOR=' + shlex.quote(str(root / 'deploy/candidate/run.sh')))
marker = '# Plant copies this driver and inserts its seed mutation immediately here.'
assert text.count(marker) == 1
call = 'bash ' + shlex.quote(str(root / 'scripts/kn2/plant-hostupgrade-reinterpret.sh')) + ' --rewrite "$S/store" ' + shlex.quote(str(out / 'f-current-epoch.txt')) + ' ' + shlex.quote(str(out))
text = text.replace(marker, marker + '\n' + call)
assert text.count(' --rewrite "$S/store" ') == 1
dest.write_text(text)
(out / 'mutant-journey.sh').write_text(text)
PY
rc=0
bash "$TMP/jhostupgrade.sh" "$E" "$F" "$OUT/journey" refuse >"$OUT/journey.out" 2>"$OUT/journey.err" || rc=$?
# These assertions are evaluated BEFORE considering the journey's verdict.
if grep -Fxq 'plant precondition: epochs identical' "$OUT/journey.err"; then
  cmp -s "$OUT/epoch-before.txt" "$OUT/f-current-epoch.txt"
  echo 'plant precondition: epochs identical' | tee "$OUT/precondition.txt"
  exit 1
fi
[ -s "$OUT/mutation.txt" ] || { echo "PLANT FAIL mutation not reached" >&2; exit 1; }
! cmp -s "$OUT/epoch-before.txt" "$OUT/epoch-after.txt"
cmp -s "$OUT/epoch-after.txt" "$OUT/f-current-epoch.txt"
cat "$OUT/mutation.txt"
if jq -e '.outcome == "reopen" and .verified == true' "$OUT/journey/result.json" >/dev/null; then
  echo "FINDING: F reopened E after epoch rewrite with every receipt/value byte-identical and a new write; epoch gate was not needed for this change" | tee "$OUT/finding.txt"
  exit 0
fi
[ "$rc" != 0 ] || { echo "PLANT FAIL epoch rewrite stayed clean-refuse" >&2; exit 1; }
grep '^HOST-UPGRADE FAIL ' "$OUT/journey/verdict.txt" >"$OUT/red.txt"
# A refused named epoch would indicate the injected equality did not remove the gate.
if grep -Fq 'this Store was born in another epoch' "$OUT/journey/serve-n1.err"; then
  echo "PLANT FAIL another-epoch gate still fired" >&2; exit 1
fi
[ -s "$OUT/red.txt" ]
echo "RED as intended: recorded epoch equality does not yield clean refuse/reopen"
cat "$OUT/red.txt"
