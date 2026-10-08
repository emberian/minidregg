#!/usr/bin/env bash
# The driver captures a separately published escrow with an asserted, exact
# double-pay mutation. Success means native admission refused it by name and
# preserved roots, funds and all three honest commission journeys.
set -euo pipefail
if [[ $# != 2 ]]; then
  echo "usage: $0 BIN_DIR NEW_RUN_ROOT" >&2
  exit 2
fi
repo=$(cd "$(dirname "$0")/../.." && pwd)
python3 "$repo/native/resource-client/commission-demo-journey.py" --bin "$1" --root "$2" --plant double-pay
python3 - "$2/results.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
assert r['allPass'], 'honest or planted rows failed'
assert r['plant'] == 'double-pay'
assert len(r['mutations']) == 1
m = r['mutations'][0]
assert m['before'] != m['after'], 'mutation changed nothing'
rows = {row['step']: row for row in r['rows']}
refusal = rows['CBP-double-pay-refused']
assert refusal['ok'] and refusal['expect'] == 'refused' and 'unfunded' in refusal['detail']
for name in ('CBP-roots-unchanged', 'CBP-balances-unchanged', 'CBP-reward-still-held'):
    assert rows[name]['ok'], name
print('PASS commission double-pay mutation: native unfunded refusal, roots and funds unchanged')
PY
