#!/bin/sh
# check-audit-corrupted-leaf.sh -- the cold audit refuses a Store with one
# corrupted leaf in the suffix after its latest checkpoint.
#
# A reopen that checks only the last root once let a corrupted leaf through
# (dregg 07-31). This gate copies a Store, proves the untouched copy audits,
# flips one byte of one accepted record above the latest checkpoint, checks the
# flip really happened, and requires `audit` to refuse it, naming the refusal.
# It also requires the receipts of the untouched copy to equal those of the
# original (`audit --receipts`), so the gate itself moved nothing.
#
# usage: check-audit-corrupted-leaf.sh HOST CONFIG.json NEW_DIRECTORY [HEIGHT]
#   CONFIG.json's storageRoot is the Store to copy (read only). HEIGHT is the
#   accepted record to corrupt (default: the last one); it must lie above the
#   latest checkpoint.
set -eu
[ "$#" -ge 3 ] || { echo "usage: $0 HOST CONFIG.json NEW_DIRECTORY [HEIGHT]" >&2; exit 2; }
HOST=$1 CONFIG=$2 OUT=$3 HEIGHT=${4:-}
case "$OUT" in /*) ;; *) echo 'NEW_DIRECTORY must be absolute' >&2; exit 2;; esac
[ ! -e "$OUT" ] || { echo "$OUT already exists" >&2; exit 2; }
mkdir -m 700 "$OUT"
ROOT=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["storageRoot"])' "$CONFIG")

copy() {  # copy NAME: a private copy of the Store and its head anchor + config
  mkdir -m 700 "$OUT/$1"
  cp -a "$ROOT" "$OUT/$1/store"
  [ -e "$ROOT.head-anchor" ] && cp -a "$ROOT.head-anchor" "$OUT/$1/store.head-anchor"
  python3 - "$CONFIG" "$OUT/$1/store" "$OUT/$1/config.json" <<'PY'
import json, os, sys
c = json.load(open(sys.argv[1])); c["storageRoot"] = sys.argv[2]
fd = os.open(sys.argv[3], os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
os.write(fd, json.dumps(c).encode()); os.close(fd)
PY
}

copy clean
copy corrupt
rc=0
"$HOST" "$OUT/clean/config.json" audit --receipts "$OUT/clean/receipts.bin" \
  >"$OUT/clean/audit.out" 2>"$OUT/clean/audit.err" || rc=$?
[ "$rc" -eq 0 ] || { echo "FAIL: the untouched copy did not audit (rc $rc): $(tail -1 "$OUT/clean/audit.err")" >&2; exit 1; }

python3 - "$OUT/corrupt/store/forward-link.sqlite3" "$HEIGHT" >"$OUT/corrupt/mutation.txt" <<'PY'
import sqlite3, sys
db = sqlite3.connect(sys.argv[1])
base = db.execute("select coalesce(max(height), 0) from durable_checkpoint").fetchone()[0]
top = db.execute("select max(height) from durable_log").fetchone()[0]
height = int(sys.argv[2]) if sys.argv[2] else top
if not (base < height <= top):
    sys.exit(f"height {height} is not in the suffix ({base}, {top}]")
before = db.execute("select record from durable_log where height = ?", (height,)).fetchone()[0]
index = len(before) // 2
after = bytearray(before); after[index] ^= 0x01
db.execute("update durable_log set record = ? where height = ?", (bytes(after), height))
db.commit()
stored = db.execute("select record from durable_log where height = ?", (height,)).fetchone()[0]
assert stored != before and len(stored) == len(before), "mutation did not take"
print(f"checkpoint {base} top {top} corrupted height {height} byte {index} of {len(before)}")
PY

rc=0
"$HOST" "$OUT/corrupt/config.json" audit >"$OUT/corrupt/audit.out" 2>"$OUT/corrupt/audit.err" || rc=$?
if [ "$rc" -eq 0 ]; then
  echo "FAIL: audit accepted a corrupted suffix leaf ($(cat "$OUT/corrupt/mutation.txt"))" >&2
  exit 1
fi
grep -q 'refused\|mismatch\|differs\|invalid\|chain\|tag' "$OUT/corrupt/audit.err" || {
  echo "FAIL: audit exited $rc without a named refusal: $(tail -1 "$OUT/corrupt/audit.err")" >&2; exit 1; }
echo "PASS audit_refuses_corrupted_suffix_leaf: $(cat "$OUT/corrupt/mutation.txt"); refused rc $rc: $(tail -1 "$OUT/corrupt/audit.err")"
