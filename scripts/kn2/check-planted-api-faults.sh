#!/bin/bash
# Each FAULT definition in planted-api-faults.lean must be refused by the guard it plants:
# an error inside the definition whose message contains its `-- EXPECT:` text.
set -u
cd "$(git rev-parse --show-toplevel)"
file=scripts/kn2/planted-api-faults.lean
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean "$file" > "$log" 2>&1
cat "$log"
python3 - "$file" "$log" <<'PY'
import re, sys
path = sys.argv[1]
lines = open(path).read().split("\n")
faults = []  # (name, start, end, expect)
for i, line in enumerate(lines, 1):
    m = re.match(r"def (fault\w+)", line)
    if m:
        expect = lines[i - 2].split("-- EXPECT:", 1)[1].strip() if "-- EXPECT:" in lines[i - 2] else None
        faults.append([m.group(1), i, None, expect])
for k, f in enumerate(faults):
    f[2] = (faults[k + 1][1] - 1) if k + 1 < len(faults) else len(lines)
out = open(sys.argv[2]).read()
errors = []  # (line, message)
for block in re.split(r"(?m)^(?=\S*planted-api-faults\.lean:\d+:\d+: )", out):
    m = re.match(r"\S*planted-api-faults\.lean:(\d+):\d+: error", block)
    if m:
        errors.append((int(m.group(1)), block))
fail = False
for name, start, end, expect in faults:
    if not expect:
        print(f"FAULT {name}: no -- EXPECT: line"); fail = True; continue
    inside = [msg for (ln, msg) in errors if start <= ln <= end]
    if not inside:
        print(f"PLANTED FAULT ELABORATED: {name} (lines {start}-{end})"); fail = True
    elif not any(expect in msg for msg in inside):
        print(f"WRONG GUARD: {name} refused, but no error names '{expect}'"); fail = True
    else:
        print(f"refused by its guard: {name} ('{expect}')")
print(f"PASS: all {len(faults)} planted API faults are refused by their guards" if not fail else "FAIL")
sys.exit(1 if fail else 0)
PY
