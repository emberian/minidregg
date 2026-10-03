#!/usr/bin/env python3
"""Compare a pinned review receipt with current source bytes, without opening Git."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--source-root", type=Path, help="source checkout to compare; default is this consumer")
parser.add_argument("--receipt", type=Path, help="review receipt; default is horse-entries/provenance.json")
args = parser.parse_args()
canon = Path(__file__).resolve().parent.parent
root = (args.source_root or canon.parent).resolve()
receipt = args.receipt or canon / "audits/horse-entries/provenance.json"
review = json.loads(receipt.read_text())
rows = []
for name, evidence in sorted(review["source_files"].items()):
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit("refused non-relative source path in receipt")
    source = root / relative
    if not source.is_file():
        rows.append({"source": name, "state": "missing", "expected_sha256": evidence["sha256"]})
        continue
    observed = hashlib.sha256(source.read_bytes()).hexdigest()
    rows.append({"source": name, "state": "match" if observed == evidence["sha256"] else "drift",
                 "expected_sha256": evidence["sha256"], "observed_sha256": observed})
print(json.dumps({"reviewed_revision": review["source_revision"],
    "workbench_revision": review["workbench_revision"], "scope": "exact file bytes, not qualification",
    "states": {state: sum(row["state"] == state for row in rows) for state in ["match", "drift", "missing"]},
    "files": rows}, indent=2))
