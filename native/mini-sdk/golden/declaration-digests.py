#!/usr/bin/env python3
"""The reference for the declaration digests asserted in tests/app_interface.rs.

The contract hashes `json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)`.
These are the values for apps/interfaces/gogs.json with one top-level member changed, in the
order the tests assert them. Run it after the declaration changes and paste the output; it
reproduces every value the tests carried before the declaration was repackaged as Forgejo.
usage: declaration-digests.py [GOGS_JSON]
"""
import hashlib, json, sys
path = sys.argv[1] if len(sys.argv) > 1 else "../../apps/interfaces/gogs.json"
base = open(path).read()
cases = [("description", "é💖\x7f"), ("number", "5e-7"), ("number", "1e16"), ("number", "100000.0"),
         ("number", "-0.0"), ("number", "1.2345678901234567e30")]
for key, literal in cases:
    d = json.loads(base)
    d[key] = literal if key == "description" else json.loads(literal)
    text = json.dumps(d, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    print(f"{key} {literal!r}: {hashlib.sha256(text.encode()).hexdigest()}")
