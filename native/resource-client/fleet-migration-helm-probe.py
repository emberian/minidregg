#!/usr/bin/env python3
"""Drive Pug's real harness code (helm, chat._sign_send) with the shim as its signer.

This is a probe of the HARNESS side of the migration, not of `mini fleet-sign`: it runs the
unmodified `_sign_send` path (one join if the cell cache is cold, then `send --to CELL`,
retried once when helm judges the answer incomplete) and prints what helm concluded as one
JSON object. The caller counts the turns that landed.

usage: fleet-migration-helm-probe.py HELM_SRC_DIR SHIM FLEET_HOME PROFILE [MINI_BIN]
HELM_SRC_DIR is the directory holding the `helm/` package (a read-only copy of akapug/helm).
"""
import json
import os
import sys
import tempfile

helm_src, shim, fleet_home, profile = sys.argv[1:5]
mini_bin = sys.argv[5] if len(sys.argv) > 5 else "mini"
home = tempfile.mkdtemp(prefix="helm-home-")
os.environ.update({
    "HELM_HOME": home,
    "HELM_CELL_BIN": shim,
    "HELM_CELL_PROFILE": profile,
    "DREGG_PROFILE": profile,
    # the room node helm believes in: an HTTP port nothing listens on (Mini has no HTTP ingress)
    "HELM_CHAT_NODE_URL": "http://127.0.0.1:9",
    "MINI_BIN": mini_bin,
    "MINI_FLEET_HOME": fleet_home,
})
sys.dont_write_bytecode = True
sys.path.insert(0, helm_src)
from helm import chat  # noqa: E402

payload = chat.digest_payload("hello from the probe")
info, diag = chat._sign_send(payload, profile)
print(json.dumps({"payload": payload, "info": info, "diag": diag}, sort_keys=True, default=str))
