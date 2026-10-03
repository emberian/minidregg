#!/usr/bin/env python3
"""Create the connector's native context and owner-delegated document reference.
No app/package grant, provider, or second authority plane is created here.
The task is a declared context cell (the current exporter reads it only), not an
executing resident grain. Native workspace journals own birth/recovery.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("same_store_inputs", HERE / "same-store-inputs.py")
s = importlib.util.module_from_spec(spec); spec.loader.exec_module(s)
load, require, sha = s.load, s.require, s.sha

def retain(path, value):
    data = (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()
    if path.exists():
        require(not path.is_symlink() and path.read_bytes() == data, "retained input differs: " + str(path))
    else:
        with path.open("xb") as out:
            os.chmod(path, 0o600); out.write(data); out.flush(); os.fsync(out.fileno())

def pending_action(attempt):
    if not attempt.exists():
        return "submit"
    # A call is an unknown-outcome boundary. Never replace it from feed absence
    # or reconstruct a fresh proposal after an unsuccessful lookup.
    return "recover" if (attempt / "call.bin").is_file() else "unresolved"

def bound_limit(head, capability):
    require(head["id"] == capability, "signed document capability differs")
    return str(min(1000000, int(head["maxCost"])))

def execute(world, root, proposal_id):
    c = s.connector_selection(world)
    owner = world.selection["app"]["owner"]
    owner_ws, _ = world.member(owner)
    connector_ws, _ = world.member(c["subject"])
    reader = c["reader"]
    require(reader["subject"] == owner, "document source must be the actual app-owner reader")
    require(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,63}", proposal_id) is not None, "invalid proposal identity")
    for name in (c["task"], c["document"]):
        require(re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]{0,63}", name) is not None, "simple connector reference name required")
    source_ref = load(owner_ws / "refs" / (reader["document"].replace("/", ".") + ".json"))
    require(source_ref["kind"] == "object" and source_ref.get("operationCapability"), "document source has no owner write grant")
    require(not source_ref.get("private") and not source_ref.get("sealedIn"), "explicit private document sharing requires its own protocol")
    root = s.absolute(root)
    if not root.exists(): root.mkdir(mode=0o700)
    s.f.protected_parent(root)
    binding = {"protocol": "mini-connector-authority-input-v1", "platformInputsSha256": sha(world.inputs_path),
               "selection": c, "owner": owner, "ownerWorkspace": str(owner_ws),
               "connectorWorkspace": str(connector_ws), "documentTarget": source_ref["target"],
               "documentSourceCapability": source_ref["operationCapability"], "proposalId": proposal_id,
               "miniSha256": world.manifest["sha256"]["mini"]}
    retain(root / "input.json", binding)
    serial = 0
    def run(workspace, *words, native=False, binary=None):
        nonlocal serial
        serial += 1
        stem = root / (f"{serial:03d}-" + os.urandom(4).hex())
        argv = ([binary or world.manifest["mini"], *map(str, words)] if native else
                [world.manifest["mini"], "workspace", "--dir", str(workspace), *map(str, words)])
        retain(Path(str(stem) + ".argv.json"), argv)
        with Path(str(stem) + ".out").open("xb") as out, Path(str(stem) + ".err").open("xb") as err:
            result = subprocess.run(argv, stdout=out, stderr=err, timeout=1800, check=False)
        retain(Path(str(stem) + ".exit.json"), {"exit": result.returncode})
        require(result.returncode == 0, "native command failed; retained " + str(stem))
    task_ref = connector_ws / "refs" / (c["task"] + ".json")
    if not task_ref.exists():
        predicate = root / "context-law.json"
        retain(predicate, {"type": "all", "predicates": []})
        run(connector_ws, "--action", "create", "--name", c["task"], "--storage", "declared", "--predicate", predicate)
    task = load(task_ref)
    require(task["kind"] == "object" and task["target"] != source_ref["target"], "connector task context overlaps document")
    # Shared-name resolution can select the room placing grant. Delegate from
    # the actual retained document root through an ordinary simple hint alias.
    alias = "connector-source-" + proposal_id
    alias_path = owner_ws / "refs" / (alias + ".json")
    if not alias_path.exists():
        run(owner_ws, "--action", "import", "--name", alias, "--kind", source_ref["kind"],
            "--target", source_ref["target"], "--observe-capability", source_ref["observeCapability"],
            "--operation-capability", source_ref["operationCapability"],
            "--provenance", owner_ws / "refs" / (reader["document"].replace("/", ".") + ".json"))
    selected = load(alias_path)
    require(all(selected.get(k) == source_ref.get(k) for k in ("kind", "target", "observeCapability", "operationCapability")),
            "retained document alias differs")
    limit_path = root / "document-grant-limit.json"
    if not limit_path.exists():
        pin = load(owner_ws / "workspace.json")
        query_dir = root / ("document-capability-" + os.urandom(8).hex())
        query_path = Path(str(query_dir) + ".json")
        retain(query_path, {"subject": owner, "nonce": str(int.from_bytes(os.urandom(16), "big")),
                           "purpose": {"type": "query", "kind": "object", "target": source_ref["target"], "view": "capability"},
                           "grants": [{"kind": "object", "target": source_ref["target"], "capability": source_ref["operationCapability"]}]})
        run(owner_ws, "query", "--host", pin["host"], "--config", pin["config"], "--socket", pin["socket"],
            "--intent", query_path, "--key", pin["key"], "--view", "capability", "--dir", query_dir, native=True)
        inspected = root / (query_dir.name + "-head.json")
        run(owner_ws, world.config_path, "inspect", "view-object-capability", query_dir / "view.bin", inspected,
            native=True, binary=world.manifest["host"])
        head = load(inspected)["head"]
        retain(limit_path, {"maxCost": bound_limit(head, source_ref["operationCapability"]),
                            "capabilityView": str(query_dir / "view.json"), "capabilityViewSha256": sha(query_dir / "view.json")})
    limit = load(limit_path)
    require(sha(limit["capabilityView"]) == limit["capabilityViewSha256"], "retained grant limit view differs")
    request = {"type": "minidregg-workspace-proposal-v1", "action": "delegate", "name": alias,
               "recipient": c["subject"], "verbs": ["observe", "mutate"], "maxCost": limit["maxCost"]}
    request_path = root / "document-grant-request-v2.json"; retain(request_path, request)
    proposal = owner_ws / "proposals" / proposal_id
    attempt = owner_ws / "attempts" / proposal_id
    if not proposal.exists():
        require(not attempt.exists(), "attempt exists without its exact proposal")
        run(owner_ws, "--action", "propose", "--request", request_path, "--proposal-id", proposal_id)
    else:
        # The retained proposal is bound to the unchanged owner request.
        require(load(proposal / "request.json") == request, "retained document proposal differs")
    disposition = pending_action(attempt)
    if disposition == "submit":
        run(owner_ws, "--action", "submit", "--intent", proposal / "intent.json", "--attempt", attempt)
    elif disposition == "recover":
        run(owner_ws, "--action", "recover", "--attempt", attempt)
    else:
        raise RuntimeError("retained document attempt has no exact call; inspect it before any new effect: " + str(attempt))
    run(owner_ws, "--action", "publish-delegation", "--proposal-id", proposal_id, "--attempt", attempt)
    recipient = proposal / "recipient-reference.json"
    granted = load(recipient)
    require(granted["recipient"] == c["subject"] and granted["target"] == source_ref["target"], "native delegated document binding differs")
    doc_ref = connector_ws / "refs" / (c["document"] + ".json")
    if not doc_ref.exists():
        run(connector_ws, "--action", "import", "--from-ref", recipient, "--name", c["document"])
    held = load(doc_ref)
    require(held["target"] == source_ref["target"] and held["operationCapability"] == granted["capability"], "held connector document grant differs")
    for name in (c["task"], c["document"]):
        run(connector_ws, "--action", "read", "--name", name)
    result = {"protocol": "mini-connector-authority-result-v1", "subject": c["subject"],
              "task": task, "document": held, "documentTarget": held["target"], "attempt": str(attempt),
              "recipientReference": str(recipient), "evidence": str(root),
              "boundary": "native signed reads and accepted delegation; task is exporter context only"}
    retain(root / "result.json", result)
    return result

def main():
    os.umask(0o077)
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("platform-inputs", "selection", "world-inventory", "root", "proposal-id"):
        p.add_argument("--" + name, required=True)
    a = p.parse_args()
    require(os.getuid() != 0, "run as Store operator")
    world = s.World(a.platform_inputs, a.selection, a.world_inventory)
    print(json.dumps(execute(world, a.root, a.proposal_id)))
if __name__ == "__main__":
    try: main()
    except (RuntimeError, ValueError, KeyError, OSError, subprocess.TimeoutExpired) as error:
        print("connector authority: " + str(error), file=sys.stderr); sys.exit(1)
