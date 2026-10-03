#!/usr/bin/env python3
"""Receive a delegated app export, exact document retry, and independent readback.

All publication and recovery decisions belong to Mini's retained operation.
This runner never recaptures an occupied ID or automatically rebases a refusal.
"""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import secrets
import subprocess
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("checkpoint_custody", HERE / "checkpoint-app.py")
custody = importlib.util.module_from_spec(spec)
spec.loader.exec_module(custody)
load, save, require, sha = custody.load, custody.save, custody.require, custody.sha


def absolute(value):
    path = Path(value)
    require(path.is_absolute() and ".." not in path.parts, "absolute canonical path required")
    return path


def reference_path(workspace, name):
    require(isinstance(name, str) and 1 <= len(name) <= 128 and all(re.fullmatch(r"[A-Za-z0-9-]{1,64}", part) for part in name.split("/")), "held reference name required")
    return workspace / "refs" / (name.replace("/", ".") + ".json")


def binding(config, provisioned):
    ws = absolute(provisioned["workspace"])
    d = provisioned["delegate"]
    require(load(ws / "workspace.json")["subject"] == provisioned["subject"] == d["subject"], "connector subject differs")
    refs = {name: load(reference_path(ws, name)) for name in ("app", "package", config["taskReference"], config["documentReference"])}
    require(refs["app"]["target"] == provisioned["app"] and refs["package"]["target"] == provisioned["packageManifest"], "held source references differ")
    register = load(absolute(provisioned["registrationRequest"]))
    require(register["expectedApp"] == provisioned["app"] and register["expectedAppGeneration"] == provisioned["generation"], "retained registration identity differs")
    route = provisioned["route"]
    web = provisioned["sessionKind"] == "web"
    require(absolute(route["tokenFile"]) == absolute(route["directory"]) / ("bootstrap.token" if web else "api.token"), "credential path differs from source route")
    # A web session's credential is its cookie value; the route's bootstrap
    # token is a browser's one-shot exchange for that cookie and stays unspent.
    token = custody.private_file(absolute(route["directory"]) / ("browser.token" if web else "api.token")).read_text().strip()
    return {"type": "mini-app-document-binding-v1", "subject": provisioned["subject"],
        "appReference": "app", "app": provisioned["app"], "generation": provisioned["generation"],
        "packageReference": "package", "packageManifest": provisioned["packageManifest"],
        "sessionKind": provisioned["sessionKind"], "credentialKind": provisioned["credentialKind"],
        "session": d["session"], "sessionGeneration": register["expectedSessionGeneration"], "ticket": d["ticket"],
        "document": config["documentReference"], "documentCapability": refs[config["documentReference"]]["operationCapability"],
        "taskReference": config["taskReference"], "task": refs[config["taskReference"]]["target"],
        "sheet": provisioned["sheet"], "endpoint": config["endpoint"], "apiPath": route["signedApiPath"],
        "token": token, "ca": config["ca"]}


def retained_effect_exit(value):
    if not isinstance(value, dict) or value.get("type") != "mini-app-document-result-v1":
        return None
    return {"failed": 1, "refused": 3, "uncertain": 4, "source-uncertain": 4}.get(value.get("status"))


def verified_readback(body, status):
    receipt = status["receipt"]
    marker = ("Export " + receipt["bodySha256"] + " · operation " + receipt["operation"] + " · receipt " + receipt["transaction"] + "\n").encode()
    require(body.count(marker) == 1, "independent document lacks one exact export attribution")
    start = body.index(marker) + len(marker)
    payload = body[start:start + int(receipt["bodyBytes"])]
    require(len(payload) == int(receipt["bodyBytes"]) and hashlib.sha256(payload).hexdigest() == receipt["bodySha256"], "independent document export bytes differ")
    return {"bodyBytes": receipt["bodyBytes"], "bodySha256": receipt["bodySha256"], "operation": receipt["operation"], "transaction": receipt["transaction"]}


def readback_bytes(page, target):
    require(page["type"] == "document" and page["host"] == target, "independent source read names another document")
    # JSON's per-line text is the reader's opened presentation. The exported
    # CSV is UTF-8 text; marks/comments/embeds and struck atoms are not its bytes.
    return b"".join((row["text"] + "\n").encode() for row in page["lines"] if row["kind"] == "atom" and row.get("struck") is not True)


def same_world(exporter, reader, fixture):
    attachment = fixture["attachment"]
    require(exporter["type"] == reader["type"] == "minidregg-participant-workspace-v1", "native participant workspaces required")
    require(exporter["config"] == reader["config"] == attachment["miniConfig"] and exporter["socket"] == reader["socket"] == attachment["publicSocket"], "independent reader belongs to another Store")
    require(sha(absolute(exporter["config"])) == attachment["miniConfigSha256"], "Store config pin differs")
    # Installation may expose the identical sealed Host under a role alias.
    # Admit aliases only through the exact pinned executable bytes.
    expected = fixture["artifacts"]["host"]["sha256"]
    require(all(sha(absolute(path)) == expected for path in (exporter["host"], reader["host"], fixture["artifacts"]["host"]["path"])), "reader/exporter Host pin differs")


def journey(path):
    c = load(absolute(path))
    require(set(c) == {"protocol", "root", "provisioned", "provisionedSha256", "mini", "endpoint", "ca", "operation", "taskReference", "documentReference", "reader"}, "exact receiving input required")
    require(c["protocol"] == "mini-app-document-journey-v1", "unknown journey protocol")
    require(re.fullmatch(r"[A-Za-z0-9-]{1,60}", c["operation"]), "operation ID must contain 1..60 ASCII letters, digits or hyphens")
    for name in (c["taskReference"], c["documentReference"], c["reader"]["document"]):
        reference_path(Path("/"), name)
    result_path = absolute(c["provisioned"])
    require(sha(result_path) == c["provisionedSha256"], "provision result pin differs")
    p = load(result_path)
    require(p["protocol"] == "mini-app-document-provisioned-v1", "source-provisioned connector required")
    mini = absolute(c["mini"]["path"])
    require(set(c["mini"]) == {"path", "sha256"} and sha(mini) == c["mini"]["sha256"], "Mini image pin differs")
    fixture = load(absolute(p["fixture"]))
    require(fixture["artifacts"]["mini"] == c["mini"], "runner Mini differs from coherent source fixture")
    ws = absolute(p["workspace"])
    reader = absolute(c["reader"]["workspace"])
    own_workspace, reader_workspace = load(ws / "workspace.json"), load(reader / "workspace.json")
    require(reader_workspace["subject"] != p["subject"], "readback must use an independent participant")
    same_world(own_workspace, reader_workspace, fixture)
    require(load(reference_path(reader, c["reader"]["document"]))["target"] == load(reference_path(ws, c["documentReference"]))["target"], "independent reader names another document")
    root = absolute(c["root"])
    if not root.exists():
        root.mkdir(mode=0o700)
    custody.private_directory(root)
    lock = os.open(root / "journey.lock", os.O_WRONLY | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        custody.private_file(root / "journey.lock")
        fcntl.flock(lock, fcntl.LOCK_EX)
        save(root / "input.json", c)
        retained_binding = root / "binding.json"
        if retained_binding.exists() or retained_binding.is_symlink():
            # Source revocation may remove the route credential. Exact document
            # recovery uses the already retained binding and needs no new token.
            custody.private_file(retained_binding)
        else:
            save(retained_binding, binding(c, p))
        run = root / ("run-" + secrets.token_hex(8))
        run.mkdir(mode=0o700)

        def invoke(label, args, raw=False):
            try:
                process = subprocess.run([str(mini), *map(str, args)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180, check=False)
            except subprocess.TimeoutExpired:
                save(run / (label + ".json"), {"phase": label, "status": "process-uncertain", "message": "Exact Mini operation remains retained; no replacement request was made."})
                raise RuntimeError("Mini timeout; inspect retained operation, never recapture")
            evidence = {"phase": label, "returnCode": process.returncode, "stdoutSha256": hashlib.sha256(process.stdout).hexdigest(), "stderrSha256": hashlib.sha256(process.stderr).hexdigest()}
            accepted = process.returncode == 0
            if not raw:
                try:
                    value = json.loads(process.stdout)
                except ValueError:
                    value = None
                if value is not None and (accepted or retained_effect_exit(value) == process.returncode):
                    evidence["result"] = value
                    accepted = True
            save(run / (label + ".json"), evidence)
            require(accepted, "Mini " + label + " did not complete; inspect retained operation")
            return process.stdout if raw else evidence["result"]

        def action(label, op, extra=()):
            return invoke(label, ["workspace", "--action", "app-document", "--dir", ws, "--op", op, "--id", c["operation"], *extra])

        occupied = ws / "app-documents" / c["operation"]
        state = action("retained-status", "status") if occupied.exists() else action("capture", "capture", ["--binding", root / "binding.json"])
        if state["status"] == "uncertain":
            state = action("recover", "recover")
        if state["status"] == "captured":
            state = action("publish", "publish")
        if state["status"] != "saved":
            summary = {"protocol": "mini-app-document-journey-result-v1", "status": state["status"], "subject": p["subject"], "operation": c["operation"], "evidence": str(run), "message": "Operation remains retained; inspect Mini status before an explicit rebase or source recovery."}
            save(run / "result.json", summary)
            return summary
        receipt = state["receipt"]
        call = absolute(state["attempt"]) / "call.bin"
        exact_call = sha(call)
        again = action("publish-repeat", "publish")
        recovered = action("exact-lookup", "recover")
        require(again["status"] == recovered["status"] == "saved" and again["receipt"] == recovered["receipt"] == receipt and sha(call) == exact_call, "repeat changed exact export or document call")
        raw = invoke("independent-readback", ["workspace", "--action", "doc-show", "--dir", reader, "--name", c["reader"]["document"], "--format", "json"], raw=True)
        checked = verified_readback(readback_bytes(json.loads(raw), state["target"]), recovered)
        summary = {"protocol": "mini-app-document-journey-result-v1", "status": "saved", "subject": p["subject"], "operation": c["operation"], "target": state["target"], "receipt": checked, "callSha256": exact_call, "evidence": str(run), "evidenceBoundary": "Native request admission plus host/TLS export custody; independent document readback."}
        save(run / "result.json", summary)
        return summary
    finally:
        os.close(lock)


def main():
    os.umask(0o077)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    args = parser.parse_args()
    print(json.dumps(journey(args.input)))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, KeyError, OSError) as error:
        print("app document journey: " + str(error), file=sys.stderr)
        sys.exit(1)
