#!/usr/bin/env python3
"""Typed same-world connector -> resident -> service-restart consumer.

The native resident journey owns births, request custody, exact effects and the
controlled crash/restart. This adapter supplies checked named-world bindings,
verifies the existing connector export through its independent document reader,
and bridges that receipt into the resident's source capture context. It never
bootstraps a Store or calls a paid provider.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PROTOCOL = "mini-same-world-resident-binding-v1"
REQUIRED = {"protocol", "platformInputs", "base", "authors", "providerWitness", "room",
            "sharedDocumentReference", "fixtureAcp", "fixtureProvider", "registration", "task"}
OPTIONAL = {"requestCounts", "prepollRows", "heldRows", "workerWallSeconds", "turnReserveSeconds",
            "nativeTimeoutSeconds", "preserveOnSuccess"}
NUMERIC = {"prepollRows": "--prepoll-rows", "heldRows": "--held-rows", "workerWallSeconds": "--worker-wall-seconds",
           "turnReserveSeconds": "--turn-reserve-seconds", "nativeTimeoutSeconds": "--native-timeout-seconds"}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def load(path):
    return json.loads(Path(path).read_text())

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def absolute(value):
    require(isinstance(value, str), "path must be a string")
    path = Path(value)
    require(path.is_absolute() and ".." not in path.parts, "absolute canonical path required")
    return path

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value

def validate(binding, world):
    require(isinstance(binding, dict) and REQUIRED <= set(binding) <= REQUIRED | OPTIONAL, "typed resident binding fields differ")
    require(binding["protocol"] == PROTOCOL, "unknown resident binding protocol")
    require(world.get("type") == "mini-world-identity-v1", "unknown supplied world")
    context = load(absolute(binding["platformInputs"]))
    manifest_path = absolute(context["manifest"])
    require(sha(manifest_path) == context["identity"]["manifestSha256"], "constructor manifest changed")
    manifest = load(manifest_path)
    for role in ("mini", "host"):
        require(sha(absolute(manifest[role])) == manifest["sha256"][role], "resident source role bytes changed: " + role)
    require(sha(absolute(context["config"])) == context["identity"]["configSha256"], "constructor configuration changed")
    members = world["members"]
    require(isinstance(binding["authors"], list) and len(binding["authors"]) >= 2
            and len(set(binding["authors"])) == len(binding["authors"]), "distinct named resident authors required")
    tokens = binding["authors"] + [binding["providerWitness"]]
    require(len(set(tokens)) == len(tokens), "provider witness must be independent of authors")
    for name in tokens:
        require(name in members, "resident participant must name a supplied world inventory member")
        row = members[name]; retained = context["memberInventory"].get(row["subject"])
        require(retained is not None and all(retained.get(k) == row.get(k) for k in ("subject", "workspace", "home")),
                "resident world and constructor participant differ: " + name)
        pin = load(absolute(row["workspace"]) / "workspace.json")
        require(pin["subject"] == row["subject"] and pin["config"] == context["config"]
                and pin["socket"] == context["publicSocket"] and sha(absolute(pin["host"])) == manifest["sha256"]["host"],
                "resident participant workspace belongs to another source world")
    room = binding["room"]
    require(isinstance(room, dict) and set(room) == {"alias", "mode"}
            and re.fullmatch(r"[A-Za-z0-9-]{1,48}", room["alias"]) and room["mode"] in ("create", "existing", "adopt"),
            "typed resident room requires alias and source create/existing/adopt mode")
    require(type(binding["task"]) is int and 0 < binding["task"] < (1 << 64) - 4, "positive resident task required")
    for key in ("base", "sharedDocumentReference", "registration"):
        absolute(binding[key])
    missing = []
    for key in ("fixtureAcp", "fixtureProvider"):
        pin = binding[key]
        require(isinstance(pin, dict) and set(pin) == {"path", "sha256"} and re.fullmatch(r"[0-9a-f]{64}", pin["sha256"]),
                "fixture source pin required")
        path = absolute(pin["path"])
        if not path.is_file():
            missing.append(str(path))
        else:
            require(sha(path) == pin["sha256"], "fixture source bytes changed")
    for key in NUMERIC:
        require(key not in binding or type(binding[key]) is int, "resident numeric option must be an integer")
    counts = binding.get("requestCounts", [1] * len(binding["authors"]))
    require(isinstance(counts, list) and len(counts) == len(binding["authors"])
            and all(type(n) is int and 1 <= n <= 8 for n in counts), "one bounded request count per author required")
    require("preserveOnSuccess" not in binding or type(binding["preserveOnSuccess"]) is bool, "preserveOnSuccess must be boolean")
    founder = members[binding["authors"][0]]
    reference = absolute(binding["sharedDocumentReference"])
    require(reference.is_file(), "founder shared document reference is absent")
    ref = load(reference)
    alias = ref["name"]
    require(isinstance(alias, str) and re.fullmatch(r"[A-Za-z0-9-]{1,64}", alias),
            "resident input needs a simple held document alias; bind the existing document without changing its target")
    require(reference == absolute(founder["workspace"]) / "refs" / (alias.replace("/", ".") + ".json"),
            "shared document must be the first author's held reference")
    return context, manifest, missing

def command(binding, world_path, capture_path, through):
    words = [sys.executable, str(HERE / "shared-resident-useful-work.py"),
        "--platform-inputs", binding["platformInputs"], "--base", binding["base"],
        "--member-names", str(world_path), "--authors", ",".join(binding["authors"]),
        "--provider-witness", binding["providerWitness"], "--room-alias", binding["room"]["alias"],
        "--room-mode", binding["room"]["mode"], "--shared-document-reference", binding["sharedDocumentReference"],
        "--capture-reference", str(capture_path), "--fixture-acp", binding["fixtureAcp"]["path"],
        "--fixture-provider", binding["fixtureProvider"]["path"], "--registration", binding["registration"],
        "--task", str(binding["task"]), "--through", through]
    if "requestCounts" in binding:
        words += ["--request-counts", ",".join(map(str, binding["requestCounts"]))]
    for name, option in NUMERIC.items():
        if name in binding:
            words += [option, str(binding[name])]
    if binding.get("preserveOnSuccess", True):
        words += ["--preserve-on-success"]
    receiving = Path(binding["base"]) / "var/lib/mini/controllers" / str(binding["task"]) / "receiving"
    if receiving.exists():
        words += ["--resume"]
    return words

def capture_context(room, result, result_path, native_page):
    require(result.get("protocol") == "mini-app-document-journey-result-v1" and result.get("status") == "saved",
            "resident requires a saved native connector journey")
    require(result.get("target") == room["documentTarget"], "connector exported to another resident document")
    require(re.fullmatch(r"[0-9a-f]{64}", str(result.get("callSha256", ""))), "connector lacks exact publication call pin")
    journey = module("source_app_document_journey", ROOT / "scripts/spk-platform/app-document-journey.py")
    checked = journey.verified_readback(journey.readback_bytes(native_page, result["target"]), result)
    context = dict(room, protocol="mini-captured-document-room-context-v1")
    context.pop("founderHome")
    context["sourceExport"] = {"result": str(result_path), "resultSha256": sha(result_path),
                               "callSha256": result["callSha256"], "receipt": checked}
    return context

def execute(binding_path, world_path, result_path, output, through):
    binding, world = load(binding_path), load(world_path)
    context, manifest, missing = validate(binding, world)
    require(not missing, "local fixture programs missing: " + ", ".join(missing))
    exported = load(result_path)
    reference = load(binding["sharedDocumentReference"])
    require(exported.get("protocol") == "mini-app-document-journey-result-v1" and exported.get("status") == "saved"
            and exported.get("target") == reference["target"], "resident requires saved export to its held source document")
    receiving = Path(binding["base"]) / "var/lib/mini/controllers" / str(binding["task"]) / "receiving"
    capture = receiving / "connector-capture-context.json"
    def invoke(stage):
        done = subprocess.run(command(binding, world_path, capture, stage), stdin=subprocess.DEVNULL,
                              capture_output=True, check=False)
        # The source journey retains per-command evidence. Keep its operator
        # hints too, particularly root registration's exact ready.json path.
        sys.stderr.buffer.write(done.stdout + done.stderr)
        return done
    boot = invoke("capture")
    require(boot.returncode in (0, 75) and (receiving / "room-context.json").is_file(),
            "native resident room/capture preparation did not complete")
    room = load(receiving / "room-context.json")
    require(room["worldConfig"] == context["config"] and room["socket"] == context["publicSocket"],
            "resident capture room belongs to another source world")
    founder = world["members"][binding["authors"][0]]
    require(room["founderSubject"] == founder["subject"] and room["founderWorkspace"] == founder["workspace"],
            "resident capture founder differs from supplied world")
    read = subprocess.run([manifest["mini"], "workspace", "--action", "doc-show", "--dir", founder["workspace"],
                           "--name", room["documentAlias"], "--format", "json"], capture_output=True, check=False)
    require(read.returncode == 0, "native resident input readback refused")
    value = capture_context(room, exported, result_path, json.loads(read.stdout))
    resident = module("resident_source", HERE / "shared-resident-useful-work.py")
    if capture.exists():
        require(load(capture) == value, "retained resident capture input changed")
    else:
        resident.publish(capture, (json.dumps(value, indent=2) + "\n").encode())
    done = invoke(through)
    if done.returncode:
        return done.returncode
    checks = load(receiving / "checks.json")
    require(checks and all(row["passed"] for row in checks)
            and any(row["check"] == "native Book payments reconcile summaries, finals and typed status notices exactly once" for row in checks),
            "native resident acceptance checks did not pass")
    result = {"protocol": "mini-same-world-resident-result-v1", "passed": True, "through": through,
              "binding": str(binding_path), "bindingSha256": sha(binding_path), "world": str(world_path),
              "capture": str(capture), "checks": str(receiving / "checks.json"), "checksSha256": sha(receiving / "checks.json")}
    if through == "retain":
        require(load(receiving / "result.json").get("passed") is True, "native restart/continuous result did not pass")
        result["nativeResult"] = str(receiving / "result.json")
        result["inventory"] = str(receiving / "controller-inventory.json")
    if output.exists():
        require(load(output) == result, "retained typed resident result changed")
    else:
        resident.publish(output, (json.dumps(result, indent=2) + "\n").encode())
    print(json.dumps(result))
    return 0

def main():
    os.umask(0o077)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("check", "run"))
    parser.add_argument("--binding", required=True)
    parser.add_argument("--world", required=True)
    parser.add_argument("--connector-result")
    parser.add_argument("--output")
    parser.add_argument("--through", choices=("verify", "retain"), default="verify")
    args = parser.parse_args()
    binding, world = absolute(args.binding), absolute(args.world)
    if args.mode == "check":
        _, _, missing = validate(load(binding), load(world))
        print(json.dumps({"protocol": "mini-same-world-resident-check-v1", "effects": False, "missing": missing, "ready": not missing}))
        return 0
    require(args.connector_result is not None and args.output is not None, "run needs retained connector result and output paths")
    return execute(binding, world, absolute(args.connector_result), absolute(args.output), args.through)

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, RuntimeError) as error:
        print("same-world resident: " + str(error), file=sys.stderr)
        sys.exit(1)
