#!/usr/bin/env python3
"""Untrusted read-only native authority probe for an existing Oracle journey.

Consume the fixed installer's hashed controller export and one successful
applicationApiHistory entry. Reinspect its actual op80 plan, authenticate its
accepted reserve by exact public lookup, then ask op80 about canonical requests
with only the event22 or event27 index changed. No signing, submission, replay
as new work, lifecycle transition, key access, or full cold history walk occurs.
"""
import argparse
import base64
import copy
import hashlib
import json
from pathlib import Path
import socket
import struct
import subprocess
import time

MAX_FRAME = 12_102_760
REQUEST_KIND = "application-agent-lifetime-reserve-request"
PLAN_KIND = "application-agent-lifetime-reserve-plan"


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bounded(path, limit):
    require(path.stat().st_size <= limit, f"input exceeds bound: {path.name}")
    raw = path.read_bytes()
    require(len(raw) <= limit, "input grew beyond bound")
    return raw


def decimal(value):
    require(isinstance(value, str) and value.isascii() and value.isdigit()
            and (value == "0" or not value.startswith("0")), "noncanonical source index")
    return int(value)


def receive(peer, size):
    raw = bytearray()
    while len(raw) < size:
        chunk = peer.recv(size - len(raw))
        require(bool(chunk), "socket closed before complete reply")
        raw.extend(chunk)
    return bytes(raw)


def exchange(path, envelope, timeout):
    with socket.socket(socket.AF_UNIX) as peer:
        peer.settimeout(timeout)
        peer.connect(str(path))
        peer.sendall(struct.pack("<I", len(envelope)) + envelope)
        width = struct.unpack("<I", receive(peer, 4))[0]
        require(0 < width <= MAX_FRAME, "reply outside frame bound")
        return receive(peer, width)


def classify_refusal(outcome, expected):
    require(outcome.get("type") == "refused", "source did not decode a refusal")
    require(outcome.get("effect") == "no-record", "source did not decide no-record")
    require(outcome.get("phase") == b"op 80".hex(), "source refusal belongs to another operation")
    detail = bytes.fromhex(outcome["detail"]).decode("utf-8")
    require(detail in expected,
            "refusal does not establish the selected history-index check: " + detail)
    return detail


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("host", "config", "operator-socket", "public-socket",
                 "controller-export", "application-attempt", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--deadline", type=float, default=180)
    args = parser.parse_args()
    require(0 < args.deadline <= 600, "deadline must be within 1..600 seconds")
    args.out.mkdir(mode=0o700, parents=False, exist_ok=False)
    config = bounded(args.config, 65536)
    with args.host.open("rb") as source:
        host_sha = hashlib.file_digest(source, "sha256").digest()
    binding = b"\x02" + struct.pack("<I", len(config)) + config + host_sha
    report = {"protocol": "mini-oracle-agent-authority-probe-v1", "passed": False,
              "scope": "actual retained positive reserve + current exact lookup + wrong-index source refusals",
              "hostSha256": host_sha.hex(), "configSha256": sha(config),
              "revocationTested": False, "unsubmittedStalePlanTested": False,
              "measurements": {}}

    def save():
        tmp = args.out / "report.json.tmp"
        tmp.write_text(json.dumps(report, indent=2) + "\n")
        tmp.replace(args.out / "report.json")

    def native(label, *command):
        start = time.monotonic()
        result = subprocess.run([str(args.host), str(args.config), *map(str, command)],
                                capture_output=True, timeout=args.deadline, check=False)
        (args.out / (label + ".stdout")).write_bytes(result.stdout)
        (args.out / (label + ".stderr")).write_bytes(result.stderr)
        report["measurements"][label] = {"seconds": time.monotonic() - start,
                                          "exit": result.returncode}
        save()
        require(result.returncode == 0, "source author/inspection failed: " + label)

    def inspect(label, kind, raw):
        source = args.out / (label + ".bin")
        source.write_bytes(raw)
        target = args.out / (label + ".json")
        native(label, "inspect", kind, source, target)
        return json.loads(bounded(target, 8 * MAX_FRAME))

    def invoke(label, socket_path, op, payload):
        start = time.monotonic()
        response = exchange(socket_path, binding + bytes([op]) + payload, args.deadline)
        (args.out / (label + ".frame")).write_bytes(response)
        report["measurements"][label] = {"seconds": time.monotonic() - start,
                                          "sha256": sha(response), "bytes": len(response)}
        save()
        return response

    try:
        export_raw = bounded(args.controller_export, 48 * 1024 * 1024)
        exported = json.loads(export_raw)
        require(exported.get("protocol") == "mini-spk-controller-evidence-v1", "wrong export protocol")
        matched_raw = bounded(args.application_attempt, 2 * 1024 * 1024)
        matched = json.loads(matched_raw)
        settlement = matched["lifetimeSettlement"]
        attempt_id = settlement["dispatchAttemptId"]
        require(isinstance(attempt_id, int) and not isinstance(attempt_id, bool)
                and 0 <= attempt_id < 2**64, "invalid dispatch attempt ID")
        require(matched.get("phase") == "definite" and matched.get("reported") is True
                and matched.get("lifetimeCommittedReceipt") is not None
                and settlement["forwardOperationId"] == matched["operationId"]
                and settlement["settlement"]["operation"] == "dispatch settle",
                "application entry is not a definite settled native lifetime call")
        prefix = f"agent-lifetime-reserve-{attempt_id:016}/"
        originals = {}
        for name in ("source.json", "pin.json", "request.bin", "plan.bin", "plan.frame",
                     "call.bin", "receipt.json", "submit-marker.json"):
            entry = exported["files"][prefix + name]
            raw = base64.b64decode(entry["base64"], validate=True)
            require(0 < len(raw) <= MAX_FRAME and sha(raw) == entry["sha256"],
                    "exported reserve evidence hash/bound mismatch: " + name)
            originals[name] = raw
            (args.out / ("original-" + name)).write_bytes(raw)
        pin = json.loads(originals["pin.json"])
        require(pin["format"] == "minidregg-agent-lifetime-reserve-custody-v1"
                and pin["hostSha256"] == host_sha.hex() and pin["configSha256"] == sha(config)
                and pin["requestSha256"] == sha(originals["request.bin"])
                and pin["planSha256"] == sha(originals["plan.bin"])
                and originals["plan.frame"] == b"\x50" + originals["plan.bin"],
                "original positive plan differs from native pins")
        source = json.loads(originals["source.json"])
        require(decimal(source["fixed"]["base"]["http"]["operationId"]) == matched["operationId"],
                "positive source belongs to another application call")
        plan = inspect("positive-plan", PLAN_KIND, originals["plan.bin"])
        require(plan.get("type") == "application-agent-lifetime-reserve-plan-v3"
                and plan.get("canonicalPlanHex") == originals["plan.bin"].hex()
                and plan.get("canonicalRequestHex") == originals["request.bin"].hex(),
                "positive plan source join differs")
        marker = json.loads(originals["submit-marker.json"])
        require(marker["type"] == "minidregg-agent-lifetime-reserve-submit-attempt-v1"
                and marker["callSha256"] == sha(originals["call.bin"]), "native submit marker differs")
        # Lookup is read-only and must return the exact original admitted receipt.
        response = invoke("positive-reserve-lookup", args.public_socket, 3, originals["call.bin"])
        require(response[:1] == b"\x03", "original reserve lookup unavailable")
        outcome = inspect("positive-reserve-outcome", "outcome", response[1:])
        receipt = json.loads(originals["receipt.json"])
        require(outcome.get("type") == "confirmed" and outcome.get("confirmation") == "replayed"
                and all(outcome.get(k) == receipt.get(k) for k in
                        ("transactionId", "eventId", "acceptedCount", "worldRoot")),
                "current source lookup did not authenticate original positive reserve")
        require(decimal(receipt["acceptedCount"]) == decimal(receipt["reserveIndex"]) + 1,
                "reserve receipt index differs")
        report.update(controllerExportSha256=sha(export_raw), applicationAttemptSha256=sha(matched_raw),
                      reserveAttempt=prefix[:-1], positiveReserveReceipt=receipt,
                      positivePlanSha256=sha(originals["plan.bin"]))
        # Round-trip the original source first, so variants modify a source the
        # pinned Host itself confirms encodes the successful original request.
        native("original-source-author", "author", REQUEST_KIND,
               args.out / "original-source.json", args.out / "original-authored.bin")
        require(bounded(args.out / "original-authored.bin", MAX_FRAME) == originals["request.bin"],
                "original source does not encode the retained request")
        expected = {
            "wrong-event22-index": ["lifetime grant differs from fixed custodian/original ticket"],
            "wrong-event27-index": ["lifetime grant absent from admitted history",
                                    "lifetime grant differs from fixed custodian/original ticket"],
        }
        for label in expected:
            changed = copy.deepcopy(source)
            if label == "wrong-event22-index":
                old = changed["fixed"]["base"]["issueIndex"]
                changed["fixed"]["base"]["issueIndex"] = str(decimal(old) + 1)
            else:
                old = changed["grantIssueIndex"]
                changed["grantIssueIndex"] = str(decimal(old) + 1)
            request_path = args.out / (label + ".source.json")
            request_path.write_text(json.dumps(changed) + "\n")
            binary = args.out / (label + ".request.bin")
            native(label + "-author", "author", REQUEST_KIND, request_path, binary)
            response = invoke(label, args.operator_socket, 80, bounded(binary, MAX_FRAME))
            require(response[:1] == b"\xfd", label + " did not explicitly refuse")
            outcome = inspect(label + "-outcome", "outcome", response[1:])
            report[label] = {"passed": True, "detail": classify_refusal(outcome, expected[label])}
            save()
        with args.host.open("rb") as current:
            require(hashlib.file_digest(current, "sha256").digest() == host_sha, "Host image changed")
        require(bounded(args.config, 65536) == config, "Host config changed")
        report["passed"] = True
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        save()
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
