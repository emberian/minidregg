#!/usr/bin/env python3
"""Untrusted read-only receiving probe for Mini's STOP inspection, not authority.

Measure resident inspections first, then compare the cold pinned Host CLI
against the same exact inputs. Partial resident results survive a cold timeout. No lifecycle submission, STOP, restart, or retry occurs.
Use only an isolated qualification Store whose Host/config pins match --host.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import socket
import struct
import subprocess
import time

OP = 155
MAX_FRAME = 12_102_760
MAX_JSON = 2 * 1024 * 1024


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def receive(sock, count):
    chunks = bytearray()
    while len(chunks) < count:
        chunk = sock.recv(count - len(chunks))
        if not chunk:
            raise RuntimeError("operator closed without a complete reply")
        chunks.extend(chunk)
    return bytes(chunks)


def exchange(path, envelope, deadline):
    with socket.socket(socket.AF_UNIX) as connection:
        connection.settimeout(deadline)
        connection.connect(str(path))
        connection.sendall(struct.pack("<I", len(envelope)) + envelope)
        width = struct.unpack("<I", receive(connection, 4))[0]
        if not 1 <= width <= MAX_FRAME:
            raise RuntimeError("reply exceeds host frame bound")
        return receive(connection, width)


def cold(args, output):
    process = subprocess.Popen(
        [str(args.host), str(args.config), "inspect-stop-claim",
         str(args.plan), str(args.committed), str(output)],
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=args.deadline)
    except subprocess.TimeoutExpired:
        # This process group was created and recorded by this probe alone.
        os.killpg(process.pid, signal.SIGTERM)
        try:
            stdout, stderr = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
        (args.out / "cold.stdout").write_bytes(stdout)
        (args.out / "cold.stderr").write_bytes(stderr)
        raise RuntimeError("cold inspection exceeded its deadline") from None
    (args.out / "cold.stdout").write_bytes(stdout)
    (args.out / "cold.stderr").write_bytes(stderr)
    if process.returncode:
        raise RuntimeError(f"cold inspection exited {process.returncode}")
    raw = output.read_bytes()
    if not 0 < len(raw) <= MAX_JSON:
        raise RuntimeError("cold JSON exceeds native inspection bound")
    return raw


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("host", "config", "operator-socket", "plan", "committed", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--public-socket", type=Path, required=True)
    parser.add_argument("--mismatched-committed", type=Path,
                        help="a different canonical claim; required on the post-append qualification pass")
    parser.add_argument("--deadline", type=float, default=1200)
    args = parser.parse_args()
    if not 0 < args.deadline <= 1800:
        parser.error("deadline must be positive and at most 1800 seconds")
    args.out.mkdir(mode=0o700, parents=False, exist_ok=False)
    config, plan, committed = (p.read_bytes() for p in (args.config, args.plan, args.committed))
    host_sha = hashlib.file_digest(args.host.open("rb"), "sha256").digest()
    pair = struct.pack("<I", len(plan)) + plan + committed
    if not plan or not committed or len(pair) >= MAX_FRAME or len(config) > 65536:
        raise RuntimeError("input outside native bounds")
    mismatched = (args.mismatched_committed.read_bytes()
                  if args.mismatched_committed is not None else None)
    if mismatched is not None and (not mismatched or mismatched == committed or
                                   4 + len(plan) + len(mismatched) >= MAX_FRAME):
        raise RuntimeError("mismatched claim must be different, nonempty and within bounds")
    binding = b"\x02" + struct.pack("<I", len(config)) + config + host_sha
    report = {"schema": "mini-stop-inspection-probe-v1", "passed": False,
              "scope": "Read-only cold/served comparison, no lifecycle operation",
              "host_sha256": host_sha.hex(), "config_sha256": digest(config),
              "plan_sha256": digest(plan), "committed_sha256": digest(committed),
              "canonical_wrong_claim_checked": False,
              "served_checks_passed": False, "cold_comparison": "pending",
              "measurements": {}}

    def save_report():
        temporary = args.out / "report.json.tmp"
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(args.out / "report.json")

    def measured(name, run):
        start = time.monotonic()
        try:
            raw = run()
        except Exception as error:
            report["measurements"][name] = {
                "seconds": time.monotonic() - start, "error": str(error)}
            save_report()
            raise
        report["measurements"][name] = {
            "seconds": time.monotonic() - start,
            "bytes": len(raw), "sha256": digest(raw)}
        save_report()
        return raw

    def served(payload):
        return exchange(args.operator_socket, binding + bytes([OP]) + payload, args.deadline)

    try:
        first = measured("served-first", lambda: served(pair))
        (args.out / "served-first.bin").write_bytes(first)
        if first[:1] != bytes([OP]) or not 0 < len(first) - 1 <= MAX_JSON:
            raise RuntimeError("resident did not return a bounded STOP inspection")
        view = json.loads(first[1:])
        if (view.get("type") != "application-lifecycle-stop-claim-verified-v1" or
                view.get("retainedPlanHex") != plan.hex() or
                view.get("freshCommittedFrameHex") != committed.hex()):
            raise RuntimeError("resident inspection differs from exact retained inputs")
        reply = measured("served-repeat", lambda: served(pair))
        (args.out / "served-repeat.bin").write_bytes(reply)
        if reply != first:
            raise RuntimeError("repeated resident inspection differs")
        # A canonical pair containing a changed inner frame must not inherit the
        # previous successful inspection. It still reaches Lean's inner decoder.
        for label, payload in (("trailing-claim", pair + b"\0"),
                               ("malformed-pair", b"\xff\xff\xff\xff")):
            reply = measured(label, lambda: served(payload))
            (args.out / (label + ".bin")).write_bytes(reply)
            if not reply or reply[0] != 255:
                raise RuntimeError(label + " did not return explicit refusal")
        if mismatched is not None:
            wrong_pair = struct.pack("<I", len(plan)) + plan + mismatched
            reply = measured("mismatched-committed", lambda: served(wrong_pair))
            (args.out / "mismatched-committed.bin").write_bytes(reply)
            if not reply or reply[0] != 255:
                raise RuntimeError("mismatched canonical claim did not return explicit refusal")
            report["canonical_wrong_claim_checked"] = True
            report["mismatched_committed_sha256"] = digest(mismatched)
        reply = measured("public-denied", lambda: exchange(
            args.public_socket, binding + bytes([OP]) + pair, args.deadline))
        (args.out / "public-denied.bin").write_bytes(reply)
        if not reply or reply[0] != 255:
            raise RuntimeError("public socket accepted STOP inspection")
        reply = measured("served-after-refusals", lambda: served(pair))
        (args.out / "served-after-refusals.bin").write_bytes(reply)
        if reply != first:
            raise RuntimeError("valid inspection changed after refused requests")
        report["served_checks_passed"] = True
        report["cold_comparison"] = "running"
        save_report()
        original = measured("cold", lambda: cold(args, args.out / "cold.json"))
        if first != bytes([OP]) + original:
            raise RuntimeError("resident inspection differs from cold inspection bytes")
        report["cold_comparison"] = "passed"
        if hashlib.file_digest(args.host.open("rb"), "sha256").digest() != host_sha:
            raise RuntimeError("Host image changed during comparison")
        if args.config.read_bytes() != config:
            raise RuntimeError("Host config changed during comparison")
        report["passed"] = True
    except Exception as error:
        report["error"] = str(error)
        if report["cold_comparison"] == "running":
            report["cold_comparison"] = "failed"
        raise
    finally:
        save_report()
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
