#!/usr/bin/env python3
"""Untrusted read-only receiving probe for Mini's STOP inspection, not authority.

Measure resident inspections first, then compare the cold pinned Host CLI
against the same exact inputs. Partial resident results survive a cold timeout.
No lifecycle submission, STOP, restart, or retry occurs. Use only an isolated
qualification Store whose Host/config pins match --host.
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
ROUTE_REFUSAL = b"\xfeoperation unavailable on selected socket"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def file_digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").digest()


def benchmark_snapshot(source_config, copy_config):
    """Bind two quiescent SQLite stores; the copy changes only its storage path.

    SQLite shared-memory/lock files are process coordination, not admitted data.
    A nonempty WAL is refused: hashing only the main database would miss it.
    """
    configs = [json.loads(path.read_bytes()) for path in (source_config, copy_config)]
    roots = [Path(config["storageRoot"]) for config in configs]
    if roots[0].resolve() == roots[1].resolve():
        raise RuntimeError("benchmark requires a separate copied Store")
    normalized = [dict(config, storageRoot="<copied>") for config in configs]
    if normalized[0] != normalized[1]:
        raise RuntimeError("benchmark configurations differ beyond storageRoot")
    result = {}
    for label, config_path, root in zip(("source", "copy"),
                                       (source_config, copy_config), roots):
        database = root / "forward-link.sqlite3"
        anchor = Path(str(root) + ".head-anchor")
        wal = root / "forward-link.sqlite3-wal"
        if wal.exists() and wal.stat().st_size:
            raise RuntimeError("benchmark Store has an uncheckpointed WAL")
        for path in (config_path, database, anchor):
            if path.is_symlink() or not path.is_file():
                raise RuntimeError("benchmark requires regular configuration/database/anchor files")
        result[label] = {"config": str(config_path), "config_sha256": file_digest(config_path).hex(),
                         "database": str(database), "database_sha256": file_digest(database).hex(),
                         "anchor": str(anchor), "anchor_sha256": file_digest(anchor).hex()}
    if (source_config.samefile(copy_config) or
            Path(result["source"]["database"]).samefile(result["copy"]["database"]) or
            Path(result["source"]["anchor"]).samefile(result["copy"]["anchor"])):
        raise RuntimeError("benchmark source and copy must not share files")
    for field in ("database_sha256", "anchor_sha256"):
        if result["source"][field] != result["copy"][field]:
            raise RuntimeError("benchmark copied Store differs from source")
    return result


def write_benchmark(args, report, before):
    """Emit the existing journey receipt from this run's full comparison only."""
    after = benchmark_snapshot(args.benchmark_source_config, args.config)
    if after != before:
        raise RuntimeError("benchmark source or copied Store/config/anchor changed")
    if not (report["passed"] and report["cold_comparison"] == "passed"
            and report["canonical_wrong_claim_checked"]):
        raise RuntimeError("benchmark requires cold equivalence and canonical wrong-claim refusal")
    receipt = {"schema": "mini-stop-inspection-continuation-v1", "passed": True,
               "scope": "Fresh same-Host cold/resident comparison on an unchanged copied Store; no lifecycle submission",
               "probe_report_sha256": file_digest(args.out / "report.json").hex(),
               "cold_sha256": file_digest(args.out / "cold.json").hex(),
               **{key: report[key] for key in ("host_sha256", "config_sha256", "plan_sha256", "committed_sha256")},
               "cold_seconds": report["measurements"]["cold"]["seconds"],
               "first_served_seconds": report["measurements"]["served-first"]["seconds"],
               "warm_repeat_seconds": report["measurements"]["served-repeat"]["seconds"],
               "controls": report["refusal_boundaries"], "canonical_wrong_claim_checked": True,
               "source_and_copied_store_and_anchor": "hashes unchanged", "store_files": after}
    with (args.out / "benchmark.json").open("x") as output:
        json.dump(receipt, output, indent=2)
        output.write("\n")


def require_refusal(label, reply, inspect=None):
    if label in ("malformed-pair", "public-denied"):
        # Transport checks pair framing and socket routing before Lean. Busy,
        # peer/config mismatch and all other transport errors fail here.
        if reply != ROUTE_REFUSAL:
            raise RuntimeError(label + " did not return the exact transport routing refusal")
        return "transport-routing"
    # Current Host distinguishes a definite no-record refusal (253) from an
    # undecided outcome (255). Ask that same pinned Host to decode the frame;
    # an arbitrary error or a valid outcome for another operation cannot pass.
    if reply[:1] != b"\xfd" or inspect is None:
        raise RuntimeError(label + " did not return a definite source refusal")
    outcome = inspect(reply[1:])
    expected_detail = {
        "trailing-claim": "noncanonical committed launch claim-v3",
        "mismatched-committed": "admitted STOP BEGIN differs from retained operator plan",
    }[label]
    if (outcome.get("type") != "refused" or outcome.get("effect") != "no-record"
            or outcome.get("phase") != b"op 155".hex()
            or outcome.get("detail") != expected_detail.encode().hex()):
        raise RuntimeError(label + " did not return the expected STOP source refusal")
    return "source"


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
    (args.out / "cold.pid").write_text(str(process.pid) + "\n")
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=args.deadline)
    except subprocess.TimeoutExpired:
        timed_out = True
        # This process group was created and recorded by this probe alone.
        os.killpg(process.pid, signal.SIGTERM)
        try:
            stdout, stderr = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
    (args.out / "cold.stdout").write_bytes(stdout)
    (args.out / "cold.stderr").write_bytes(stderr)
    if timed_out:
        raise RuntimeError("cold inspection exceeded its deadline")
    if process.returncode:
        raise RuntimeError(f"cold inspection exited {process.returncode}")
    raw = output.read_bytes()
    if not 0 < len(raw) <= MAX_JSON:
        raise RuntimeError("cold JSON exceeds native inspection bound")
    return raw


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("host", "config", "operator-socket", "public-socket", "plan", "committed", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--mismatched-committed", type=Path,
                        help="a different canonical claim; required on the post-append qualification pass")
    parser.add_argument("--resident-only", action="store_true",
                        help="check the resident and refusals without claiming cold equivalence")
    parser.add_argument("--benchmark-source-config", type=Path,
                        help="quiescent source config for this copied Store; emit benchmark.json after full comparison")
    parser.add_argument("--deadline", type=float, default=1200)
    args = parser.parse_args()
    if not 0 < args.deadline <= 1800:
        parser.error("deadline must be positive and at most 1800 seconds")
    if args.benchmark_source_config and (args.resident_only or not args.mismatched_committed):
        parser.error("benchmark requires cold comparison and --mismatched-committed")
    args.out.mkdir(mode=0o700, parents=False, exist_ok=False)
    before = (benchmark_snapshot(args.benchmark_source_config, args.config)
              if args.benchmark_source_config else None)
    config, plan, committed = (p.read_bytes() for p in (args.config, args.plan, args.committed))
    host_sha = file_digest(args.host)
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
              "scope": ("Read-only resident/refusal controls; no cold equivalence"
                        if args.resident_only else "Read-only cold/served comparison, no lifecycle operation"),
              "mode": "resident-only" if args.resident_only else "cold-and-resident",
              "host_sha256": host_sha.hex(), "config_sha256": digest(config),
              "plan_sha256": digest(plan), "committed_sha256": digest(committed),
              "canonical_wrong_claim_checked": False,
              "served_checks_passed": False, "cold_comparison": "pending",
              "refusal_boundaries": {},
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

    def inspect_refusal(label, raw):
        payload = struct.pack("<H", 7) + b"outcome" + raw
        reply = exchange(args.operator_socket, binding + b"\x08" + payload, args.deadline)
        (args.out / (label + "-inspected.bin")).write_bytes(reply)
        if reply[:1] != b"\x08" or not 0 < len(reply) - 1 <= MAX_JSON:
            raise RuntimeError("Host could not decode " + label + " refusal")
        return json.loads(reply[1:])

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
        for label, payload in (("trailing-claim", pair + b"\0"),
                               ("malformed-pair", b"\xff\xff\xff\xff")):
            reply = measured(label, lambda: served(payload))
            (args.out / (label + ".bin")).write_bytes(reply)
            report["refusal_boundaries"][label] = require_refusal(
                label, reply, lambda raw: inspect_refusal(label, raw))
        if mismatched is not None:
            wrong_pair = struct.pack("<I", len(plan)) + plan + mismatched
            reply = measured("mismatched-committed", lambda: served(wrong_pair))
            (args.out / "mismatched-committed.bin").write_bytes(reply)
            report["refusal_boundaries"]["mismatched-committed"] = require_refusal(
                "mismatched-committed", reply,
                lambda raw: inspect_refusal("mismatched-committed", raw))
            report["canonical_wrong_claim_checked"] = True
            report["mismatched_committed_sha256"] = digest(mismatched)
        # A valid config/image envelope is essential: malformed-envelope denial
        # alone would not establish that op155 is unavailable on the public route.
        reply = measured("public-denied", lambda: exchange(
            args.public_socket, binding + bytes([OP]) + pair, args.deadline))
        (args.out / "public-denied.bin").write_bytes(reply)
        report["refusal_boundaries"]["public-denied"] = require_refusal("public-denied", reply)
        reply = measured("served-after-refusals", lambda: served(pair))
        (args.out / "served-after-refusals.bin").write_bytes(reply)
        if reply != first:
            raise RuntimeError("valid inspection changed after refused requests")
        report["served_checks_passed"] = True
        if args.resident_only:
            report["cold_comparison"] = "not-performed"
        else:
            report["cold_comparison"] = "running"
            save_report()
            original = measured("cold", lambda: cold(args, args.out / "cold.json"))
            if first != bytes([OP]) + original:
                raise RuntimeError("resident inspection differs from cold inspection bytes")
            report["cold_comparison"] = "passed"
        if file_digest(args.host) != host_sha:
            raise RuntimeError("Host image changed during comparison")
        if args.config.read_bytes() != config:
            raise RuntimeError("Host config changed during comparison")
        if args.plan.read_bytes() != plan or args.committed.read_bytes() != committed:
            raise RuntimeError("retained STOP inputs changed during comparison")
        if mismatched is not None and args.mismatched_committed.read_bytes() != mismatched:
            raise RuntimeError("canonical wrong claim changed during comparison")
        report["passed"] = True
        if before is not None:
            save_report()
            write_benchmark(args, report, before)
    except Exception as error:
        report["passed"] = False
        report["error"] = str(error)
        if report["cold_comparison"] == "running":
            report["cold_comparison"] = "failed"
        raise
    finally:
        save_report()
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
