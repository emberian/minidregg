#!/usr/bin/env python3
"""Read-only four-process original-call recovery through the actual native reader.

No submit opcode, engine input, source append or authored replacement command is
issued. The reader's canonical codec interprets each returned Outcome.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import struct
import subprocess
import tempfile

spec = importlib.util.spec_from_file_location(
    "source_reader_probe", Path(__file__).with_name("probe-source-agreement-reader.py"))
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)


def lookup(reader, config, original):
    with tempfile.TemporaryFile() as errors:
        child = subprocess.Popen([reader, str(config), "stdio"], stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=errors, start_new_session=True)
        try:
            op, native = probe.exchange(child, 3, original)
            if op != 3:
                raise RuntimeError("native original-call lookup refused")
            kind = b"outcome"
            op, rendered = probe.exchange(child, 8, struct.pack("<H", len(kind)) + kind + native)
            if op != 8:
                raise RuntimeError("native outcome codec refused lookup response")
            value = json.loads(rendered)
            child.stdin.close()
            if child.wait(timeout=30) != 0:
                raise RuntimeError("native reader failed after lookup")
            return native, value
        finally:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("reader")
    parser.add_argument("status")
    parser.add_argument("original_call")
    parser.add_argument("--expect", choices=("confirmed", "absent"), default="confirmed")
    parser.add_argument("--accepted-count")
    args = parser.parse_args()
    status = json.loads(Path(args.status).read_text())
    paths = status["hostSettings"]
    if len(paths) != 4 or len(set(paths)) != 4:
        raise RuntimeError("requires four distinct configured source readers")
    original = Path(args.original_call).read_bytes()
    results = [lookup(args.reader, Path(path), original) for path in paths]
    if not all(native == results[0][0] for native, _ in results):
        raise RuntimeError("four original-call native outcomes differ")
    for _, value in results:
        if value["type"] != args.expect:
            raise RuntimeError("unexpected original-call outcome: " + value["type"])
        if args.accepted_count is not None and value.get("acceptedCount") != args.accepted_count:
            raise RuntimeError("original receipt has unexpected accepted count")
    print(json.dumps({"status": "PASS", "lookupProcesses": 4,
                      "originalCallSha256": hashlib.sha256(original).hexdigest(),
                      "nativeOutcomeSha256": hashlib.sha256(results[0][0]).hexdigest(),
                      "outcome": results[0][1], "mutationsIssued": 0}, sort_keys=True))


if __name__ == "__main__":
    main()
