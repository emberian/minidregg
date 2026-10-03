#!/usr/bin/env python3
"""Actual narrow-reader probe; caller supplies an executable and private configs."""
import argparse
import json
import os
from pathlib import Path
import struct
import subprocess
import tempfile

MAX_FRAME = 12_102_760

def exact(stream, count):
    result = bytearray()
    while len(result) < count:
        chunk = stream.read(count - len(result))
        if not chunk:
            raise RuntimeError("reader closed before complete response")
        result.extend(chunk)
    return bytes(result)

def exchange(child, operation, payload=b""):
    child.stdin.write(struct.pack("<I", len(payload) + 1) + bytes([operation]) + payload)
    child.stdin.flush()
    length, = struct.unpack("<I", exact(child.stdout, 4))
    if not 0 < length <= MAX_FRAME:
        raise RuntimeError("reader response exceeded protocol bound")
    body = exact(child.stdout, length)
    return body[0], body[1:]

def probe(reader, config_path, expected_semantics):
    config = json.loads(config_path.read_text())
    with tempfile.TemporaryFile() as errors:
        child = subprocess.Popen([reader, str(config_path), "stdio"],
                                 stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errors)
        try:
            operation, payload = exchange(child, 0)
            assert operation == 0
            description = json.loads(payload)
            assert description["domain"] == str(config["domain"])
            assert description["semantics"] == expected_semantics
            operation, payload = exchange(child, 6)
            assert operation == 6
            profile = json.loads(payload)
            assert profile["expectedSeed"] == str(config["expectedSeed"])
            assert profile["semantics"] == expected_semantics
            assert profile["domain"] == str(config["domain"])
            assert profile["nativeChecked"] is True
            # This executable must expose no direct submit or unknown-op escape.
            assert exchange(child, 2)[0] == 255
            assert exchange(child, 12)[0] == 255
            assert exchange(child, 6)[0] == 6
            child.stdin.close()
            assert child.wait(timeout=30) == 0
            return profile["runtimeParameters"]
        finally:
            if child.poll() is None:
                child.kill()
                child.wait()
def mismatch_refuses(reader, config_path):
    source = json.loads(config_path.read_text())
    with tempfile.TemporaryDirectory(prefix="source-reader-refusal-") as directory:
        for field in ("domain", "expectedSeed"):
            altered = dict(source)
            altered[field] += 1
            target = Path(directory) / (field + ".json")
            descriptor = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            with os.fdopen(descriptor, "w") as stream:
                json.dump(altered, stream)
            result = subprocess.run([reader, str(target), "stdio"], input=b"",
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
            assert result.returncode != 0 and result.stdout == b""
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("reader")
    parser.add_argument("status")
    args = parser.parse_args()
    status = json.loads(Path(args.status).read_text())
    profiles = [probe(args.reader, Path(path), status["sourceSemantics"])
                for path in status["hostSettings"]]
    assert len(profiles) == 4 and all(profile == profiles[0] for profile in profiles)
    mismatch_refuses(args.reader, Path(status["hostSettings"][0]))
    print("PASS actual four reader profiles; direct submit refused; mismatched source pins refused")
if __name__ == "__main__":
    main()
