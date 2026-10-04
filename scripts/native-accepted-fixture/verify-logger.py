#!/usr/bin/env python3
"""A `serve` helper for the native signature verifier (Compiler/NativeCoprocess.lean
frames) that records every `verify` triple and the real verifier's exact answer, then
forwards. Used only by generate.sh to record a transcript.
env: REAL_VERIFIER (the pinned binary), VERIFY_LOG (JSON lines, appended)."""
import json, os, struct, subprocess, sys
REAL, LOG = os.environ["REAL_VERIFIER"], os.environ["VERIFY_LOG"]
def read(n):
    data = b""
    while len(data) < n:
        chunk = sys.stdin.buffer.read(n - len(data))
        if not chunk:
            sys.exit(0)
        data += chunk
    return data
if len(sys.argv) > 1 and sys.argv[1] != "serve":
    sys.exit(subprocess.run([REAL] + sys.argv[1:]).returncode)
while True:
    argc = struct.unpack(">I", read(4))[0]
    args = [read(struct.unpack(">I", read(4))[0]).decode() for _ in range(argc)]
    result = subprocess.run([REAL] + args, capture_output=True)
    if args and args[0] == "verify":
        key, frame, signature = (open(path, "rb").read().hex() for path in args[1:4])
        with open(LOG, "a") as log:
            log.write(json.dumps({"key": key, "frame": frame, "signature": signature,
                                  "code": result.returncode, "stdout": result.stdout.decode(),
                                  "stderr": result.stderr.decode()}) + "\n")
    out = sys.stdout.buffer
    out.write(struct.pack(">I", result.returncode))
    out.write(struct.pack(">Q", len(result.stdout)) + result.stdout)
    out.write(struct.pack(">Q", len(result.stderr)) + result.stderr)
    out.flush()
