#!/usr/bin/env python3
"""consent-admit.py CONSENT SETTINGS [ANCHORFILE]: time one consent provider's history admission.
Frames: optional 228 (the retained anchor from a custody file, header stripped), then 226 with an
empty payload. Frame 226 admits the Store before it inspects its payload (and then refuses the
payload), so the time to its answer is the admission time. Prints JSON."""
import json, os, struct, subprocess, sys, time
consent, settings = sys.argv[1], sys.argv[2]
anchor = None
if len(sys.argv) > 3:
    raw = open(sys.argv[3], 'rb').read()
    tag = b"MINI-CONSENT-ANCHOR-CUSTODY/v1\n"
    assert raw.startswith(tag)
    anchor = raw[len(tag) + 32:]
t0 = time.monotonic()
p = subprocess.Popen([consent, settings, "stdio"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
def frame(op, payload):
    body = bytes([op]) + payload
    p.stdin.write(struct.pack('<I', len(body)) + body); p.stdin.flush()
    n = struct.unpack('<I', p.stdout.read(4))[0]
    reply = p.stdout.read(n)
    return reply[0], reply[1:]
out = {}
if anchor is not None:
    op, body = frame(228, anchor)
    out["offer"] = "accepted" if op == 228 else body.decode(errors="replace")
t1 = time.monotonic()
op, body = frame(226, b"")
t2 = time.monotonic()
op9, anc = frame(229, b"")
p.stdin.close(); p.wait()
out.update({"spawnToReady_s": round(t1 - t0, 3), "admission_s": round(t2 - t1, 3), "total_s": round(t2 - t0, 3),
            "frame226": op, "refusal": body.decode(errors="replace")[:120], "anchorHeight": None})
print(json.dumps(out))
