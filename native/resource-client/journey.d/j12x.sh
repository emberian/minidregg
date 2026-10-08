#!/usr/bin/env bash
# Journey hook j12x: malformed requests do not stop the shared service.
#
# On this journey's live Store (after J3, before J4), every row sends one
# request the grammar refuses — through the client (`mini author`, the path a
# friend's draft takes: the client's own pure native Host, which refuses with exit 2
# and the encoded outcome) or as raw socket frames — and asserts:
#   * the answer is the named refusal: a Host frame `refused malformed`, phase
#     `op N`, with the decoder's position; or the socket's own 254 refusal for an
#     envelope the Host never sees;
#   * the Host process that answered is the SAME process that started the row
#     (a Host exit masked by `mini serve` restarting it is a FAIL here);
#   * a describe (op 0) is answered afterwards.
# The last row kills the Host by PID and asserts `mini serve` keeps the socket
# and the next request reaches a fresh Host. J4 then runs unchanged: its
# `accept` demands acceptedCount = previous + 1, so a malformed request that
# left a record fails J4.
set -u
: "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}" "${JOURNEY_WORLD:?}" "${JOURNEY_STEP_DIR:?}"
D=$JOURNEY_STEP_DIR/j12x
mkdir -p -m 700 "$D"
export D
python3 - <<'PY'
import json, os, re, signal, socket, struct, subprocess, sys, time

D = os.environ["D"]; MINI = os.environ["MINI"]; HOST = os.environ["HOST"]
CONFIG = os.environ["CONFIG"]; SOCKET = os.environ["SOCKET"]
SPONSOR = os.environ["SPONSOR_WS"]; WORLD = os.environ["JOURNEY_WORLD"]
TAG = b"DREGG/NATIVE-HOST/OUTCOME/v5"
rows = []; failed = []

def server_pid():
    return open(os.path.join(WORLD, "public", "server.pid")).read().strip()

def host_pid():
    out = subprocess.run(["pgrep", "-P", server_pid()], capture_output=True, text=True).stdout.split()
    return out[0] if len(out) == 1 else None

def frame_of(sock):
    def exact(n):
        b = b""
        while len(b) < n:
            c = sock.recv(n - len(b))
            if not c: return None
            b += c
        return b
    head = exact(4)
    if head is None: return None
    return exact(struct.unpack("<I", head)[0])

config = open(CONFIG, "rb").read()
def raw(request, version=1, body=None, timeout=120):
    s = socket.socket(socket.AF_UNIX); s.settimeout(timeout); s.connect(SOCKET)
    if body is None:
        body = bytes([version]) + struct.pack("<I", len(config)) + config + request
    s.sendall(struct.pack("<I", len(body)) + body)
    try: return frame_of(s)
    finally: s.close()

def alive():
    reply = raw(bytes([0]))
    return reply is not None and reply[0] == 0

def row(name, ok, detail):
    rows.append((name, "PASS" if ok else "FAIL", detail))
    if not ok: failed.append(name)

def check(name, act):
    before = host_pid()
    try:
        ok, detail = act()
    except Exception as e:  # a transport failure is the defect under test
        ok, detail = False, f"{type(e).__name__}: {e}"
    after = host_pid(); live = False
    try: live = alive()
    except Exception as e: detail += f"; describe after: {e}"
    same = before is not None and before == after
    row(name, ok and same and live,
        f"{detail}; host pid {before}->{after}; describe {'answered' if live else 'FAILED'}")

def host_refused(reply, op, needle, answer=255):
    if reply is None: return False, "no reply (connection closed)"
    if reply[0] != answer: return False, f"reply op {reply[0]}"
    body = reply[1:]
    ok = body.startswith(TAG) and f"op {op}".encode() in body and needle.encode() in body
    return ok, "255 " + body[len(TAG):].decode("utf-8", "replace").replace("\n", " ")[:160]

def socket_refused(reply, needle):
    if reply is None: return False, "no reply"
    ok = reply[0] == 254 and needle.encode() in reply[1:]
    return ok, f"{reply[0]} {reply[1:].decode('utf-8', 'replace')[:120]}"

# ------------------------------------------------------------- client rows
base_path = os.path.join(SPONSOR, "proposals", "grant-newcomer", "intent.json")
base = json.load(open(base_path))
def decimal_paths(value, path=()):
    if isinstance(value, dict):
        for k, v in value.items(): yield from decimal_paths(v, path + (k,))
    elif isinstance(value, list):
        for i, v in enumerate(value): yield from decimal_paths(v, path + (i,))
    elif isinstance(value, str) and re.fullmatch(r"[0-9]+", value):
        yield path
deepest = max(decimal_paths(base["purpose"]), key=len)
def set_at(doc, path, value):
    doc = json.loads(json.dumps(doc)); cur = doc["purpose"]
    for k in path[:-1]: cur = cur[k]
    cur[path[-1]] = value; return doc
where = "$.purpose" + "".join(f"[{k}]" if isinstance(k, int) else f".{k}" for k in deepest)

def author(name, data, needle):
    src = os.path.join(D, f"{name}.json"); out = os.path.join(D, f"{name}.out")
    open(src, "wb").write(data)
    p = subprocess.run([MINI, "author", "--socket", SOCKET, "--host", HOST, "--config", CONFIG,
                        "--kind", "intent", "--input", src, "--output", out],
                       capture_output=True, timeout=600)
    err = p.stderr.decode("utf-8", "replace").strip().splitlines()
    line = next((l for l in err if "host refused author" in l), err[-1] if err else "")
    ok = p.returncode != 0 and "refused: malformed:" in line and "phase op 7" in line and needle in line
    return ok, f"exit {p.returncode}: {line[:200]}"

dumps = lambda d: json.dumps(d).encode()
cases = [
    ("number-for-string", dumps(set_at(base, deepest, 1)), "string expected"),
    ("missing-field", dumps({k: v for k, v in base.items() if k != "nonce"}), "$"),
    ("extra-field", dumps(dict(base, extra="1")), "$"),
    ("negative-index", dumps(set_at(base, deepest, "-1")), "decimal"),
    ("nan", dumps(base).replace(b'"subject": "7"', b'"subject": NaN', 1), ""),
    ("truncated-json", dumps(base)[: len(dumps(base)) // 2], ""),
    ("non-utf8", dumps(base)[:20] + b"\xff\xfe" + dumps(base)[20:], "not UTF-8"),
    ("deep-nesting-100k", b"[" * 100000 + b"]" * 100000, "nesting"),
    ("ten-mb-body", dumps(dict(base, pad="a" * (10 * 1024 * 1024))), "$"),
]
for name, data, needle in cases:
    check(f"client {name} ({where})" if name in ("number-for-string", "negative-index") else f"client {name}",
          lambda data=data, name=name, needle=needle: author(name, data, needle))

# ------------------------------------------------------------- raw rows
def kind_frame(kind, body):
    return struct.pack("<H", len(kind)) + kind + body
check("raw op 7 kind frame shorter than its width",
      lambda: host_refused(raw(bytes([7, 9])), 7, "short native host kind frame"))
check("raw op 7 kind width past the payload",
      lambda: host_refused(raw(bytes([7]) + struct.pack("<H", 500) + b"intent"), 7, "invalid native host kind length"))
check("raw op 10 pair width past the payload",
      lambda: host_refused(raw(bytes([10]) + struct.pack("<I", 1 << 20) + b"xx"), 10, "invalid native host pair length"))
check("raw op 11 noncanonical plan",
      lambda: host_refused(raw(bytes([11]) + struct.pack("<I", 3) + b"abc" + b"\x00"), 11, "noncanonical signing plan"))
# Ops 0 and 6 take no body: the service refuses one (254, never forwarded; 8ac769d7) before the
# Host would answer 255 `describe does not accept a payload`. Both are definite and named.
check("raw op 0 describe with a payload (service refusal, never forwarded)",
      lambda: socket_refused(raw(bytes([0, 1])), "operation takes no request body"))
check("raw op 6 profile with a payload (service refusal, never forwarded)",
      lambda: socket_refused(raw(bytes([6, 1])), "operation takes no request body"))
def blind_submission():
    reply = raw(bytes([2]) + b"garbage")
    if reply is None: return False, "no reply (connection closed)"
    body = reply[1:]
    ok = reply[0] == 2 and body.startswith(TAG) and b"admission" in body and b"request refused" in body
    return ok, f"{reply[0]} " + body[len(TAG):].decode("utf-8", "replace")[:120]
# A submission's refusal stays undisclosed (MR): phase admission, "request refused".
check("raw op 2 submit of garbage call bytes (blind submission refusal)", blind_submission)
check("raw envelope version 3 (socket refusal; Host never sees it)",
      lambda: socket_refused(raw(b"", body=bytes([3]) + struct.pack("<I", len(config)) + config + b"\x00"), "invalid socket envelope"))
check("raw operation 200 on the public socket (socket refusal)",
      lambda: socket_refused(raw(bytes([200])), "operation unavailable"))
def truncated():
    s = socket.socket(socket.AF_UNIX); s.connect(SOCKET)
    s.sendall(struct.pack("<I", 1000) + b"\x01" * 10); s.close()
    return True, "length 1000, 10 bytes, closed"
check("raw truncated socket frame", truncated)

# ------------------------------------------------------------- supervisor row
def kill_host():
    before = host_pid(); serve = server_pid()
    os.kill(int(before), signal.SIGKILL)
    for _ in range(100):
        if subprocess.run(["kill", "-0", before], capture_output=True).returncode != 0: break
        time.sleep(0.1)
    live = alive(); after = host_pid()
    ok = live and after is not None and after != before and server_pid() == serve and os.path.exists(SOCKET)
    return ok, f"killed host {before}; serve {serve} kept the socket; describe answered by host {after}"
try:
    ok, detail = kill_host()
except Exception as e:
    ok, detail = False, f"{type(e).__name__}: {e}"
row("host killed by PID: mini serve restarts it and keeps the socket", ok, detail)

with open(os.path.join(D, "malformed-rows.tsv"), "w") as f:
    for r in rows: f.write("\t".join(r) + "\n")
print(os.path.join(D, "malformed-rows.tsv"))
n = len(rows); p = n - len(failed)
if failed:
    print(f"{p}/{n} malformed rows as expected; FAIL: {', '.join(failed)}", file=sys.stderr); sys.exit(1)
print(f"{p}/{n} malformed rows as expected: each refused by name, same Host process, describe answered after; a killed Host is restarted under the same socket", file=sys.stderr)
PY
