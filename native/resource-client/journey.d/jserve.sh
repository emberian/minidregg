#!/usr/bin/env bash
# Journey hook jserve: one hostile client cannot stall or stop the shared
# service (lane SERVE-ROBUST).
#
# On this journey's live Store (after J4: the newcomer holds a grant on
# `shared`), each row runs an attack against the public socket while an
# honest client — the newcomer's signed read, `mini workspace --action read`,
# the path a friend takes — is timed, and asserts expected vs got:
#   (a) a client sends 3 bytes of a frame and sleeps 30 s: the honest read is
#       answered in < 2 s; the staller is refused by name at its 10 s deadline;
#   (b) a long Host request (a large op 7 body the Host parses and refuses):
#       an envelope the socket refuses itself is answered at once while the
#       Host is busy; the honest read is read, queued, and answered right
#       after the long request (both measured); 40 requests behind a long one
#       meet the queue bound (32) and are refused `busy: host queue full`;
#   (b3) an op 7 object of 1M distinct keys costs the Host linear time (the
#       duplicate-key scan was quadratic: > 330 s), and a repeated key is
#       still refused by name;
#   (c) 50 connections that send nothing: the honest read is answered;
#       filled to the connection bound (64), the next is refused
#       `busy: connection limit`, and is answered once the idle ones expire;
#   (d) the J-PAY-6 route-mismatch grain intent through op 7 (raw frame and
#       `mini author`): 255 with `route-mismatch` named, the same Host process
#       answers on, and a fresh connection is answered;
#   (e) host-malformed's whole malformed-request table (journey.d/j12x.sh)
#       replayed after all of the above: every row refused by name.
# Every row also requires the Host process to be the one the row started with
# (a Host restart masked by `mini serve` is a FAIL), except (e)'s last row,
# which kills the Host on purpose.
set -u
: "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${NEWCOMER_WS:?}" "${JOURNEY_WORLD:?}" "${JOURNEY_STEP_DIR:?}"
D=$JOURNEY_STEP_DIR/jserve
mkdir -p -m 700 "$D"
export D HERE_HOOKS=$(cd "$(dirname "$0")" && pwd)
python3 - <<'PY'
import json, os, socket, struct, subprocess, sys, threading, time

D = os.environ["D"]; MINI = os.environ["MINI"]; HOST = os.environ["HOST"]
CONFIG = os.environ["CONFIG"]; SOCKET = os.environ["SOCKET"]
NEWCOMER = os.environ["NEWCOMER_WS"]; WORLD = os.environ["JOURNEY_WORLD"]
TAG = b"DREGG/NATIVE-HOST/OUTCOME/v4"
rows = []; failed = []; latencies = []
config = open(CONFIG, "rb").read()

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

def envelope(request, version=1):
    return bytes([version]) + struct.pack("<I", len(config)) + config + request

def raw(request, body=None, timeout=600):
    s = socket.socket(socket.AF_UNIX); s.settimeout(timeout); s.connect(SOCKET)
    body = envelope(request) if body is None else body
    try:
        s.sendall(struct.pack("<I", len(body)) + body)
    except OSError:
        pass  # a refusal sent before the read is still waiting to be read
    try: return frame_of(s)
    finally: s.close()

def timed(fn):
    t0 = time.monotonic(); r = fn(); return r, time.monotonic() - t0

counter = [0]
def honest_read():
    counter[0] += 1
    out = os.path.join(D, f"read{counter[0]}.out"); err = os.path.join(D, f"read{counter[0]}.err")
    t0 = time.monotonic()
    p = subprocess.run([MINI, "workspace", "--action", "read", "--dir", NEWCOMER, "--name", "shared"],
                       stdout=open(out, "wb"), stderr=open(err, "wb"), timeout=900)
    wall = time.monotonic() - t0
    text = open(err, "rb").read().decode("utf-8", "replace").strip().splitlines()
    return p.returncode == 0, wall, (text[-1] if text else "")

def honest_reads(n=3):
    """n signed reads back to back: (all answered, median wall, walls, last detail)."""
    walls = []; detail = ""; good = True
    for _ in range(n):
        ok, wall, detail = honest_read()
        good = good and ok; walls.append(wall)
    return good, sorted(walls)[n // 2], walls, detail

def describe():
    r = raw(bytes([0]), timeout=30)
    return r is not None and r[0] == 0

def row(name, expected, got, ok):
    rows.append((name, "PASS" if ok else "FAIL", expected, got))
    if not ok: failed.append(name)
    print(f"{'PASS' if ok else 'FAIL'} {name}: {got}", file=sys.stderr)

def guarded(name, expected, act):
    before = host_pid()
    try:
        ok, got = act()
    except Exception as e:
        ok, got = False, f"{type(e).__name__}: {e}"
    after = host_pid(); live = False
    try: live = describe()
    except Exception as e: got += f"; describe after: {e}"
    same = before is not None and before == after
    row(name, expected, f"{got}; host pid {before}->{after}; describe {'answered' if live else 'FAILED'}",
        ok and same and live)

def socket_refusal(reply, needle):
    return reply is not None and reply[0] == 254 and needle.encode() in reply[1:]

def show(reply):
    if reply is None: return "no reply"
    body = reply[1:]
    if body.startswith(TAG): body = body[len(TAG):]
    return f"{reply[0]} " + body.decode("utf-8", "replace").replace("\n", " ")[:140]

# ---------------------------------------------------------------- baseline
ok0, base, walls0, d0 = honest_reads()
row("baseline: the newcomer's signed read, no attack (3 reads)", "answered",
    f"median {base:.3f} s of {['%.3f' % w for w in walls0]}" if ok0 else d0, ok0)
latencies.append(("baseline", base))

# ---------------------------------------------------------------- (a) trickle
def trickle():
    s = socket.socket(socket.AF_UNIX); s.settimeout(40); s.connect(SOCKET)
    s.sendall(b"\x09\x00\x00")  # 3 of a frame's 4 length bytes, then nothing
    t0 = time.monotonic()
    ok, wall, walls, detail = honest_reads()
    latencies.append(("(a) staller holds 3 bytes (slowest of 3)", max(walls)))
    refusal = frame_of(s); refused_at = time.monotonic() - t0
    s.close()
    named = refusal is not None and refusal[0] == 254 and b"frame read deadline" in refusal
    good = ok and max(walls) < 2.0 and named
    return good, (f"honest reads slowest {max(walls):.3f} s of {['%.3f' % w for w in walls]} ({'answered' if ok else detail}); staller refused "
                  f"{show(refusal)!r} {refused_at:.1f} s after it stalled")
guarded("(a) a client sends 3 bytes then sleeps 30 s",
        "3 honest reads during the stall, each < 2 s; staller refused `frame read deadline` at ~10 s", trickle)

# ---------------------------------------------------------------- (b) long Host request
# An op 7 body of 4 M array elements: the Host parses all of it, then refuses
# it by name (`intent` takes no field `pad`). It occupies the one Host.
long_body = bytes([7]) + struct.pack("<H", 6) + b"intent" + b'{"pad":[' + b"0," * 4_000_000 + b'0]}'
_, alone = timed(lambda: raw(long_body))
latencies.append(("(b) the long request alone", alone))

def long_request():
    out = {}
    def slow():
        out["reply"], out["wall"] = timed(lambda: raw(long_body))
    t = threading.Thread(target=slow); t.start()
    time.sleep(0.3)
    bad, bad_wall = timed(lambda: raw(b"", body=bytes([3]) + struct.pack("<I", len(config)) + config + b"\x00", timeout=30))
    ok, wall, detail = honest_read()
    t.join()
    latencies.append(("(b) honest read behind the long request", wall))
    slow_named = out["reply"] is not None and out["reply"][0] == 255 and b"op 7" in out["reply"]
    good = ok and slow_named and socket_refusal(bad, "invalid socket envelope") and bad_wall < 1.0 \
        and wall <= out["wall"] + base + 2.0
    return good, (f"long request {out['wall']:.3f} s (alone {alone:.3f} s) -> {show(out['reply'])!r}; "
                  f"socket refusal while the Host was busy {bad_wall:.3f} s; honest read {wall:.3f} s "
                  f"({'answered' if ok else detail}), queued behind the long one")
guarded("(b) a long Host request while an honest client reads",
        "socket refusal < 1 s while the Host is busy; honest read answered right after the long request",
        long_request)

def queue_bound():
    out = {}
    def slow():
        out["reply"] = raw(long_body)
    t = threading.Thread(target=slow); t.start()
    time.sleep(0.3)
    replies = [None] * 40
    def one(i):
        replies[i] = raw(bytes([0]), timeout=120)
    ts = [threading.Thread(target=one, args=(i,)) for i in range(40)]
    for x in ts: x.start(); time.sleep(0.005)
    for x in ts: x.join()
    t.join()
    busy = sum(1 for r in replies if socket_refusal(r, "busy: host queue full"))
    answered = sum(1 for r in replies if r is not None and r[0] == 0)
    good = busy >= 1 and answered >= 30 and busy + answered == 40
    return good, f"40 describes behind a long request: {answered} answered, {busy} refused `busy: host queue full`"
guarded("(b2) requests beyond the Host queue bound (32)",
        "each extra request refused `busy: host queue full` by name; the rest answered", queue_bound)

# An op 7 object of 1M distinct keys (~12 MB): the duplicate-key scan was
# quadratic in keys (a list), so this one public request held the Host for
# longer than mini serve's 600 s deadline. It must now cost linear time.
keys_body = bytes([7]) + struct.pack("<H", 6) + b"intent" + b'{"pad":{' + \
    b",".join(b'"k%d":0' % i for i in range(1_000_000)) + b"}}"
def many_keys():
    out = {}
    def slow():
        out["reply"], out["wall"] = timed(lambda: raw(keys_body))
    t = threading.Thread(target=slow); t.start()
    time.sleep(0.3)
    ok, wall, detail = honest_read()
    t.join()
    latencies.append(("(b3) honest read behind a 1M-key object", wall))
    named = out["reply"] is not None and out["reply"][0] == 255 and b"op 7" in out["reply"]
    return named and ok and out["wall"] < 60, \
        (f"{len(keys_body)} byte body answered in {out['wall']:.3f} s -> {show(out['reply'])!r}; "
         f"honest read {wall:.3f} s ({'answered' if ok else detail})")
guarded("(b3) an op 7 object of 1M distinct keys",
        "refused by name in linear time (< 60 s; the list scan took > 330 s offline); honest read answered after",
        many_keys)
def duplicate_key():
    reply = raw(bytes([7]) + struct.pack("<H", 6) + b"intent" + b'{"a":"1","a":"2"}', timeout=60)
    return reply is not None and reply[0] == 255 and b"duplicate JSON object field: a" in reply, show(reply)
guarded("(b4) an op 7 object naming one key twice",
        "255 refused malformed, `duplicate JSON object field: a`", duplicate_key)

# ---------------------------------------------------------------- (c) silent connections
def silent(n):
    socks = []
    for _ in range(n):
        s = socket.socket(socket.AF_UNIX); s.settimeout(40); s.connect(SOCKET); socks.append(s)
    return socks

def fifty_silent():
    socks = silent(50)
    time.sleep(0.3)
    ok, wall, walls, detail = honest_reads()
    latencies.append(("(c) 50 silent connections (slowest of 3)", max(walls)))
    refused = sum(1 for s in socks if (lambda r: r is not None and b"frame read deadline" in r)(frame_of(s)))
    for s in socks: s.close()
    return ok and max(walls) < 2.0 and refused == 50, \
        f"honest reads slowest {max(walls):.3f} s of {['%.3f' % w for w in walls]} ({'answered' if ok else detail}); {refused}/50 silent refused `frame read deadline`"
guarded("(c) 50 connections that send nothing",
        "3 honest reads while they are held, each < 2 s; each silent one refused by name at its deadline", fifty_silent)

def connection_bound():
    socks = silent(64)
    time.sleep(0.5)
    over = raw(bytes([0]), timeout=30)
    for s in socks: frame_of(s)
    for s in socks: s.close()
    time.sleep(0.3)
    after, wall = timed(describe)
    return socket_refusal(over, "busy: connection limit") and after, \
        f"65th connection -> {show(over)!r}; after the 64 expired, describe answered in {wall:.3f} s"
guarded("(c2) connections beyond the bound (64)",
        "the next is refused `busy: connection limit`; answered once the idle ones expire", connection_bound)

# ---------------------------------------------------------------- (d) authoring refusal through op 7
grain = {"task": "7111", "subject": "7", "capability": "101", "schemaVersion": "1",
         "expectedTargetRoot": "1",
         "context": {"operationId": "61001", "payload": "settle the pool hold as a user call"},
         "before": {"generation": "1", "status": "1", "remaining": "100", "reserved": "7", "route": "2"},
         "operation": {"type": "settle", "charge": "5", "route": "user"},
         "publications": [], "observeCapability": "101"}
intent = {"grain": grain, "grants": [{"kind": "object", "target": "7111", "capability": "101"}],
          "intentNonce": "61001"}
source = json.dumps(intent).encode()
open(os.path.join(D, "route-mismatch-intent.json"), "wb").write(source)

def route_mismatch_raw():
    reply = raw(bytes([7]) + struct.pack("<H", 12) + b"grain-intent" + source, timeout=60)
    named = reply is not None and reply[0] == 255 and b"op 7" in reply and b"route-mismatch" in reply
    fresh = describe()
    return named and fresh, f"{show(reply)!r}; fresh connection answered: {fresh}"
guarded("(d) J-PAY-6 route-mismatch grain intent, raw op 7 frame",
        "255 refused, phase op 7, `route-mismatch` named; the next connection answered", route_mismatch_raw)

def route_mismatch_client():
    out = os.path.join(D, "route-mismatch.bin")
    p = subprocess.run([MINI, "author", "--socket", SOCKET, "--host", HOST, "--config", CONFIG,
                        "--kind", "grain-intent", "--input", os.path.join(D, "route-mismatch-intent.json"),
                        "--output", out], capture_output=True, timeout=120)
    err = p.stderr.decode("utf-8", "replace").strip().splitlines()
    line = next((l for l in err if "route-mismatch" in l), err[-1] if err else "")
    ok, wall, detail = honest_read()
    good = p.returncode != 0 and "route-mismatch" in line and "phase op 7" in line and ok
    return good, f"exit {p.returncode}: {line[:200]}; next signed read {'answered' if ok else detail} in {wall:.3f} s"
guarded("(d) J-PAY-6 route-mismatch grain intent, `mini author --socket`",
        "client exits refused, `route-mismatch` named, phase op 7; the next signed read answered",
        route_mismatch_client)

# ---------------------------------------------------------------- (e) the malformed table, after all of it
def replay():
    step = os.path.join(D, "j12x-replay"); os.makedirs(step, exist_ok=True)
    env = dict(os.environ, JOURNEY_STEP_DIR=step)
    p = subprocess.run([os.path.join(os.environ["HERE_HOOKS"], "j12x.sh")], env=env,
                       capture_output=True, timeout=1800)
    tail = p.stderr.decode("utf-8", "replace").strip().splitlines()
    return p.returncode == 0, (tail[-1] if tail else f"exit {p.returncode}")
try:
    ok, got = replay()
except Exception as e:
    ok, got = False, f"{type(e).__name__}: {e}"
row("(e) host-malformed's malformed-request table replayed after (a)-(d)",
    "every row refused by name; the killed Host restarted under the same socket", got, ok)
ok, wall, detail = honest_read()
latencies.append(("after everything", wall))
row("after everything: the newcomer's signed read", "answered", f"answered in {wall:.3f} s" if ok else detail, ok)

with open(os.path.join(D, "serve-rows.tsv"), "w") as f:
    f.write("row\tstatus\texpected\tgot\n")
    for r in rows: f.write("\t".join(r) + "\n")
with open(os.path.join(D, "latencies.tsv"), "w") as f:
    for name, s in latencies: f.write(f"{name}\t{s:.3f}\n")
print(os.path.join(D, "serve-rows.tsv"))
n = len(rows); p = n - len(failed)
if failed:
    print(f"{p}/{n} serve rows; FAIL: {', '.join(failed)}", file=sys.stderr); sys.exit(1)
print(f"{p}/{n} serve rows: no hostile client stalled the honest read or stopped the service", file=sys.stderr)
PY
