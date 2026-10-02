#!/usr/bin/env bash
# J-NOCK-5 (NOCK.md §2.7, N11): a NockApp kernel door, refereed by re-execution.
#
# Journey hook contract (journey.sh header): HOST, MINI, STORE, VERIFIER and
# JOURNEY_STEP_DIR exported; it bootstraps its OWN fresh Store and service under
# JOURNEY_STEP_DIR (newparticipant-acceptance.sh, the J0 fixture), never touches
# the journey's service, and stops what it starts. Exit 0 = PASS. The last stdout
# line is the deciding artifact (rows.tsv); the verdict is the last stderr line.
#
# Also needs: NOCK_DOOR_JAM (the counter kernel: jnock5-counter.hoon compiled by
# the pinned hoonc pipeline, minimal bytes) and NOCK_DOOR_FUEL (its ABI fuel).
# jnock5-counter-keep.hoon is the same kernel under hoon/common/wrapper's +keep;
# its +soft molds run +mink, which unjetted does not finish (see N11's report).
# Optional: NOCK_RUN (nockvm runner) for the runner cross-check row.
#
# Rows: the counter kernel is born as a door program (poke 23 / peek 22, state in
# field 2, event number in field 3, the effect 'count' a write of field 4); an
# instance cell gets the law `ran counter`. Unloaded, its state is the booted
# trap's and peek answers 0. poke 1 -> 1; poke 1 -> 2 (each: op 135 dry run, then
# the signed claim). Refusals by NAME: a claim over the old state (sampleStale), a
# wrong stateOut (outputMismatch), an %exit effect (effectNotWrite). peek -> 2 and
# nothing is written. Cold reopen + audit re-admits every poke; the reopened
# service reads state 2.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR NOCK_DOOR_JAM NOCK_DOOR_FUEL; do
  if [ -z "${!name:-}" ]; then echo "jnock5: $name is required" >&2; exit 2; fi
done
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
. "$HERE/journey.d/lib/shortdir.sh"
journey_shortdir jnock5   # its Store's socket lives in a short directory, kept as $JOURNEY_STEP_DIR/rt
DIR=$JOURNEY_D
mkdir -p "$DIR"
W="$DIR/world"
# A hoonc kernel carries the whole stdlib (~574 KB): its birth intent costs that
# much against the owner budget (J-NOCK-2b).
NEWPARTICIPANT_OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-4000000} \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W" \
  >"$DIR/bootstrap.out" 2>"$DIR/bootstrap.err" || { echo "jnock5: bootstrap failed: $(tail -1 "$DIR/bootstrap.err")" >&2; exit 1; }
stop() { if [ -s "$W/public/server.pid" ]; then kill "$(cat "$W/public/server.pid")" 2>/dev/null || true; fi; }
trap 'stop; journey_shortdir_return' EXIT
set +e
python3 - "$DIR" "$W" <<'PY'
import hashlib, json, os, re, socket, struct, subprocess, sys, time
DIR, W = sys.argv[1], sys.argv[2]
MINI, HOST = os.environ["MINI"], os.environ["HOST"]
JAM, FUEL = os.environ["NOCK_DOOR_JAM"], os.environ["NOCK_DOOR_FUEL"]
NOCK_RUN = os.environ.get("NOCK_RUN", "")
CONFIG = os.path.join(W, "deployment", "pinned-config.json")
SOCK = os.path.join(W, "public", "mini.sock")
WS = os.path.join(W, "sponsor")
ROWS = []
def path(n): return os.path.join(DIR, n)
def row(name, ok, detail):
    ROWS.append((name, "PASS" if ok else "FAIL", detail))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{detail}", file=sys.stderr)

cfg = open(CONFIG, "rb").read()
def frame(b): return struct.pack("<I", len(b)) + b
def op(code, payload):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.connect(SOCK)
    s.sendall(frame(bytes([1]) + struct.pack("<I", len(cfg)) + cfg + bytes([code]) + payload))
    def exact(n):
        out = b""
        while len(out) < n:
            chunk = s.recv(n - len(out))
            if not chunk: raise RuntimeError("short reply")
            out += chunk
        return out
    n = struct.unpack("<I", exact(4))[0]; body = exact(n); s.close()
    if body[0] != code: raise RuntimeError(f"op {code} answered {body[0]}: {body[1:200]!r}")
    return json.loads(body[1:].decode())
def pair(a, b): return struct.pack("<I", len(a)) + a + b
def mini(*args):
    return subprocess.run([MINI, "workspace", *args], capture_output=True, text=True)
def last_line(r, attempt_dir=None):
    last = (r.stderr.strip().splitlines() or [""])[-1]
    if attempt_dir:
        retained = os.path.join(attempt_dir, "reply.frame")
        if "retained encoded Host outcome" in last and os.path.exists(retained):
            last = open(retained, "rb").read().decode("latin1").replace("\xff", " | ")
    m = re.search(r"([0-9a-f]{40,})", last)
    if m:
        try: last = bytes.fromhex(m.group(1)).decode("latin1").replace("\xff", " | ")
        except ValueError: pass
    return last

# Nock atoms as minimal jams (tag 0, then mat), for the wire, causes and path.
def jam_atom(n):
    bits = [0]
    if n == 0: bits += [1]
    else:
        b = n.bit_length(); c = b.bit_length()
        bits += [0] * c + [1] + [(b >> i) & 1 for i in range(c - 1)] + [(n >> i) & 1 for i in range(b)]
    v = sum(bit << i for i, bit in enumerate(bits))
    return v.to_bytes((v.bit_length() + 7) // 8, "little").hex()
def cord(s): return int.from_bytes(s.encode(), "little")
NIL = jam_atom(0)

STATE, EVENT, COUNT = 2, 3, 4
open(path("permit-all.json"), "w").write('{"type":"all","predicates":[]}\n')
kernel = open(JAM, "rb").read()
ABI = {"evaluator": "nock", "version": "5", "context": "live", "arm": "23", "fuel": FUEL, "sample": [], "libraries": [],
       "outputs": [{"key": "count", "target": "0", "field": str(COUNT), "type": "nat"}],
       "door": {"peek": "22", "state": str(STATE), "event": str(EVENT)}}

# 1. the kernel is born as a door program
t0 = time.time()
v = op(131, pair(kernel, json.dumps(ABI).encode()))
json.dump(v, open(path("counter.check.json"), "w"))
r = mini("--action", "create", "--dir", WS, "--name", "counter", "--storage", "nock",
    "--predicate", path("permit-all.json"), "--program", path("counter.check.json"))
open(path("counter.birth.err"), "w").write(r.stderr)
PID = v.get("programId")
row("the hoonc counter kernel is born as a door program (arm 23, peek 22, state field 2, event field 3)",
    r.returncode == 0 and v.get("verdict") == "admissible" and v.get("abi", ABI) is not None,
    f"rc={r.returncode} verdict={v.get('verdict')} programId={PID} jamBytes={v.get('jamBytes')} "
    f"({time.time()-t0:.1f}s) {last_line(r)[:120] if r.returncode else ''}")

# 2. the instance cell, under the law `ran counter`
counter = [0]
def submit(label, targets, run=None):
    counter[0] += 1
    pid = re.sub(r"[^A-Za-z0-9-]+", "-", label).strip("-") + f"-{counter[0]}"
    req = {"type": "minidregg-workspace-proposal-v1", "action": "invoke", "targets": targets}
    if run is not None: req["run"] = run
    json.dump(req, open(path(f"{pid}.request.json"), "w"))
    r = mini("--action", "propose", "--dir", WS, "--request", path(f"{pid}.request.json"),
        "--proposal-id", pid)
    if r.returncode != 0:
        return r.returncode, "propose: " + last_line(r)
    attempt = os.path.join(WS, "attempts", pid)
    r = mini("--action", "submit", "--dir", WS, "--intent", os.path.join(WS, "proposals", pid, "intent.json"),
        "--attempt", attempt)
    open(path(f"{pid}.submit.err"), "w").write(r.stderr)
    last = last_line(r, attempt)
    outcome = os.path.join(attempt, "outcome.json")
    if "exact outcome evidence was retained" in last and os.path.exists(outcome):
        o = json.load(open(outcome))
        last = "outcome " + o.get("type", "?") + " | " + bytes.fromhex(o.get("phase", "")).decode("latin1") \
            + " | " + bytes.fromhex(o.get("detail", "")).decode("latin1")
    return r.returncode, last
def scalar(actions): return [{"name": "ctr", "payload": {"type": "scalar", "actions": actions}}]
def create(f, v): return {"type": "create", "key": {"type": "object", "field": str(f)}, "value": str(v)}
def write(f, v, e): return {"type": "write", "key": {"type": "object", "field": str(f)}, "value": str(v), "expected": str(e)}
def read_fields(tag):
    r = mini("--action", "read", "--dir", WS, "--name", "ctr")
    open(path(f"ctr.read.{tag}.json"), "w").write(r.stdout)
    vals = {}
    try:
        for e in json.loads(r.stdout)["cell"]["entries"]:
            vals[e["key"]["field"]] = e["value"]
    except Exception: pass
    return vals, r.stdout

r = mini("--action", "create", "--dir", WS, "--name", "ctr", "--storage", "declared",
    "--predicate", path("permit-all.json"), "--fields", "%d-%d" % (STATE, COUNT))
CTR = json.load(open(os.path.join(WS, "refs", "ctr.json")))["target"] if r.returncode == 0 else None
LAW = {"type": "any", "predicates": [
    {"type": "not", "predicate": {"type": "eq", "slot": "request/verb", "value": "2"}},
    {"type": "ran", "program": PID}]}
json.dump({"type": "minidregg-workspace-proposal-v1", "action": "install-policy", "name": "ctr",
           "predicate": LAW}, open(path("law.request.json"), "w"))
r2 = mini("--action", "propose", "--dir", WS, "--request", path("law.request.json"), "--proposal-id", "law")
r3 = mini("--action", "submit", "--dir", WS, "--intent", os.path.join(WS, "proposals", "law", "intent.json"),
    "--attempt", os.path.join(WS, "attempts", "law")) if r2.returncode == 0 else r2
row("the instance cell `ctr` is born and given the law `ran counter`",
    CTR is not None and r3.returncode == 0, f"ctr={CTR} law rc={r3.returncode} {last_line(r3)[:160]}")

def view(fields):
    st = fields.get(str(STATE))
    return {"programId": PID, "state": st, "event": fields.get(str(EVENT), "0")}
def peek(fields, tag):
    t = time.time(); p = op(136, json.dumps(dict(view(fields), path=NIL)).encode())
    json.dump(p, open(path(f"peek.{tag}.json"), "w")); return p, time.time() - t
def dry(fields, cause, tag):
    t = time.time(); d = op(135, json.dumps(dict(view(fields), wire=NIL, cause=cause)).encode())
    json.dump(d, open(path(f"poke.{tag}.json"), "w")); return d, time.time() - t
def writes_for(fields, d, with_count=True):
    out = []
    for t_, f, val in d.get("writes") or []:
        old = fields.get(f)
        out.append(create(f, val) if old is None else write(f, val, old))
    return out

# 3. unloaded: the booted trap's state; peek answers 0
f0, _ = read_fields("0")
s0 = op(137, json.dumps(view(f0)).encode()); json.dump(s0, open(path("state.0.json"), "w"))
p0, dt = peek(f0, "0")
row("unloaded: the state is the booted trap's axis 6 (op 137) and peek answers 0 (op 136)",
    s0.get("verdict") == "ok" and p0.get("verdict") == "ok" and p0.get("value") == "0",
    f"state jam={s0.get('state')} steps={s0.get('steps')}; peek value={p0.get('value')} steps={p0.get('steps')} ({dt:.1f}s)")

# 4. poke 1 -> 1
d1, dt = dry(f0, jam_atom(1), "1")
row("op 135 on the unloaded instance: poke 1 runs, its writes are state, event 1, count 1",
    d1.get("verdict") == "ok" and d1.get("writes") is not None
    and [w[1:] for w in d1["writes"]][1:] == [[str(EVENT), "1"], [str(COUNT), "1"]],
    f"lean steps={d1.get('steps')} ({dt:.1f}s) writes={d1.get('writes')} stateOut={d1.get('stateOut')}")
open(path("sf.1.jam"), "wb").write(bytes.fromhex(d1.get("subjectFormula", "")))
open(path("product.1.hex"), "w").write(d1.get("product", ""))
if NOCK_RUN:
    nr = subprocess.run([NOCK_RUN, "--subject-formula", path("sf.1.jam"), "--fuel", "1000000000000",
        "--jets", "off"], capture_output=True, text=True)
    open(path("nock-run.1.json"), "w").write(nr.stdout + nr.stderr)
    try: runner = json.loads(nr.stdout)
    except Exception: runner = {}
    product = bytes.fromhex(d1.get("product", ""))
    row("the runner (nockvm, jets off) on the kernel's subject/formula gets the kernel's product",
        runner.get("status") == "ok" and runner.get("out_sha256") == hashlib.sha256(product).hexdigest(),
        f"nockvm items={runner.get('steps')} lean steps={d1.get('steps')}")
rc, last = submit("poke-1", scalar(writes_for(f0, d1)), d1.get("claim"))
f1, _ = read_fields("1")
row("poke 1 is admitted: state field holds the kernel's state', event 1, count 1",
    rc == 0 and f1.get(str(STATE)) == d1.get("stateOut") and f1.get(str(EVENT)) == "1" and f1.get(str(COUNT)) == "1",
    f"rc={rc} fields={f1} {last[:120] if rc else ''}")

# 5. poke 1 -> 2
d2, dt = dry(f1, jam_atom(1), "2")
rc, last = submit("poke-2", scalar(writes_for(f1, d2)), d2.get("claim"))
f2, raw2 = read_fields("2")
row("poke 1 again is admitted: event 2, count 2",
    d2.get("verdict") == "ok" and rc == 0 and f2.get(str(STATE)) == d2.get("stateOut")
    and f2.get(str(EVENT)) == "2" and f2.get(str(COUNT)) == "2",
    f"rc={rc} lean steps={d2.get('steps')} ({dt:.1f}s) fields={f2} {last[:120] if rc else ''}")

# 6-8. refusals, each by name, against state 2
def refused(label, targets, run, name):
    rc, last = submit(label, targets, run)
    row(f"{label}: refused {name}", rc != 0 and name in last, f"rc={rc} last={last[:220]}")
refused("a claim over the unloaded state (poke 1's claim, replayed)",
    scalar([write(STATE, d1["stateOut"], f2[str(STATE)]), write(EVENT, 1, 2), write(COUNT, 1, 2)]),
    d1.get("claim"), "sampleStale")
d3, _ = dry(f2, jam_atom(1), "3")
wrong = dict(d3.get("claim") or {}, output=d2.get("output"))
refused("a claim whose stateOut is the old state",
    scalar([write(STATE, d2["stateOut"], f2[str(STATE)]), write(EVENT, 3, 2), write(COUNT, 2, 2)]),
    wrong, "outputMismatch")
dx, _ = dry(f2, jam_atom(cord("exit")), "exit")
row("op 135 on cause %exit: the kernel's effect is not a write",
    dx.get("verdict") == "ok" and dx.get("writesRefusal") == "effectNotWrite",
    f"writesRefusal={dx.get('writesRefusal')} steps={dx.get('steps')}")
refused("a poke whose effect is %exit",
    scalar([write(STATE, dx.get("stateOut"), f2[str(STATE)]), write(EVENT, 3, 2)]),
    dx.get("claim"), "effectNotWrite")

# 9. peek -> 2, and nothing written
before, rawb = read_fields("peek-before")
p2, dt = peek(f2, "2")
after, rawa = read_fields("peek-after")
row("peek answers 2 and writes nothing (the cell reads byte-identical before and after)",
    p2.get("verdict") == "ok" and p2.get("value") == "2" and rawb == rawa and before == f2,
    f"value={p2.get('value')} steps={p2.get('steps')} ({dt:.1f}s) answer={p2.get('answer')}")

# 10. cold reopen + operator audit: every poke re-executes and re-admits
pid = open(os.path.join(W, "public", "server.pid")).read().strip()
subprocess.run(["kill", pid]); time.sleep(3)
a = subprocess.run([HOST, CONFIG, "audit"], capture_output=True, text=True)
open(path("audit.out"), "w").write(a.stdout + a.stderr)
row("cold reopen: the operator audit re-admits every record, both pokes included",
    a.returncode == 0 and "audited" in a.stdout, (a.stdout.strip() or a.stderr.strip())[-200:])

# 11. the reopened service reads state 2
if os.path.exists(SOCK): os.unlink(SOCK)
srv = subprocess.Popen([MINI, "serve", "--host", HOST, "--config", CONFIG, "--socket", SOCK],
    stdout=open(path("serve2.log"), "w"), stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
open(os.path.join(W, "public", "server.pid"), "w").write(f"{srv.pid}\n")
for _ in range(1200):
    if os.path.exists(SOCK): break
    time.sleep(0.1)
f4, _ = read_fields("reopened")
p4, _ = peek(f4, "reopened")
row("the reopened Store holds state 2: count 2, event 2, and peek over the stored state answers 2",
    f4 == f2 and p4.get("value") == "2", f"fields={f4} peek={p4.get('value')}")

with open(path("rows.tsv"), "w") as f:
    for name, status, detail in ROWS: f.write(f"{status}\t{name}\t{detail}\n")
passed = sum(1 for r in ROWS if r[1] == "PASS")
verdict = f"J-NOCK-5 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)}"
print(verdict); print(path("rows.tsv"))
print(verdict, file=sys.stderr)
sys.exit(0 if passed == len(ROWS) else 1)
PY
rc=$?
exit $rc
