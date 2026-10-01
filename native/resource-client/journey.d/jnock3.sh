#!/usr/bin/env bash
# J-NOCK-3 (NOCK.md K-RAN): the kernel checks a run by re-executing it.
#
# Journey hook contract (journey.sh header): HOST, MINI, STORE, VERIFIER and
# JOURNEY_STEP_DIR exported; it bootstraps its OWN fresh Store and service under
# JOURNEY_STEP_DIR (newparticipant-acceptance.sh, the J0 fixture), never touches
# the journey's service, and stops what it starts. Exit 0 = PASS. The last stdout
# line is the deciding artifact (rows.tsv); the verdict is the last stderr line.
#
# Also needs: NOCK_TEMPLATES (forge.jam and melt.jam, minimal bytes) and NOCK_RUN
# (the untrusted nockvm runner, used to compute the claimed output).
#
# Rows: forge, melt and a low-fuel forge are born; an inventory cell is created,
# filled (iron 3, wood 2, sword 0) and given the law `ran forge`. A human's direct
# write is law-denied. op 134 gives the kernel's sample and Lean steps; nock-run
# on that sample gives the output the claim names. Refusals by NAME: a wrong
# output (outputMismatch), wrong steps (stepsMismatch), melt (crash), the low-fuel
# forge (exhausted / fuelExceeded), an extra write (writeNotInOutput), a missing
# write (outputNotWritten). The correct claim is admitted and the cell reads
# iron 1, wood 1, sword 1. The same claim again, after that write changed the
# inputs, is sampleStale. Cold reopen + audit re-admits every record.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR NOCK_TEMPLATES NOCK_RUN; do
  if [ -z "${!name:-}" ]; then echo "jnock3: $name is required" >&2; exit 2; fi
done
DIR="$JOURNEY_STEP_DIR/jnock3"
if [ -e "$DIR" ]; then echo "jnock3: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
W="$DIR/world"
# Program births cost their ~566 KB intent against the owner budget (J-NOCK-2b).
NEWPARTICIPANT_OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-4000000} \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W" \
  >"$DIR/bootstrap.out" 2>"$DIR/bootstrap.err" || { echo "jnock3: bootstrap failed: $(tail -1 "$DIR/bootstrap.err")" >&2; exit 1; }
stop() { if [ -s "$W/public/server.pid" ]; then kill "$(cat "$W/public/server.pid")" 2>/dev/null || true; fi; }
trap stop EXIT
set +e
python3 - "$DIR" "$W" <<'PY'
import hashlib, json, os, re, socket, struct, subprocess, sys, time
DIR, W = sys.argv[1], sys.argv[2]
MINI, NOCK_RUN, TPL = os.environ["MINI"], os.environ["NOCK_RUN"], os.environ["NOCK_TEMPLATES"]
CONFIG = os.path.join(W, "deployment", "pinned-config.json")
SOCK = os.path.join(W, "public", "mini.sock")
WS = os.path.join(W, "sponsor")
SUBJECT = 7
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

forge = open(os.path.join(TPL, "forge.jam"), "rb").read()
melt = open(os.path.join(TPL, "melt.jam"), "rb").read()
# Field 1 is the declared object's birth field (0); the inventory is fields 2-4.
FIELDS = {"inv/iron": 2, "inv/wood": 3, "inv/sword": 4}
IRON, WOOD, SWORD = 2, 3, 4
def slot(f, k): return {"target": "0", "slot": f"resource/field/{f}/before", "key": k, "type": "nat"}
def out(k, f): return {"key": k, "target": "0", "field": str(f), "type": "nat"}
def abi(fuel): return {"evaluator": "nock", "version": "5", "context": "live", "arm": "2", "fuel": str(fuel),
  "sample": [slot(f, k) for k, f in FIELDS.items()],
  "outputs": [out(k, f) for k, f in FIELDS.items()], "libraries": []}
open(path("permit-all.json"), "w").write('{"type":"all","predicates":[]}\n')

def birth(name, jam, a):
    v = op(131, pair(jam, json.dumps(a).encode()))
    json.dump(v, open(path(f"{name}.check.json"), "w"))
    r = mini("--action", "create", "--dir", WS, "--name", name, "--storage", "nock",
        "--predicate", path("permit-all.json"), "--program", path(f"{name}.check.json"))
    open(path(f"{name}.birth.err"), "w").write(r.stderr)
    return v, r.returncode
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
def scalar(actions): return [{"name": "inv", "payload": {"type": "scalar", "actions": actions}}]
def create(f, v): return {"type": "create", "key": {"type": "object", "field": str(f)}, "value": str(v)}
def write(f, v, e): return {"type": "write", "key": {"type": "object", "field": str(f)}, "value": str(v), "expected": str(e)}
def read_fields():
    r = mini("--action", "read", "--dir", WS, "--name", "inv")
    open(path("inv.read.json"), "w").write(r.stdout)
    text = r.stdout
    vals = {}
    try:
        for e in json.loads(text)["cell"]["entries"]:
            vals[e["key"]["field"]] = e["value"]
    except Exception: pass
    return vals

# 1. births: forge, melt (crash), forge with ABI fuel 500
P = {}
for name, jam, fuel in [("forge", forge, 1000000), ("melt", melt, 1000000), ("forgelow", forge, 500)]:
    v, rc = birth(name, jam, abi(fuel))
    P[name] = v.get("programId")
    row(f"{name} born (ABI fuel {fuel})", rc == 0 and v.get("verdict") == "admissible",
        f"rc={rc} programId={P[name]}")

# 2. the inventory cell, filled under all[], then the law `ran forge`
r = mini("--action", "create", "--dir", WS, "--name", "inv", "--storage", "declared",
    "--predicate", path("permit-all.json"), "--fields", "%d-%d" % (IRON, SWORD + 1))
# Field 5 is declared (K-FIELD-CLOSURE) but never in forge's product: row 13 writes it beside
# forge's writes, and the run check (writeNotInOutput) must be what refuses, not the closure.
INV = json.load(open(os.path.join(WS, "refs", "inv.json")))["target"] if r.returncode == 0 else None
rc, last = submit("fill", scalar([create(IRON, 3), create(WOOD, 2), create(SWORD, 0)]))
# Every mutation must be forge's checked product; observation and the other verbs stay open.
LAW = {"type": "any", "predicates": [
    {"type": "not", "predicate": {"type": "eq", "slot": "request/verb", "value": "2"}},
    {"type": "ran", "program": P["forge"]}]}
open(path("law.json"), "w").write(json.dumps(LAW))
law = {"type": "minidregg-workspace-proposal-v1", "action": "install-policy", "name": "inv",
       "predicate": LAW}
json.dump(law, open(path("law.request.json"), "w"))
r2 = mini("--action", "propose", "--dir", WS, "--request", path("law.request.json"), "--proposal-id", "law")
r3 = mini("--action", "submit", "--dir", WS, "--intent", os.path.join(WS, "proposals", "law", "intent.json"),
    "--attempt", os.path.join(WS, "attempts", "law")) if r2.returncode == 0 else r2
row("inventory cell filled (iron 3, wood 2, sword 0) and given the law `ran forge`",
    INV is not None and rc == 0 and r3.returncode == 0,
    f"inv={INV} fill rc={rc} law propose rc={r2.returncode} submit rc={r3.returncode} {last_line(r3)[:160]}")

# 3. a human's direct write of the same fields: law-denied
rc, last = submit("human", scalar([write(IRON, 1, 3), write(WOOD, 1, 2), write(SWORD, 1, 0)]))
# The authorized prepare names the law leaf that refused (MR's `law-denied` frame,
# on this line since the final integration): `law-denied: ran <forge>`. The run
# check passed at prepare (no claim, nothing to check); the identical writes WITH
# forge's claim are admitted below.
row("a direct write (no run claim) is refused by the law, naming its `ran forge` leaf",
    rc != 0 and f"law-denied: ran {P['forge']}" in last, f"rc={rc} last={last[:200]}")

# 4. op 134: the kernel's sample and the Lean steps; nock-run computes the output on it
def dry(program, values):
    req = {"programId": program, "caller": str(SUBJECT), "room": "0", "targets": [INV],
           "values": [["0", f"resource/field/{f}/before", str(v)] for f, v in values]}
    return op(134, json.dumps(req).encode())
d = dry(P["forge"], [(IRON, 3), (WOOD, 2), (SWORD, 0)])
json.dump(d, open(path("forge.dry.json"), "w"))
open(path("kernel-sample.jam"), "wb").write(bytes.fromhex(d.get("sample", "")))
nr = subprocess.run([NOCK_RUN, "--program", os.path.join(TPL, "forge.jam"), "--sample", path("kernel-sample.jam"),
    "--fuel", "100000000", "--jets", "off", "--writes"], capture_output=True, text=True)
open(path("nock-run.json"), "w").write(nr.stdout)
try: runner = json.loads(nr.stdout)
except Exception: runner = {}
claim = {"programId": P["forge"], "sample": d.get("sample"), "output": runner.get("out_hex", ""),
         "steps": d.get("steps")}
row("op 134 answers ok; the runner (nockvm) on the kernel's sample gets the kernel's output",
    d.get("verdict") == "ok" and runner.get("status") == "ok" and runner.get("out_hex") == d.get("output")
    and d.get("writes") == [["0", str(IRON), "1"], ["0", str(WOOD), "1"], ["0", str(SWORD), "1"]],
    f"height={d.get('height')} lean steps={d.get('steps')} nockvm items={runner.get('steps')} "
    f"writes={d.get('writes')} out={d.get('output')}")
FORGE_WRITES = [write(IRON, 1, 3), write(WOOD, 1, 2), write(SWORD, 1, 0)]

# 5. refusals, each by name, all against the same pre-state
def refused(label, targets, run, name):
    rc, last = submit(label, targets, run)
    row(f"{label}: refused {name}", rc != 0 and name in last, f"rc={rc} last={last[:220]}")
wrong = dict(claim, output="02")   # jam of 0 (`~`), not forge's product
refused("wrong output", scalar(FORGE_WRITES), wrong, "outputMismatch")
refused("wrong steps", scalar(FORGE_WRITES), dict(claim, steps=str(int(claim["steps"]) + 1)), "stepsMismatch")
dm = dry(P["melt"], [(IRON, 3), (WOOD, 2), (SWORD, 0)])
json.dump(dm, open(path("melt.dry.json"), "w"))
refused("melt crashes", scalar(FORGE_WRITES),
    {"programId": P["melt"], "sample": dm.get("sample"), "output": claim["output"], "steps": "100000"}, "crash")
dl = dry(P["forgelow"], [(IRON, 3), (WOOD, 2), (SWORD, 0)])
json.dump(dl, open(path("forgelow.dry.json"), "w"))
row("op 134 on the low-fuel forge answers exhausted at its ABI fuel", dl.get("verdict") == "exhausted"
    and dl.get("steps") == "500", f"{dl.get('verdict')} {dl.get('steps')}")
refused("fuel too low", scalar(FORGE_WRITES),
    {"programId": P["forgelow"], "sample": dl.get("sample"), "output": claim["output"], "steps": "500"}, "exhausted")
refused("claim above the ABI fuel", scalar(FORGE_WRITES),
    {"programId": P["forgelow"], "sample": dl.get("sample"), "output": claim["output"], "steps": claim["steps"]},
    "fuelExceeded")
refused("a write not in the output", scalar(FORGE_WRITES + [create(5, 9)]), claim, "writeNotInOutput")
refused("an output not written", scalar(FORGE_WRITES[:2]), claim, "outputNotWritten")

# 6. the correct claim is admitted, and the cell holds forge's product
before = read_fields()
rc, last = submit("forge", scalar(FORGE_WRITES), claim)
after = read_fields()
row("the correct claim is admitted; the cell holds forge's product",
    rc == 0 and all(after.get(str(f)) == "1" for f in (IRON, WOOD, SWORD)),
    f"rc={rc} before={before} after={after} last={last[:160]}")

# 7. the same claim again: its sample is no longer the kernel's
rc, last = submit("stale", scalar([write(IRON, 1, 1), write(WOOD, 1, 1), write(SWORD, 1, 1)]), claim)
row("the same claim after the write changed the inputs: refused sampleStale",
    rc != 0 and "sampleStale" in last, f"rc={rc} last={last[:220]}")

# 8. cold reopen + operator audit: every record (the checked run included) re-admits
pid = open(os.path.join(W, "public", "server.pid")).read().strip()
subprocess.run(["kill", pid]); time.sleep(3)
a = subprocess.run([os.environ["HOST"], CONFIG, "audit"], capture_output=True, text=True)
open(path("audit.out"), "w").write(a.stdout + a.stderr)
row("cold reopen: the operator audit re-admits every record, the checked run included",
    a.returncode == 0 and "audited" in a.stdout, (a.stdout.strip() or a.stderr.strip())[-200:])

with open(path("rows.tsv"), "w") as f:
    for name, status, detail in ROWS: f.write(f"{status}\t{name}\t{detail}\n")
passed = sum(1 for r in ROWS if r[1] == "PASS")
verdict = f"J-NOCK-3 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)}"
print(verdict); print(path("rows.tsv"))
print(verdict, file=sys.stderr)
sys.exit(0 if passed == len(ROWS) else 1)
PY
rc=$?
exit $rc
