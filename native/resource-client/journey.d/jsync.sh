#!/usr/bin/env bash
# JSYNC: the operator's synchronous run budget `nockFSync` (Host config, default
# 1,000,000 Lean steps, C17's measured F_sync) at both poles, and the lifetime
# proofWork meter it is not.
#
# Journey hook contract (journey.sh header): HOST, MINI, STORE, VERIFIER and
# JOURNEY_STEP_DIR exported; it bootstraps its OWN fresh Store (the J0 fixture),
# never touches the journey's service, and stops what it starts. Exit 0 = PASS.
# The last stdout line is the deciding artifact (rows.tsv); the verdict is the
# last stderr line.
#
# The gate is a raw-Nock loop (C13's synthetic gate, run/synth.py, wrapped in
# [7 [2 [0 1] [1 F]] [0 1]]): it costs exactly 10n + 30 Lean steps, so n = 99997
# is a run of exactly 1,000,000 steps and n = 99998 one of 1,000,010.
#
# Rows: describe names nockFSync 1000000; a real run of exactly 1,000,000 steps
# is admitted; a real run of 1,000,010 steps is refused overSyncBudget naming
# both numbers; the admitted claim re-labelled 1,000,001 steps is refused
# overSyncBudget naming 1000001 before the referee re-executes it; 1,000,000-step
# turns repeated until the deployment's lifetime proofWork meter (genesis
# meterAllowance.proofWork = 10,000,000, never replenished) refuses one, and the
# operator log names that meter; the operator audit re-admits every record cold.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jsync: $name is required" >&2; exit 2; fi
done
DIR="$JOURNEY_STEP_DIR/jsync"
if [ -e "$DIR" ]; then echo "jsync: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
W="$DIR/world"
# A run claim's proofWork charge is checked against the owner capability's
# maxCost (the template ownerBudget), so this world's budget covers 10^6 steps.
NEWPARTICIPANT_OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-1000000000000} \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W" \
  >"$DIR/bootstrap.out" 2>"$DIR/bootstrap.err" || { echo "jsync: bootstrap failed: $(tail -1 "$DIR/bootstrap.err")" >&2; exit 1; }
stop() { if [ -s "$W/public/server.pid" ]; then kill "$(cat "$W/public/server.pid")" 2>/dev/null || true; fi; }
trap stop EXIT
set +e
python3 - "$DIR" "$W" <<'PY'
import json, os, re, socket, struct, subprocess, sys, time
DIR, W = sys.argv[1], sys.argv[2]
MINI, HOST = os.environ["MINI"], os.environ["HOST"]
CONFIG = os.path.join(W, "deployment", "pinned-config.json")
SOCK = os.path.join(W, "public", "mini.sock")
WS = os.path.join(W, "sponsor")
ROWS = []
def path(n): return os.path.join(DIR, n)
def row(name, ok, detail):
    ROWS.append((name, "PASS" if ok else "FAIL", detail))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{detail}", file=sys.stderr, flush=True)
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
def mini(*args): return subprocess.run([MINI, "workspace", *args], capture_output=True, text=True)
def said(r, attempt=None):
    text = r.stdout + r.stderr
    if attempt:
        for leaf in ("reply.frame", "outcome.json"):
            f = os.path.join(attempt, leaf)
            if os.path.exists(f): text += open(f, "rb").read().decode("latin1")
    for m in re.findall(r"([0-9a-f]{40,})", text):
        try: text += " " + bytes.fromhex(m).decode("latin1")
        except ValueError: pass
    return text.replace("\xff", " | ")
SEQ = [0]
def submit(label, targets, run=None):
    SEQ[0] += 1; pid = f"{label}-{SEQ[0]}"
    req = {"type": "minidregg-workspace-proposal-v1", "action": "invoke", "targets": targets}
    if run is not None: req["run"] = run
    json.dump(req, open(path(f"{pid}.request.json"), "w"))
    r = mini("--action", "propose", "--dir", WS, "--request", path(f"{pid}.request.json"), "--proposal-id", pid)
    if r.returncode: return r.returncode, said(r)
    attempt = os.path.join(WS, "attempts", pid)
    r = mini("--action", "submit", "--dir", WS, "--intent", os.path.join(WS, "proposals", pid, "intent.json"), "--attempt", attempt)
    open(path(f"{pid}.submit.err"), "w").write(r.stderr)
    return r.returncode, said(r, attempt)
def scalar(name, actions): return [{"name": name, "payload": {"type": "scalar", "actions": actions}}]
def create(f, v): return {"type": "create", "key": {"type": "object", "field": str(f)}, "value": str(v)}
def write(f, v, e): return {"type": "write", "key": {"type": "object", "field": str(f)}, "value": str(v), "expected": str(e)}
def ref(name): return json.load(open(os.path.join(WS, "refs", f"{name}.json")))["target"]
def field(name, f):
    r = mini("--action", "read", "--dir", WS, "--name", name)
    for e in json.loads(r.stdout)["cell"]["entries"]:
        if e["key"]["field"] == str(f): return int(e["value"])
open(path("permit-all.json"), "w").write('{"type":"all","predicates":[]}\n')

GATE = bytes.fromhex("c5855fc892e320581c76e196c804d3be8ae1e3301354f7b1212bcc716ea2133b0836046ec846c321e247c3cab4003d5d98dc5919dd0b6cc1dd167cac0a")
def slot(f, k): return {"target": "0", "slot": f"resource/field/{f}/before", "key": k, "type": "nat"}
ABI = {"version": "2", "arm": "2", "fuel": "1000000000", "sample": [slot(2, "n"), slot(3, "c")],
       "outputs": [{"key": "c", "target": "0", "field": "3", "type": "nat"}], "libraries": []}
d = subprocess.run([HOST, CONFIG, "describe"], capture_output=True, text=True)
budget = json.loads(d.stdout).get("nockFSync") if d.returncode == 0 else None
row("describe names the operator's synchronous budget", str(budget) == "1000000", f"nockFSync={budget}")

v = op(131, pair(GATE, json.dumps(ABI).encode())); json.dump(v, open(path("gate.check.json"), "w"))
PID = v.get("programId")
r = mini("--action", "create", "--dir", WS, "--name", "gate", "--storage", "nock",
         "--predicate", path("permit-all.json"), "--program", path("gate.check.json"))
LAW = {"type": "any", "predicates": [{"type": "not", "predicate": {"type": "eq", "slot": "request/verb", "value": "2"}},
                                     {"type": "ran", "program": PID}]}
for name, n in (("at", 99997), ("over", 99998)):
    mini("--action", "create", "--dir", WS, "--name", name, "--storage", "declared", "--predicate", path("permit-all.json"))
    rc, _ = submit("fill-" + name, scalar(name, [create(2, n), create(3, 0)]))
    json.dump({"type": "minidregg-workspace-proposal-v1", "action": "install-policy", "name": name, "predicate": LAW},
              open(path(f"law-{name}.json"), "w"))
    mini("--action", "propose", "--dir", WS, "--request", path(f"law-{name}.json"), "--proposal-id", f"law-{name}")
    r2 = mini("--action", "submit", "--dir", WS, "--intent", os.path.join(WS, "proposals", f"law-{name}", "intent.json"),
              "--attempt", os.path.join(WS, "attempts", f"law-{name}"))
    if rc or r2.returncode: row(f"setup {name}", False, f"fill rc={rc} law rc={r2.returncode}")
def dry(name, c):
    n = field(name, 2)
    req = {"programId": PID, "caller": "7", "room": "0", "targets": [ref(name)],
           "values": [["0", "resource/field/2/before", str(n)], ["0", "resource/field/3/before", str(c)]]}
    return op(134, json.dumps(req).encode())

# the admitted pole: a real run of exactly nockFSync steps
d = dry("at", 0); json.dump(d, open(path("at.dry.json"), "w"))
rc, text = submit("at", scalar("at", [write(3, 1, 0)]), d.get("claim"))
row("a run of exactly 1,000,000 steps is admitted", d.get("steps") == "1000000" and rc == 0 and field("at", 3) == 1,
    f"steps={d.get('steps')} rc={rc} c={field('at', 3)}")
claim = d.get("claim")

# a real run over the budget
d2 = dry("over", 0); json.dump(d2, open(path("over.dry.json"), "w"))
rc, text = submit("over", scalar("over", [write(3, 1, 0)]), d2.get("claim"))
named = "overSyncBudget" in text and "1000010" in text and "nockFSync 1000000" in text
row("a run of 1,000,010 steps is refused overSyncBudget, both numbers named", d2.get("steps") == "1000010" and rc != 0 and named and field("over", 3) == 0,
    f"steps={d2.get('steps')} rc={rc} named={named} c={field('over', 3)}")

# exactly one step over: the admitted claim re-labelled, refused before re-execution
d3 = dry("at", 1); forged = dict(d3.get("claim") or {}); forged["steps"] = "1000001"
rc, text = submit("one-over", scalar("at", [write(3, 2, 1)]), forged)
named = "overSyncBudget" in text and "1000001" in text and "nockFSync 1000000" in text
row("a claim of 1,000,001 steps is refused overSyncBudget by name", rc != 0 and named and field("at", 3) == 1,
    f"rc={rc} named={named} c={field('at', 3)}")

# the lifetime meter: 1,000,000-step turns until one is refused
admitted, refused_at, c = 1, None, 1
for i in range(14):
    d = dry("at", c)
    rc, text = submit(f"meter-{i}", scalar("at", [write(3, c + 1, c)]), d.get("claim"))
    if rc == 0: admitted += 1; c += 1
    else: refused_at = admitted; break
log = ""
for root, _, files in os.walk(os.path.join(W, "public")):
    for f in files:
        if f.endswith(".log"):
            try: log += open(os.path.join(root, f), errors="replace").read()
            except OSError: pass
named = "lifetime proofWork meter holds" in log
row("1,000,000-step turns exhaust the lifetime proofWork meter, named in the operator log",
    refused_at is not None and 8 <= refused_at <= 10 and named,
    f"admitted {admitted} run turns before a refusal; operator log names the meter: {named}")

pid = open(os.path.join(W, "public", "server.pid")).read().strip()
subprocess.run(["kill", pid]); time.sleep(3)
a = subprocess.run([HOST, CONFIG, "audit"], capture_output=True, text=True)
open(path("audit.out"), "w").write(a.stdout + a.stderr)
row("cold reopen: operator audit re-admits every record (admission policy is not replay)",
    a.returncode == 0 and "audited" in a.stdout, (a.stdout.strip() or a.stderr.strip())[-200:])

with open(path("rows.tsv"), "w") as f:
    for r in ROWS: f.write("\t".join(r) + "\n")
print(path("rows.tsv"))
bad = [r for r in ROWS if r[1] != "PASS"]
print(f"{len(ROWS) - len(bad)}/{len(ROWS)} rows pass" + (f"; first failure: {bad[0][0]}" if bad else ""), file=sys.stderr)
sys.exit(1 if bad else 0)
PY
