#!/usr/bin/env bash
# J-EVAL (EVAL.md §7, lanes E2/E3): the evaluator registry, end to end.
#
# Journey hook contract (journey.sh header): HOST, MINI, STORE, VERIFIER and
# JOURNEY_STEP_DIR exported; it bootstraps its OWN fresh Stores under
# JOURNEY_STEP_DIR (newparticipant-acceptance.sh, the J0 fixture), never touches
# the journey's service, and stops what it starts. Exit 0 = PASS. The last stdout
# line is the deciding artifact (rows.tsv); the verdict is the last stderr line.
#
# Also needs: NOCK_TEMPLATES (forge.jam) and NOCK_RUN (the untrusted runner).
#
# Two Stores from two genesis params files:
#   A — nothing disabled. forge's record names `nock` (by registry name) and is
#       born at its content address; an inventory under a law pinning
#       `run/evaluator/<nock>` admits forge's checked run; one pinning
#       `run/evaluator/<ski>` refuses the same run by the law; a record naming
#       `ski` ({"name":"ski","semantics":"SKI/v1"}, an id no compiled-in entry
#       has) is refused unknownEvaluator at the check AND at birth; an ABI with a
#       NUL in a key is refused nulInName at the check and refused at birth.
#   B — genesis params with "disabledEvaluators": ["nock"]. Its semantics digest
#       differs from A's; forge's record is refused evaluatorDisabled at the check
#       AND at birth; a run claim of forge under a law pinning run/evaluator/<nock>
#       is refused (programUnknown: the record could not be born here).
# Both: stop, cold operator audit re-admits every record.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR NOCK_TEMPLATES NOCK_RUN; do
  if [ -z "${!name:-}" ]; then echo "jeval: $name is required" >&2; exit 2; fi
done
DIR="$JOURNEY_STEP_DIR/jeval"
if [ -e "$DIR" ]; then echo "jeval: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
WA="$DIR/a"
WB="$DIR/b"
# Program births cost their ~566 KB intent against the owner budget (J-NOCK-2b).
NEWPARTICIPANT_OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-4000000} \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$WA" \
  >"$DIR/bootstrap-a.out" 2>"$DIR/bootstrap-a.err" || { echo "jeval: bootstrap A failed: $(tail -1 "$DIR/bootstrap-a.err")" >&2; exit 1; }
stop() {
  for w in "$WA" "$WB"; do
    if [ -s "$w/public/server.pid" ]; then kill "$(cat "$w/public/server.pid")" 2>/dev/null || true; fi
  done
}
trap stop EXIT
NEWPARTICIPANT_OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-4000000} NEWPARTICIPANT_DISABLED_EVALUATORS=nock \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$WB" \
  >"$DIR/bootstrap-b.out" 2>"$DIR/bootstrap-b.err" || { echo "jeval: bootstrap B failed: $(tail -1 "$DIR/bootstrap-b.err")" >&2; exit 1; }
set +e
python3 - "$DIR" "$WA" "$WB" <<'PY'
import json, os, re, socket, struct, subprocess, sys, time
DIR, WA, WB = sys.argv[1], sys.argv[2], sys.argv[3]
MINI, NOCK_RUN, TPL = os.environ["MINI"], os.environ["NOCK_RUN"], os.environ["NOCK_TEMPLATES"]
SUBJECT = 7
ROWS = []
def path(n): return os.path.join(DIR, n)
def row(name, expected, ok, got):
    ROWS.append((name, "PASS" if ok else "FAIL", expected, got))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\texpected: {expected}\tgot: {got}", file=sys.stderr)

class World:
    def __init__(self, root, tag):
        self.root, self.tag = root, tag
        self.config = os.path.join(root, "deployment", "pinned-config.json")
        self.sock = os.path.join(root, "public", "mini.sock")
        self.ws = os.path.join(root, "sponsor")
        self.cfg = open(self.config, "rb").read()
        self.counter = 0
    def op(self, code, payload):
        def frame(b): return struct.pack("<I", len(b)) + b
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.connect(self.sock)
        s.sendall(frame(bytes([1]) + struct.pack("<I", len(self.cfg)) + self.cfg + bytes([code]) + payload))
        def exact(n):
            out = b""
            while len(out) < n:
                chunk = s.recv(n - len(out))
                if not chunk: raise RuntimeError("short reply")
                out += chunk
            return out
        n = struct.unpack("<I", exact(4))[0]; body = exact(n); s.close()
        if body[0] != code: return {"hostError": body[1:300].decode("latin1")}
        return json.loads(body[1:].decode())
    def mini(self, *args):
        return subprocess.run([MINI, "workspace", *args], capture_output=True, text=True)
    def name(self, n): return f"{self.tag}-{n}"
    def check(self, n, jam, abi):
        v = self.op(131, struct.pack("<I", len(jam)) + jam + json.dumps(abi).encode())
        json.dump(v, open(path(f"{self.name(n)}.check.json"), "w"))
        return v
    def birth(self, n):
        r = self.mini("--action", "create", "--dir", self.ws, "--name", n, "--storage", "nock",
            "--predicate", path("permit-all.json"), "--program", path(f"{self.name(n)}.check.json"))
        open(path(f"{self.name(n)}.birth.err"), "w").write(r.stderr)
        return r.returncode, last_line(r)
    def submit(self, label, targets, run=None):
        self.counter += 1
        pid = re.sub(r"[^A-Za-z0-9-]+", "-", label).strip("-") + f"-{self.counter}"
        req = {"type": "minidregg-workspace-proposal-v1", "action": "invoke", "targets": targets}
        if run is not None: req["run"] = run
        json.dump(req, open(path(f"{self.name(pid)}.request.json"), "w"))
        r = self.mini("--action", "propose", "--dir", self.ws, "--request", path(f"{self.name(pid)}.request.json"),
            "--proposal-id", pid)
        if r.returncode != 0: return r.returncode, "propose: " + last_line(r)
        attempt = os.path.join(self.ws, "attempts", pid)
        r = self.mini("--action", "submit", "--dir", self.ws, "--intent",
            os.path.join(self.ws, "proposals", pid, "intent.json"), "--attempt", attempt)
        open(path(f"{self.name(pid)}.submit.err"), "w").write(r.stderr)
        last = last_line(r, attempt)
        outcome = os.path.join(attempt, "outcome.json")
        if "exact outcome evidence was retained" in last and os.path.exists(outcome):
            o = json.load(open(outcome))
            last = "outcome " + o.get("type", "?") + " | " + bytes.fromhex(o.get("phase", "")).decode("latin1") \
                + " | " + bytes.fromhex(o.get("detail", "")).decode("latin1")
        return r.returncode, last
    def cell(self, n, law):
        r = self.mini("--action", "create", "--dir", self.ws, "--name", n, "--storage", "declared",
            "--predicate", path("permit-all.json"))
        target = json.load(open(os.path.join(self.ws, "refs", f"{n}.json")))["target"] if r.returncode == 0 else None
        rc, last = self.submit(f"fill-{n}", scalar(n, [create(IRON, 3), create(WOOD, 2), create(SWORD, 0)]))
        req = {"type": "minidregg-workspace-proposal-v1", "action": "install-policy", "name": n, "predicate": law}
        json.dump(req, open(path(f"{self.name(n)}.law.json"), "w"))
        r2 = self.mini("--action", "propose", "--dir", self.ws, "--request", path(f"{self.name(n)}.law.json"),
            "--proposal-id", f"law-{n}")
        r3 = self.mini("--action", "submit", "--dir", self.ws, "--intent",
            os.path.join(self.ws, "proposals", f"law-{n}", "intent.json"),
            "--attempt", os.path.join(self.ws, "attempts", f"law-{n}")) if r2.returncode == 0 else r2
        return target, rc == 0 and r3.returncode == 0, f"cell rc={r.returncode} fill rc={rc} law rc={r3.returncode} {last_line(r3)[:120]}"
    def dry(self, program, target):
        req = {"programId": program, "caller": str(SUBJECT), "room": "0", "targets": [target],
               "values": [["0", f"resource/field/{f}/before", str(v)] for f, v in [(IRON, 3), (WOOD, 2), (SWORD, 0)]]}
        return self.op(134, json.dumps(req).encode())
    def audit(self):
        pid = open(os.path.join(self.root, "public", "server.pid")).read().strip()
        subprocess.run(["kill", pid]); time.sleep(3)
        a = subprocess.run([os.environ["HOST"], self.config, "audit"], capture_output=True, text=True)
        open(path(f"{self.tag}-audit.out"), "w").write(a.stdout + a.stderr)
        return a.returncode == 0 and "audited" in a.stdout, (a.stdout.strip() or a.stderr.strip())[-160:]

def last_line(r, attempt_dir=None):
    last = (r.stderr.strip().splitlines() or [""])[-1]
    if attempt_dir:
        retained = os.path.join(attempt_dir, "reply.frame")
        if "retained encoded Host outcome" in last and os.path.exists(retained):
            last = open(retained, "rb").read().decode("latin1").replace("\xff", " | ")
    named = re.search(r"retained (\S+/reply\.frame)", last)
    if named and os.path.exists(named.group(1)):
        last = open(named.group(1), "rb").read().decode("latin1").replace("\xff", " | ")
    m = re.search(r"([0-9a-f]{40,})", last)
    if m:
        try: last = bytes.fromhex(m.group(1)).decode("latin1").replace("\xff", " | ")
        except ValueError: pass
    return last

IRON, WOOD, SWORD = 2, 3, 4
FIELDS = {"inv/iron": IRON, "inv/wood": WOOD, "inv/sword": SWORD}
def scalar(n, actions): return [{"name": n, "payload": {"type": "scalar", "actions": actions}}]
def create(f, v): return {"type": "create", "key": {"type": "object", "field": str(f)}, "value": str(v)}
def write(f, v, e): return {"type": "write", "key": {"type": "object", "field": str(f)}, "value": str(v), "expected": str(e)}
def slot(f, k): return {"target": "0", "slot": f"resource/field/{f}/before", "key": k, "type": "nat"}
def out(k, f): return {"key": k, "target": "0", "field": str(f), "type": "nat"}
def abi(evaluator="nock", keys=None):
    keys = keys or list(FIELDS)
    return {"evaluator": evaluator, "version": "5", "context": "live", "arm": "2", "fuel": "1000000",
            "sample": [slot(f, k) for k, f in zip(keys, FIELDS.values())],
            "outputs": [out(k, f) for k, f in FIELDS.items()], "libraries": []}
def law(program, evaluator_id):
    return {"type": "any", "predicates": [
        {"type": "not", "predicate": {"type": "eq", "slot": "request/verb", "value": "2"}},
        {"type": "all", "predicates": [{"type": "ran", "program": program},
            {"type": "eq", "slot": f"run/evaluator/{evaluator_id}", "value": "1"}]}]}
open(path("permit-all.json"), "w").write('{"type":"all","predicates":[]}\n')
forge = open(os.path.join(TPL, "forge.jam"), "rb").read()
FORGE_WRITES = [write(IRON, 1, 3), write(WOOD, 1, 2), write(SWORD, 1, 0)]
A, B = World(WA, "a"), World(WB, "b")

# --- Store A: nothing disabled -------------------------------------------------
def semantics(w): return json.load(open(os.path.join(w.root, "deployment", "profile.json"))).get("semantics")
semA, semB = semantics(A), semantics(B)
offA = json.load(open(A.config)).get("disabledEvaluators")
offB = json.load(open(B.config)).get("disabledEvaluators")
row("two genesis params files: B disables nock, its semantics digest differs from A's",
    "A: none disabled; B.disabledEvaluators = [nock]; profile semantics A != B",
    offA in (None, []) and offB == ["nock"] and semA and semB and semA != semB,
    f"A.disabledEvaluators={offA} B.disabledEvaluators={offB} A.sem={str(semA)[:12]}... B.sem={str(semB)[:12]}...")

v = A.check("forge", forge, abi())
P, NOCK_ID = v.get("programId"), v.get("evaluator")
rc, last = A.birth("forge")
ref = os.path.join(A.ws, "refs", "forge.json")
target = json.load(open(ref)).get("target") if os.path.exists(ref) else None
row("A: a record naming nock is admissible and born at its content address (J-NOCK-3's forge)",
    "check admissible; birth rc=0 at cellId", v.get("verdict") == "admissible" and rc == 0 and target == v.get("cellId"),
    f"check={v.get('verdict')} evaluator={str(NOCK_ID)[:16]}... arm={v.get('arm')} birth rc={rc} target={target} cellId={v.get('cellId')}")

vs = A.check("ski", forge, abi(evaluator={"name": "ski", "semantics": "SKI/v1"}))
SKI_ID = vs.get("evaluator")
try:
    prog = bytes.fromhex(vs.get("program", ""))
except ValueError:
    prog = b""
row("A: a record naming ski (unregistered) is refused at the check, by name",
    "verdict refused, reason unknownEvaluator", vs.get("verdict") == "refused" and vs.get("reason") == "unknownEvaluator",
    f"{vs.get('verdict')}/{vs.get('reason')} evaluator={str(SKI_ID)[:16]}... record bytes={len(prog)}")
rc, last = A.birth("ski")
row("A: the ski record is REFUSED AT BIRTH, by name",
    "birth rc!=0 naming unknownEvaluator", rc != 0 and "unknownEvaluator" in last, f"rc={rc} last={last[:200]}")

nul_keys = ["inv/iron\u0000", "inv/wood", "inv/sword"]
vn = A.check("nul", forge, abi(keys=nul_keys))
row("A: an ABI with a NUL in a key is refused at the ABI decoder, by name",
    "verdict refused, reason nulInName", vn.get("verdict") == "refused" and vn.get("reason") == "nulInName",
    f"{vn.get('verdict')}/{vn.get('reason')}")
rc, last = A.birth("nul")
row("A: the NUL record is refused at birth (the cell law)", "birth rc!=0 (initialPayload)",
    rc != 0 and "initialPayload" in last, f"rc={rc} last={last[:200]}")

# the run under a law pinning run/evaluator/<nock>, and under one pinning ski's id
inv, ok, detail = A.cell("inv", law(P, NOCK_ID))
row("A: inventory filled (3, 2, 0) under the law `ran forge ∧ run/evaluator/<nock> = 1`", "cell, fill, law rc=0",
    inv is not None and ok, f"inv={inv} {detail}")
d = A.dry(P, inv)
json.dump(d, open(path("a-forge.dry.json"), "w"))
open(path("a-sample.jam"), "wb").write(bytes.fromhex(d.get("sample", "")))
nr = subprocess.run([NOCK_RUN, "--program", os.path.join(TPL, "forge.jam"), "--sample", path("a-sample.jam"),
    "--fuel", "100000000", "--jets", "off", "--writes"], capture_output=True, text=True)
try: runner = json.loads(nr.stdout)
except Exception: runner = {}
claim = {"programId": P, "sample": d.get("sample"), "output": runner.get("out_hex", ""), "steps": d.get("steps")}
rc, last = A.submit("forge-nock", scalar("inv", FORGE_WRITES), claim)
row("A: forge's checked run is admitted under the law pinning nock",
    "op 134 ok, runner agrees, submit rc=0", d.get("verdict") == "ok" and runner.get("out_hex") == d.get("output") and rc == 0,
    f"dry={d.get('verdict')} steps={d.get('steps')} runner={runner.get('status')} submit rc={rc} {last[:120]}")

inv2, ok, detail = A.cell("inv2", law(P, SKI_ID))
d2 = A.dry(P, inv2)
open(path("a-sample2.jam"), "wb").write(bytes.fromhex(d2.get("sample", "")))
nr2 = subprocess.run([NOCK_RUN, "--program", os.path.join(TPL, "forge.jam"), "--sample", path("a-sample2.jam"),
    "--fuel", "100000000", "--jets", "off", "--writes"], capture_output=True, text=True)
try: runner2 = json.loads(nr2.stdout)
except Exception: runner2 = {}
claim2 = {"programId": P, "sample": d2.get("sample"), "output": runner2.get("out_hex", ""), "steps": d2.get("steps")}
rc, last = A.submit("forge-other", scalar("inv2", FORGE_WRITES), claim2)
row("A: forge's checked run under a law pinning run/evaluator/<ski> is refused by the law",
    "submit rc!=0, law-denied", inv2 is not None and ok and SKI_ID not in (None, NOCK_ID) and rc != 0
    and "law-denied" in last,
    f"law={detail[:60]} rc={rc} last={last[:200]}")

# --- Store B: nock disabled at genesis --------------------------------------------
vb = B.check("forge", forge, abi())
row("B: forge's record is refused at the check, by name", "verdict refused, reason evaluatorDisabled",
    vb.get("verdict") == "refused" and vb.get("reason") == "evaluatorDisabled", f"{vb.get('verdict')}/{vb.get('reason')}")
rc, last = B.birth("forge")
row("B: forge's record is REFUSED AT BIRTH, by name", "birth rc!=0 naming evaluatorDisabled",
    rc != 0 and "evaluatorDisabled" in last, f"rc={rc} last={last[:200]}")
invb, ok, detail = B.cell("inv", law(P, NOCK_ID))
rc, last = B.submit("forge-b", scalar("inv", FORGE_WRITES), dict(claim, sample=d.get("sample")))
row("B: a run claim of forge under a law pinning run/evaluator/<nock> is refused",
    "submit rc!=0, programUnknown (the record could not be born here)",
    invb is not None and ok and rc != 0 and "programUnknown" in last, f"law={detail[:60]} rc={rc} last={last[:200]}")

# --- cold audits ---------------------------------------------------------------------
okA, outA = A.audit()
row("A: cold reopen, the operator audit re-admits every record", "rc=0 audited", okA, outA)
okB, outB = B.audit()
row("B: cold reopen, the operator audit re-admits every record", "rc=0 audited", okB, outB)

with open(path("rows.tsv"), "w") as f:
    f.write("status\trow\texpected\tgot\n")
    for name, status, expected, got in ROWS: f.write(f"{status}\t{name}\t{expected}\t{got}\n")
passed = sum(1 for r in ROWS if r[1] == "PASS")
verdict = f"J-EVAL {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)}"
print(verdict); print(path("rows.tsv"))
print(verdict, file=sys.stderr)
sys.exit(0 if passed == len(ROWS) else 1)
PY
rc=$?
exit $rc
