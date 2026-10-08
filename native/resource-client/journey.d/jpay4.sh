#!/usr/bin/env bash
# J-PAY-4 (PAY.md P4): the payment rail through the client, on a fresh private Store, with the
# P1/P1b fixture watcher driven by the real tick script (deploy/pay/mini-pay-watcher).
#
# Follows the journey hook contract (journey.sh header): executed with HOST, MINI, STORE,
# VERIFIER and JOURNEY_STEP_DIR exported; it starts its OWN `mini serve` on its OWN fresh Store
# under JOURNEY_STEP_DIR (it never touches the journey's service) and stops it. Exit 0 = PASS.
# The verdict `J-PAY-4 PASS n/n` is the last stderr line and the line before the last stdout
# line; the last stdout line is the deciding artifact (rows.tsv).
#
# Standalone: HOST=... MINI=... STORE=... VERIFIER=... JOURNEY_STEP_DIR=NEW_DIR jpay4.sh
# PAY_WATCHER_BIN defaults to native/pay-watcher/target/release/pay-watcher.
#
# Every Host byte goes through `mini` (bootstrap, serve, workspace, pay ...): ops 103-111 pass
# the public socket's allowed_operation or the run fails. Every tick is a fixture endpoint
# pair built from P1's vectors with the tip rewritten (tips advance across ticks).
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jpay4: $name is required" >&2; exit 2; fi
done
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
TREE=$(CDPATH='' cd -- "$HERE/../../.." && pwd)
export PAY_WATCHER_BIN=${PAY_WATCHER_BIN:-$TREE/native/pay-watcher/target/release/pay-watcher}
export PAY_FIXTURES=$TREE/native/pay-watcher/fixtures
export PAY_TICK_SCRIPT=$TREE/deploy/pay/mini-pay-watcher
export ACCEPTANCE=$TREE/native/resource-client/newparticipant-acceptance.sh
for tool in python3 jq; do
  command -v "$tool" >/dev/null || { echo "jpay4: $tool is required" >&2; exit 2; }
done
[ -x "$PAY_WATCHER_BIN" ] || { echo "J-PAY-4 FAIL setup: pay-watcher binary missing at $PAY_WATCHER_BIN" >&2; exit 1; }
# Its Store's socket lives in a short directory, kept as $JOURNEY_STEP_DIR/rt
# (journey.d/lib/shortdir.sh); python runs as a child so the copy-back runs.
. "$HERE/lib/shortdir.sh"
journey_shortdir jpay4
DIR=$JOURNEY_D
mkdir -p "$DIR"
python3 - "$DIR" <<'PY'
import json, os, shutil, signal, subprocess, sys, time

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
WATCHER, FIXTURES = os.environ["PAY_WATCHER_BIN"], os.environ["PAY_FIXTURES"]
TICK_SCRIPT, ACCEPTANCE = os.environ["PAY_TICK_SCRIPT"], os.environ["ACCEPTANCE"]
ROWS, STARTED = [], time.time()
EMBER, FACTORY_CONTROL, OBSERVER, OBSERVER_CAP = 7, 53, 30, 4030
FRIENDS = [8, 9]
def acct(s): return 100 + s
CAP, RATE, MIN_TICK, INITIAL = 2000000000, 1, 1500, 100

def path(*names): return os.path.join(DIR, *names)
def fail(message):
    print(f"J-PAY-4 FAIL: {message}", file=sys.stderr); sys.exit(1)

def row(name, ok, observed):
    observed = " ".join(str(observed).split())
    ROWS.append(("PASS" if ok else "FAIL", name, observed))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{observed}", file=sys.stderr)

B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58decode(text):
    n = 0
    for c in text: n = n * 58 + B58.index(c)
    raw = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    return b"\0" * (len(text) - len(text.lstrip("1"))) + raw
def b58encode(data):
    n = int.from_bytes(data, "big"); out = ""
    while n: n, r = divmod(n, 58); out = B58[r] + out
    return "1" * (len(data) - len(data.lstrip(b"\0"))) + out

def run(argv, env=None, check=False):
    result = subprocess.run(argv, capture_output=True, text=True, env=env)
    if check and result.returncode != 0:
        fail(f"{' '.join(map(str, argv[:3]))} exit {result.returncode}: {result.stderr[-600:]}")
    return result
def mini(*words, check=False): return run([MINI, *map(str, words)], check=check)

# P1's vectors: the happy address (book 0), book 1 (no token account) and P1b's enrollment
# address; P1's mint and Token-2022.
happy = json.load(open(os.path.join(FIXTURES, "happy", "config.json")))
enrol = json.load(open(os.path.join(FIXTURES, "enrol-dust", "config.json")))
ROW0 = b58decode(happy["book"][0]["address"]).hex()
ROW1 = b58decode(happy["book"][1]["address"]).hex()
ENROL_ROW = b58decode(enrol["book"][0]["address"]).hex()
FILLER = bytes(range(1, 33)).hex()
MINT = b58decode(happy["asset"]["mint"]).hex()
PROGRAM = b58decode(happy["asset"]["tokenProgram"]).hex()

# ------------------------------------------------------------ row 0: the bootstrap tooling
acc = run(["sh", ACCEPTANCE, HOST, MINI, STORE, VERIFIER, path("acceptance")])
try:
    if acc.returncode != 0:
        row("acceptance bootstrap writes payObserver; its observer workspace reaches the kernel", False,
            f"acceptance exit {acc.returncode}: {acc.stderr.strip()[-200:]}")
    else:
        handoff = json.load(open(acc.stdout.strip().splitlines()[-1]))
        hb = mini("pay", "heartbeat", "--dir", handoff["payObserver"]["workspace"], "--capability",
                  handoff["payObserver"]["capability"], "--slot", "1500", "--block-time", "1")
        refused = [l for l in hb.stdout.splitlines() if l.startswith("refused")]
        row("acceptance bootstrap writes payObserver; its observer workspace reaches the kernel",
            handoff["payObserver"]["capability"] == "4030" and hb.returncode == 3
            and refused and "refused tariffInvalid" in refused[0],
            f"payObserver={handoff['payObserver']['subject']}/{handoff['payObserver']['capability']} "
            f"heartbeat exit={hb.returncode}: {refused[0].split(chr(9))[-1] if refused else hb.stderr.strip()[-120:]}")
finally:
    pid_file = path("acceptance", "public", "server.pid")
    if os.path.exists(pid_file):
        try: os.kill(int(open(pid_file).read()), signal.SIGTERM)
        except ProcessLookupError: pass

# ------------------------------------------------------------ genesis
SUBJECTS = [EMBER, OBSERVER] + FRIENDS
os.makedirs(path("keys"))
public = {}
for s in SUBJECTS:
    mini("keygen", "--secret", path("keys", f"{s}.key"), "--public", path("keys", f"{s}.pub"), "--no-prerotation", check=True)
    public[s] = open(path("keys", f"{s}.pub"), "rb").read().hex()
def enrollment(s):
    return {"key": {"keyId": str(7000 + s), "keyEpoch": "2", "algorithm": "1", "subject": str(s),
                    "publicKey": public[s], "activeFrom": "0", "activeUntil": "1000000", "nextKeyDigest": None},
            "accountId": str(acct(s)), "spendCapabilityId": str(1000 + s),
            "controlCapabilityId": str(2000 + s), "factoryObserveCapabilityId": str(3000 + s),
            "initialBalance": str(INITIAL), "accountPredicate": {"type": "all", "predicates": []}}
operator = {"domain": 8501, "federation": 9, "factoryId": 10, "resourceBookId": 11,
            "authorityCellId": 12, "issuer": 5, "ownerBudget": 100000, "lifetime": 10000,
            "tariffBase": 3, "tariffPerBirth": 2, "tariffPerGrant": 1,
            "tariffPerInitialPayloadByte": 0, "collector": 99, "asset": 0, "genesisHeight": 10,
            "expectedSeed": 0, "storageBinary": STORE, "storageRoot": path("store"),
            "signatureBinary": VERIFIER}
json.dump(operator, open(path("operator.json"), "w"))
profile = json.loads(run([HOST, path("operator.json"), "profile"], check=True).stdout)
genesis = {"domain": "8501", "factoryId": "10", "resourceBookId": "11", "authorityCellId": "12",
           "federation": "9", "tariffBase": "3", "tariffPerBirth": "2", "tariffPerGrant": "1",
           "tariffPerInitialPayloadByte": "0", "collector": "99", "asset": "0",
           "expectedSemantics": profile["semantics"], "issuerEpoch": "2", "genesisHeight": "10",
           "clockTickers": [], "tailBound":"1000000",
           "factoryPredicate": {"type": "all", "predicates": []},
           "enrollments": [enrollment(s) for s in SUBJECTS],
           "factoryControllerSubject": str(EMBER), "factoryControllerCapability": str(FACTORY_CONTROL),
           "meterAllowance": {k: "10000000" for k in ("incidences", "turnBytes", "memoryTouches",
               "witnessBytes", "proofWork", "storageBytes", "networkBytes", "sideEffectCount",
               "feeDebit", "leaseByteBlocks")},
           "payObserver": {"subject": str(OBSERVER), "capability": str(OBSERVER_CAP),
                           "controlCapability": "4031", "enrolCapability": "4032"}}
json.dump(genesis, open(path("genesis.json"), "w"))
mini("bootstrap", "--host", HOST, "--config", path("operator.json"), "--source", path("genesis.json"),
     "--dir", path("deployment"), check=True)
CONFIG = path("deployment", "pinned-config.json")
ledger0 = json.load(open(path("deployment", "pay-ledger-genesis.json")))
row("bootstrap retains the genesis pay ledger", ledger0["well"] == str(-INITIAL * len(SUBJECTS)),
    f"well={ledger0['well']} clock={ledger0['clock']}")

# ------------------------------------------------------------ the service and the workspaces
os.makedirs(path("public"), mode=0o700)
SOCKET = path("public", "mini.sock")
server = None
def start_server():
    global server
    server = subprocess.Popen([MINI, "serve", "--host", HOST, "--config", CONFIG, "--socket", SOCKET],
                              stdout=open(path("serve.log"), "ab"), stderr=subprocess.STDOUT,
                              start_new_session=True)
    for _ in range(1200):
        if os.path.exists(SOCKET): return
        if server.poll() is not None: fail("mini serve exited")
        time.sleep(0.1)
    fail("socket did not appear")
def stop_server():
    global server
    if server is not None and server.poll() is None:
        os.killpg(server.pid, signal.SIGTERM); server.wait(timeout=60)
    server = None
# A failing row exits through fail(); the server must not outlive the hook (the
# journey's next steps and the box's other runs share the machine).
import atexit
atexit.register(stop_server)
start_server()

WS = {}
for s in SUBJECTS:
    WS[s] = path("ws", str(s))
    os.makedirs(path("ws"), exist_ok=True)
    mini("workspace", "--action", "init", "--host", HOST, "--config", CONFIG, "--socket", SOCKET,
         "--key", path("keys", f"{s}.key"), "--subject", s, "--dir", WS[s], "--no-prerotation", check=True)
for s in FRIENDS:
    mini("workspace", "--action", "import", "--dir", WS[s], "--name", "account", "--kind", "account",
         "--target", acct(s), "--observe-capability", 1000 + s, "--operation-capability", 1000 + s,
         check=True)
# subject 9 also holds a reference to subject 8's account, with its OWN capability
mini("workspace", "--action", "import", "--dir", WS[9], "--name", "stolen", "--kind", "account",
     "--target", acct(8), "--observe-capability", 1009, "--operation-capability", 1009, check=True)
OBS = WS[OBSERVER]

def balance(s):
    status = mini("pay", "status", "--dir", WS[s], "--account", "account", check=True).stdout
    for line in status.splitlines():
        if line.startswith("credit "): return int(line.split()[1])
    fail(f"no credit line in status: {status}")
def clock():
    status = mini("pay", "status", "--dir", WS[8], "--account", "account", check=True).stdout
    for line in status.splitlines():
        if line.startswith("clock slot "): return int(line.split()[2])
    fail("no clock line")
def credit_for(amount): return min(amount, CAP) * RATE

# ------------------------------------------------------------ fixture ticks
def endpoints(tag, tip, primary, extras=()):
    """A fixture endpoint pair: `primary`'s answers, then any file only `extras` have, with the
    finalized tip rewritten to `tip`."""
    out = []
    for side in ("a", "b"):
        dest = path("ticks", tag, side)
        shutil.copytree(os.path.join(FIXTURES, primary, "endpoints", side), dest)
        for extra in extras:
            src = os.path.join(FIXTURES, extra, "endpoints", side)
            for base, _, files in os.walk(src):
                for name in files:
                    rel = os.path.relpath(os.path.join(base, name), src)
                    target = os.path.join(dest, rel)
                    if not os.path.exists(target):
                        os.makedirs(os.path.dirname(target), exist_ok=True)
                        shutil.copyfile(os.path.join(base, name), target)
        json.dump({"id": 1, "jsonrpc": "2.0", "result": tip},
                  open(os.path.join(dest, "getSlot", "finalized.json"), "w"))
        json.dump({"id": 1, "jsonrpc": "2.0", "result": 1759249000 + tip},
                  open(os.path.join(dest, "getBlockTime", f"{tip}.json"), "w"))
        out.append(dest)
    return out
STATE = path("watcher-state")
def tick(tag, tip, primary, extras=(), enrol_row=False, background=False):
    env = dict(os.environ, MINI=MINI, PAY_WATCHER=WATCHER, PAY_STATE=STATE,
               PAY_OBSERVER_WS=OBS, PAY_OBSERVER_CAPABILITY=str(OBSERVER_CAP),
               PAY_RPC_FIXTURES=" ".join(endpoints(tag, tip, primary, extras)))
    env.pop("PAY_RPC_ENDPOINTS", None)
    if enrol_row:
        env.update(PAY_ENROL_INDEX="2", PAY_JOURNAL_FLOOR="1000000")
    if background:
        return subprocess.Popen(["sh", TICK_SCRIPT], env=env, stdout=open(path(f"tick-{tag}.out"), "w"),
                                stderr=subprocess.STDOUT, start_new_session=True)
    result = run(["sh", TICK_SCRIPT], env=env)
    open(path(f"tick-{tag}.out"), "w").write(result.stdout + result.stderr)
    for name in ("observations", "events"):
        source = os.path.join(STATE, "tick", f"{name}.json")
        if os.path.exists(source):
            shutil.copyfile(source, path(f"tick-{tag}.{name}.json"))
    return result
def watch_only(tag, tip, primary):
    """The watcher alone (no submit), for a report the journey holds before submitting."""
    config, out = path(f"{tag}-watcher.json"), path(f"{tag}-out")
    mini("pay", "watch-config", "--dir", OBS, "--out", config, check=True)
    os.makedirs(out)
    argv = [WATCHER, "--config", config, "--out", out]
    for endpoint in endpoints(tag, tip, primary): argv += ["--rpc-fixture", endpoint]
    env = dict(os.environ); env.pop("PAY_RPC_ENDPOINTS", None)
    result = run(argv, env=env)
    shutil.copyfile(os.path.join(out, "observations.json"), path(f"tick-{tag}.observations.json"))
    return result
def lines(result, first):
    return [l.split("\t") for l in result.stdout.splitlines() if l.split("\t")[0] == first]
def summary(result):
    found = [l for l in result.stdout.splitlines() if l.startswith("pay observe:")]
    return found[-1] if found else (result.stdout + result.stderr).strip()[-200:]
def observe(file, *extra):
    return mini("pay", "observe", "--dir", OBS, "--capability", OBSERVER_CAP, "--from", file, *extra)

# ------------------------------------------------------------ rows
r = mini("pay", "address", "--dir", WS[8])
# Op 105 is a blind submission (MR's rule): the refusal built to hit tariffInvalid reads
# undisclosed on the wire; the address attempt is retained as refused and no index exists.
row("pay address before a valid tariff", r.returncode == 3 and "refused undisclosed" in r.stderr,
    f"exit={r.returncode} {r.stderr.strip()[-100:]}")

json.dump({"control": str(FACTORY_CONTROL),
           "book": [b58encode(bytes.fromhex(ROW0)), ROW1, b58encode(bytes.fromhex(ENROL_ROW)), FILLER],
           "tariff": {"version": "1", "asset": "0", "mint": b58encode(bytes.fromhex(MINT)),
                      "tokenProgram": PROGRAM, "decimals": "6", "creditPerAtomic": str(RATE),
                      "maxPerObservation": str(CAP), "minTickSlots": str(MIN_TICK),
                      "nodeWeekRate": "999999840", "enrolIndex": None, "journalFloor": "1000000", "slashCallerPermille": "500"}},
          open(path("book.json"), "w"))
r = mini("pay", "book", "--dir", WS[EMBER], "--source", path("book.json"))
row("operator installs a 4-row book (base58 and hex rows) and the tariff", r.returncode == 0 and "confirmed" in r.stdout,
    r.stdout.strip() or r.stderr.strip()[-160:])

r = mini("pay", "address", "--dir", WS[8])
first = r.stdout.splitlines()[0] if r.stdout else ""
row("friend 8: pay address → index 0 (base58 of book row 0)",
    r.returncode == 0 and first == f"index 0 → {b58encode(bytes.fromhex(ROW0))}", first or r.stderr[-160:])
attempts_before = len([n for n in os.listdir(os.path.join(WS[8], "attempts")) if n.startswith("pay-assign")])
r2 = mini("pay", "address", "--dir", WS[8])
attempts_after = len([n for n in os.listdir(os.path.join(WS[8], "attempts")) if n.startswith("pay-assign")])
row("pay address again: the retained index, no second request",
    r2.returncode == 0 and r2.stdout == r.stdout and attempts_after == attempts_before,
    f"same_output={r2.stdout == r.stdout} assign_attempts={attempts_before}->{attempts_after}")
r = mini("pay", "address", "--dir", WS[9], "--account", "stolen")
# Built to hit notOwner; op 105 is blind (MR's rule), so the wire says undisclosed.
row("subject 9 asks an address for subject 8's account", r.returncode == 3 and "refused undisclosed" in r.stderr,
    f"exit={r.returncode} {r.stderr.strip()[-100:]}")

# A hostile fixture first, while nothing is credited: pay-1's POST balance is another mint.
t = tick("H", 905, "wrong-mint", ("happy",))
ev = json.load(open(path("tick-H.events.json")))
row("hostile fixture (wrong mint): the watcher refuses the index; only a too-soon heartbeat is submitted",
    t.returncode == 0 and any(e["reason"] == "wrongMint" for e in ev) and "exit=3" in t.stdout
    and "waiting tickTooSoon" in summary(t) and balance(8) == INITIAL,
    f"watcher reasons={sorted({e['reason'] for e in ev})} {summary(t)}")

# tick A: tip 920 → pay-1 (slot 900). Built and HELD; an assignment lands; then submitted.
t = watch_only("A0", 920, "happy")
obs_a = json.load(open(path("tick-A0.observations.json")))
held = observe(path("tick-A0.observations.json"), "--hold", "true")
held_attempt = lines(held, "held")[0][1] if lines(held, "held") else None
r9 = mini("pay", "address", "--dir", WS[9], "--account", "account")
resumed = mini("pay", "observe", "--dir", OBS, "--capability", OBSERVER_CAP, "--resume", held_attempt or "-")
stale = lines(resumed, "stale")
credited_a = lines(resumed, "credited")
decision = json.load(open(os.path.join(held_attempt, "decision.json"))) if held_attempt else {}
row("tick A: the watcher reads pay-1 at tip 920; the report is built and held",
    held_attempt is not None and len(obs_a["observations"]) == 1, f"records={len(obs_a['observations'])} held={held_attempt is not None}")
row("friend 9 takes index 1 between the report's read and its submit",
    r9.returncode == 0 and r9.stdout.startswith("index 1 → "), r9.stdout.splitlines()[0] if r9.stdout else r9.stderr[-100:])
row("held report submitted → stalePay → re-read op 107 → retried → credited",
    resumed.returncode == 0 and len(stale) == 1 and "stalePay" in decision.get("host", "")
    and len(credited_a) == 1, f"{decision.get('host')} then {summary(resumed)}")
pay1 = obs_a["observations"][0]
bal8 = balance(8)
row("pay status shows the credit", bal8 == INITIAL + credit_for(pay1["amount"]), f"credit={bal8}")

# tick B: the same fixture tip again: the receipt skips the fetch; a heartbeat is too soon.
t = tick("B", 920, "happy")
ev = json.load(open(path("tick-B.events.json")))
retained = [e for e in ev if e["reason"] == "alreadyRetained"]
row("the SAME fixture tick again: the watcher skips the receipted transfer; nothing minted",
    t.returncode == 0 and len(retained) == 2 and "waiting tickTooSoon" in summary(t) and balance(8) == bal8,
    f"alreadyRetained={len(retained)} (2 endpoints) {summary(t)}")
r = observe(path("tick-A0.observations.json"))
row("tick A's records submitted again: every record already credited (receipt)",
    r.returncode == 0 and len(lines(r, "already-credited")) == 1 and lines(r, "already-credited")[0][3] == "receipt"
    and balance(8) == bal8, summary(r))

# The observer's retained reports are lost (PAY §3.4: "if the attempt directory is lost"): the
# receipts are derived from the credited attempts, so both go. They come back after tick D, as a
# restored backup would, so the audit below sees every report.
LOST = path("lost-observer-state")
os.makedirs(os.path.join(LOST, "attempts"))
os.rename(os.path.join(OBS, "pay", "receipts"), os.path.join(LOST, "receipts"))
os.mkdir(os.path.join(OBS, "pay", "receipts"), 0o700)
for name in os.listdir(os.path.join(OBS, "attempts")):
    if name.startswith("pay-report-"):
        os.rename(os.path.join(OBS, "attempts", name), os.path.join(LOST, "attempts", name))
r = observe(path("tick-A0.observations.json"))
row("reports and receipts lost, same tip: the kernel refuses alreadyConsumed at the clock's tip → wait",
    r.returncode == 0 and "waiting tipReported" in summary(r) and balance(8) == bal8, summary(r))
before_c = set(os.listdir(os.path.join(OBS, "attempts")))
c_started = time.monotonic()
t = tick("C", 910, "happy")
c_elapsed = time.monotonic() - c_started
c_attempts = [os.path.join(OBS, "attempts", n) for n in
              set(os.listdir(os.path.join(OBS, "attempts"))) - before_c if n.startswith("pay-report-")]
c_decisions = [json.load(open(os.path.join(a, "decision.json"))) for a in c_attempts]
c_refused = lines(t, "refused")
row("tick C behind retained tip: refused tipInvalidOrRegressing immediately",
    t.returncode == 3 and len(c_refused) == 1
    and c_refused[0][2] == "refused tipInvalidOrRegressing (phase pay-observation)"
    and not lines(t, "waiting") and "waiting" not in summary(t)
    and len(c_decisions) == 1 and c_decisions[0].get("decision") == "refused"
    and c_elapsed < 10 and balance(8) == bal8,
    f"exit={t.returncode} elapsed={c_elapsed:.2f}s attempts={len(c_attempts)} "
    f"{c_refused[0][2] if c_refused else 'no named refusal'}; {summary(t)}")
t = tick("D", 1000, "happy")
obs_d = json.load(open(path("tick-D.observations.json")))["observations"]
pay2 = [o for o in obs_d if o["signature"] != pay1["signature"]][0]
kernel_already = [l for l in lines(t, "already-credited") if l[3] == "kernel"]
row("tick D (tip 1000, still lost): alreadyConsumed → probe: pay-1 already credited, pay-2 credited",
    t.returncode == 0 and len(obs_d) == 2 and len(kernel_already) == 1 and len(lines(t, "credited")) == 1
    and balance(8) == bal8 + credit_for(pay2["amount"]), summary(t))
bal8 = balance(8)
for name in os.listdir(os.path.join(LOST, "attempts")):
    os.rename(os.path.join(LOST, "attempts", name), os.path.join(OBS, "attempts", name))

# tick E: P1's `retained` answers add pay-3 (slot 990); the tick is killed mid-submit.
proc = tick("E", 1100, "retained", ("happy",), background=True)
killed_at = None
deadline = time.time() + 600
while time.time() < deadline and proc.poll() is None:
    marks = [os.path.join(OBS, "attempts", n) for n in os.listdir(os.path.join(OBS, "attempts"))
             if n.startswith("pay-report-1100-")
             and os.path.exists(os.path.join(OBS, "attempts", n, "submit-marker.json"))]
    if marks:
        # Freeze the service first, then give the client half a second to connect and send its
        # frame into the socket buffer, then kill it: the frame is sent and no outcome can come
        # back. A timing-only kill raced a fast Host (BRAID-HOST, 10-01: the submit answered
        # inside the half second, the outcome landed, and there was no lost submit to settle).
        os.killpg(server.pid, signal.SIGSTOP)
        try:
            time.sleep(0.5)
            os.killpg(proc.pid, signal.SIGKILL); killed_at = marks[0]
        finally:
            os.killpg(server.pid, signal.SIGCONT)
        break
    time.sleep(0.02)
proc.wait()
obs_e = json.load(open(os.path.join(STATE, "tick", "observations.json")))["observations"]
pay3 = obs_e[0] if len(obs_e) == 1 else None
landed = killed_at and os.path.exists(os.path.join(killed_at, "outcome.json"))
row("tick E (tip 1100, pay-3) killed after its submit marker, before any outcome",
    killed_at is not None and pay3 is not None and not landed, f"killed={killed_at is not None} outcome_written={bool(landed)}")
time.sleep(3)   # the Host finishes (or never received) the orphaned frame
t = tick("F", 1200, "retained", ("happy",))
resolved = lines(t, "resolved")
row("tick F (tip 1200) converges: the lost submit is settled by lookup; pay-3 credited exactly once",
    t.returncode == 0 and len(resolved) == 1 and pay3 is not None
    and balance(8) == bal8 + credit_for(pay3["amount"]), f"{resolved[0][2] if resolved else 'no resolution'}; {summary(t)}")
bal8 = balance(8)

c = clock()
t = tick("G", c + MIN_TICK, "retained", ("happy",))
row("a heartbeat tick (tip = clock + minTickSlots) advances the clock",
    t.returncode == 0 and len(lines(t, "heartbeat")) == 1 and clock() == c + MIN_TICK, f"clock {c} -> {clock()}; {summary(t)}")
c = clock()
doctored = {"tip": {"slot": c, "blockTime": 1759249000 + c}, "observations": [
    dict(pay1, index=0, address=ROW1, signature="ab" * 64),
    dict(pay1, index=2, address=ENROL_ROW, signature="cd" * 64)]}
json.dump(doctored, open(path("doctored.json"), "w"))
r = observe(path("doctored.json"))
q = {l[3] for l in lines(r, "quarantined")}
row("kernel per-observation refusals: the report is probed; each record quarantined with its reason",
    r.returncode == 3 and q == {"addressMismatch", "unassignedIndex"}
    and len(os.listdir(os.path.join(OBS, "pay", "quarantine"))) == 2 and balance(8) == bal8,
    f"quarantined={sorted(q)} {summary(r)}")

journal_dir = os.path.join(STATE, "tick", "ticks")
def journal_lines():
    # Full ticks are the durable audit authority; legacy daily files are historical.
    files = [os.path.join(journal_dir, f) for f in sorted(os.listdir(journal_dir)) if f.endswith(".json")]
    pending = os.path.join(STATE, "tick", "pending.json")
    if os.path.exists(pending):
        files.append(pending)
    return [event for f in files for event in json.load(open(f))["events"]]
before = [e for e in journal_lines() if e["reason"] == "belowJournalFloor"]
t = tick("J", c + 10, "retained", ("happy", "enrol-dust"), enrol_row=True)
dust = [e for e in journal_lines() if e["reason"] == "belowJournalFloor"]
ev = json.load(open(path("tick-J.events.json")))
row("enrollment dust: each below-floor payment is archived once in the journal; nothing minted",
    len(dust) - len(before) == len([e for e in ev if e["reason"] == "belowJournalFloor"]) == 2
    and balance(8) == bal8 and balance(9) == INITIAL,
    f"journal belowJournalFloor +{len(dust) - len(before)}; {summary(t)} (the at-floor enrollment: "
    f"{[l[3] for l in lines(t, 'quarantined')] or 'none'})")

expected8 = INITIAL + sum(credit_for(o["amount"]) for o in (pay1, pay2, pay3))
row("final balances: friend 8 = 100 + creditFor(pay-1, pay-2, pay-3); friend 9 untouched",
    balance(8) == expected8 and balance(9) == INITIAL, f"8={balance(8)} expected={expected8} 9={balance(9)}")
r = mini("pay", "audit", "--dir", OBS)
credited_line = [l for l in r.stdout.splitlines() if l.startswith("credited")]
row("pay audit (online): every credited report is journaled (op 111 replayed)",
    r.returncode == 0 and "FINDING" not in r.stdout and credited_line,
    credited_line[0] if credited_line else r.stderr[-160:])
stop_server()
r = mini("pay", "audit", "--dir", OBS, "--offline", "true")
led = [l for l in r.stdout.splitlines() if l.startswith("ledger")]
row("pay audit (offline): -well_now = -well_genesis + Σ credited; the Host re-admits every record",
    r.returncode == 0 and led and "identity holds" in led[0] and "FINDING" not in r.stdout,
    " | ".join(l for l in r.stdout.splitlines() if l.startswith(("ledger", "host-audit"))) or r.stderr[-200:])

with open(path("rows.tsv"), "w") as out:
    out.write("verdict\tstep\tobserved\n")
    for verdict, name, observed in ROWS: out.write(f"{verdict}\t{name}\t{observed}\n")
passed = sum(1 for v, _, _ in ROWS if v == "PASS")
verdict = f"J-PAY-4 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - STARTED:.1f} s)"
print(verdict); print(path("rows.tsv")); print(verdict, file=sys.stderr)
sys.exit(0 if passed == len(ROWS) else 1)
PY
