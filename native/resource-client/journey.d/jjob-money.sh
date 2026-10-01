#!/usr/bin/env bash
# J-JOB-MONEY (COMPUTE §2.6, lane C3 K-JOB-MONEY): a job's money — the caller's
# escrow, the provider's bond, and the payout or slash — as conservation-checked
# Book turns, on a fresh private Store. The Book holds a job's credit in the
# account whose id is the job cell's id (`pay-job`'s bookHeld); the job cell's
# escrow + bond is the law's view of it, and every row checks the two agree.
#
# Hook contract (journey.sh header): executed with HOST, MINI, STORE, VERIFIER
# and JOURNEY_STEP_DIR exported; it starts its OWN Host on its OWN fresh Store
# under JOURNEY_STEP_DIR and stops it. Exit 0 = PASS. The verdict
# `J-JOB-MONEY PASS n/n` is the last stderr line and the line before the last
# stdout line; the last stdout line is the deciding artifact (rows.tsv).
#
# Job fields are C1 JOB-LAW's (fields.json): state 0, caller 3, callerAcct 4,
# price 5, escrow 8, provider 9, providerAcct 10, bond 11.
#
# Genesis enrolls the operator (subject 7), a caller A (subject/account 20), a
# provider P (subject/account 21) and a stranger (22); A and P hold 60 000 000
# credit of asset 0. The first event births two jobs through `mini serve` +
# `mini submit` with birth storage `job` (the Host authors the order fields and
# the job law `JobMoney.standInLaw`): 7101 and 7102, each ordered by A
# (refund account 20) at a price of 10 000 000, owned by the operator; and a
# forgery, 7103, an ordinary declared object under a law that admits anything,
# whose fields the operator then writes to look like an upheld, funded job. The
# operator installs a two-row book and a tariff (credit asset 0, slash split
# 500 permille); A and P take indexes 0 and 1 so `pay-ledger` lists them.
#
# The money turns drive the Host's raw operations 160-163 (131-134 before the final merge) over stdio, signed
# with PyNaCl, so the hook can also author the refusal poles the decision names
# (notCaller, unbalanced, notFunded, alreadyFunded, bondBelowPrice,
# notTerminal, alreadySettled). Op 162 is a blind submission (MR's rule, as op
# 115): every refusal is the uniform `undisclosed` frame, so each refusal row is
# followed by a row that checks nothing moved.
#
# C1 JOB-LAW (the job's non-money edges: answer, truth, decide) is on a sibling
# branch. Here the operator hand-sets a claimed job's state to 3 (upheld) or 4
# (slashed) with an ordinary declared write, which the stand-in law admits only
# when it changes no money field and never closes the job; the same write
# reaching for the escrow field is refused.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jjob-money: $name is required" >&2; exit 2; fi
done
command -v python3 >/dev/null || { echo "jjob-money: python3 is required" >&2; exit 2; }
python3 -c 'import nacl.signing' 2>/dev/null || { echo "jjob-money: PyNaCl is required" >&2; exit 2; }
DIR="$JOURNEY_STEP_DIR/jjob-money"
if [ -e "$DIR" ]; then echo "jjob-money: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
exec python3 - "$DIR" <<'PY'
import json, os, signal, struct, subprocess, sys, time
import nacl.signing

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
ROWS = []
OPERATOR, CALLER, PROVIDER, STRANGER = 7, 20, 21, 22
FACTORY_CONTROL = 53
JOB, JOB2, FORGED = 7101, 7102, 7103
JOB_CAP = {JOB: 71, JOB2: 81, FORGED: 91}
PRICE, BOND = 10_000_000, 10_000_000
START = 60_000_000
SUBJECTS = [OPERATOR, CALLER, PROVIDER, STRANGER]
CAPS = {OPERATOR: (41, 51, 54), CALLER: (1020, 2020, 3020), PROVIDER: (1021, 2021, 3021),
        STRANGER: (1022, 2022, 3022)}
BALANCE = {OPERATOR: 100, CALLER: START, PROVIDER: START, STRANGER: 100}
FUND, CLAIM, SETTLE = 1, 2, 3

def path(name): return os.path.join(DIR, name)
LIVE = []
def cleanup():
    for proc in LIVE:
        if proc.poll() is None:
            try:
                proc.terminate(); proc.wait(timeout=30)
            except Exception:
                proc.kill()
import atexit
atexit.register(cleanup)
signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
def fail(message):
    print(f"J-JOB-MONEY FAIL: {message}", file=sys.stderr); sys.exit(1)

# ---------------------------------------------------------------- keys and genesis
os.makedirs(path("keys"), mode=0o700)
keys = {}
for s in SUBJECTS:
    keys[s] = nacl.signing.SigningKey.generate()
    fd = os.open(path(f"keys/{s}.key"), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    os.write(fd, bytes(keys[s])); os.close(fd)
def enrollment(s):
    spend, control, observe = CAPS[s]
    return {"key": {"keyId": str(7000 + s if s >= 20 else 1001 * s), "keyEpoch": "2", "algorithm": "1",
                    "subject": str(s), "publicKey": keys[s].verify_key.encode().hex(),
                    "activeFrom": "0", "activeUntil": "1000000", "nextKeyDigest": None},
            "accountId": str(s), "spendCapabilityId": str(spend), "controlCapabilityId": str(control),
            "factoryObserveCapabilityId": str(observe), "initialBalance": str(BALANCE[s]),
            "accountPredicate": {"type": "all", "predicates": []}}
operator = {"domain": 8501, "federation": 9, "factoryId": 10, "resourceBookId": 11,
            "authorityCellId": 12, "issuer": 5, "ownerBudget": 100000, "lifetime": 10000,
            "tariffBase": 3, "tariffPerBirth": 2, "tariffPerGrant": 1,
            "tariffPerInitialPayloadByte": 0, "collector": 99, "asset": 0, "genesisHeight": 10,
            "expectedSeed": 0, "storageBinary": STORE, "storageRoot": path("store"),
            "signatureBinary": VERIFIER}
json.dump(operator, open(path("operator.json"), "w"), indent=1)
profile = json.loads(subprocess.run([HOST, path("operator.json"), "profile"], check=True,
                                    capture_output=True).stdout)
genesis = {"domain": "8501", "factoryId": "10", "resourceBookId": "11", "authorityCellId": "12",
           "federation": "9", "tariffBase": "3", "tariffPerBirth": "2", "tariffPerGrant": "1",
           "tariffPerInitialPayloadByte": "0", "collector": "99", "asset": "0",
           "expectedSemantics": profile["semantics"], "issuerEpoch": "2", "genesisHeight": "10",
           "factoryPredicate": {"type": "all", "predicates": []},
           "enrollments": [enrollment(s) for s in SUBJECTS],
           "factoryControllerSubject": str(OPERATOR),
           "factoryControllerCapability": str(FACTORY_CONTROL),
           "meterAllowance": {k: "10000000" for k in ("incidences", "turnBytes", "memoryTouches",
               "witnessBytes", "proofWork", "storageBytes", "networkBytes", "sideEffectCount",
               "feeDebit", "leaseByteBlocks")}}
json.dump(genesis, open(path("genesis.json"), "w"), indent=1)
boot = subprocess.run([MINI, "bootstrap", "--host", HOST, "--config", path("operator.json"),
                       "--source", path("genesis.json"), "--dir", path("deployment")], capture_output=True)
if boot.returncode != 0:
    fail("bootstrap: " + (boot.stdout + boot.stderr).decode("utf-8", "replace")[-400:])
CONFIG = path("deployment/pinned-config.json")
SEMANTICS = profile["semantics"]

# ---------------------------------------------------------------- mini serve + mini submit (birth, declared writes)
os.makedirs(path("session"), mode=0o700)
SOCKET = path("session/host.sock")
class Serve:
    def __init__(self):
        self.log = open(path("serve.stderr"), "ab")
        self.proc = subprocess.Popen([MINI, "serve", "--host", HOST, "--config", CONFIG, "--socket", SOCKET],
                                     stdout=self.log, stderr=self.log)
        LIVE.append(self.proc)
        for _ in range(1200):
            if os.path.exists(SOCKET): return
            if self.proc.poll() is not None: fail("mini serve exited")
            time.sleep(0.5)
        fail("mini serve socket timeout")
    def stop(self):
        self.proc.terminate(); self.proc.wait(timeout=60); self.log.close()
        if os.path.exists(SOCKET): os.unlink(SOCKET)
def mini_submit(name, intent, signer, kind=None):
    json.dump(intent, open(path(f"{name}-intent.json"), "w"))
    words = [MINI, "submit", "--host", HOST, "--config", CONFIG, "--socket", SOCKET,
             "--intent", path(f"{name}-intent.json"), "--key", path(f"keys/{signer}.key"),
             "--dir", path(f"{name}-attempt")]
    if kind: words[words.index("--intent"):words.index("--intent")] = ["--intent-kind", kind]
    done = subprocess.run(words, capture_output=True)
    open(path(f"{name}.stderr"), "wb").write(done.stdout + done.stderr)
    try: return json.load(open(path(f"{name}-attempt/outcome.json")))
    except (OSError, ValueError): return {"type": "no-outcome", "exit": done.returncode}

def job_birth(target, caps):
    owner_cap, control_cap = caps
    return {"kind": "object", "storage": "job", "target": str(target), "owner": str(OPERATOR),
            "ownerCapability": str(owner_cap), "controlCapability": str(control_cap),
            "caller": str(CALLER), "callerAcct": str(CALLER), "price": str(PRICE)}
birth = {"subject": str(OPERATOR), "nonce": "22000",
         "birth": {"genesis": genesis, "template": {"issuer": "5", "ownerBudget": "100000", "lifetime": "10000"},
                   "creator": str(OPERATOR), "nonce": "22000",
                   "resources": [job_birth(JOB, (71, 72)), job_birth(JOB2, (81, 82)),
                       {"kind": "object", "storage": "declared", "target": str(FORGED), "owner": str(OPERATOR),
                        "ownerCapability": "91", "controlCapability": "92",
                        "predicate": {"type": "all", "predicates": []}}],
                   "sourceCapabilities": ["41"], "funding": [], "feePayer": "7"},
         "grants": [{"kind": "object", "target": "10", "capability": "54"},
                    {"kind": "account", "target": "7", "capability": "41"}]}

# ---------------------------------------------------------------- Host plumbing (the jpay6 pattern)
def cli(*words):
    return subprocess.run([HOST, CONFIG, *words], check=True, capture_output=True)
counter = [0]
def scratch(stem):
    counter[0] += 1
    return path(f"work/{counter[0]:04d}-{stem}")
os.makedirs(path("work"))
def author(kind, value):
    source, out = scratch(kind + ".json"), scratch(kind + ".bin")
    json.dump(value, open(source, "w"))
    cli("author", kind, source, out)
    return open(out, "rb").read()
def inspect(kind, data):
    source, out = scratch(kind + ".bin"), scratch(kind + ".json")
    open(source, "wb").write(data)
    cli("inspect", kind, source, out)
    return json.load(open(out))
def ledger():
    out = scratch("ledger.json"); cli("pay-ledger", out); return json.load(open(out))
def job(target=JOB):
    out = scratch("job.json"); cli("pay-job", str(target), out); return json.load(open(out))
def balance(led, account):
    for r in led["payers"]:
        if r["account"] == str(account): return int(r["balance"])
    fail(f"account {account} not in ledger")
def circulating(led): return int(led["total"]) - int(led["well"])

class Host:
    def __init__(self):
        self.log = open(path("host.stderr"), "ab")
        self.proc = subprocess.Popen([HOST, CONFIG, "stdio"], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=self.log)
        LIVE.append(self.proc)
    def call(self, op, payload=b""):
        frame = bytes([op]) + payload
        self.proc.stdin.write(struct.pack("<I", len(frame)) + frame); self.proc.stdin.flush()
        header = self.proc.stdout.read(4)
        if len(header) != 4: fail(f"host closed on op {op}")
        body = self.proc.stdout.read(struct.unpack("<I", header)[0])
        return body[0], body[1:]
    def stop(self):
        self.proc.stdin.close(); self.proc.wait(timeout=60); self.log.close()

def outcome(data):
    view = inspect("outcome", data)
    for field in ("phase", "detail"):
        if field in view: view[field] = bytes.fromhex(view[field]).decode("utf-8", "replace")
    return view
def view(host):
    op, data = host.call(107)
    if op != 107: fail(f"pay view failed: {data!r}")
    return inspect("pay-view", data)
def sign_and_submit(host, kind, command, signer, ops):
    plan_op, assemble_op, submit_op = ops
    op, plan = host.call(plan_op, author(kind, command))
    if op != plan_op: return {"type": "plan-failed", "detail": plan[-200:].decode("utf-8", "replace")}, None
    header = bytes.fromhex(inspect("pay-plan", plan)["header"]["canonical"])
    signature = keys[signer].sign(header).signature
    op, ingress = host.call(assemble_op, struct.pack("<I", len(plan)) + plan + signature)
    if op != assemble_op: fail(f"assembly failed: {ingress!r}")
    op, result = host.call(submit_op, ingress)
    if op != submit_op: fail(f"submit failed: {result!r}")
    return outcome(result), ingress
PAY_OPS, JOB_OPS = (103, 104, 105), (160, 161, 162)

def row(name, expected, observed, ok):
    observed = " ".join(str(observed).split())
    ROWS.append((name, expected, observed, "PASS" if ok else "FAIL"))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{observed}", file=sys.stderr)
def refused_with(result, reason):
    # `reason` names the branch the command was built to hit; the blind wire
    # answers `undisclosed`, and the next row checks that nothing moved.
    return result.get("type") == "refused" and result.get("reason") == "undisclosed"
def show(result): return f"{result.get('type')} {result.get('reason', '')} {result.get('detail', '')}".strip()

nonce = [100]
def fresh():
    nonce[0] += 1; return str(nonce[0])
def money(host, signer, capability, target, action, account, amount):
    command = {"subject": str(signer), "capability": str(capability), "job": str(target),
               "action": str(action), "account": str(account), "amount": str(amount),
               "nonce": fresh(), "expectedAuthorityRoot": view(host)["authorityRoot"]}
    return sign_and_submit(host, "job-money", command, signer, JOB_OPS)
def fund(host, target=JOB, signer=CALLER, amount=PRICE):
    return money(host, signer, CAPS[signer][0], target, FUND, signer, amount)
def claim(host, target=JOB, signer=PROVIDER, amount=BOND):
    return money(host, signer, CAPS[signer][0], target, CLAIM, signer, amount)
def settle(host, target=JOB, signer=OPERATOR, capability=None):
    return money(host, signer, JOB_CAP[target] if capability is None else capability, target, SETTLE, 0, 0)
def money_fields(j):
    return f"state={j['state']} escrow={j['escrow']} provider={j['provider']} providerAcct={j['providerAcct']} bond={j['bond']} held={j['held']} bookHeld={j['bookHeld']}"
def agrees(j): return j["held"] == j["bookHeld"]
def all_held(): return sum(int(job(t)["bookHeld"]) for t in (JOB, JOB2))
def outside(led, held): return int(led["total"]) - int(led["well"]) - held

query_nonce = [40000]
def mini_query(name, subject, target, capability):
    query_nonce[0] += 1
    intent = {"subject": str(subject), "nonce": str(query_nonce[0]),
              "purpose": {"type": "query", "kind": "object", "target": str(target), "view": "resource"},
              "grants": [{"kind": "object", "target": str(target), "capability": str(capability)}]}
    json.dump(intent, open(path(f"{name}-query.json"), "w"))
    done = subprocess.run([MINI, "query", "--host", HOST, "--config", CONFIG, "--socket", SOCKET,
                           "--intent", path(f"{name}-query.json"), "--key", path(f"keys/{subject}.key"),
                           "--view", "resource", "--dir", path(f"{name}-query")], capture_output=True)
    if done.returncode != 0:
        fail(f"query {name}: " + (done.stdout + done.stderr).decode("utf-8", "replace")[-300:])
    view = json.load(open(path(f"{name}-query/view.json")))
    return view.get("cell") or view.get("page")

decl_nonce = [50000]
def hand_set(name, target, field, expected, value):
    """The operator's ordinary declared write of one job field (stand-in for C1's law edges)."""
    j = job(target)
    decl_nonce[0] += 2
    command = {"subject": str(OPERATOR), "nonce": str(decl_nonce[0] + 1), "targets": [
        {"kind": "object", "target": str(target), "capability": str(JOB_CAP[target]),
         "observeCapability": None, "schemaVersion": "1", "expectedTargetRoot": j["root"],
         "payload": {"type": "scalar", "actions": [
             {"type": "write", "key": {"type": "object", "resource": str(target), "field": str(field)},
              "expected": str(expected), "value": str(value)}]}}]}
    intent = {"subject": str(OPERATOR), "nonce": str(decl_nonce[0]),
              "purpose": {"type": "prepare", "draft": {"type": "invoke", "command": command}},
              "grants": [{"kind": "object", "target": str(target), "capability": str(JOB_CAP[target])}]}
    serve = Serve()
    try: return mini_submit(name, intent, OPERATOR)
    finally: serve.stop()

def forge(name, target, fields):
    """The operator creates job-shaped fields on an ordinary declared object (its law admits anything)."""
    serve = Serve()
    try:
        cell = mini_query(name + "-pre", OPERATOR, target, JOB_CAP[target])
        decl_nonce[0] += 2
        command = {"subject": str(OPERATOR), "nonce": str(decl_nonce[0] + 1), "targets": [
            {"kind": "object", "target": str(target), "capability": str(JOB_CAP[target]),
             "observeCapability": None, "schemaVersion": "1", "expectedTargetRoot": cell["root"],
             "payload": {"type": "scalar", "actions": [
                 {"type": "create", "key": {"type": "object", "resource": str(target), "field": str(f)},
                  "value": str(v)} for f, v in fields]}}]}
        intent = {"subject": str(OPERATOR), "nonce": str(decl_nonce[0]),
                  "purpose": {"type": "prepare", "draft": {"type": "invoke", "command": command}},
                  "grants": [{"kind": "object", "target": str(target), "capability": str(JOB_CAP[target])}]}
        return mini_submit(name, intent, OPERATOR)
    finally: serve.stop()

# ---------------------------------------------------------------- the journey
started = time.time()
serve = Serve()
born = mini_submit("birth", birth, OPERATOR, kind="birth-intent")
serve.stop()
row("job birth (7101, 7102; storage job: the Host authors the order fields and the job law; 7103 an ordinary declared object) is the first event",
    "confirmed installed", f"{born.get('type')} {born.get('confirmation')}",
    born.get("type") == "confirmed" and born.get("confirmation") == "installed")
j0 = job()
row("job 7101 at birth: ordered by A (refund account 20) at price 10 000 000, nothing held",
    "state 0, caller 20, callerAcct 20, price 10000000, escrow 0, provider 0, bond 0, Book holds 0",
    f"caller={j0['caller']} callerAcct={j0['callerAcct']} price={j0['price']} " + money_fields(j0),
    (j0["state"], j0["caller"], j0["callerAcct"], j0["price"], j0["escrow"], j0["provider"], j0["bond"],
     j0["bookHeld"]) == ("0", "20", "20", str(PRICE), "0", "0", "0", "0"))

host = Host()
r, _ = fund(host)
row("fund before a valid tariff (the credit asset and slash split are the tariff's)",
    "refused undisclosed (built to hit tariffInvalid)", show(r), refused_with(r, "tariffInvalid"))
v = view(host)
tariff = {"version": "1", "asset": "0", "mint": "85" * 32, "tokenProgram": "06" * 32, "decimals": "6",
          "creditPerAtomic": "1", "maxPerObservation": "2000000000", "minTickSlots": "1500",
          "nodeHourRate": "5952380", "enrolIndex": None, "journalFloor": "1000000",
          "slashCallerPermille": "500"}
book_cmd = {"sponsor": str(OPERATOR), "control": str(FACTORY_CONTROL), "nonce": fresh(),
            "expectedFactoryRoot": v["factoryRoot"], "expectedAuthorityRoot": v["authorityRoot"],
            "expectedPayRoot": v["payRoot"], "bookStart": "0", "book": ["16" * 32, "17" * 32], "tariff": tariff}
r, _ = sign_and_submit(host, "pay-book", book_cmd, OPERATOR, PAY_OPS)
row("operator installs a two-row book and a tariff (credit asset 0, slash split 500 permille)",
    "confirmed", show(r), r.get("type") == "confirmed")
for who, index in ((CALLER, 0), (PROVIDER, 1)):
    v = view(host)
    assign = {"subject": str(who), "capability": str(CAPS[who][0]), "account": str(who), "index": str(index),
              "nonce": fresh(), "expectedAuthorityRoot": v["authorityRoot"], "expectedPayRoot": v["payRoot"]}
    r, _ = sign_and_submit(host, "pay-assign", assign, who, PAY_OPS)
    row(f"account {who} takes index {index}", "confirmed", show(r), r.get("type") == "confirmed")
host.stop()
led0 = ledger()
row("ledger before any job money", f"A {START}, P {START}",
    f"A={balance(led0, CALLER)} P={balance(led0, PROVIDER)} well={led0['well']} total={led0['total']}",
    balance(led0, CALLER) == START and balance(led0, PROVIDER) == START)

# ---- refusal poles before funding
host = Host()
r, _ = fund(host, signer=STRANGER)
row("a stranger (subject 22, its own account) funds A's job", "refused undisclosed (built to hit notCaller)",
    show(r), refused_with(r, "notCaller"))
r, _ = fund(host, amount=PRICE - 1_000_000)
row("A funds 9 000 000 against a 10 000 000 price", "refused undisclosed (built to hit unbalanced: the joint commit)",
    show(r), refused_with(r, "unbalanced"))
r, _ = claim(host)
row("P claims an unfunded job", "refused undisclosed (built to hit notFunded)", show(r), refused_with(r, "notFunded"))
r, _ = settle(host)
row("the operator settles an open job", "refused undisclosed (built to hit notTerminal)", show(r),
    refused_with(r, "notTerminal"))
host.stop()
led_p, j_p = ledger(), job()
row("the refused turns moved nothing", "ledger and job unchanged",
    f"A={balance(led_p, CALLER)} P={balance(led_p, PROVIDER)} well={led_p['well']} job root equal={j_p['root'] == j0['root']}",
    led_p == led0 and j_p == j0)

# ---- FUND
host = Host()
r, fund_ingress = fund(host)
row("A funds job 7101 with the price (into the job's held account and its escrow field, one joint turn)", "confirmed",
    show(r), r.get("type") == "confirmed")
op, data = host.call(163, fund_ingress)
looked = outcome(data) if op == 163 else {"type": "op-failed"}
row("receipt-only lookup of that fund (op 163)", "confirmed replayed",
    f"{looked.get('type')} {looked.get('confirmation')}",
    looked.get("type") == "confirmed" and looked.get("confirmation") == "replayed")
op, data = host.call(162, fund_ingress)
again = outcome(data) if op == 162 else {"type": "op-failed"}
row("the same signed fund submitted again", "confirmed replayed (no second burn)",
    f"{again.get('type')} {again.get('confirmation')}",
    again.get("type") == "confirmed" and again.get("confirmation") == "replayed")
r, _ = fund(host)
row("A funds job 7101 a second time (a fresh command)", "refused undisclosed (built to hit alreadyFunded)",
    show(r), refused_with(r, "alreadyFunded"))
host.stop()
led1, j1 = ledger(), job()
row("Book after the fund: A -10 000 000 into job 7101's held account; well and total unchanged",
    "A 50000000, bookHeld 10000000", f"A={balance(led1, CALLER)} bookHeld={j1['bookHeld']} well {led0['well']} -> {led1['well']} total {led0['total']} -> {led1['total']}",
    balance(led1, CALLER) == START - PRICE and j1["bookHeld"] == str(PRICE) and led1["well"] == led0["well"]
    and led1["total"] == led0["total"])
row("job 7101 after the fund: escrow = price, the cell and the Book agree, nothing else moved",
    "state 0 escrow 10000000 provider 0 bond 0 held 10000000 = bookHeld", money_fields(j1),
    (j1["state"], j1["escrow"], j1["provider"], j1["bond"], j1["held"]) == ("0", str(PRICE), "0", "0", str(PRICE))
    and agrees(j1))
row("the fund's joint delta: dheld + dcirculating = 0 (the well does not move)", "held +10000000, circulating -10000000",
    f"held={int(j1['held']) - int(j0['held'])} circulating={outside(led1, int(j1['bookHeld'])) - outside(led0, 0)}",
    int(j1["held"]) - int(j0["held"]) + outside(led1, int(j1["bookHeld"])) - outside(led0, 0) == 0)

# ---- CLAIM (the provider's bond)
host = Host()
r, _ = claim(host, amount=BOND - 1_000_000)
row("P claims with a 9 000 000 bond against a 10 000 000 price", "refused undisclosed (built to hit bondBelowPrice)",
    show(r), refused_with(r, "bondBelowPrice"))
r, _ = claim(host)
row("P claims job 7101, bonding 10 000 000 (bond >= price, moved into the held account in the same turn)", "confirmed",
    show(r), r.get("type") == "confirmed")
host.stop()
led2, j2 = ledger(), job()
row("Book after the claim: P -10 000 000 into the held account; well and total unchanged", "P 50000000, bookHeld 20000000",
    f"P={balance(led2, PROVIDER)} bookHeld={j2['bookHeld']} well {led1['well']} -> {led2['well']} total {led1['total']} -> {led2['total']}",
    balance(led2, PROVIDER) == START - BOND and j2["bookHeld"] == str(PRICE + BOND)
    and led2["well"] == led1["well"] and led2["total"] == led1["total"])
row("job 7101 after the claim: state 1, provider 21 on account 21, bond 10 000 000, held 20 000 000 = bookHeld",
    "state 1 provider 21 providerAcct 21 bond 10000000 held 20000000", money_fields(j2),
    (j2["state"], j2["provider"], j2["providerAcct"], j2["bond"], j2["held"]) ==
    ("1", "21", "21", str(BOND), str(PRICE + BOND)) and agrees(j2))
row("the claim's joint delta: dheld + dcirculating = 0", "held +10000000, circulating -10000000",
    f"held={int(j2['held']) - int(j1['held'])} circulating={outside(led2, int(j2['bookHeld'])) - outside(led1, int(j1['bookHeld']))}",
    int(j2["held"]) - int(j1["held"]) + outside(led2, int(j2["bookHeld"])) - outside(led1, int(j1["bookHeld"])) == 0)

# ---- the stand-in for C1's law: a hand-set terminal state; money fields are not the law's to write
r = hand_set("handset-escrow", JOB, 8, PRICE, 0)
j_e = job()
denied = open(path("handset-escrow.stderr"), "rb").read().decode("utf-8", "replace").splitlines()
denied = denied[0][:40] if denied else ""
row("the operator's ordinary write of job 7101's escrow field (no money slot)",
    "refused law-denied at prepare (stand-in law: money is frozen without the money slot); job unchanged",
    f"{show(r)} [{denied}] escrow={j_e['escrow']}",
    r.get("type") != "confirmed" and denied.startswith("refused: law-denied") and j_e == j2)
r = hand_set("handset-upheld", JOB, 0, 1, 3)
j3 = job()
row("operator hand-sets job 7101 to state 3 (upheld; C1's decide edge is on a sibling branch)",
    "confirmed, state 3, money unchanged", f"{show(r)} " + money_fields(j3),
    r.get("type") == "confirmed" and j3["state"] == "3" and j3["held"] == j2["held"])

# ---- SETTLE: upheld
host = Host()
r, _ = settle(host, signer=STRANGER, capability=CAPS[STRANGER][0])
row("a stranger settles with no capability on the job", "refused undisclosed (built to hit capabilityRejected)",
    show(r), refused_with(r, "capabilityRejected"))
r, _ = settle(host)
row("settle job 7101 (upheld): payouts leave the held account, a pure function of the job", "confirmed",
    show(r), r.get("type") == "confirmed")
r, _ = settle(host)
row("settle job 7101 again", "refused undisclosed (built to hit alreadySettled)", show(r),
    refused_with(r, "alreadySettled"))
host.stop()
led3, j4 = ledger(), job()
row("Book after the upheld settle: P paid exactly price + bond out of the held account, A nothing back",
    "P 50000000 -> 70000000 (net +price), A 50000000, well and total unchanged",
    f"P={balance(led3, PROVIDER)} A={balance(led3, CALLER)} well {led2['well']} -> {led3['well']} total {led2['total']} -> {led3['total']}",
    balance(led3, PROVIDER) == START - BOND + PRICE + BOND and balance(led3, CALLER) == START - PRICE
    and led3["well"] == led2["well"] and led3["total"] == led2["total"])
row("job 7101 closed and empty, in the cell and in the Book", "state 6 escrow 0 bond 0 held 0 bookHeld 0", money_fields(j4),
    (j4["state"], j4["escrow"], j4["bond"], j4["held"], j4["bookHeld"]) == ("6", "0", "0", "0", "0"))
row("the settle's joint delta: dheld + dcirculating = 0 (nothing retired)", "held -20000000, circulating +20000000",
    f"held={int(j4['held']) - int(j3['held'])} circulating={outside(led3, 0) - outside(led2, int(j3['bookHeld']))}",
    int(j4["held"]) - int(j3["held"]) + outside(led3, 0) - outside(led2, int(j3["bookHeld"])) == 0)

# ---- job 7102: fund, claim, a mismatch, slash
host = Host()
r1, _ = fund(host, target=JOB2)
r2, _ = claim(host, target=JOB2)
host.stop()
row("A funds and P claims job 7102 (10 000 000 each)", "confirmed confirmed", f"{show(r1)} / {show(r2)}",
    r1.get("type") == "confirmed" and r2.get("type") == "confirmed")
r = hand_set("handset-slashed", JOB2, 0, 1, 4)
row("operator hand-sets job 7102 to state 4 (slashed: truth differs from the output)", "confirmed", show(r),
    r.get("type") == "confirmed")
led4, k4 = ledger(), job(JOB2)
host = Host()
r, _ = settle(host, target=JOB2)
row("settle job 7102 (slashed)", "confirmed", show(r), r.get("type") == "confirmed")
host.stop()
led5, k5 = ledger(), job(JOB2)
SHARE = BOND * 500 // 1000
row("Book after the slash: A gets escrow + half the bond, P nothing; the other half is burned into the well",
    f"A +{PRICE + SHARE}, P +0, well +{BOND - SHARE}, total unchanged",
    f"A {balance(led4, CALLER)} -> {balance(led5, CALLER)} P {balance(led4, PROVIDER)} -> {balance(led5, PROVIDER)} well {led4['well']} -> {led5['well']}",
    balance(led5, CALLER) == balance(led4, CALLER) + PRICE + SHARE and balance(led5, PROVIDER) == balance(led4, PROVIDER)
    and int(led5["well"]) == int(led4["well"]) + (BOND - SHARE) and led5["total"] == led4["total"])
row("the slash's legs: dheld + dcirculating + dwell = 0; the retired share is in the well",
    f"held -{PRICE + BOND}, circulating +{PRICE + SHARE}, well +{BOND - SHARE}",
    f"held={int(k5['held']) - int(k4['held'])} circulating={outside(led5, 0) - outside(led4, int(k4['bookHeld']))} well={int(led5['well']) - int(led4['well'])} " + money_fields(k5),
    int(k5["held"]) - int(k4["held"]) + outside(led5, 0) - outside(led4, int(k4["bookHeld"])) + int(led5["well"]) - int(led4["well"]) == 0
    and k5["state"] == "6" and k5["held"] == "0" and k5["bookHeld"] == "0")

# ---- a forgery: job-shaped fields on an ordinary declared object pay nothing
r = forge("forge", FORGED, [(0, 3), (3, CALLER), (4, CALLER), (5, PRICE), (8, PRICE), (9, PROVIDER),
                            (10, PROVIDER), (11, BOND)])
f0 = job(FORGED)
row("the operator writes upheld, funded job fields onto 7103 (its law admits anything)",
    "confirmed; the cell claims 20000000 held, the Book holds 0", f"{show(r)} " + money_fields(f0),
    r.get("type") == "confirmed" and f0["held"] == str(PRICE + BOND) and f0["bookHeld"] == "0")
led_f = ledger()
host = Host()
r, _ = settle(host, target=FORGED)
row("settle the forged job 7103", "refused undisclosed (built to hit notJobLaw; heldMismatch behind it)", show(r),
    refused_with(r, "notJobLaw"))
host.stop()
led_g = ledger()
row("the forgery minted and moved nothing", "ledger unchanged", f"P={balance(led_g, PROVIDER)} well={led_g['well']}",
    led_g == led_f)

# ---- the identities on this Store
RETIRED = BOND - SHARE
row("ledger identity: -well_h = -well_0 + credited - refilled - retired",
    f"-well_h = {-int(led0['well'])} + 0 - 0 - {RETIRED}",
    f"-well_h={-int(led5['well'])}",
    -int(led5["well"]) == -int(led0["well"]) - RETIRED)
held_h = all_held()
row("conservation over the well: circulating_h + held_h + retired = circulating_0 (both jobs closed)",
    f"{outside(led0, 0)}", f"{outside(led5, held_h)} + {held_h} + {RETIRED} = {outside(led5, held_h) + held_h + RETIRED}",
    outside(led5, held_h) + held_h + RETIRED == outside(led0, 0) and held_h == 0)
row("totals: the Book's total in credit (well included) never moved", f"{led0['total']}",
    f"{led5['total']}", led5["total"] == led0["total"])
audit = subprocess.run([HOST, CONFIG, "audit"], capture_output=True)
audit_text = (audit.stdout + audit.stderr).decode("utf-8", "replace").strip().splitlines()
row("operator audit re-admits every record (NativeHostReplay, incl. every job-money turn)", "exit 0",
    f"exit={audit.returncode} {audit_text[-1] if audit_text else ''}", audit.returncode == 0)

rows_path = path("rows.tsv")
with open(rows_path, "w") as out:
    out.write("verdict\tstep\texpected\tobserved\n")
    for name, expected, observed, verdict in ROWS:
        out.write(f"{verdict}\t{name}\t{expected}\t{observed}\n")
passed = sum(1 for r in ROWS if r[3] == "PASS")
verdict = f"J-JOB-MONEY {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - started:.1f} s)"
print(verdict)
print(verdict, file=sys.stderr)
print(rows_path)
sys.exit(0 if passed == len(ROWS) else 1)
PY
