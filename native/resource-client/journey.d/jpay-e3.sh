#!/usr/bin/env bash
# J-PAY-E3 (PAY.md §11.9 P3b-2): the self-enrollment RECEIVER on a fresh Store.
#
# Follows the journey hook contract (journey.sh header): executed with HOST,
# MINI, STORE, VERIFIER and JOURNEY_STEP_DIR exported; it starts its OWN Host on
# its OWN fresh Store under JOURNEY_STEP_DIR and stops it. Exit 0 = PASS. The
# verdict `J-PAY-E3 PASS n/n` is the last stderr line and the line before the
# last stdout line; the last stdout line is the deciding artifact (rows.tsv).
# VERIFIER must have the `verify-sshsig` verb (P3b-1 or later).
#
# The observer (subject 30) submits watcher records for the enrollment index 0
# through the Host's raw operations 117-120 (plan, detached assembly, submit,
# receipt-only lookup), signed with its `C_enrol` (4032). The records follow P1b's
# enrollment vectors (enrol-happy, the same memo twice, dust, two memos, no memo,
# a malformed memo) in P1's record shape; every signed memo is REAL, made in
# this run: a PyNaCl Mini key, `ssh-keygen -t ed25519` and `ssh-keygen -Y sign
# -n dregg-enrol@v1` (P1b's fixture memos carry placeholder signatures).
#
# Checked: the enrollment's subject, account, funding, book index, lease and ssh
# row; the renewal; the consumed nullifier; every journal reason with the Book
# unchanged; a verifier failure refused (not journaled); the new subject reading
# its own account (admitted) and another friend's (refused); the observer's
# factory policy install and factory observation refused by the confined factory law
# (the install never reaches the install receiver: its plan must first observe the
# factory, which the law refuses the observer); cold reopen equal;
# the operator audit re-admitting every record.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jpay-e3: $name is required" >&2; exit 2; fi
done
command -v python3 >/dev/null || { echo "jpay-e3: python3 is required" >&2; exit 2; }
command -v ssh-keygen >/dev/null || { echo "jpay-e3: ssh-keygen is required" >&2; exit 2; }
python3 -c 'import nacl.signing' 2>/dev/null || { echo "jpay-e3: PyNaCl is required" >&2; exit 2; }
DIR="$JOURNEY_STEP_DIR/jpay-e3"
if [ -e "$DIR" ]; then echo "jpay-e3: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
exec python3 - "$DIR" <<'PY'
import base64, json, os, struct, subprocess, sys, time
import nacl.signing

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
ROWS = []
EMBER, FACTORY, BOOK_ID, AUTH_ID, FACTORY_CONTROL = 7, 10, 11, 12, 53
OBSERVER, OBSERVER_CAP, PAY_CONTROL, ENROL_CAP = 30, 4030, 4031, 4032
FLOAT, FRIEND = 20, 40
SUBJECTS = [EMBER, FLOAT, OBSERVER, FRIEND]
def acct(s): return 100 + s
COLLECTOR = 99

P1_ADDRESS = "16946aa663362d557dd21ee08e8da60c2ea8a73467713c7c5205991e36634af5"
P1_MINT = "8525966c00f39ff54ef5e537a4736af436494d1f1681c659bd98e37ac28beff1"
P1_PROGRAM = "06ddf6e1ee758fde18425dbce46ccddab61afc4d83b90d27febdf928d8a18bfc"
WEEK = 999999840
# The factory tariff below: base 3 + perBirth 2 + 2 grants x perGrant 1 + 0 per byte.
BIRTH_FEE = 3 + 2 + 2
PRICE = BIRTH_FEE + WEEK
FLOOR = 1000000

def path(name): return os.path.join(DIR, name)
def fail(message):
    print(f"J-PAY-E3 FAIL: {message}", file=sys.stderr); sys.exit(1)
def row(name, expected, observed, ok):
    observed = " ".join(str(observed).split())
    ROWS.append((name, expected, observed, "PASS" if ok else "FAIL"))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{observed}", file=sys.stderr)
started = time.time()

# ---------------------------------------------------------------- genesis
keys = {s: nacl.signing.SigningKey.generate() for s in SUBJECTS}
for s in SUBJECTS:
    with open(path(f"subject-{s}.key"), "wb") as out: out.write(keys[s].encode())
def enrollment(s):
    return {"key": {"keyId": str(7000 + s), "keyEpoch": "2", "algorithm": "1", "subject": str(s),
                    "publicKey": keys[s].verify_key.encode().hex(), "activeFrom": "0",
                    "activeUntil": "1000000", "nextKeyDigest": None},
            "accountId": str(acct(s)), "spendCapabilityId": str(1000 + s),
            "controlCapabilityId": str(2000 + s), "factoryObserveCapabilityId": str(3000 + s),
            "initialBalance": "100", "accountPredicate": {"type": "all", "predicates": []}}
operator = {"domain": 8501, "federation": 9, "factoryId": FACTORY, "resourceBookId": BOOK_ID,
            "authorityCellId": AUTH_ID, "issuer": 5, "ownerBudget": 100000, "lifetime": 10000,
            "tariffBase": 3, "tariffPerBirth": 2, "tariffPerGrant": 1,
            "tariffPerInitialPayloadByte": 0, "collector": COLLECTOR, "asset": 0, "genesisHeight": 10,
            "expectedSeed": 0, "storageBinary": STORE, "storageRoot": path("store"),
            "signatureBinary": VERIFIER}
json.dump(operator, open(path("operator.json"), "w"), indent=1)
profile = json.loads(subprocess.run([HOST, path("operator.json"), "profile"], check=True,
                                    capture_output=True).stdout)
SEMANTICS = profile["semantics"]
genesis = {"domain": "8501", "factoryId": str(FACTORY), "resourceBookId": str(BOOK_ID),
           "authorityCellId": str(AUTH_ID), "federation": "9", "tariffBase": "3",
           "tariffPerBirth": "2", "tariffPerGrant": "1", "tariffPerInitialPayloadByte": "0",
           "collector": str(COLLECTOR), "asset": "0", "expectedSemantics": SEMANTICS,
           "issuerEpoch": "2", "genesisHeight": "10",
           "factoryPredicate": {"type": "all", "predicates": []},
           "enrollments": [enrollment(s) for s in SUBJECTS],
           "factoryControllerSubject": str(EMBER),
           "factoryControllerCapability": str(FACTORY_CONTROL),
           "meterAllowance": {k: "10000000" for k in ("incidences", "turnBytes", "memoryTouches",
               "witnessBytes", "proofWork", "storageBytes", "networkBytes", "sideEffectCount",
               "feeDebit", "leaseByteBlocks")},
           "payObserver": {"subject": str(OBSERVER), "capability": str(OBSERVER_CAP),
                           "controlCapability": str(PAY_CONTROL), "enrolCapability": str(ENROL_CAP)}}
json.dump(genesis, open(path("genesis.json"), "w"), indent=1)
boot = subprocess.run([MINI, "bootstrap", "--host", HOST, "--config", path("operator.json"),
                       "--source", path("genesis.json"), "--dir", path("deployment")], capture_output=True)
if boot.returncode != 0:
    fail("bootstrap: " + (boot.stdout + boot.stderr).decode("utf-8", "replace")[-400:])
CONFIG = path("deployment/pinned-config.json")
described = json.loads(subprocess.run([HOST, CONFIG, "describe"], check=True, capture_output=True).stdout)
PAY_CELL = described["payCell"]

# ---------------------------------------------------------------- Host plumbing
def cli(*words, config=None):
    return subprocess.run([HOST, config or CONFIG, *words], check=True, capture_output=True)
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
class Host:
    def __init__(self, config=None):
        self.log = open(path("host.stderr"), "ab")
        self.proc = subprocess.Popen([HOST, config or CONFIG, "stdio"], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=self.log)
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
    result = inspect("outcome", data)
    for field in ("phase", "detail"):
        if field in result: result[field] = bytes.fromhex(result[field]).decode("utf-8", "replace")
    return result
def view(host):
    op, data = host.call(107)
    if op != 107: fail(f"pay view failed: {data!r}")
    return inspect("pay-view", data)
def enrolment_view(host):
    op, data = host.call(112)
    if op != 112: fail(f"enrolment view failed: {data!r}")
    return inspect("pay-enrolment-view", data)
def sign_and_submit(host, kind, command, signer, ops):
    plan_op, assemble_op, submit_op = ops
    op, plan = host.call(plan_op, author(kind, command))
    if op != plan_op: return {"type": "plan-failed", "detail": plan[-300:].decode("utf-8", "replace")}, None
    header = bytes.fromhex(inspect("pay-plan", plan)["header"]["canonical"])
    signature = keys[signer].sign(header).signature
    op, ingress = host.call(assemble_op, struct.pack("<I", len(plan)) + plan + signature)
    if op != assemble_op: fail(f"assembly failed: {ingress!r}")
    op, result = host.call(submit_op, ingress)
    if op != submit_op: fail(f"submit failed: {result!r}")
    return outcome(result), ingress
PAY_OPS, ENROL_OPS = (103, 104, 105), (117, 118, 119)
def show(result): return f"{result.get('type')} {result.get('detail', '')}".strip()
def refused(result, reason):
    return result.get("type") == "refused" and reason in result.get("detail", "")
nonce = [500]
def fresh():
    nonce[0] += 1
    return str(nonce[0])
def ledger():
    out = scratch("ledger.json")
    cli("pay-ledger", out)
    return json.load(open(out))
def balance(led, account):
    for r in led["payers"]:
        if r["account"] == str(account): return int(r["balance"])
    return None

# ---------------------------------------------------------------- memos (real signatures)
mint, address = bytes.fromhex(P1_MINT), bytes.fromhex(P1_ADDRESS)
def make_memo(label):
    mini = nacl.signing.SigningKey.generate()
    ssh_dir = path(f"ssh-{label}"); os.makedirs(ssh_dir)
    subprocess.run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", f"jpay-e3-{label}", "-f",
                    os.path.join(ssh_dir, "key")], check=True)
    blob = base64.b64decode(open(os.path.join(ssh_dir, "key.pub")).read().split()[1])
    open(os.path.join(ssh_dir, "message"), "wb").write(mint + address + mini.verify_key.encode())
    subprocess.run(["ssh-keygen", "-Y", "sign", "-n", "dregg-enrol@v1", "-f", os.path.join(ssh_dir, "key"),
                    os.path.join(ssh_dir, "message")], check=True, capture_output=True)
    armour = open(os.path.join(ssh_dir, "message.sig")).read()
    body = base64.b64decode("".join(l for l in armour.splitlines() if not l.startswith("-----")))
    ssh_sig = body[-64:]
    mini_sig = mini.sign(b"DREGG/PAY/ENROL/POSSESSION/v1" + mint + address + blob).signature
    memo = ("enrol:v1:" + mini.verify_key.encode().hex() + ":" + base64.b64encode(blob).decode().rstrip("=")
            + ":" + mini_sig.hex() + ":" + ssh_sig.hex())
    return mini, blob, memo
def flip(memo, at):
    c = memo[at]
    return memo[:at] + ("0" if c != "0" else "1") + memo[at + 1:]

TX = [0]
def record(amount, memo=None, memo_error=None, signature=None, slot=None):
    TX[0] += 1
    s = slot if slot is not None else 800 + TX[0]
    return {"index": 0, "address": P1_ADDRESS,
            "signature": signature or (f"{TX[0]:02x}" * 64)[:128], "slot": s,
            "blockTime": 1799999000 + s, "amount": amount, "mint": P1_MINT, "tokenProgram": P1_PROGRAM,
            "memo": None if memo is None else memo.encode().hex(), "memoError": memo_error}
TIP = [2000]
def tip():
    TIP[0] += 1
    return {"slot": TIP[0], "blockTime": 1800000000 + TIP[0]}
def enrol(host, rec, config_tip=None):
    v = view(host)
    command = {"observer": str(OBSERVER), "capability": str(ENROL_CAP), "nonce": fresh(),
               "expectedAuthorityRoot": v["authorityRoot"], "expectedPayRoot": v["payRoot"],
               "tip": config_tip or tip(), "observation": rec}
    return sign_and_submit(host, "pay-enrol", command, OBSERVER, ENROL_OPS)
def ids_of(mini):
    out = scratch("ids.json")
    cli("pay-enrol-ids", mini.verify_key.encode().hex(), out)
    return json.load(open(out))
def journal_reasons(ev):
    return [j["reason"] for j in ev.get("journal", [])]

# ---------------------------------------------------------------- bootstrap of the rail
host = Host()
v = view(host)
book = {"sponsor": str(EMBER), "control": str(FACTORY_CONTROL), "nonce": fresh(),
        "expectedFactoryRoot": v["factoryRoot"], "expectedAuthorityRoot": v["authorityRoot"],
        "expectedPayRoot": v["payRoot"], "bookStart": "0",
        "book": [P1_ADDRESS, "01" * 32, "02" * 32],
        "tariff": {"version": "2", "asset": "0", "mint": P1_MINT, "tokenProgram": P1_PROGRAM,
                   "decimals": "6", "creditPerAtomic": "1", "maxPerObservation": "100000000000",
                   "minTickSlots": "1", "nodeWeekRate": str(WEEK), "enrolIndex": None,
                   "journalFloor": str(FLOOR), "slashCallerPermille": "500"}}
r, _ = sign_and_submit(host, "pay-book", book, EMBER, PAY_OPS)
row("operator installs a 3-row book (row 0 = the enrollment address) + tariff v2", "confirmed",
    show(r), r.get("type") == "confirmed")
v = view(host)
assign = {"subject": str(FLOAT), "capability": str(1000 + FLOAT), "account": str(acct(FLOAT)),
          "index": "0", "nonce": fresh(), "expectedAuthorityRoot": v["authorityRoot"],
          "expectedPayRoot": v["payRoot"]}
r, _ = sign_and_submit(host, "pay-assign", assign, FLOAT, PAY_OPS)
row("the enrollment float (account 120) takes index 0", "confirmed", show(r), r.get("type") == "confirmed")
v = view(host)
enrol_on = dict(book, nonce=fresh(), expectedAuthorityRoot=v["authorityRoot"], expectedPayRoot=v["payRoot"],
                expectedFactoryRoot=v["factoryRoot"], bookStart="3", book=[],
                tariff=dict(book["tariff"], version="3", enrolIndex="0"))
r, _ = sign_and_submit(host, "pay-book", enrol_on, EMBER, PAY_OPS)
row("tariff names index 0 the enrollment index", "confirmed", show(r), r.get("type") == "confirmed")
host.stop()
led0 = ledger()

# ---------------------------------------------------------------- the happy enrollment
alice, alice_blob, alice_memo = make_memo("alice")
ALICE = ids_of(alice)
with open(path("subject-alice.key"), "wb") as out: out.write(alice.encode())
REMAINDER = 1000
happy = record(PRICE + REMAINDER, alice_memo)
host = Host()
r, happy_ingress = enrol(host, happy)
row("enrol-happy: a real memo paying the price + 1000", "confirmed", show(r), r.get("type") == "confirmed")
ev = enrolment_view(host)
entry = next((e for e in ev.get("entries", []) if e["miniKey"] == alice.verify_key.encode().hex()), None)
hour = ev.get("clock", {}).get("hour")
row("the view lists the key: derived subject, ssh blob, index 1, a week's lease",
    f"subject {ALICE['subject']}, index 1, expiresAt = hour + 168",
    json.dumps(entry, sort_keys=True)[:260] + f" hour={hour}",
    entry is not None and entry["subject"] == ALICE["subject"] and entry["sshBlob"] == alice_blob.hex()
    and entry["index"] == 1 and entry["lease"] == {"expiresAt": hour + 168} and ev["view"] == "DREGG/PAY/ENROLMENT-VIEW/v3")
op, data = host.call(120, happy_ingress)
r = outcome(data) if op == 120 else {}
row("receipt-only lookup of the enrollment (op 120)", "confirmed replayed", show(r),
    r.get("type") == "confirmed")
host.stop()
led1 = ledger()
row("the new account is index 1's payer, funded amount - price", f"{acct(FLOAT)} unchanged; {ALICE['account']} = {REMAINDER}",
    f"float {balance(led0, acct(FLOAT))}->{balance(led1, acct(FLOAT))} new {balance(led1, ALICE['account'])} "
    f"well {led0['well']}->{led1['well']}",
    balance(led1, acct(FLOAT)) == balance(led0, acct(FLOAT)) == 100
    and balance(led1, ALICE["account"]) == REMAINDER
    and int(led1["well"]) == int(led0["well"]) - (PRICE + REMAINDER))

def query(name, signer_key, subject, kind, target, capability, view_name="resource"):
    intent = {"subject": str(subject), "nonce": fresh(),
              "purpose": {"type": "query", "kind": kind, "target": str(target), "view": view_name},
              "grants": [{"kind": kind, "target": str(target), "capability": str(capability)}]}
    source = path(f"{name}-intent.json")
    json.dump(intent, open(source, "w"))
    done = subprocess.run([MINI, "query", "--host", HOST, "--config", CONFIG, "--intent", source,
                           "--key", signer_key, "--view", view_name, "--dir", path(name)], capture_output=True)
    return done.returncode, (done.stdout + done.stderr).decode("utf-8", "replace")
rc, out = query("alice-own", path("subject-alice.key"), ALICE["subject"], "account", ALICE["account"],
                ALICE["ownerCapability"])
row("the new subject reads its own account (its owner grant)", "exit 0", f"rc={rc} {out[-160:] if rc else ''}", rc == 0)
rc, out = query("alice-friend", path("subject-alice.key"), ALICE["subject"], "account", acct(FRIEND),
                ALICE["ownerCapability"])
row("the new subject reads another friend's account (140)", "refused", f"rc={rc} {out[-200:]}", rc != 0)
rc, out = query("alice-factory", path("subject-alice.key"), ALICE["subject"], "object", FACTORY,
                ALICE["observeCapability"])
row("the new subject observes the factory (its factory-observation grant)", "exit 0",
    f"rc={rc} {out[-160:] if rc else ''}", rc == 0)

# ---------------------------------------------------------------- renewal, replay, journal
host = Host()
renewal = record(2 * WEEK + 500, alice_memo)
r, _ = enrol(host, renewal)
ev = enrolment_view(host)
entry2 = next((e for e in ev.get("entries", []) if e["miniKey"] == alice.verify_key.encode().hex()), None)
row("the same memo again (P1b same-memo-twice): renewal by two weeks", "confirmed; one entry; expiresAt + 336",
    f"{show(r)} entries={len(ev.get('entries', []))} expiresAt {entry['lease']['expiresAt']}->"
    f"{(entry2 or {}).get('lease')}",
    r.get("type") == "confirmed" and len(ev.get("entries", [])) == 1
    and entry2["lease"] == {"expiresAt": entry["lease"]["expiresAt"] + 336} and entry2["subject"] == entry["subject"])
r, _ = enrol(host, happy)
row("the happy observation resubmitted (new nonce)", "refused: its nullifier is consumed", show(r),
    r.get("type") == "refused" and ("durable" in r.get("phase", "") + r.get("detail", "")))
host.stop()
led2 = ledger()
row("renewal funds the friend's account with the remainder after the lease", f"+500 to {ALICE['account']}",
    f"{balance(led1, ALICE['account'])}->{balance(led2, ALICE['account'])} float {balance(led2, acct(FLOAT))}",
    balance(led2, ALICE["account"]) == REMAINDER + 500 and balance(led2, acct(FLOAT)) == 100)

bob, bob_blob, bob_memo = make_memo("bob")
JOURNALED = [
    ("below the price (a fresh real memo)", record(PRICE - 1, bob_memo), "belowPrice"),
    ("enrol-no-memo: a memo-less payment", record(5 * FLOOR), "memoMissing"),
    ("enrol-memo-bind: two memo instructions", record(5 * FLOOR, None, "memoUnbound"), "memoUnbound"),
    ("enrol-memo-bind: a non-UTF-8 memo", record(5 * FLOOR, None, "memoInvalid"), "memoInvalid"),
    ("a malformed (truncated) memo", record(PRICE, bob_memo[:-1]), "memoMalformed:memoShape"),
    ("a mini-sig that fails", record(PRICE, flip(bob_memo, 150)), "miniSigInvalid"),
    ("an ssh-sig that fails", record(PRICE, flip(bob_memo, 300)), "sshSigInvalid"),
]
host = Host()
for name, rec, reason in JOURNALED:
    before = enrolment_view(host)
    r, _ = enrol(host, rec)
    after = enrolment_view(host)
    added = [j for j in after.get("journal", []) if j not in before.get("journal", [])]
    row(name, f"journaled {reason}", f"{show(r)} {[j['reason'] for j in added]}",
        r.get("type") == "confirmed" and [j["reason"] for j in added] == [reason]
        and added[0]["signature"] == rec["signature"])
dust = record(FLOOR - 1, bob_memo)
r, _ = enrol(host, dust)
row("enrol-dust: below the journal floor", "refused belowJournalFloor (nothing journaled)", show(r),
    refused(r, "belowJournalFloor"))
host.stop()
led3 = ledger()
row("the journal mints nothing", "well and every payer unchanged by the 7 journaled payments",
    f"well {led2['well']}->{led3['well']}", led3["well"] == led2["well"] and led3["payers"] == led2["payers"])

# A verifier that cannot answer `verify-sshsig`: the payment is REFUSED, not journaled.
broken = path("verifier-broken.sh")
with open(broken, "w") as out:
    out.write(f"#!/bin/sh\nif [ \"$1\" = verify-sshsig ]; then echo 'verifier offline' >&2; exit 70; fi\n"
              f"exec {VERIFIER} \"$@\"\n")
os.chmod(broken, 0o700)
pinned = json.load(open(CONFIG))
pinned["signatureBinary"] = broken
BROKEN_CONFIG = path("deployment/pinned-config-broken-verifier.json")
json.dump(pinned, open(BROKEN_CONFIG, "w"))
host = Host(BROKEN_CONFIG)
before = enrolment_view(host)
carol, _, carol_memo = make_memo("carol")
r, _ = enrol(host, record(PRICE, carol_memo))
after = enrolment_view(host)
row("verifier unavailable for the ssh-sig", "refused (verifier), nothing journaled or enrolled",
    f"{show(r)} journal {len(before.get('journal', []))}->{len(after.get('journal', []))}",
    refused(r, "verifier") and after.get("journal") == before.get("journal") and after["entries"] == before["entries"])
host.stop()

# ---------------------------------------------------------------- the observer is confined
def mini_submit(name, intent, signer):
    source = path(f"{name}-intent.json")
    json.dump(intent, open(source, "w"))
    done = subprocess.run([MINI, "submit", "--host", HOST, "--config", CONFIG, "--intent", source,
                           "--key", path(f"subject-{signer}.key"), "--dir", path(f"{name}-attempt")],
                          capture_output=True)
    result_path = path(f"{name}-attempt/outcome.json")
    result = json.load(open(result_path)) if os.path.exists(result_path) else {}
    return done.returncode, result, (done.stdout + done.stderr).decode("utf-8", "replace")[-400:]
def factory_policy(name):
    intent = {"subject": str(EMBER), "nonce": fresh(),
              "purpose": {"type": "query", "kind": "object", "target": str(FACTORY), "view": "policy"},
              "grants": [{"kind": "object", "target": str(FACTORY), "capability": str(3000 + EMBER)}]}
    source = path(f"{name}-intent.json")
    json.dump(intent, open(source, "w"))
    done = subprocess.run([MINI, "query", "--host", HOST, "--config", CONFIG, "--intent", source,
                           "--key", path(f"subject-{EMBER}.key"), "--view", "policy",
                           "--dir", path(name)], capture_output=True)
    if done.returncode != 0:
        fail(f"factory policy query: " + (done.stdout + done.stderr).decode("utf-8", "replace")[-400:])
    return json.load(open(path(f"{name}/view.json"))), json.load(open(path(f"{name}/challenge.json")))
policy, challenge = factory_policy("factory-policy")
rc, r, tail = mini_submit("observer-install", {"subject": str(OBSERVER), "nonce": fresh(), "purpose": {
    "type": "prepare", "draft": {"type": "install-source", "subject": str(OBSERVER), "control": str(ENROL_CAP),
        "declaration": {"expectedPreRoot": challenge["authorityRoot"],
            "expected": {"version": policy["version"], "address": policy["address"]},
            "nonce": fresh(), "source": {"policyId": str(FACTORY), "version": str(int(policy["version"]) + 1),
                "domain": "8501", "semantics": SEMANTICS, "previous": policy["address"],
                "predicate": {"type": "all", "predicates": []}}}}},
    "grants": [{"kind": "program", "target": str(FACTORY), "capability": str(ENROL_CAP)}]}, OBSERVER)
# Final's Host answers this blind prepare with the uniform undisclosed refusal (MR's rule);
# the next row shows the confined law is still the factory's.
row("the observer installs a factory law with C_enrol", "refused undisclosed: the plan's factory observation is refused",
    f"rc={rc} {r.get('type')} {tail[-120:]}", rc != 0 and r.get("type") != "confirmed"
    and "refused: undisclosed" in tail)
rc, out = query("observer-factory", path(f"subject-{OBSERVER}.key"), OBSERVER, "object", FACTORY,
                3000 + OBSERVER, "policy")
row("the observer observes the factory with its genesis observe grant (3030)",
    "refused by the confined factory law (ember's identical grant was admitted above)",
    f"rc={rc} {out[-100:]}", rc != 0 and 'not (subject == 30)' in out
    and 'not (slot "authority/operation/pay-self-enrol" == 1)' in out)

# ---------------------------------------------------------------- cold reopen + audit
host = Host()
v_before, e_before = view(host), enrolment_view(host)
host.stop()
audit = subprocess.run([HOST, CONFIG, "audit"], capture_output=True)
audit_text = (audit.stdout + audit.stderr).decode("utf-8", "replace").strip().splitlines()
row("operator audit re-admits every record (NativeHostReplay, incl. enrolments)", "exit 0",
    f"exit={audit.returncode} {audit_text[-1] if audit_text else ''}", audit.returncode == 0)
host = Host()
v_after, e_after = view(host), enrolment_view(host)
host.stop()
row("cold reopen: pay view and enrollment view equal", "equal roots, entries, journal",
    f"payRoot {v_before['payRoot'][:12]}.. authorityRoot {v_before['authorityRoot'][:12]}.. "
    f"entries={len(e_after.get('entries', []))} journal={len(e_after.get('journal', []))}",
    v_before == v_after and e_before == e_after)

rows_path = path("rows.tsv")
with open(rows_path, "w") as out:
    out.write("verdict\tstep\texpected\tobserved\n")
    for name, expected, observed, verdict_ in ROWS:
        out.write(f"{verdict_}\t{name}\t{expected}\t{observed}\n")
passed = sum(1 for r in ROWS if r[3] == "PASS")
final = f"J-PAY-E3 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - started:.1f} s)"
print(final)
print(final, file=sys.stderr)
print(rows_path)
sys.exit(0 if passed == len(ROWS) else 1)
PY
