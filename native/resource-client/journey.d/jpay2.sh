#!/usr/bin/env bash
# J-PAY-2 (PAY.md P2): the pay cell on a fresh private Store.
#
# Follows the journey hook contract (journey.sh header): executed with HOST,
# MINI, STORE, VERIFIER and JOURNEY_STEP_DIR exported; it starts its OWN Host on
# its OWN fresh Store under JOURNEY_STEP_DIR (it never touches the journey's
# service) and stops it. Exit 0 = PASS. The verdict `J-PAY-2 PASS n/n` is the
# last stderr line and the line before the last stdout line; the last stdout
# line is the deciding artifact (rows.tsv).
#
# Standalone: HOST=... MINI=... STORE=... VERIFIER=... JOURNEY_STEP_DIR=NEW_DIR jpay2.sh
#
# Drives the Host's raw session operations 103-107 (the client verb is lane
# P4's). Keys are generated and headers signed here with PyNaCl, standing in
# for client custody; every byte the Host accepts is authored and inspected by
# the Host's own source-owned codecs (`author pay-book|pay-assign`,
# `inspect pay-plan|pay-view|outcome`).
#
# Rows: the operator installs a 64-row book and a valid tariff; a friend's
# assignment yields index 0 for an account they own; a second request for the
# same account is refused; a non-owner is refused notOwner; 63 more owners take
# indices 1..63; index 64 is refused bookExhausted; a tariff at a version <= the
# current one is refused; a receipt-only lookup replays; a cold reopen and the
# operator audit re-admit every record through NativeHostReplay.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jpay2: $name is required" >&2; exit 2; fi
done
command -v python3 >/dev/null || { echo "jpay2: python3 is required" >&2; exit 2; }
python3 -c 'import nacl.signing' 2>/dev/null || { echo "jpay2: PyNaCl is required" >&2; exit 2; }
DIR="$JOURNEY_STEP_DIR/jpay2"
if [ -e "$DIR" ]; then echo "jpay2: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
exec python3 - "$DIR" <<'PY'
import hashlib, json, os, struct, subprocess, sys, time
import nacl.signing

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
ROWS = []
EMBER, FACTORY, BOOK_ID, AUTH_ID, FACTORY_CONTROL = 7, 10, 11, 12, 53
PAYERS = list(range(8, 72))          # 64 payer subjects; subject s owns account acct(s)
LATE = 72                            # the 65th owner: meets an exhausted book
SUBJECTS = [EMBER] + PAYERS + [LATE]
def acct(s): return 100 + s        # clear of the factory/Book/authority ids 10-12

def path(name): return os.path.join(DIR, name)
def fail(message):
    print(f"J-PAY-2 FAIL: {message}", file=sys.stderr); sys.exit(1)

# ---------------------------------------------------------------- genesis
keys = {s: nacl.signing.SigningKey.generate() for s in SUBJECTS}
def enrollment(s):
    return {"key": {"keyId": str(7000 + s), "keyEpoch": "2", "algorithm": "1", "subject": str(s),
                    "publicKey": keys[s].verify_key.encode().hex(), "activeFrom": "0",
                    "activeUntil": "1000000"},
            "accountId": str(acct(s)), "spendCapabilityId": str(1000 + s),
            "controlCapabilityId": str(2000 + s), "factoryObserveCapabilityId": str(3000 + s),
            "initialBalance": "100", "accountPredicate": {"type": "all", "predicates": []}}
operator = {"domain": 8501, "federation": 9, "factoryId": FACTORY, "resourceBookId": BOOK_ID,
            "authorityCellId": AUTH_ID, "issuer": 5, "ownerBudget": 100000, "lifetime": 10000,
            "tariffBase": 3, "tariffPerBirth": 2, "tariffPerGrant": 1,
            "tariffPerInitialPayloadByte": 0, "collector": 99, "asset": 0, "genesisHeight": 10,
            "expectedSeed": 0, "storageBinary": STORE, "storageRoot": path("store"),
            "signatureBinary": VERIFIER}
json.dump(operator, open(path("operator.json"), "w"), indent=1)
profile = json.loads(subprocess.run([HOST, path("operator.json"), "profile"], check=True,
                                    capture_output=True).stdout)
genesis = {"domain": "8501", "factoryId": str(FACTORY), "resourceBookId": str(BOOK_ID),
           "authorityCellId": str(AUTH_ID), "federation": "9", "tariffBase": "3",
           "tariffPerBirth": "2", "tariffPerGrant": "1", "tariffPerInitialPayloadByte": "0",
           "collector": "99", "asset": "0", "expectedSemantics": profile["semantics"],
           "issuerEpoch": "2", "genesisHeight": "10",
           "factoryPredicate": {"type": "all", "predicates": []},
           "enrollments": [enrollment(s) for s in SUBJECTS],
           "factoryControllerSubject": str(EMBER),
           "factoryControllerCapability": str(FACTORY_CONTROL),
           "meterAllowance": {k: "10000000" for k in ("incidences", "turnBytes", "memoryTouches",
               "witnessBytes", "proofWork", "storageBytes", "networkBytes", "sideEffectCount",
               "feeDebit", "leaseByteBlocks")}}
json.dump(genesis, open(path("genesis.json"), "w"), indent=1)
subprocess.run([MINI, "bootstrap", "--host", HOST, "--config", path("operator.json"),
                "--source", path("genesis.json"), "--dir", path("deployment")],
               check=True, capture_output=True)
CONFIG = path("deployment/pinned-config.json")

# ---------------------------------------------------------------- Host plumbing
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

class Host:
    def __init__(self):
        self.log = open(path("host.stderr"), "ab")
        self.proc = subprocess.Popen([HOST, CONFIG, "stdio"], stdin=subprocess.PIPE,
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
    view = inspect("outcome", data)
    for field in ("phase", "detail"):
        if field in view: view[field] = bytes.fromhex(view[field]).decode("utf-8", "replace")
    return view

def view(host):
    op, data = host.call(107)
    if op != 107: fail(f"pay view failed: {data!r}")
    return inspect("pay-view", data)

def sign_and_submit(host, kind, command, signer):
    op, plan = host.call(103, author(kind, command))
    if op != 103: return {"type": "plan-failed", "detail": plan[-200:].decode("utf-8", "replace")}, None
    header = bytes.fromhex(inspect("pay-plan", plan)["header"]["canonical"])
    signature = keys[signer].sign(header).signature
    op, ingress = host.call(104, struct.pack("<I", len(plan)) + plan + signature)
    if op != 104: fail(f"assembly failed: {ingress!r}")
    op, result = host.call(105, ingress)
    if op != 105: fail(f"submit failed: {result!r}")
    return outcome(result), ingress

def row(name, expected, observed, ok):
    ROWS.append((name, expected, observed, "PASS" if ok else "FAIL"))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{observed}", file=sys.stderr)

def refused_with(result, reason):
    # A pay submission is blind (MR's rule, applied at the merge): every refusal,
    # including the receiver's pre-signature `reason`, is the uniform
    # `undisclosed` frame. The row therefore checks the uniform frame and that
    # the pay cell did not move; `reason` names the branch the command was built
    # to hit, which the wire deliberately does not confirm.
    return (result.get("type") == "refused" and result.get("reason") == "undisclosed"
            and view(host)["payRoot"] == v["payRoot"])

address = lambda i: hashlib.sha256(f"jpay2 fixture deposit address {i}".encode()).hexdigest()
tariff = lambda version: {"version": str(version), "asset": "0", "mint": "07" * 32,
                          "tokenProgram": "09" * 32, "decimals": "6", "creditPerAtomic": "1",
                          "maxPerObservation": "10000000000", "minTickSlots": "1500",
                          "nodeHourRate": "5952380", "enrolIndex": None, "journalFloor": "1000000"}
nonce = [100]
def book_command(v, book, start, t):
    nonce[0] += 1
    return {"sponsor": str(EMBER), "control": str(FACTORY_CONTROL), "nonce": str(nonce[0]),
            "expectedFactoryRoot": v["factoryRoot"], "expectedAuthorityRoot": v["authorityRoot"],
            "expectedPayRoot": v["payRoot"], "bookStart": str(start), "book": book, "tariff": t}
def assign_command(v, subject, capability_holder, account, index):
    nonce[0] += 1
    return {"subject": str(subject), "capability": str(1000 + capability_holder),
            "account": str(account), "index": str(index), "nonce": str(nonce[0]),
            "expectedAuthorityRoot": v["authorityRoot"], "expectedPayRoot": v["payRoot"]}

# ---------------------------------------------------------------- the journey
started = time.time()
host = Host()
v = view(host)
row("genesis pay cell", "tariff invalid, empty book, no clock (time is the clock cell's)",
    f"type={v['type']} tariff.valid={v['tariff']['valid']} bookSize={v['bookSize']} nextFree={v['nextFree']} clock={'clock' in v}",
    v["type"] == "pay-view-v2" and v["tariff"]["valid"] is False and v["bookSize"] == "0"
    and v["nextFree"] == "0" and "clock" not in v)

r, _ = sign_and_submit(host, "pay-assign", assign_command(v, 8, 8, acct(8), 0), 8)
row("assignment before a valid tariff", "refused undisclosed (built to hit tariffInvalid), pay root unchanged", f"{r.get('type')} {r.get('reason','')}",
    refused_with(r, "tariffInvalid"))

r, _ = sign_and_submit(host, "pay-book", book_command(v, [address(i) for i in range(64)], 0, tariff(1)), EMBER)
row("operator installs 64-row book + tariff v1", "confirmed", f"{r.get('type')} acceptedCount={r.get('acceptedCount')}",
    r.get("type") == "confirmed")
v = view(host)
row("view after install", "bookSize 64, tariff v1 valid, nextFree 0",
    f"bookSize={v['bookSize']} tariff.version={v['tariff']['version']} valid={v['tariff']['valid']} nextFree={v['nextFree']}",
    v["bookSize"] == "64" and v["tariff"]["version"] == "1" and v["tariff"]["valid"] is True
    and v["nextFree"] == "0" and v["book"][0] == address(0) and v["book"][63] == address(63))

r, friend_ingress = sign_and_submit(host, "pay-assign", assign_command(v, 8, 8, acct(8), 0), 8)
row("friend (subject 8) takes index 0 for owned account 108", "confirmed", f"{r.get('type')} acceptedCount={r.get('acceptedCount')}",
    r.get("type") == "confirmed")
v = view(host)
row("index 0 is the friend's; address is book[0]", "nextFree 1", f"nextFree={v['nextFree']} book[0]={v['book'][0][:16]}...",
    v["nextFree"] == "1" and v["book"][0] == address(0))

r, _ = sign_and_submit(host, "pay-assign", assign_command(v, 8, 8, acct(8), 1), 8)
row("second request for account 108", "refused undisclosed (built to hit alreadyAssigned), pay root unchanged", f"{r.get('type')} {r.get('reason','')}",
    refused_with(r, "alreadyAssigned"))

r, _ = sign_and_submit(host, "pay-assign", assign_command(v, 9, 9, acct(8), 1), 9)
row("non-owner (subject 9, own grant) for account 108", "refused undisclosed (built to hit notOwner), pay root unchanged", f"{r.get('type')} {r.get('reason','')}",
    refused_with(r, "notOwner"))
r, _ = sign_and_submit(host, "pay-assign", assign_command(v, 9, 8, acct(8), 1), 9)
row("non-owner (subject 9, presenting subject 8's grant)", "refused undisclosed (built to hit notOwner), pay root unchanged", f"{r.get('type')} {r.get('reason','')}",
    refused_with(r, "notOwner"))

confirmed = 0
for s in PAYERS[1:]:
    v = view(host)
    r, _ = sign_and_submit(host, "pay-assign", assign_command(v, s, s, acct(s), int(v["nextFree"])), s)
    confirmed += r.get("type") == "confirmed"
v = view(host)
row("owners 9..71 take indices 1..63", "63 confirmed, nextFree 64", f"confirmed={confirmed} nextFree={v['nextFree']}",
    confirmed == 63 and v["nextFree"] == "64")

r, _ = sign_and_submit(host, "pay-assign", assign_command(v, LATE, LATE, acct(LATE), 64), LATE)
row("owner 72 (account 172) asks for index 64 of a 64-row book", "refused undisclosed (built to hit bookExhausted), pay root unchanged", f"{r.get('type')} {r.get('reason','')}",
    refused_with(r, "bookExhausted"))

r, _ = sign_and_submit(host, "pay-book", book_command(v, [], 64, tariff(1)), EMBER)
row("tariff set again at version 1 (= current)", "refused undisclosed (built to hit tariffVersionNotIncreasing), pay root unchanged", f"{r.get('type')} {r.get('reason','')}",
    refused_with(r, "tariffVersionNotIncreasing"))
r, _ = sign_and_submit(host, "pay-book", book_command(v, [], 64, tariff(2)), EMBER)
row("tariff raised to version 2", "confirmed", f"{r.get('type')} acceptedCount={r.get('acceptedCount')}",
    r.get("type") == "confirmed")
v = view(host)
r, _ = sign_and_submit(host, "pay-book", book_command(v, [], 64, tariff(1)), EMBER)
row("tariff set back to version 1 (< current 2)", "refused undisclosed (built to hit tariffVersionNotIncreasing), pay root unchanged", f"{r.get('type')} {r.get('reason','')}",
    refused_with(r, "tariffVersionNotIncreasing"))
r, _ = sign_and_submit(host, "pay-book", book_command(v, [], 64, tariff(0)), EMBER)
row("tariff at version 0 (not a valid tariff)", "refused undisclosed (built to hit tariffInvalid), pay root unchanged", f"{r.get('type')} {r.get('reason','')}",
    refused_with(r, "tariffInvalid"))

op, data = host.call(106, friend_ingress)
r = outcome(data) if op == 106 else {"type": "op-failed"}
row("receipt-only lookup of the friend's assignment", "confirmed replayed", f"{r.get('type')} {r.get('confirmation')}",
    r.get("type") == "confirmed" and r.get("confirmation") == "replayed")
host.stop()

host = Host()
v2 = view(host)
host.stop()
row("cold reopen", "same pay root, nextFree 64", f"payRoot equal={v2['payRoot'] == v['payRoot']} nextFree={v2['nextFree']}",
    v2["payRoot"] == v["payRoot"] and v2["nextFree"] == "64")
audit = subprocess.run([HOST, CONFIG, "audit"], capture_output=True)
audit_text = (audit.stdout + audit.stderr).decode("utf-8", "replace").strip().splitlines()
row("operator audit re-admits every record (NativeHostReplay)", "exit 0",
    f"exit={audit.returncode} {audit_text[-1] if audit_text else ''}", audit.returncode == 0)

rows_path = path("rows.tsv")
with open(rows_path, "w") as out:
    out.write("verdict\tstep\texpected\tobserved\n")
    for name, expected, observed, verdict in ROWS:
        out.write(f"{verdict}\t{name}\t{expected}\t{observed}\n")
passed = sum(1 for r in ROWS if r[3] == "PASS")
verdict = f"J-PAY-2 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - started:.1f} s)"
print(verdict)
print(verdict, file=sys.stderr)
print(rows_path)
sys.exit(0 if passed == len(ROWS) else 1)
PY
