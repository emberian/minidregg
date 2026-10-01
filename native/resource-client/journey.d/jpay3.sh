#!/usr/bin/env bash
# J-PAY-3 (PAY.md P3): observed payments become Book credit, on a fresh private Store.
#
# Follows the journey hook contract (journey.sh header): executed with HOST,
# MINI, STORE, VERIFIER and JOURNEY_STEP_DIR exported; it starts its OWN Host on
# its OWN fresh Store under JOURNEY_STEP_DIR (it never touches the journey's
# service) and stops it. Exit 0 = PASS. The verdict `J-PAY-3 PASS n/n` is the
# last stderr line and the line before the last stdout line; the last stdout
# line is the deciding artifact (rows.tsv).
#
# Standalone: HOST=... MINI=... STORE=... VERIFIER=... JOURNEY_STEP_DIR=NEW_DIR jpay3.sh
#
# Genesis names the observer (subject 30, capability 4030 = observePayment on
# the pay cell under the pay law `eq request/subject 30`). The operator installs
# a 4-row book whose row 0 is P1's happy-vector deposit address and a tariff on
# P1's mint and Token-2022; subjects 8 and 9 take indices 0 and 1; index 2 stays
# unassigned. The observer then drives the Host's raw operations 108-111 (the
# client verb `pay observe` is lane P4's), signing with PyNaCl in place of
# client custody; every byte the Host accepts is authored and inspected by the
# Host's own codecs (`author pay-observation`, `inspect pay-plan|pay-view|
# pay-observation-ingress|outcome`). Balances come from the Host's local
# `pay-ledger` read of the Store, taken with the Host stopped.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jpay3: $name is required" >&2; exit 2; fi
done
command -v python3 >/dev/null || { echo "jpay3: python3 is required" >&2; exit 2; }
python3 -c 'import nacl.signing' 2>/dev/null || { echo "jpay3: PyNaCl is required" >&2; exit 2; }
DIR="$JOURNEY_STEP_DIR/jpay3"
if [ -e "$DIR" ]; then echo "jpay3: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
exec python3 - "$DIR" <<'PY'
import hashlib, json, os, struct, subprocess, sys, time
import nacl.signing

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
ROWS = []
EMBER, FACTORY, BOOK_ID, AUTH_ID, FACTORY_CONTROL = 7, 10, 11, 12, 53
OBSERVER, OBSERVER_CAP = 30, 4030
PAYERS = [8, 9]
SUBJECTS = [EMBER, OBSERVER] + PAYERS
def acct(s): return 100 + s

# P1's happy vector (planning/pay/p1-watcher.md §1): the deposit address, the
# mint, Token-2022, and the first transfer record, byte for byte.
P1_ADDRESS = "16946aa663362d557dd21ee08e8da60c2ea8a73467713c7c5205991e36634af5"
P1_MINT = "8525966c00f39ff54ef5e537a4736af436494d1f1681c659bd98e37ac28beff1"
P1_PROGRAM = "06ddf6e1ee758fde18425dbce46ccddab61afc4d83b90d27febdf928d8a18bfc"
P1_RECORD = {"address": P1_ADDRESS, "amount": 1000000000, "blockTime": 1759249950, "index": 0,
             "mint": P1_MINT,
             "signature": "e895db8f0638e377a2e3c110b1a7f6266170e27f135964a0aec2df1c5fec95359102463a545e6eac2104ed10ef18980a8a59c9224c8a46b64e571122734f586a",
             "slot": 900, "tokenProgram": P1_PROGRAM}
CAP, RATE, MIN_TICK = 2000000000, 1, 1500

def path(name): return os.path.join(DIR, name)
def fail(message):
    print(f"J-PAY-3 FAIL: {message}", file=sys.stderr); sys.exit(1)

# ---------------------------------------------------------------- genesis
keys = {s: nacl.signing.SigningKey.generate() for s in SUBJECTS}
def enrollment(s):
    return {"key": {"keyId": str(7000 + s), "keyEpoch": "2", "algorithm": "1", "subject": str(s),
                    "publicKey": keys[s].verify_key.encode().hex(), "activeFrom": "0",
                    "activeUntil": "1000000", "revoked": False},
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
               "feeDebit", "leaseByteBlocks")},
           "payObserver": {"subject": str(OBSERVER), "capability": str(OBSERVER_CAP)}}
json.dump(genesis, open(path("genesis.json"), "w"), indent=1)
boot = subprocess.run([MINI, "bootstrap", "--host", HOST, "--config", path("operator.json"),
                       "--source", path("genesis.json"), "--dir", path("deployment")], capture_output=True)
if boot.returncode != 0:
    fail("bootstrap: " + (boot.stdout + boot.stderr).decode("utf-8", "replace")[-400:])
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
def ledger():
    out = scratch("ledger.json")
    cli("pay-ledger", out)
    return json.load(open(out))
def balance(led, account):
    for r in led["payers"]:
        if r["account"] == str(account): return int(r["balance"])
    fail(f"account {account} not in ledger")

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
PAY_OPS, OBSERVE_OPS = (103, 104, 105), (108, 109, 110)

def row(name, expected, observed, ok):
    observed = " ".join(str(observed).split())   # a Lean repr may wrap; keep one TSV line
    ROWS.append((name, expected, observed, "PASS" if ok else "FAIL"))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{observed}", file=sys.stderr)

def refused_with(result, reason):
    return result.get("type") == "refused" and result.get("detail", "").endswith("." + reason)
def show(result): return f"{result.get('type')} {result.get('detail', '')}".strip()

address = lambda i: hashlib.sha256(f"jpay3 fixture deposit address {i}".encode()).hexdigest()
signature = lambda label: hashlib.sha512(f"jpay3 transfer {label}".encode()).hexdigest()
tariff = {"version": "1", "asset": "0", "mint": P1_MINT, "tokenProgram": P1_PROGRAM, "decimals": "6",
          "creditPerAtomic": str(RATE), "maxPerObservation": str(CAP), "minTickSlots": str(MIN_TICK)}
def credit_for(amount): return min(amount, CAP) * RATE
nonce = [100]
def book_command(v, book, start, t):
    nonce[0] += 1
    return {"sponsor": str(EMBER), "control": str(FACTORY_CONTROL), "nonce": str(nonce[0]),
            "expectedFactoryRoot": v["factoryRoot"], "expectedAuthorityRoot": v["authorityRoot"],
            "expectedPayRoot": v["payRoot"], "bookStart": str(start), "book": book, "tariff": t}
def assign_command(v, subject, index):
    nonce[0] += 1
    return {"subject": str(subject), "capability": str(1000 + subject), "account": str(acct(subject)),
            "index": str(index), "nonce": str(nonce[0]),
            "expectedAuthorityRoot": v["authorityRoot"], "expectedPayRoot": v["payRoot"]}
def tip(slot): return {"slot": slot, "blockTime": 1759249000 + slot}
def record(index, addr, sig, slot, amount, mint=P1_MINT):
    return {"index": index, "address": addr, "signature": sig, "slot": slot,
            "blockTime": 1759249000 + slot, "amount": amount, "mint": mint, "tokenProgram": P1_PROGRAM}
def report(v, t, observations):
    nonce[0] += 1
    return {"observer": str(OBSERVER), "capability": str(OBSERVER_CAP), "nonce": str(nonce[0]),
            "expectedAuthorityRoot": v["authorityRoot"], "expectedPayRoot": v["payRoot"],
            "tip": t, "observations": observations}
CREDITED = []          # every observation of a confirmed report, for the audit identity
def observe(host, t, observations):
    v = view(host)
    r, ingress = sign_and_submit(host, "pay-observation", report(v, t, observations), OBSERVER, OBSERVE_OPS)
    if r.get("type") == "confirmed": CREDITED.extend(observations)
    return r, ingress

# ---------------------------------------------------------------- the journey
started = time.time()
led0 = ledger()
row("genesis ledger (before any turn)", "clock 0/0, well = -(4 x 100), payers none",
    f"well={led0['well']} clock={led0['clock']['slot']}/{led0['clock']['blockTime']} payers={len(led0['payers'])}",
    led0["well"] == "-400" and led0["clock"] == {"slot": "0", "blockTime": "0"} and led0["payers"] == [])

host = Host()
v = view(host)
r, _ = observe(host, tip(1000), [P1_RECORD])
row("observation before a valid tariff", "refused tariffInvalid", show(r), refused_with(r, "tariffInvalid"))

r, _ = sign_and_submit(host, "pay-book", book_command(v, [P1_ADDRESS, address(1), address(2), address(3)], 0, tariff),
                       EMBER, PAY_OPS)
row("operator installs 4-row book (row 0 = P1's address) + tariff on P1's mint", "confirmed", show(r),
    r.get("type") == "confirmed")
for s, index in ((8, 0), (9, 1)):
    v = view(host)
    r, _ = sign_and_submit(host, "pay-assign", assign_command(v, s, index), s, PAY_OPS)
    row(f"subject {s} takes index {index} for account {acct(s)}", "confirmed", show(r), r.get("type") == "confirmed")

r, first_ingress = observe(host, tip(1000), [P1_RECORD])
row("P1 happy record (1e9 atomic to index 0) at tip 1000", "confirmed", show(r), r.get("type") == "confirmed")
v = view(host)
row("clock is the tip", "clock 1000/1759250000", f"clock={v['clock']['slot']}/{v['clock']['blockTime']}",
    v["clock"] == {"slot": "1000", "blockTime": "1759250000"})
host.stop()
led1 = ledger()
host = Host()
delta = balance(led1, 108) - 100
row("payer 108 credited exactly creditFor(amount)", f"+{credit_for(P1_RECORD['amount'])}",
    f"+{delta} well {led0['well']} -> {led1['well']}",
    delta == credit_for(P1_RECORD["amount"]) and int(led1["well"]) == int(led0["well"]) - delta)

r, _ = observe(host, tip(1100), [P1_RECORD])
row("the SAME transfer resubmitted in a new report (tip 1100)", "refused durable alreadyConsumed", show(r),
    r.get("type") == "refused" and r.get("phase") == "durable" and "alreadyConsumed" in r.get("detail", ""))

r, _ = observe(host, tip(1100), [P1_RECORD, dict(P1_RECORD, amount=1)])
row("the same transfer twice in one report", "refused duplicateInBatch", show(r), refused_with(r, "duplicateInBatch"))

same_sig_other_address = record(1, address(1), P1_RECORD["signature"], 1150, 250000000)
r, _ = observe(host, tip(1200), [same_sig_other_address])
row("same signature, DIFFERENT address (index 1, account 109)", "confirmed (a second credit)", show(r),
    r.get("type") == "confirmed")

overcap = record(0, P1_ADDRESS, signature("overcap"), 1250, 3000000000)
r, overcap_ingress = observe(host, tip(1300), [overcap])
row("over-cap transfer (3e9 atomic, cap 2e9)", "confirmed", show(r), r.get("type") == "confirmed")
op, data = host.call(111, overcap_ingress)
looked = outcome(data) if op == 111 else {"type": "op-failed"}
journal = inspect("pay-observation-ingress", overcap_ingress)
row("receipt-only lookup of the over-cap report; its journaled command", "confirmed replayed, amount 3000000000",
    f"{looked.get('type')} {looked.get('confirmation')} amount={journal['command']['observations'][0]['amount']}",
    looked.get("type") == "confirmed" and looked.get("confirmation") == "replayed"
    and journal["command"]["observations"][0]["amount"] == "3000000000")

r, _ = observe(host, tip(1300 + MIN_TICK - 1), [])
row("heartbeat 1499 slots after the clock", "refused tickTooSoon", show(r), refused_with(r, "tickTooSoon"))
r, _ = observe(host, tip(1300 + MIN_TICK), [])
v = view(host)
row("heartbeat 1500 slots after the clock", "confirmed, clock 2800",
    f"{show(r)} clock={v['clock']['slot']}/{v['clock']['blockTime']}",
    r.get("type") == "confirmed" and v["clock"] == {"slot": "2800", "blockTime": str(1759249000 + 2800)})
r, _ = observe(host, tip(2700), [record(0, P1_ADDRESS, signature("late"), 2650, 5)])
row("report at a tip behind the clock (2700 < 2800)", "refused tipBehindClock", show(r), refused_with(r, "tipBehindClock"))
r, _ = observe(host, tip(2900), [record(2, address(2), signature("unassigned"), 2850, 5)])
row("observation for the unassigned index 2", "refused unassignedIndex", show(r), refused_with(r, "unassignedIndex"))
r, _ = observe(host, tip(2900), [record(0, P1_ADDRESS, signature("mint"), 2850, 5, mint="07" * 32)])
row("observation of a different mint", "refused wrongMint", show(r), refused_with(r, "wrongMint"))
r, _ = observe(host, tip(2900), [record(0, address(3), signature("address"), 2850, 5)])
row("observation naming another index's address", "refused addressMismatch", show(r), refused_with(r, "addressMismatch"))
v_final = view(host)
host.stop()

led2 = ledger()
credited = sum(credit_for(o["amount"]) for o in CREDITED)
over_delta = balance(led2, 108) - balance(led1, 108)
row("over-cap credits the cap", f"payer 108 +{CAP}", f"+{over_delta}", over_delta == CAP)
row("same signature to index 1 credited account 109", "+250000000", f"+{balance(led2, 109) - 100}",
    balance(led2, 109) - 100 == 250000000)
row("well_tracks_observed on this Store: -well_h = -well_0 + sum creditFor", f"-well_h = {-int(led0['well']) + credited}",
    f"-well_h={-int(led2['well'])} -well_0={-int(led0['well'])} credited={credited} "
    f"payers_delta={sum(int(r['balance']) - 100 for r in led2['payers'])}",
    -int(led2["well"]) == -int(led0["well"]) + credited
    and sum(int(r["balance"]) - 100 for r in led2["payers"]) == credited)

host = Host()
v2 = view(host)
host.stop()
row("cold reopen", "same pay root, clock 2800", f"payRoot equal={v2['payRoot'] == v_final['payRoot']} clock={v2['clock']['slot']}",
    v2["payRoot"] == v_final["payRoot"] and v2["clock"]["slot"] == "2800" and led2["payRoot"] == v2["payRoot"])
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
verdict = f"J-PAY-3 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - started:.1f} s)"
print(verdict)
print(verdict, file=sys.stderr)
print(rows_path)
sys.exit(0 if passed == len(ROWS) else 1)
PY
