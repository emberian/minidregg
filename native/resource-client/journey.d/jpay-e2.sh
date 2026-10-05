#!/usr/bin/env bash
# J-PAY-E2 (PAY.md §11.9 P3b-1): the self-enrollment decision with real signatures,
# the public enrollment view, and the pay-cell observer replaced at runtime.
#
# Follows the journey hook contract (journey.sh header): executed with HOST,
# MINI, STORE, VERIFIER and JOURNEY_STEP_DIR exported; it starts its OWN Host on
# its OWN fresh Store under JOURNEY_STEP_DIR and stops it. Exit 0 = PASS. The
# verdict `J-PAY-E2 PASS n/n` is the last stderr line and the line before the
# last stdout line; the last stdout line is the deciding artifact (rows.tsv).
# VERIFIER must have the `verify-sshsig` verb (native/credential-signature-verifier
# at P3b-1 or later).
#
# Part A — the decision (`minidregg-host CONFIG pay-enrol-probe`): a pay cell in
# JSON, one watcher observation to the enrollment index, both memo signatures
# checked by the pinned native verifier. The committed memo (a real
# `ssh-keygen -Y sign` run, `PayEnrolMemo.fixtureBytes`) and a FRESH one made in
# this run (PyNaCl Mini key, `ssh-keygen -t ed25519` + `ssh-keygen -Y sign -n
# dregg-enrol@v1`) must enroll; every journal reason and refusal is named.
#
# Part B — on a fresh Store: the controller (subject 7, pay-control capability
# 4031) revokes the observer's (30, 4030) grant through the ordinary revocation
# receiver; the next report is refused; it delegates `observePayment` (4040) to
# subject 31 and installs the pay law naming 31; 31's reports are accepted and
# 30's stay refused. The enrollment view (op 112) is read and rendered in the
# ROSTER-SYNC shape. Subject 31 is enrolled at genesis (its key); what is new at
# runtime is its grant and the law naming it.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jpay-e2: $name is required" >&2; exit 2; fi
done
command -v python3 >/dev/null || { echo "jpay-e2: python3 is required" >&2; exit 2; }
command -v ssh-keygen >/dev/null || { echo "jpay-e2: ssh-keygen is required" >&2; exit 2; }
python3 -c 'import nacl.signing' 2>/dev/null || { echo "jpay-e2: PyNaCl is required" >&2; exit 2; }
DIR="$JOURNEY_STEP_DIR/jpay-e2"
if [ -e "$DIR" ]; then echo "jpay-e2: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
exec python3 - "$DIR" <<'PY'
import base64, hashlib, json, os, struct, subprocess, sys, time
import nacl.signing

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
ROWS = []
EMBER, FACTORY, BOOK_ID, AUTH_ID, FACTORY_CONTROL = 7, 10, 11, 12, 53
OBSERVER, OBSERVER_CAP, PAY_CONTROL = 30, 4030, 4031
NEW_OBSERVER, NEW_OBSERVER_CAP = 31, 4040
SUBJECTS = [EMBER, OBSERVER, NEW_OBSERVER]
def acct(s): return 100 + s

P1_ADDRESS = "16946aa663362d557dd21ee08e8da60c2ea8a73467713c7c5205991e36634af5"
P1_MINT = "8525966c00f39ff54ef5e537a4736af436494d1f1681c659bd98e37ac28beff1"
P1_PROGRAM = "06ddf6e1ee758fde18425dbce46ccddab61afc4d83b90d27febdf928d8a18bfc"
# PayEnrolMemo.fixtureBytes: the committed real memo (mint P1_MINT, address P1_ADDRESS).
FIXTURE_MEMO = ("enrol:v1:197f6b23e16c8532c6abc838facd5ea789be0c76b2920334039bfa8b3d368d61:"
                "AAAAC3NzaC1lZDI1NTE5AAAAIG07ssw/nVQyEp4fbo6x0DefttH5CdsmuUI28/nc/UkK:"
                "1a89a4544250df3be16bd701357d114ccb00dabd79da77f35c8a394875cf78d8ef66b47d8a3cde4c21efd6c9aefd2fe7430adc047d67746498280c274adae202:"
                "e3024a122f7f20335c168b22d428617cbcfb4dc6d0b68f26dae8e2c2038641fd40d672e739b8a1d1a681f6d8488f46046985570f0ee30db01ae361309ff21f09")
BIRTH_FEE, WEEK_RATE = 9, 999999840
PRICE = BIRTH_FEE + WEEK_RATE          # 999 999 849 atomic units at rate 1

def path(name): return os.path.join(DIR, name)
def fail(message):
    print(f"J-PAY-E2 FAIL: {message}", file=sys.stderr); sys.exit(1)
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
            "tariffPerInitialPayloadByte": 0, "collector": 99, "asset": 0, "genesisHeight": 10,
            "expectedSeed": 0, "storageBinary": STORE, "storageRoot": path("store"),
            "signatureBinary": VERIFIER}
json.dump(operator, open(path("operator.json"), "w"), indent=1)
profile = json.loads(subprocess.run([HOST, path("operator.json"), "profile"], check=True,
                                    capture_output=True).stdout)
SEMANTICS = profile["semantics"]
genesis = {"domain": "8501", "factoryId": str(FACTORY), "resourceBookId": str(BOOK_ID),
           "authorityCellId": str(AUTH_ID), "federation": "9", "tariffBase": "3",
           "tariffPerBirth": "2", "tariffPerGrant": "1", "tariffPerInitialPayloadByte": "0",
           "collector": "99", "asset": "0", "expectedSemantics": SEMANTICS,
           "issuerEpoch": "2", "genesisHeight": "10",
           "factoryPredicate": {"type": "all", "predicates": []},
           "enrollments": [enrollment(s) for s in SUBJECTS],
           "factoryControllerSubject": str(EMBER),
           "factoryControllerCapability": str(FACTORY_CONTROL),
           "clockTickers": [],
           "tailBound": "1000000",
           "meterAllowance": {k: "10000000" for k in ("incidences", "turnBytes", "memoryTouches",
               "witnessBytes", "proofWork", "storageBytes", "networkBytes", "sideEffectCount",
               "feeDebit", "leaseByteBlocks")},
           "payObserver": {"subject": str(OBSERVER), "capability": str(OBSERVER_CAP),
                           "controlCapability": str(PAY_CONTROL), "enrolCapability": "4032"}}
json.dump(genesis, open(path("genesis.json"), "w"), indent=1)
boot = subprocess.run([MINI, "bootstrap", "--host", HOST, "--config", path("operator.json"),
                       "--source", path("genesis.json"), "--dir", path("deployment")], capture_output=True)
if boot.returncode != 0:
    fail("bootstrap: " + (boot.stdout + boot.stderr).decode("utf-8", "replace")[-400:])
CONFIG = path("deployment/pinned-config.json")
described = json.loads(subprocess.run([HOST, CONFIG, "describe"], check=True, capture_output=True).stdout)
PAY_CELL = described["payCell"]

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
PAY_OPS, OBSERVE_OPS = (103, 104, 105), (108, 109, 110)
def show(result): return f"{result.get('type')} {result.get('detail', '')}".strip()
def refused(result, reason):
    return result.get("type") == "refused" and reason in result.get("detail", "")
nonce = [500]
def fresh():
    nonce[0] += 1
    return str(nonce[0])

# ---------------------------------------------------------------- Part A: the decision
def tariff_json(enrol_index=0, mint=P1_MINT):
    return {"version": "2", "asset": "0", "mint": mint, "tokenProgram": P1_PROGRAM, "decimals": "6",
            "creditPerAtomic": "1", "maxPerObservation": "10000000000", "minTickSlots": "1500",
            "nodeWeekRate": str(WEEK_RATE),
            "enrolIndex": None if enrol_index is None else str(enrol_index), "journalFloor": "1000000", "slashCallerPermille": "500"}
def obs(amount, memo=None, memo_error=None, index=0, mint=P1_MINT, signature="55" * 64):
    return {"index": index, "address": P1_ADDRESS, "signature": signature, "slot": 900,
            "blockTime": 1799999000, "amount": amount, "mint": mint, "tokenProgram": P1_PROGRAM,
            "memo": None if memo is None else memo.encode().hex(), "memoError": memo_error}
def probe(observation, enrolments=(), ssh_index=(), subject_taken=False, **tariff_args):
    source = {"tariff": tariff_json(**tariff_args),
              "book": [P1_ADDRESS, "01" * 32, "02" * 32],
              "assignments": [{"index": "0", "account": "107"}],
              "enrolments": list(enrolments), "sshIndex": list(ssh_index),
              "birthFee": str(BIRTH_FEE), "subjectTaken": subject_taken,
              "tip": {"slot": "1000", "blockTime": "1800000000"}, "observation": observation}
    src, out = scratch("probe.json"), scratch("decision.json")
    json.dump(source, open(src, "w"))
    done = subprocess.run([HOST, CONFIG, "pay-enrol-probe", src, out], capture_output=True)
    if done.returncode != 0:
        return {"verdict": "error", "reason": (done.stdout + done.stderr).decode("utf-8", "replace")[-300:]}
    return json.load(open(out))
def verdict(d): return f"{d.get('verdict')} {d.get('reason', '')} verified={d.get('verified')}".strip()
def memo_fields(memo):
    return inspect("pay-enrol-memo", memo.encode())

fixture = memo_fields(FIXTURE_MEMO)
row("the committed memo parses under the Lean codec", "accepted, 400 bytes",
    f"accepted={fixture['accepted']} bytes={len(FIXTURE_MEMO)}", fixture["accepted"] and len(FIXTURE_MEMO) == 400)
HOUR = 1800000000 // 3600
d = probe(obs(1000000000, FIXTURE_MEMO))
row("committed real memo, 1000 DREGG", "enrol 1 week, index 1, both signatures verified",
    verdict(d) + f" weeks={d.get('weeks')} index={d.get('index')} leaseUntil={d.get('leaseUntil')}",
    d.get("verdict") == "enrol" and d.get("verified") == {"mini": True, "ssh": True}
    and d.get("weeks") == "1" and d.get("index") == "1" and d.get("leaseUntil") == str(HOUR + 168))

# A fresh enrollment made in this run with the real tools.
mini = nacl.signing.SigningKey.generate()
ssh_dir = path("ssh"); os.makedirs(ssh_dir)
subprocess.run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", "jpay-e2", "-f",
                os.path.join(ssh_dir, "key")], check=True)
blob = base64.b64decode(open(os.path.join(ssh_dir, "key.pub")).read().split()[1])
mint, address = bytes.fromhex(P1_MINT), bytes.fromhex(P1_ADDRESS)
open(os.path.join(ssh_dir, "message"), "wb").write(mint + address + mini.verify_key.encode())
subprocess.run(["ssh-keygen", "-Y", "sign", "-n", "dregg-enrol@v1", "-f", os.path.join(ssh_dir, "key"),
                os.path.join(ssh_dir, "message")], check=True, capture_output=True)
armour = open(os.path.join(ssh_dir, "message.sig")).read()
body = base64.b64decode("".join(l for l in armour.splitlines() if not l.startswith("-----")))
ssh_sig = body[-64:]
mini_sig = mini.sign(b"DREGG/PAY/ENROL/POSSESSION/v1" + mint + address + blob).signature
fresh_memo = ("enrol:v1:" + mini.verify_key.encode().hex() + ":" + base64.b64encode(blob).decode().rstrip("=")
              + ":" + mini_sig.hex() + ":" + ssh_sig.hex())
d = probe(obs(3 * PRICE, fresh_memo))
row("fresh memo (PyNaCl + ssh-keygen -Y sign), 3 weeks' worth", "enrol 3 weeks",
    verdict(d) + f" weeks={d.get('weeks')} len={len(fresh_memo)}",
    d.get("verdict") == "enrol" and d.get("verified") == {"mini": True, "ssh": True}
    and d.get("weeks") == "3" and len(fresh_memo) == 400)
d = probe(obs(PRICE, fresh_memo))
row("exactly the price", "enrol 1 week", verdict(d), d.get("verdict") == "enrol" and d.get("weeks") == "1")
d = probe(obs(PRICE - 1, fresh_memo))
row("one unit below the price", "journal belowPrice", verdict(d), d.get("verdict") == "journal" and d.get("reason") == "belowPrice")

fixture_key, fixture_blob = fixture["miniKey"], fixture["sshBlob"]
enrolled = [{"miniKey": fixture_key, "sshBlob": fixture_blob, "account": "150", "index": "1",
             "leaseUntil": str(HOUR + 100), "enrolledSlot": "800"}]
d = probe(obs(2 * PRICE, FIXTURE_MEMO), enrolments=enrolled)
row("the same memo again (a replay or a renewal)", "renew account 150 from the expiry, 2 weeks",
    verdict(d) + f" account={d.get('account')} from={d.get('leaseFrom')} until={d.get('leaseUntil')}",
    d.get("verdict") == "renew" and d.get("account") == "150" and d.get("leaseFrom") == str(HOUR + 100)
    and d.get("leaseUntil") == str(HOUR + 100 + 336))
lapsed = [dict(enrolled[0], leaseUntil=str(HOUR - 50))]
d = probe(obs(PRICE, FIXTURE_MEMO), enrolments=lapsed)
row("renewal of a lapsed lease", "renew from now, never from the past",
    verdict(d) + f" from={d.get('leaseFrom')}", d.get("verdict") == "renew" and d.get("leaseFrom") == str(HOUR))
d = probe(obs(1000000000, None))
row("no memo", "journal memoMissing", verdict(d), d.get("reason") == "memoMissing")
d = probe(obs(1000000000, None, "memoUnbound"))
row("two memo instructions (watcher memoUnbound)", "journal memoUnbound", verdict(d), d.get("reason") == "memoUnbound")
d = probe(obs(1000000000, None, "memoInvalid"))
row("non-UTF-8 memo (watcher memoInvalid)", "journal memoInvalid", verdict(d), d.get("reason") == "memoInvalid")
d = probe(obs(1000000000, FIXTURE_MEMO.replace("enrol:v1:", "enrol:v2:")))
row("memo version v2", "journal memoMalformed:memoVersion", verdict(d), d.get("reason") == "memoMalformed:memoVersion")
d = probe(obs(1000000000, FIXTURE_MEMO[:-1]))
row("truncated memo", "journal memoMalformed:memoShape", verdict(d), d.get("reason") == "memoMalformed:memoShape")
upper = FIXTURE_MEMO[:9] + FIXTURE_MEMO[9:73].upper() + FIXTURE_MEMO[73:]
d = probe(obs(1000000000, upper))
row("uppercase hex Mini key", "journal memoMalformed:memoBadMiniKey", verdict(d),
    d.get("reason") == "memoMalformed:memoBadMiniKey")
rsa_like = FIXTURE_MEMO[:74] + "AAAAB3NzaC1yc2EAAAADAQABAAAAIG07ssw/nVQyEp4fbo6x0DefttH5CdsmuUI28/nc/UkK"[:68] + FIXTURE_MEMO[142:]
d = probe(obs(1000000000, rsa_like))
row("an ssh-rsa blob in the memo", "journal memoMalformed:memoBadSshKey", verdict(d),
    d.get("reason") == "memoMalformed:memoBadSshKey")
def flip(memo, at):
    c = memo[at]
    return memo[:at] + ("0" if c != "0" else "1") + memo[at + 1:]
d = probe(obs(1000000000, flip(FIXTURE_MEMO, 150)))
row("mini-sig altered (someone else's Mini key)", "journal miniSigInvalid, native mini=false",
    verdict(d), d.get("reason") == "miniSigInvalid" and d.get("verified", {}).get("mini") is False)
d = probe(obs(1000000000, flip(FIXTURE_MEMO, 300)))
row("ssh-sig altered", "journal sshSigInvalid, native ssh=false",
    verdict(d), d.get("reason") == "sshSigInvalid" and d.get("verified") == {"mini": True, "ssh": False})
# Squat: the attacker's own Mini key signs the victim's ssh blob, but cannot make the SSHSIG.
attacker = nacl.signing.SigningKey.generate()
squat_sig = attacker.sign(b"DREGG/PAY/ENROL/POSSESSION/v1" + mint + address + bytes.fromhex(fixture_blob)).signature
squat = ("enrol:v1:" + attacker.verify_key.encode().hex() + FIXTURE_MEMO[73:143] + squat_sig.hex()
         + FIXTURE_MEMO[271:])
d = probe(obs(1000000000, squat))
row("squat: a stranger's Mini key with the victim's public ssh key", "journal sshSigInvalid",
    verdict(d), d.get("reason") == "sshSigInvalid" and d.get("verified") == {"mini": True, "ssh": False})
d = probe(obs(1000000000, FIXTURE_MEMO), ssh_index=[{"sshBlob": fixture_blob, "miniKey": "03" * 32}])
row("the ssh key is already enrolled under another Mini key", "journal sshKeyTaken", verdict(d),
    d.get("reason") == "sshKeyTaken")
other_blob = "0000000b7373682d6564323535313900000020" + "04" * 32
d = probe(obs(1000000000, FIXTURE_MEMO), enrolments=[dict(enrolled[0], sshBlob=other_blob)])
row("the Mini key is enrolled with another ssh key", "journal sshKeyMismatch", verdict(d),
    d.get("reason") == "sshKeyMismatch")
d = probe(obs(1000000000, FIXTURE_MEMO), subject_taken=True)
row("the derived subject is an operator-enrolled subject", "journal subjectTaken", verdict(d),
    d.get("reason") == "subjectTaken")
other_mint = "0a" * 32
d = probe(obs(1000000000, FIXTURE_MEMO, mint=other_mint), mint=other_mint)
row("the devnet memo replayed against another mint", "journal miniSigInvalid (the frames bind the mint)",
    verdict(d), d.get("reason") == "miniSigInvalid" and d.get("verified") == {"mini": False, "ssh": False})
d = probe(obs(999999, FIXTURE_MEMO))
row("below the journal floor", "refused belowJournalFloor", verdict(d),
    d.get("verdict") == "refused" and "belowJournalFloor" in d.get("reason", ""))
d = probe(obs(1000000000, FIXTURE_MEMO, index=1))
row("an ordinary index", "refused notEnrolIndex", verdict(d),
    d.get("verdict") == "refused" and "notEnrolIndex" in d.get("reason", ""))
d = probe(obs(1000000000, FIXTURE_MEMO), enrol_index=None)
row("self-enrollment off", "refused selfEnrolOff", verdict(d),
    d.get("verdict") == "refused" and "selfEnrolOff" in d.get("reason", ""))
d1 = probe(obs(2 * PRICE, FIXTURE_MEMO, signature="66" * 64), enrolments=enrolled)
d2 = probe(obs(2 * PRICE, FIXTURE_MEMO, signature="77" * 64), enrolments=enrolled)
row("the decision ignores which transaction carried the memo", "identical decisions",
    f"{verdict(d1)} == {verdict(d2)}", d1 == d2 and d1.get("verdict") == "renew")

# ---------------------------------------------------------------- Part B: observer replacement
def report(v, t, observer, capability):
    return {"observer": str(observer), "capability": str(capability), "nonce": fresh(),
            "expectedAuthorityRoot": v["authorityRoot"], "expectedPayRoot": v["payRoot"],
            "tip": t, "observations": []}
def tip(slot): return {"slot": slot, "blockTime": 1759249000 + slot}
def heartbeat(host, slot, observer, capability):
    v = view(host)
    return sign_and_submit(host, "pay-observation", report(v, tip(slot), observer, capability), observer,
                           OBSERVE_OPS)[0]
def mini_submit(name, intent, signer):
    source = path(f"{name}-intent.json")
    json.dump(intent, open(source, "w"))
    done = subprocess.run([MINI, "submit", "--host", HOST, "--config", CONFIG, "--intent", source,
                           "--key", path(f"subject-{signer}.key"), "--dir", path(f"{name}-attempt")],
                          capture_output=True)
    result_path = path(f"{name}-attempt/outcome.json")
    result = json.load(open(result_path)) if os.path.exists(result_path) else {}
    return done.returncode, result, (done.stdout + done.stderr).decode("utf-8", "replace")[-300:]
def mini_policy(name, signer, capability):
    intent = {"subject": str(signer), "nonce": fresh(),
              "purpose": {"type": "query", "kind": "program", "target": PAY_CELL, "view": "policy"},
              "grants": [{"kind": "program", "target": PAY_CELL, "capability": str(capability)}]}
    source = path(f"{name}-intent.json")
    json.dump(intent, open(source, "w"))
    done = subprocess.run([MINI, "query", "--host", HOST, "--config", CONFIG, "--intent", source,
                           "--key", path(f"subject-{signer}.key"), "--view", "policy",
                           "--dir", path(name)], capture_output=True)
    if done.returncode != 0:
        fail(f"policy query {name}: " + (done.stdout + done.stderr).decode("utf-8", "replace")[-400:])
    return json.load(open(path(f"{name}/view.json"))), json.load(open(path(f"{name}/challenge.json")))
def law(observer):
    return {"type": "any", "predicates": [
        {"type": "all", "predicates": [
            {"type": "eq", "slot": "request/verb", "value": "6"},
            {"type": "eq", "slot": "request/subject", "value": str(observer)}]},
        {"type": "all", "predicates": [
            {"type": "eq", "slot": "request/subject", "value": str(EMBER)},
            {"type": "memberOf", "slot": "request/verb", "values": ["1", "3", "4", "5"]}]}]}

host = Host()
op, data = host.call(112)
ev = inspect("pay-enrolment-view", data) if op == 112 else {}
row("op 112 on a fresh Store (the ROSTER-SYNC shape)", "view DREGG/PAY/ENROLMENT-VIEW/v3, clock.hour 0, no entries, no journal",
    json.dumps(ev, sort_keys=True)[:200],
    op == 112 and ev.get("view") == "DREGG/PAY/ENROLMENT-VIEW/v3" and ev.get("clock") == {"hour": 0}
    and ev.get("journal") == []
    and ev.get("entries") == [])
v = view(host)
book = {"sponsor": str(EMBER), "control": str(FACTORY_CONTROL), "nonce": fresh(),
        "expectedFactoryRoot": v["factoryRoot"], "expectedAuthorityRoot": v["authorityRoot"],
        "expectedPayRoot": v["payRoot"], "bookStart": "0", "book": [P1_ADDRESS],
        "tariff": tariff_json(enrol_index=None)}
r, _ = sign_and_submit(host, "pay-book", book, EMBER, PAY_OPS)
row("operator installs a 1-row book and tariff v2 (self-enrollment off)", "confirmed", show(r), r.get("type") == "confirmed")
v = view(host)
enrol_on = dict(book, nonce=fresh(), expectedAuthorityRoot=v["authorityRoot"], expectedPayRoot=v["payRoot"],
                expectedFactoryRoot=v["factoryRoot"], bookStart="1", book=[],
                tariff=dict(tariff_json(enrol_index=0), version="3"))
r, _ = sign_and_submit(host, "pay-book", enrol_on, EMBER, PAY_OPS)
# Op 105 is blind (MR's rule): built to hit enrolIndexUnassigned, the wire answers the
# uniform undisclosed frame, and the pay cell does not move.
row("tariff naming an unassigned enrollment index", "refused undisclosed (built to hit enrolIndexUnassigned), pay root unchanged",
    f"{r.get('type')} {r.get('reason', '')}",
    r.get("type") == "refused" and r.get("reason") == "undisclosed" and view(host)["payRoot"] == v["payRoot"])
r = heartbeat(host, 2000, OBSERVER, OBSERVER_CAP)
row("genesis observer 30 heartbeat", "confirmed", show(r), r.get("type") == "confirmed")
r = heartbeat(host, 3600, EMBER, PAY_CONTROL)
row("the controller's own report under its pay-control grant", "refused by the pay law", show(r),
    r.get("type") == "refused" and "policyRejected" in r.get("detail", ""))
v = view(host)
host.stop()

rc, r, tail = mini_submit("revoke", {"subject": str(EMBER), "nonce": fresh(), "purpose": {"type": "prepare", "draft": {
    "type": "revoke-source", "command": {"kind": "program", "subject": str(EMBER), "nonce": fresh(),
        "target": PAY_CELL, "victimKind": "program", "capability": str(OBSERVER_CAP),
        "controlCapability": str(PAY_CONTROL), "expectedTargetRoot": v["payRoot"],
        "expectedAuthorityRoot": v["authorityRoot"]}}},
    "grants": [{"kind": "program", "target": PAY_CELL, "capability": str(PAY_CONTROL)}]}, EMBER)
row("controller revokes observer 30's grant (ordinary revocation receiver)", "confirmed",
    f"rc={rc} {r.get('type')} {r.get('confirmation', '')} {tail if rc else ''}", rc == 0 and r.get("type") == "confirmed")

host = Host()
r = heartbeat(host, 5200, OBSERVER, OBSERVER_CAP)
row("observer 30 reports after the revocation", "refused (revoked grant)", show(r), r.get("type") == "refused")
v = view(host)
host.stop()

child = {"id": str(NEW_OBSERVER_CAP), "root": str(PAY_CONTROL), "parent": str(PAY_CONTROL), "issuer": "5",
         "holder": {"type": "subject", "subject": str(NEW_OBSERVER)}, "targets": [PAY_CELL],
         "verbs": ["observePayment"], "maxCost": "50000", "notBefore": "10", "notAfter": "10000",
         "issuerEpoch": "2", "policyId": PAY_CELL, "policyEpoch": "0", "ancestors": [str(PAY_CONTROL)],
         "channels": []}
rc, r, tail = mini_submit("delegate", {"subject": str(EMBER), "nonce": fresh(), "purpose": {"type": "prepare", "draft": {
    "type": "delegate-source", "command": {"kind": "program", "domain": "8501", "semantics": SEMANTICS,
        "subject": str(EMBER), "nonce": fresh(), "expectedTargetRoot": v["payRoot"], "parentId": str(PAY_CONTROL),
        "target": PAY_CELL, "expectedPreRoot": v["authorityRoot"], "child": child}}},
    "grants": [{"kind": "program", "target": PAY_CELL, "capability": str(PAY_CONTROL)}]}, EMBER)
row("controller delegates observePayment to subject 31 at runtime", "confirmed",
    f"rc={rc} {r.get('type')} {tail if rc else ''}", rc == 0 and r.get("type") == "confirmed")

host = Host()
r = heartbeat(host, 5300, NEW_OBSERVER, NEW_OBSERVER_CAP)
row("subject 31 reports before the law names it", "refused by the pay law", show(r),
    r.get("type") == "refused" and "policyRejected" in r.get("detail", ""))
host.stop()

policy, challenge = mini_policy("pay-policy-before", EMBER, PAY_CONTROL)
old_address = policy["address"]
rc, r, tail = mini_submit("install", {"subject": str(EMBER), "nonce": fresh(), "purpose": {"type": "prepare", "draft": {
    "type": "install-source", "subject": str(EMBER), "control": str(PAY_CONTROL), "declaration": {
        "expectedPreRoot": challenge["authorityRoot"],
        "expected": {"version": policy["version"], "address": old_address},
        "nonce": fresh(), "source": {"policyId": PAY_CELL, "version": str(int(policy["version"]) + 1),
            "domain": "8501", "semantics": SEMANTICS, "previous": old_address, "predicate": law(NEW_OBSERVER)}}}},
    "grants": [{"kind": "program", "target": PAY_CELL, "capability": str(PAY_CONTROL)}]}, EMBER)
row("controller installs the pay law naming subject 31", "confirmed",
    f"rc={rc} {r.get('type')} {tail if rc else ''}", rc == 0 and r.get("type") == "confirmed")

host = Host()
r = heartbeat(host, 5400, NEW_OBSERVER, NEW_OBSERVER_CAP)
row("subject 31 heartbeat under its delegated grant", "confirmed (reports resume)", show(r), r.get("type") == "confirmed")
r = heartbeat(host, 7000, OBSERVER, OBSERVER_CAP)
row("observer 30 after the replacement", "refused", show(r), r.get("type") == "refused")
v_final = view(host)
host.stop()

audit = subprocess.run([HOST, CONFIG, "audit"], capture_output=True)
audit_text = (audit.stdout + audit.stderr).decode("utf-8", "replace").strip().splitlines()
row("operator audit re-admits every record (NativeHostReplay)", "exit 0",
    f"exit={audit.returncode} {audit_text[-1] if audit_text else ''}", audit.returncode == 0)

rows_path = path("rows.tsv")
with open(rows_path, "w") as out:
    out.write("verdict\tstep\texpected\tobserved\n")
    for name, expected, observed, verdict_ in ROWS:
        out.write(f"{verdict_}\t{name}\t{expected}\t{observed}\n")
passed = sum(1 for r in ROWS if r[3] == "PASS")
final = f"J-PAY-E2 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - started:.1f} s)"
print(final)
print(final, file=sys.stderr)
print(rows_path)
sys.exit(0 if passed == len(ROWS) else 1)
PY
