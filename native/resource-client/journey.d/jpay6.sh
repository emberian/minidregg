#!/usr/bin/env bash
# J-PAY-6 (PAY P6): a Book burn funds an AgentGrain purse in one joint turn,
# on a fresh private Store.
#
# Follows the journey hook contract (journey.sh header): executed with HOST,
# MINI, STORE, VERIFIER and JOURNEY_STEP_DIR exported; it starts its OWN Host on
# its OWN fresh Store under JOURNEY_STEP_DIR and stops it. Exit 0 = PASS. The
# verdict `J-PAY-6 PASS n/n` is the last stderr line and the line before the
# last stdout line; the last stdout line is the deciding artifact (rows.tsv).
#
# Standalone: HOST=... MINI=... STORE=... VERIFIER=... GRAIN=grain-runtime
#   TEST_PROVIDER=mini-hermes-test-provider LAUNCH_GATE=launch-gate (the candidate's
#   bin/launch-gate, native/launch-gate) JOURNEY_STEP_DIR=NEW_DIR jpay6.sh
#
# The Hermes half runs the real grain-runtime controller (a transient
# `systemd-run --user` unit with Restart=on-failure) with a metered
# providerTask on purse 7004 and the deterministic `hermes-test-provider
# --metered-usage` upstream (1 prompt + 2 completion tokens). The worker is the
# real bwrap launcher running `jpay6-hermes-acp`, a scripted ACP stand-in that
# makes one chat-completions request per prompt through the controller's
# gateway (no Hermes checkout exists on hbox). The Host pins a per-route
# provider tariff (HERMES-TARIFF), in credit: the user route (the friend's own
# key) costs a per-operation fee of 5 and nothing else; the pool route costs a
# fee of 7 plus 20 credits per million input and 40 per million output tokens,
# so one metered completion charges 7 + ceil((1*20e6 + 2*40e6)/1e6) = 107; the
# homelab route costs a fee of 3. The purse is born under that per-route law,
# so it records the route at reserve and charges by it at settle.
# HERMES-TARIFF rows: a call on the friend's own key (user route) debits the
# fee exactly and the upstream saw the friend's bearer; after the friend
# revokes, a call with no payer is refused before any reserve; a pool call is
# metered with the pool bearer; and once the uncertain pool call is held, a
# settle of that hold as a user call is refused three ways (Host authoring by
# name, the receiver's old-value check, the route law's pool fee).
# The uncertain attempt: the upstream is SIGSTOPped, a second prompt crosses
# the gateway's durable send boundary, the controller is SIGKILLed, systemd
# restarts it, the upstream is SIGCONTed (it receives the one stalled request),
# and the owner's reconnect runs `recover` (on this branch recovery is the
# owner's explicit command). The provider's own request log is the count.
#
# Genesis enrolls the grain acceptance's three hosted subjects (7 operator and
# parent-grain owner, 8 tool worker, 9 provider worker; accounts 7/8/9) plus a
# friend (subject 20, account 20, genesis balance 60 000 000 credit in asset 0)
# and a stranger (subject 21). The first event is the grain acceptance's
# historical birth: parent 7001 (workers 8 and 9), tool 7002, publication 7003
# and the provider purse 7004 (owner 9, budget 50), through `mini serve` and
# `mini submit`. The operator then installs a one-row book and a tariff whose
# credit asset is 0; the friend takes index 0 (so `pay-ledger` lists it). The
# friend's refills drive the Host's raw operations 113-116 (`mini pay refill`
# is the client verb; this hook signs with PyNaCl so it can also author the
# refusal poles the client never would, e.g. a purse leg claiming more than the
# burn). Every byte the Host accepts is authored and inspected by the Host's own
# codecs. Balances and the purse come from the Host's local `pay-ledger` and
# `pay-purse` reads of the Store, taken with the Host stopped.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR GRAIN TEST_PROVIDER LAUNCH_GATE; do
  if [ -z "${!name:-}" ]; then echo "jpay6: $name is required" >&2; exit 2; fi
done
REPO=$(CDPATH='' cd -- "$(dirname -- "$0")/../../.." && pwd)
. "$REPO/native/resource-client/journey.d/lib/genesis-params.sh"
resolve_params_sh "$REPO" || exit 2
export REPO
HERMES_STANDIN="$REPO/native/resource-client/journey.d/jpay6-hermes-acp"
export HERMES_STANDIN
[ -x "$HERMES_STANDIN" ] || { echo "jpay6: $HERMES_STANDIN is required" >&2; exit 2; }
command -v python3 >/dev/null || { echo "jpay6: python3 is required" >&2; exit 2; }
python3 -c 'import nacl.signing' 2>/dev/null || { echo "jpay6: PyNaCl is required" >&2; exit 2; }
# Its Host socket and the grain controller's control, admin and MCP sockets
# live in a short directory, kept as $JOURNEY_STEP_DIR/rt
# (journey.d/lib/shortdir.sh); python runs as a child so the copy-back runs.
. "$REPO/native/resource-client/journey.d/lib/shortdir.sh"
journey_shortdir jpay6
DIR=$JOURNEY_D
mkdir -p "$DIR"
python3 - "$DIR" <<'PY'
import json, os, signal, socket, struct, subprocess, sys, time
import nacl.signing
def attempt_answer(p):  # an attempt's retained answer via `mini attempt-state` (repaired from seal.record), never the file
    r = subprocess.run([MINI, "attempt-state", "--attempt", os.path.dirname(p), "--file", os.path.basename(p)], capture_output=True, text=True)
    if r.returncode: raise OSError(r.stderr.strip() or "no answer")
    return json.loads(r.stdout)

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
GRAIN, TEST_PROVIDER, REPO, STANDIN, LAUNCH_GATE = (os.environ[k] for k in
    ("GRAIN", "TEST_PROVIDER", "REPO", "HERMES_STANDIN", "LAUNCH_GATE"))
MODEL = "mini-hermes-protocol-fixture"
RATE_IN, RATE_OUT = 20_000_000, 40_000_000       # credit per million tokens
USER_FEE, POOL_FEE, HOMELAB_FEE = 5, 7, 3
METERED_CHARGE = POOL_FEE + (1 * RATE_IN + 2 * RATE_OUT + 999_999) // 1_000_000
PROVIDER_RESERVE = 30_000
MAX_IN, MAX_OUT = 1000, 100
FRIEND_KEY, POOL_KEY = "friend-fixture-key", "local-fixture-key"
import hashlib
def bearer_digest(token): return "sha256:" + hashlib.sha256(("Bearer " + token).encode()).hexdigest()
ROWS = []
OPERATOR, TOOL, PROVIDER, FRIEND, STRANGER = 7, 8, 9, 20, 21
FACTORY_CONTROL = 53
# JPAY6_BASE moves the four ids (and so the controller unit name) off a box's live
# mini-grain-controller@7001 (persvati keeps one); the default is the historical birth.
BASE = int(os.environ.get("JPAY6_BASE", "7001"))
PARENT, TOOL_TASK, PUBLICATION, PURSE = BASE, BASE + 1, BASE + 2, BASE + 3
FRIEND_BALANCE = 60_000_000
REFILL = 50_000_000
SUBJECTS = [OPERATOR, TOOL, PROVIDER, FRIEND, STRANGER]
CAPS = {OPERATOR: (41, 51, 54), TOOL: (42, 52, 55), PROVIDER: (43, 56, 57),
        FRIEND: (1020, 2020, 3020), STRANGER: (1021, 2021, 3021)}
BALANCE = {OPERATOR: 100, TOOL: 100, PROVIDER: 100, FRIEND: FRIEND_BALANCE, STRANGER: 100}

def path(name): return os.path.join(DIR, name)
# Consent anchors and resident providers of every mini this journey starts (the
# controller unit too, by --setenv) stay in its own directory, never ~/.mini.
os.environ["MINI_CONSENT_ANCHOR_DIR"] = path("consent-anchors")
LIVE = []          # child processes to stop on any exit
UNITS = []         # transient systemd units to stop on any exit
def cleanup():
    for unit in UNITS:
        subprocess.run(["systemctl", "--user", "stop", unit], capture_output=True)
    for proc in LIVE:
        if proc.poll() is None:
            try:
                proc.send_signal(signal.SIGCONT); proc.terminate(); proc.wait(timeout=30)
            except Exception:
                proc.kill()
import atexit
atexit.register(cleanup)
signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
def fail(message):
    print(f"J-PAY-6 FAIL: {message}", file=sys.stderr); sys.exit(1)

# ---------------------------------------------------------------- keys and genesis
os.makedirs(path("keys"), mode=0o700)
keys = {}
for s in SUBJECTS:
    keys[s] = nacl.signing.SigningKey.generate()
    fd = os.open(path(f"keys/{s}.key"), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    os.write(fd, bytes(keys[s])); os.close(fd)
TAIL_BOUND = 1000000
NEXT_PUBLIC = {}   # subject -> its next public key (hex); genesis.sh commits the digest
def enrollment(s):
    # the compact form genesis.sh completes (keyEpoch, activity window, nextKeyDigest, accountPredicate)
    spend, control, observe = CAPS[s]
    entry = {"subject": s, "keyId": 7000 + s if s >= 20 else 1001 * s,
             "publicKey": keys[s].verify_key.encode().hex(), "accountId": s, "spendCapabilityId": spend,
             "controlCapabilityId": control, "factoryObserveCapabilityId": observe, "initialBalance": BALANCE[s]}
    if s in NEXT_PUBLIC: entry["nextPublicKey"] = NEXT_PUBLIC[s]
    return entry
# The provider service pin (the purse's per-route tariff), pinned at genesis.
operator = {"providerServices": [{"providerResourceId": PURSE, "tariff": {
                "version": "1", "model": MODEL, "routes": {
                    "user": {"perOp": str(USER_FEE)},
                    "pool": {"perOp": str(POOL_FEE), "inputMicroPerMillion": str(RATE_IN),
                             "outputMicroPerMillion": str(RATE_OUT)},
                    "homelab": {"perOp": str(HOMELAB_FEE), "inputMicroPerMillion": "0",
                                "outputMicroPerMillion": "0"}}}}]}
# genesis seam: extractors adjust TAIL_BOUND, NEXT_PUBLIC and operator["providerServices"] here
# The genesis is the one template's (scenario-genesis.sh): this journey passes only what its world
# differs by. OPERATOR is the sponsor (its keyId, account and capabilities are the example's).
with open(path("enrollments.json"), "w") as out:
    json.dump([enrollment(s) for s in SUBJECTS if s != OPERATOR], out)
spend, control, observe = CAPS[OPERATOR]
# The clock subject keeps its frame role but not the example's capability numbers
# 71-74: the historical birth installs 71/72 (the parent's owner and control
# capabilities) and the delegations install 73 and 75 (the parent witnesses), and
# a birth whose grants reuse an installed capability is refused at prepare
# (ResourceBirthController `authorityBatch`) - the grain acceptance moves its
# clock the same way (native/grain-runtime/acceptance.sh).
overlay = (f"del(.grainPlatform) | .clock += {{tickCapabilityId: 4071, spendCapabilityId: 4072,"
           f" controlCapabilityId: 4073, factoryObserveCapabilityId: 4074}}"
           f" | .tailBound = {TAIL_BOUND} | .factoryControllerCapability = {FACTORY_CONTROL}"
           f" | .sponsor.subject = {OPERATOR} | .sponsor.keyId = {1001 * OPERATOR} | .sponsor.accountId = {OPERATOR}"
           f" | .sponsor.spendCapabilityId = {spend} | .sponsor.controlCapabilityId = {control}"
           f" | .sponsor.factoryObserveCapabilityId = {observe} | .sponsor.initialBalance = {BALANCE[OPERATOR]}"
           f" | .providerServices = {json.dumps(operator['providerServices'])}")
subprocess.run(["sh", os.path.join(os.environ["REPO"], "native/resource-client/scenario-genesis.sh"), DIR,
                keys[OPERATOR].verify_key.encode().hex(), overlay, path("enrollments.json")], check=True,
               env=dict(os.environ, HOST=HOST, MINI=MINI, STORE=STORE, VERIFIER=VERIFIER))
profile = json.load(open(path("profile.json")))
# The birth intent embeds the FILLED genesis: the Host refuses a birth whose genesis lacks the clock
# fields the helper wrote ("$.birth.genesis: missing field clockGenesisNow", the real JPAY6 red of a0db11f8).
genesis = json.load(open(path("genesis.json")))
boot = subprocess.run([MINI, "bootstrap", "--host", HOST, "--config", path("operator.json"),
                       "--source", path("genesis.json"), "--dir", path("deployment")], capture_output=True)
if boot.returncode != 0:
    fail("bootstrap: " + (boot.stdout + boot.stderr).decode("utf-8", "replace")[-400:])
CONFIG = path("deployment/pinned-config.json")
# The provider service pin is in force from the first event: the purse's birth
# reads the Host's per-route tariff to install its route law, and the local
# consent provider (same settings file) refuses a purse law without it.
pinned = json.load(open(CONFIG))
pinned.setdefault("providerServices", operator["providerServices"])
CONFIG = path("deployment/continuity-config.json")
json.dump(pinned, open(CONFIG, "w"), indent=1)

# ---------------------------------------------------------------- the purse: the grain birth (first event)
os.makedirs(path("session"), mode=0o700)
SOCKET = path("session/host.sock")
ACTIVE = [CONFIG]
class Serve:
    def __init__(self):
        self.log = open(path("serve.stderr"), "ab")
        self.proc = subprocess.Popen([MINI, "serve", "--host", HOST, "--config", ACTIVE[0], "--socket", SOCKET],
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

birth = {"subject": str(OPERATOR), "nonce": "22000",
         "birth": {"genesis": genesis, "template": {"issuer": "5", "ownerBudget": "100000", "lifetime": "10000"},
                   "creator": str(OPERATOR), "nonce": "22000", "resources": [
                       {"kind": "object", "storage": "grain", "target": str(PARENT), "owner": "7",
                        "ownerCapability": "71", "controlCapability": "72", "budget": "100",
                        "workerSubjects": ["8", "9"], "workerGeneration": "1"},
                       {"kind": "object", "storage": "grain", "target": str(TOOL_TASK), "owner": "8",
                        "ownerCapability": "81", "controlCapability": "82", "budget": "50"},
                       {"kind": "object", "storage": "declared", "target": str(PUBLICATION), "owner": "7",
                        "ownerCapability": "91", "controlCapability": "92",
                        "predicate": {"type": "all", "predicates": []}},
                       {"kind": "object", "storage": "grain", "target": str(PURSE), "owner": "9",
                        "ownerCapability": "101", "controlCapability": "102", "budget": "50"}],
                   "sourceCapabilities": ["41"], "funding": [], "feePayer": "7"},
         "grants": [{"kind": "object", "target": "10", "capability": "54"},
                    {"kind": "account", "target": "7", "capability": "41"}]}
json.dump(birth, open(path("birth-intent.json"), "w"))
SEMANTICS = profile["semantics"]
def mini_submit(name, intent, signer, kind=None):
    json.dump(intent, open(path(f"{name}-intent.json"), "w"))
    words = [MINI, "submit", "--host", HOST, "--config", CONFIG, "--socket", SOCKET,
             "--intent", path(f"{name}-intent.json"), "--key", path(f"keys/{signer}.key"),
             "--dir", path(f"{name}-attempt")]
    if kind: words[words.index("--intent"):words.index("--intent")] = ["--intent-kind", kind]
    done = subprocess.run(words, capture_output=True)
    open(path(f"{name}.stderr"), "wb").write(done.stdout + done.stderr)
    try: return attempt_answer(path(f"{name}-attempt/outcome.json"))
    except (OSError, ValueError): return {"type": "no-outcome", "exit": done.returncode}
query_nonce = [40000]
def mini_query(name, subject, target, capability):
    query_nonce[0] += 1
    intent = {"subject": str(subject), "nonce": str(query_nonce[0]),
              "purpose": {"type": "query", "kind": "object", "target": str(target), "view": "resource"},
              "grants": [{"kind": "object", "target": str(target), "capability": str(capability)}]}
    json.dump(intent, open(path(f"{name}-query.json"), "w"))
    done = subprocess.run([MINI, "query", "--host", HOST, "--config", ACTIVE[0], "--socket", SOCKET,
                           "--intent", path(f"{name}-query.json"), "--key", path(f"keys/{subject}.key"),
                           "--view", "resource", "--dir", path(f"{name}-query")], capture_output=True)
    if done.returncode != 0:
        fail(f"query {name}: " + (done.stdout + done.stderr).decode("utf-8", "replace")[-300:])
    view = json.load(open(path(f"{name}-query/view.json")))
    challenge = json.load(open(path(f"{name}-query/challenge.json")))
    cell = view.get("cell") or view.get("page")
    return cell, challenge["authorityRoot"]
def delegate(name, target, parent, child, holder, verbs, nonce):
    cell, authority = mini_query(name + "-pre", OPERATOR, target, parent)
    intent = {"subject": "7", "nonce": str(nonce), "purpose": {"type": "prepare", "draft": {
        "type": "delegate-source", "command": {"kind": "object", "domain": "8501",
        "semantics": SEMANTICS, "subject": "7", "nonce": str(nonce + 1),
        "expectedTargetRoot": cell["root"], "parentId": str(parent), "target": str(target),
        "child": {"id": str(child), "root": str(parent), "parent": str(parent), "issuer": "5",
                  "holder": {"type": "subject", "subject": str(holder)}, "targets": [str(target)],
                  "verbs": verbs, "maxCost": "50000", "notBefore": "10", "notAfter": "1000",
                  "issuerEpoch": "2", "policyId": str(target), "policyEpoch": "0",
                  "ancestors": [str(parent)], "channels": []}}}},
        "grants": [{"kind": "object", "target": str(target), "capability": str(parent)}]}
    return mini_submit(name, intent, OPERATOR)

serve = Serve()
born = mini_submit("birth", birth, OPERATOR, kind="birth-intent")
delegations = [delegate("parent-witness-tool", PARENT, 71, 73, TOOL, ["observe", "mutate"], 31000),
               delegate("parent-witness-provider", PARENT, 71, 75, PROVIDER, ["observe", "mutate"], 31004),
               delegate("publication-tool", PUBLICATION, 91, 93, TOOL, ["observe", "mutate"], 31010),
               delegate("publication-read", PUBLICATION, 91, 94, TOOL, ["observe"], 31020)]
serve.stop()
sub = subprocess.CompletedProcess([], 0 if born.get("type") == "confirmed" else 1)

# ---------------------------------------------------------------- Host plumbing (the jpay3 pattern)
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
def purse(task=PURSE):
    out = scratch("purse.json"); cli("pay-purse", str(task), out); return json.load(open(out))
def balance(led, account):
    for r in led["payers"]:
        if r["account"] == str(account): return int(r["balance"])
    fail(f"account {account} not in ledger")

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
PAY_OPS, REFILL_OPS = (103, 104, 105), (113, 114, 115)

def row(name, expected, observed, ok):
    observed = " ".join(str(observed).split())
    ROWS.append((name, expected, observed, "PASS" if ok else "FAIL"))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{observed}", file=sys.stderr)
def refused_with(result, reason):
    # Op 115 is a blind submission (MR's rule, as op 105): every refusal is the
    # uniform `undisclosed` frame. `reason` names the branch the command was
    # built to hit, which the wire deliberately does not confirm; the ledger and
    # purse rows that follow each refusal check that nothing moved.
    return result.get("type") == "refused" and result.get("reason") == "undisclosed"
def show(result): return f"{result.get('type')} {result.get('reason', '')} {result.get('detail', '')}".strip()

nonce = [100]
def fresh():
    nonce[0] += 1; return str(nonce[0])
def refill_command(v, subject, capability, account, amount, gain, task=PURSE):
    return {"subject": str(subject), "capability": str(capability), "account": str(account),
            "task": str(task), "amount": str(amount), "gain": str(gain), "nonce": fresh(),
            "expectedAuthorityRoot": v["authorityRoot"]}
def refill(host, subject, capability, account, amount, gain, task=PURSE):
    return sign_and_submit(host, "pay-refill", refill_command(view(host), subject, capability, account,
                                                              amount, gain, task), subject, REFILL_OPS)
def budget(p): return int(p["remaining"]) + int(p["reserved"])

# ---------------------------------------------------------------- the journey
started = time.time()
row(f"grain birth (parent {PARENT}, tool {TOOL_TASK}, publication {PUBLICATION}, provider purse {PURSE}) is the first event",
    "confirmed installed", f"{born.get('type')} {born.get('confirmation')} exit={sub.returncode}",
    born.get("type") == "confirmed" and born.get("confirmation") == "installed")
p0 = purse()
row("the hosted grain's four ordinary delegations (73, 75, 93, 94)", "4 x confirmed installed",
    " ".join(f"{d.get('type')}/{d.get('confirmation')}" for d in delegations),
    all(d.get("type") == "confirmed" for d in delegations))
row(f"purse {PURSE} at birth", "generation 0, status 0, remaining 50, reserved 0",
    f"g={p0['generation']} s={p0['status']} remaining={p0['remaining']} reserved={p0['reserved']}",
    (p0["generation"], p0["status"], p0["remaining"], p0["reserved"]) == ("0", "0", "50", "0"))

host = Host()
r, _ = refill(host, FRIEND, CAPS[FRIEND][0], FRIEND, REFILL, REFILL)
row("refill before a valid tariff (the credit asset is the tariff's)", "refused undisclosed (built to hit tariffInvalid)", show(r),
    refused_with(r, "tariffInvalid"))
v = view(host)
tariff = {"version": "1", "asset": "0", "mint": "85" * 32, "tokenProgram": "06" * 32, "decimals": "6",
          "creditPerAtomic": "1", "maxPerObservation": "2000000000", "minTickSlots": "1500",
          "nodeWeekRate": "999999840", "enrolIndex": None, "journalFloor": "1000000", "slashCallerPermille": "500"}
book_cmd = {"sponsor": str(OPERATOR), "control": str(FACTORY_CONTROL), "nonce": fresh(),
            "expectedFactoryRoot": v["factoryRoot"], "expectedAuthorityRoot": v["authorityRoot"],
            "expectedPayRoot": v["payRoot"], "bookStart": "0", "book": ["16" * 32], "tariff": tariff}
r, _ = sign_and_submit(host, "pay-book", book_cmd, OPERATOR, PAY_OPS)
row("operator installs a one-row book and a tariff (credit asset 0)", "confirmed", show(r), r.get("type") == "confirmed")
v = view(host)
assign = {"subject": str(FRIEND), "capability": str(CAPS[FRIEND][0]), "account": str(FRIEND), "index": "0",
          "nonce": fresh(), "expectedAuthorityRoot": v["authorityRoot"], "expectedPayRoot": v["payRoot"]}
r, _ = sign_and_submit(host, "pay-assign", assign, FRIEND, PAY_OPS)
row("friend takes index 0 for account 20", "confirmed", show(r), r.get("type") == "confirmed")
host.stop()
led0, p1 = ledger(), purse()
row("ledger before any refill", f"friend {FRIEND_BALANCE}, purse 50",
    f"friend={balance(led0, FRIEND)} well={led0['well']} total={led0['total']} purse={p1['remaining']}",
    balance(led0, FRIEND) == FRIEND_BALANCE and p1["remaining"] == "50")

host = Host()
r, _ = refill(host, FRIEND, CAPS[FRIEND][0], FRIEND, REFILL, REFILL + 10_000_000)
row("a purse leg claiming 60 000 000 with a 50 000 000 burn", "refused undisclosed (built to hit unbalanced (the joint commit))",
    show(r), refused_with(r, "unbalanced"))
r, _ = refill(host, STRANGER, CAPS[STRANGER][0], FRIEND, 1_000_000, 1_000_000)
row("a stranger (subject 21, its own capability) burns the friend's account", "refused undisclosed (built to hit notOwner)",
    show(r), refused_with(r, "notOwner"))
r, _ = refill(host, STRANGER, CAPS[FRIEND][0], FRIEND, 1_000_000, 1_000_000)
row("a stranger presents the friend's capability", "refused undisclosed (built to hit notOwner)", show(r), refused_with(r, "notOwner"))
r, _ = refill(host, FRIEND, CAPS[FRIEND][0], FRIEND, 0, 0)
row("a zero refill", "refused undisclosed (built to hit zeroAmount)", show(r), refused_with(r, "zeroAmount"))
r, _ = refill(host, FRIEND, CAPS[FRIEND][0], FRIEND, 1_000_000, 1_000_000, task=PUBLICATION)
row("a refill of a declared object that is not an AgentGrain purse", "refused undisclosed (built to hit purseUnreadable)",
    show(r), refused_with(r, "purseUnreadable"))
host.stop()
led_poles, p_poles = ledger(), purse()
row("the refused refills moved nothing", "ledger and purse unchanged",
    f"friend={balance(led_poles, FRIEND)} well={led_poles['well']} purse root equal={p_poles['root'] == p1['root']}",
    led_poles == led0 and p_poles == p1)

host = Host()
r, refill_ingress = refill(host, FRIEND, CAPS[FRIEND][0], FRIEND, REFILL, REFILL)
row(f"friend refills purse {PURSE} with 50 000 000 credit", "confirmed", show(r), r.get("type") == "confirmed")
op, data = host.call(116, refill_ingress)
looked = outcome(data) if op == 116 else {"type": "op-failed"}
row("receipt-only lookup of that refill (op 116)", "confirmed replayed",
    f"{looked.get('type')} {looked.get('confirmation')}",
    looked.get("type") == "confirmed" and looked.get("confirmation") == "replayed")
op, data = host.call(115, refill_ingress)
again = outcome(data) if op == 115 else {"type": "op-failed"}
row("the same signed refill submitted again", "confirmed replayed (no second burn)",
    f"{again.get('type')} {again.get('confirmation')}",
    again.get("type") == "confirmed" and again.get("confirmation") == "replayed")
host.stop()
led1, p2 = ledger(), purse()
row("Book: friend -50 000 000, well +50 000 000, total (well included) unchanged",
    "friend 10000000", f"friend={balance(led1, FRIEND)} well {led0['well']} -> {led1['well']} total {led0['total']} -> {led1['total']}",
    balance(led1, FRIEND) == FRIEND_BALANCE - REFILL and int(led1["well"]) == int(led0["well"]) + REFILL
    and led1["total"] == led0["total"])
row(f"purse {PURSE}: remaining +50 000 000, nothing else moved", "remaining 50000050, g 0 s 0 reserved 0",
    f"g={p2['generation']} s={p2['status']} remaining={p2['remaining']} reserved={p2['reserved']}",
    int(p2["remaining"]) == int(p1["remaining"]) + REFILL and
    (p2["generation"], p2["status"], p2["reserved"]) == (p1["generation"], p1["status"], p1["reserved"]))
row("the joint delta at the credit coordinate", "Book circulating -50000000 + purse +50000000 = 0",
    f"book={(int(led1['total']) - int(led1['well'])) - (int(led0['total']) - int(led0['well']))} purse={budget(p2) - budget(p1)}",
    (int(led1['total']) - int(led1['well'])) - (int(led0['total']) - int(led0['well'])) + budget(p2) - budget(p1) == 0)

host = Host()
r, _ = refill(host, FRIEND, CAPS[FRIEND][0], FRIEND, 20_000_000, 20_000_000)
row("refill 20 000 000 with a 10 000 000 balance", "refused undisclosed (built to hit bookRefused)", show(r), refused_with(r, "bookRefused"))
host.stop()

# ---------------------------------------------------------------- the Hermes half: the controller draws on the purse
def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0)); return probe.getsockname()[1]
def wait_for(label, predicate, seconds=600, step=0.5):
    deadline = time.time() + seconds
    while time.time() < deadline:
        try:
            value = predicate()
            if value: return value
        except (OSError, ValueError, KeyError):
            pass
        time.sleep(step)
    fail(f"timed out waiting for {label}")
def upstream_requests():
    try: lines = open(path("upstream.log")).read().splitlines()
    except OSError: return 0
    return sum(1 for line in lines if line.startswith(("completion", "reject", "metered-422")))
UPORT, GPORT = free_port(), free_port()
STATE, RUNTIME, WORK = path("runtime-state"), path("runtime-root"), path("worker-work")
for d in (STATE, RUNTIME, WORK, path("launcher")): os.makedirs(d, mode=0o700)
os.chmod(RUNTIME, 0o755)
for source, name in ((GRAIN, "grain-runtime"), (STANDIN, "hermes-acp")):
    data = open(source, "rb").read()
    open(os.path.join(RUNTIME, name), "wb").write(data); os.chmod(os.path.join(RUNTIME, name), 0o755)
# The physical bwrap (MINI_BWRAP selects; see resolve-bwrap) and the launcher materialized for it.
resolved = subprocess.run(["sh", os.path.join(REPO, "deploy/grain-host/resolve-bwrap")], capture_output=True, text=True)
if resolved.returncode != 0:
    fail("bwrap: " + resolved.stderr.strip())
BWRAP = resolved.stdout.strip()
LAUNCHER = path("launcher/bwrap")
materialized = subprocess.run([sys.executable, os.path.join(REPO, "deploy/grain-host/materialize-bwrap.py"),
                               "--physical-bwrap", BWRAP, "--physical-sha256",
                               hashlib.sha256(open(BWRAP, "rb").read()).hexdigest(), "--output", LAUNCHER],
                              capture_output=True, text=True)
if materialized.returncode != 0:
    fail("materialize-bwrap: " + materialized.stderr.strip())
open(path("launcher.json"), "w").write(materialized.stdout)
os.chmod(LAUNCHER, 0o700)
open(path("launcher/launch-gate"), "wb").write(open(LAUNCH_GATE, "rb").read())
os.chmod(path("launcher/launch-gate"), 0o700)
# HERMES-KEYS/-TARIFF: the provider request's route is a row of the operator's
# provider table (root-owned, as in production: `sudo -n install`); the row's
# credential kind is the route (user | pool | homelab), and the Host's
# per-route tariff prices it. The pool row carries the operator's caps.
CRED, CKEY = path("credentials"), path("etc/credentials.key")
os.makedirs(CRED, mode=0o700); os.makedirs(path("etc"), mode=0o700)
open(CKEY, "wb").write(os.urandom(32)); os.chmod(CKEY, 0o600)
TABLE_SOURCE, TABLE = path("providers-source.json"), path("etc/providers.json")
ENDPOINT = f"http://127.0.0.1:{UPORT}/v1/chat/completions"
TABLE_ROWS = {
    "user": {"name": "friendkey", "endpoint": ENDPOINT, "kind": "openai-compatible",
             "models": [MODEL], "credential": "user"},
    "pool": {"name": "local", "endpoint": ENDPOINT, "kind": "openai-compatible",
             "models": [MODEL], "credential": "pool", "caps": {"perCall": "64", "perDay": "10"}}}
INSTALL = "/usr/bin/install"
# The one root step of this journey, probed as the one rule it needs (a targeted sudoers rule satisfies it;
# a broad one is never required): RUNNER ALL=(root) NOPASSWD: /usr/bin/install
probe = subprocess.run(["sudo", "-n", "-l", INSTALL], capture_output=True)
if probe.returncode != 0:
    import pwd
    fail(f"missing input: sudoers rule {pwd.getpwuid(os.getuid()).pw_name} ALL=(root) NOPASSWD: {INSTALL} "
         "(the provider table is root-owned, as in production): " + probe.stderr.decode("utf-8", "replace")[-160:])
def install_table(*routes):
    json.dump({"type": "mini-provider-table-v2", "providers": [TABLE_ROWS[r] for r in routes]},
              open(TABLE_SOURCE, "w"))
    installed = subprocess.run(["sudo", "-n", INSTALL, "-o", "root", "-g", "root", "-m", "0644",
                                TABLE_SOURCE, TABLE], capture_output=True)
    if installed.returncode != 0:
        fail(f"the provider table must be root-owned; sudo -n {INSTALL} failed: "
             + installed.stderr.decode("utf-8", "replace")[-200:])
install_table("user", "pool")
# Credential custody is the key broker's (native/mini-keys): same account in this
# journey, production binary and checks. `mini key` and the controller ask it.
sys.path.insert(0, os.path.join(REPO, "native/mini-keys"))
import atexit, journey_broker
KEYS_PROC, KEYS_CLIENT = journey_broker.start(DIR, MINI, providers=TABLE, host=HOST, host_config=CONFIG,
                                              public_socket=SOCKET, seal_key=CKEY, credentials=CRED)
atexit.register(KEYS_PROC.kill)
def mini_key(label, *words, secret=None):
    words = list(words)
    if secret is not None:
        secret_path = path(f"{label}.secret")
        open(secret_path, "w").write(secret + "\n"); os.chmod(secret_path, 0o600)
        words += ["--secret", secret_path]
    done = subprocess.run([MINI, "key", *words, "--broker", KEYS_CLIENT], capture_output=True)
    if secret is not None: os.unlink(secret_path)
    open(path(f"key-{label}.out"), "wb").write(done.stdout + done.stderr)
    if done.returncode != 0:
        fail(f"mini key {label}: " + (done.stdout + done.stderr).decode("utf-8", "replace")[-300:])
mini_key("pool", "--action", "set", "--pool", "true", "--provider", "local", secret=POOL_KEY)
# The friend's own provider key, in the friend's own namespace (their
# workspace's subject and signing key), granted to the provider runner 9.
FRIEND_WS = path("friend-workspace")
# `workspace init` and the key grants reach the Host through --socket, so the Hermes half's Serve
# starts here and lives until that half stops it.
serve = Serve()
ws = subprocess.run([MINI, "workspace", "--action", "init", "--host", HOST, "--config", CONFIG, "--socket", SOCKET,
                     "--key", path(f"keys/{FRIEND}.key"), "--subject", str(FRIEND), "--dir", FRIEND_WS,
                     "--no-prerotation"],  # a fixture key with no next key (jpay-v2.sh idiom)
                    capture_output=True)
if ws.returncode != 0:
    fail("friend workspace: " + (ws.stdout + ws.stderr).decode("utf-8", "replace")[-300:])
mini_key("friend", "--action", "set", "--dir", FRIEND_WS, "--provider", "friendkey", secret=FRIEND_KEY)
mini_key("friend-grant", "--action", "grant", "--dir", FRIEND_WS, "--provider", "friendkey",
         "--runner", str(PROVIDER), "--per-call", "64", "--per-day", "10", "--until", "1000000")
pinned = json.load(open(CONFIG))
added = []
if "providerServices" not in pinned:
    pinned["providerServices"] = operator["providerServices"]; added.append("providerServices")
CONFIG_B = CONFIG
if added:
    # as docs/evidence/2026-09-26-provider-gateway-continuity/configure-case.sh
    CONFIG_B = path("deployment/continuity-config.json")
    json.dump(pinned, open(CONFIG_B, "w"), indent=1)
prof = json.loads(subprocess.run([MINI, "profile", "--host", HOST, "--config", CONFIG_B],
                                 capture_output=True).stdout or b"{}")
services = prof.get("providerMeterings") or []
pin = services[0] if len(services) == 1 else {}
routes = pin.get("routes") or {}
row(f"the Host profile pins the per-route provider tariff in credit for purse {PURSE}",
    f"providerResourceId {PURSE}, model {MODEL}, user fee {USER_FEE}; pool fee {POOL_FEE} + {RATE_IN}/{RATE_OUT} per million tokens; homelab fee {HOMELAB_FEE}",
    f"pin={json.dumps(pin, sort_keys=True)} addedToPinnedConfig={added}",
    str(pin.get("providerResourceId")) == str(PURSE) and pin.get("model") == MODEL
    and routes.get("user") == {"perOp": str(USER_FEE)}
    and routes.get("pool") == {"perOp": str(POOL_FEE), "inputMicroPerMillion": str(RATE_IN),
                               "outputMicroPerMillion": str(RATE_OUT)}
    and (routes.get("homelab") or {}).get("perOp") == str(HOMELAB_FEE))
# PLANT (consent honours the pinned service, Kernel.ProviderRouteConsent): the
# purse's birth intent authored under another tariff (user fee + 1) carries a
# route law the pin does not; the local consent provider, reading the pinned
# config, refuses it by name at intent consent (frame 230) before any key
# signs, while the same intent authored under the pinned config is consented.
CONSENT = os.path.join(os.path.dirname(HOST), "minidregg-client-consent")
rogue = json.load(open(CONFIG_B))
rogue["providerServices"][0]["tariff"]["routes"]["user"]["perOp"] = str(USER_FEE + 1)
json.dump(rogue, open(path("rogue-tariff-config.json"), "w"), indent=1)
def grain_peer(task, capability):
    return {"task": str(task), "capability": str(capability), "observeCapability": str(capability),
            "targetRoot": "0", "before": {"generation": "1", "status": "0", "remaining": "100", "reserved": "0"}}
# The purse's birth is a grain-backed source (the tool/parent composite, `grain-birth-intent`): that is
# what the 230 frame consents by the provider-route check alone. The plain `birth-intent` kind authors an
# ordinary birth, which the thin birth arm owns (234/235) and frame 230 refuses by name.
json.dump({"subject": birth["subject"], "nonce": birth["nonce"],
           "grainBirth": {"tariff": {"base": "5", "perBirth": "2"}, "birth": birth["birth"],
                          "tool": grain_peer(TOOL_TASK, 81), "parent": grain_peer(PARENT, 71)},
           "grants": birth["grants"]}, open(path("grain-birth-intent.json"), "w"))
def consent_230(author_config, label, source="grain-birth-intent.json", kind="grain-birth-intent"):
    out = path(f"{label}-birth-intent.bin")
    subprocess.run([HOST, author_config, "author", kind, path(source), out],
                   check=True, capture_output=True)
    intent = open(out, "rb").read()
    signer = keys[OPERATOR].verify_key.encode()
    payload = struct.pack("<I", len(intent)) + intent + struct.pack("<I", len(signer)) + signer
    frame = struct.pack("<I", len(payload) + 1) + bytes([230]) + payload
    done = subprocess.run([CONSENT, CONFIG_B, "stdio"], input=frame, capture_output=True, timeout=600)
    reply = done.stdout
    if len(reply) < 5: return (None, (done.stderr or b"").decode("utf-8", "replace")[-200:])
    return (reply[4], reply[5:].decode("utf-8", "replace") if reply[4] == 255 else f"{len(reply) - 5} intent bytes")
ok_op, ok_body = consent_230(CONFIG_B, "pinned")
bad_op, bad_body = consent_230(path("rogue-tariff-config.json"), "rogue")
row(f"consent refuses a purse law off the pinned tariff (plant) and consents to the pinned one",
    f"pinned: op 230; rogue: op 255 'provider service {PURSE}: ... does not carry the pinned per-route schedule'",
    f"pinned: op {ok_op} ({ok_body}); rogue: op {bad_op} ({bad_body})",
    ok_op == 230 and bad_op == 255
    and f"provider service {PURSE}: the law this draft installs does not carry the pinned per-route schedule" in bad_body)
# PLANT (the thin birth arm's discriminator, NativeThinBirth.thinBirthIntent): an ordinary
# (declared, not grain-backed) birth on the thin intent frame is refused by name, since it is
# consented only with the member's source (frames 234/235); the grain purse birth above is not
# a thin birth and must never reach that refusal (a red here is the purse consent routed to the
# thin birth arm again).
THIN_BIRTH_REFUSAL = "a thin birth is consented with the member's source (thin birth frames 234/235)"
ordinary = json.loads(json.dumps(birth))
ordinary["nonce"] = ordinary["birth"]["nonce"] = "22001"
ordinary["birth"]["resources"] = [r for r in ordinary["birth"]["resources"] if r["storage"] == "declared"]
json.dump(ordinary, open(path("ordinary-birth-intent.json"), "w"))
plain_op, plain_body = consent_230(CONFIG_B, "ordinary", "ordinary-birth-intent.json", "birth-intent")
row("discriminator (plant): an ordinary birth on frame 230 is refused for its source; the grain purse birth is not",
    f"ordinary: op 255 '{THIN_BIRTH_REFUSAL}'; purse: op 230, no thin birth refusal",
    f"ordinary: op {plain_op} ({plain_body}); purse: op {ok_op} ({ok_body})",
    plain_op == 255 and THIN_BIRTH_REFUSAL in plain_body
    and ok_op == 230 and THIN_BIRTH_REFUSAL not in ok_body)
runtime = {"mini": MINI, "host": HOST, "hostConfig": CONFIG_B, "hostSocket": SOCKET,
           "controlSocket": os.path.join(STATE, "control.sock"), "custodyKey": path(f"keys/{OPERATOR}.key"),
           "stateDir": STATE, "cwd": DIR, "task": str(PARENT), "subject": "7", "capability": "71",
           "queryCapability": "71", "policyControlCapability": "72",
           "toolTask": {"task": str(TOOL_TASK), "subject": "8", "capability": "81", "queryCapability": "81",
                        "custodyKey": path(f"keys/{TOOL}.key"), "parentCapability": "73",
                        "parentObserveCapability": "73", "reserve": "2", "charge": "1",
                        "allowedPublications": [{"kind": "object", "target": str(PUBLICATION),
                                                 "capability": "93", "observeCapability": "93"}],
                        "allowedReads": [{"name": "publication", "kind": "object", "target": str(PUBLICATION),
                                          "observeCapability": "94", "maxResultBytes": 65536}]},
           "providerTask": {"task": str(PURSE), "subject": "9", "capability": "101", "queryCapability": "101",
                            "custodyKey": path(f"keys/{PROVIDER}.key"), "parentCapability": "75",
                            "parentObserveCapability": "75", "reserve": str(PROVIDER_RESERVE),
                            "maxInputTokens": MAX_IN, "maxOutputTokens": MAX_OUT,
                            "onBehalfOf": {"subject": str(FRIEND),
                                           "publicKey": keys[FRIEND].verify_key.encode().hex()},
                            "model": MODEL, "providers": TABLE, "credentialBroker": str(KEYS_CLIENT),
                            "gatewayBind": f"127.0.0.1:{GPORT}", "maxRequestBytes": 1048576,
                            "maxResponseBytes": 8388608, "timeoutSeconds": 600, "localFixtureHostNetwork": True},
           "commands": [{"name": "hermes-acp", "program": LAUNCHER,
                         "args": ["--workspace", WORK, "--runtime-root", RUNTIME, "--network", "host", "--",
                                  "/agent/hermes-acp"],
                         "systemdScope": True, "wallTimeSeconds": 1500, "reserve": "3", "charge": "1"}]}
json.dump(runtime, open(path("runtime-config.json"), "w"), indent=1)

ACTIVE[0] = CONFIG_B
if CONFIG_B != CONFIG:
    # The broker asks the Store (op 144) under the config the Host now serves.
    KEYS_PROC.kill(); KEYS_PROC.wait()
    KEYS_PROC, KEYS_CLIENT = journey_broker.start(DIR, MINI, providers=TABLE, host=HOST, host_config=CONFIG_B,
                                                  public_socket=SOCKET, seal_key=CKEY, credentials=CRED)
    atexit.register(KEYS_PROC.kill)
upstream = subprocess.Popen([TEST_PROVIDER, f"127.0.0.1:{UPORT}", path("upstream.log"), "--metered-usage"],
                            stdout=open(path("upstream.stdout"), "wb"), stderr=open(path("upstream.stderr"), "wb"))
LIVE.append(upstream)
# grain-runtime's systemdScope requires the controller to be the active
# MainPID of exactly mini-grain-controller@<task>.service.
UNIT = f"mini-grain-controller@{PARENT}"
if subprocess.run(["systemctl", "--user", "show", "-p", "LoadState", "--value", UNIT + ".service"],
                  capture_output=True, text=True).stdout.strip() != "not-found":
    fail(f"{UNIT}.service already exists on this box; refusing to share it")
UNITS.append(UNIT + ".service")
def unit_prop(name):
    return subprocess.run(["systemctl", "--user", "show", "-p", name, "--value", UNIT + ".service"],
                          capture_output=True, text=True).stdout.strip()
controller = subprocess.run(["systemd-run", "--user", "--collect", f"--unit={UNIT}",
                             "--property=KillMode=control-group", "--property=Restart=on-failure",
                             "--property=RestartSec=2", "--property=RuntimeMaxSec=3600s",
                             f"--setenv=MINI_CONSENT_ANCHOR_DIR={os.environ['MINI_CONSENT_ANCHOR_DIR']}",
                             # Explicit user fixture selection (grain-runtime systemd_manager::fixture): no
                             # root registration exists for a journey task, and without it the controller
                             # refuses "managed proof requires root registration or explicit user fixture
                             # selection" and never launches the worker (the Hermes-half red on hbox).
                             "--setenv=MINI_GRAIN_CONTROLLER_MANAGER=user", "--setenv=MINI_GRAIN_WORKER_MANAGER=user",
                             f"--setenv=MINI_GRAIN_CONTROLLER_UNIT={UNIT}.service",
                             f"--property=StandardOutput=append:{path('controller.stdout')}",
                             f"--property=StandardError=append:{path('controller.stderr')}",
                             GRAIN, "serve", path("runtime-config.json")], capture_output=True, text=True)
if controller.returncode != 0: fail("controller unit: " + controller.stderr[-300:])
def journal():
    return json.load(open(os.path.join(STATE, "journal.json")))
try:
    def socket_or_crash():
        if int(unit_prop("NRestarts") or 0) > 0:
            fail("controller crashed at startup: " + subprocess.run([GRAIN, "serve", path("runtime-config.json")],
                 capture_output=True, text=True, timeout=60).stderr[-300:])
        return os.path.exists(os.path.join(STATE, "control.sock"))
    wait_for("controller socket", socket_or_crash, 900)
    connector = subprocess.Popen([GRAIN, "connect", os.path.join(STATE, "control.sock")], stdin=subprocess.PIPE,
                                 stdout=open(path("connector.stdout"), "ab"), stderr=open(path("connector.stderr"), "ab"))
    LIVE.append(connector)
    connector.stdin.write(b"attach soft\n"); connector.stdin.flush()
    wait_for("soft attach", lambda: journal().get("connection") == "soft" and journal().get("pending") is None, 900)
    row("controller attaches under the managed worker law this Host authors (refill arm re-emitted)",
        "connection soft", f"connection={journal().get('connection')}", journal().get("connection") == "soft")
    def upstream_auth():
        lines = [l for l in open(path("upstream.log")).read().splitlines() if l.startswith("completion")]
        return lines[-1].rsplit("auth=", 1)[-1] if lines and "auth=" in lines[-1] else "-"
    def standin_statuses():
        try: return [w for w in open(os.path.join(WORK, "standin.log")).read().split() if w.startswith("status=")]
        except OSError: return []
    def prompt_done():
        j = journal()
        return (j.get("providerAttempt") is None and j.get("providerHold") is None
                and j.get("pending") is None and j.get("connection") == "soft" and j.get("child") is None)
    def new_conversation():
        # the stand-in keeps no Hermes state.db, so the controller asks for an
        # explicit new conversation before another prompt
        connector.stdin.write(b"conversation new\n"); connector.stdin.flush()
        wait_for("conversation new", lambda: journal().get("hermesSession") is None, 300)
    def grain_of(name):
        cell, _ = mini_query(name, PROVIDER, PURSE, 101)
        return cell["grain"], cell["root"]

    # -- the user route: the friend's own key; the purse pays only the fee
    b, _ = grain_of("purse-before-user")
    row(f"purse {PURSE} was born a provider purse: route field 0 under the Host's per-route law",
        "route 0, reserved 0", f"route={b.get('route')} reserved={b['reserved']}",
        b.get("route") == "0" and b["reserved"] == "0")
    connector.stdin.write(b"hermes Read the publication and report its root.\n"); connector.stdin.flush()
    wait_for("user-route provider request", lambda: upstream_requests() >= 1, 900)
    wait_for("user-route prompt settled", prompt_done, 900)
    a, _ = grain_of("purse-after-user")
    row("a call on the friend's own key (user route) debits exactly the per-operation fee",
        f"remaining -{USER_FEE}, reserved 0, route 0; upstream saw the friend's bearer",
        f"remaining {b['remaining']} -> {a['remaining']} reserved={a['reserved']} route={a.get('route')} "
        f"upstream_auth={upstream_auth()[:20]}... friend={bearer_digest(FRIEND_KEY)[:20]}...",
        int(b["remaining"]) - int(a["remaining"]) == USER_FEE and a["reserved"] == "0"
        and a.get("route") == "0" and upstream_auth() == bearer_digest(FRIEND_KEY)
        and upstream_requests() == 1)

    # -- no route: the friend revokes; the user row has no payer and nothing falls through
    new_conversation()
    mini_key("friend-revoke", "--action", "revoke", "--dir", FRIEND_WS, "--provider", "friendkey")
    seen = len(standin_statuses())
    connector.stdin.write(b"hermes Read the publication once more.\n"); connector.stdin.flush()
    wait_for("refused request answered", lambda: len(standin_statuses()) > seen, 900)
    wait_for("refused prompt settled", prompt_done, 900)
    n, _ = grain_of("purse-after-none")
    row("a call with no payer (the friend revoked; the user row is first) is refused before any reserve",
        "worker got 403; purse unchanged (no hold, no fee); no upstream request; no pool fallthrough",
        f"standin={standin_statuses()[-1:]} remaining {a['remaining']} -> {n['remaining']} reserved={n['reserved']} "
        f"g {a['generation']} -> {n['generation']} upstream_requests={upstream_requests()}",
        standin_statuses()[-1:] == ["status=403"] and n["remaining"] == a["remaining"]
        and n["reserved"] == "0" and upstream_requests() == 1)

    # -- the pool route: the operator's key; the purse pays the metered tariff
    new_conversation()
    install_table("pool")
    connector.stdin.write(b"hermes Read the publication and report its root.\n"); connector.stdin.flush()
    wait_for("pool provider request", lambda: upstream_requests() >= 2, 900)
    wait_for("pool prompt settled", prompt_done, 900)
    after_prompt, _ = mini_query("purse-after-prompt", PROVIDER, PURSE, 101)
    p = after_prompt["grain"]
    row("a pool call reserves from the refilled purse and settles the metered tariff",
        f"remaining -{METERED_CHARGE} (fee {POOL_FEE} + 1 in + 2 out tokens at {RATE_IN}/{RATE_OUT}), reserved 0; upstream saw the pool bearer",
        f"remaining {n['remaining']} -> {p['remaining']} reserved={p['reserved']} route={p.get('route')} "
        f"upstream_requests={upstream_requests()} upstream_auth={upstream_auth()[:20]}...",
        int(n["remaining"]) - int(p["remaining"]) == METERED_CHARGE and p["reserved"] == "0"
        and upstream_requests() == 2 and upstream_auth() == bearer_digest(POOL_KEY))
    standin = open(os.path.join(WORK, "standin.log")).read().split()
    row("the worker received the provider's answer through the gateway", "status=200",
        " ".join(standin[-2:]), "status=200" in standin[-2:])

    # the uncertain attempt: the upstream holds the request; the controller dies mid-send
    new_conversation()
    upstream.send_signal(signal.SIGSTOP)
    connector.stdin.write(b"hermes Read the publication again.\n"); connector.stdin.flush()
    wait_for("second send boundary", lambda: (journal().get("providerAttempt") or {}).get("sendStarted") is True, 900, 0.1)
    time.sleep(2)
    main_pid = unit_prop("MainPID")
    os.kill(int(main_pid), signal.SIGKILL)
    upstream.send_signal(signal.SIGCONT)
    wait_for("the stalled request reaches the provider", lambda: upstream_requests() >= 3, 120)
    wait_for("systemd restart", lambda: int(unit_prop("NRestarts") or 0) >= 1 and unit_prop("MainPID") not in ("0", main_pid), 300)
    row("controller SIGKILLed after the send boundary; systemd restarted it (Restart=on-failure)",
        "NRestarts >= 1, new MainPID", f"killed={main_pid} now={unit_prop('MainPID')} NRestarts={unit_prop('NRestarts')}",
        int(unit_prop("NRestarts") or 0) >= 1)
    # On final the restarted controller runs M5's provable recovery at startup,
    # and an owner's attach to a fenced task runs it again first; recovery
    # cannot prove the uncertain provider send, so the attach is refused with
    # the provider hold still fenced. The owner reconnects (the killed
    # controller's socket file lingers until the new one binds, so retry a
    # refused connect), then also asks `recover` explicitly.
    def owner_connected():
        owner = subprocess.Popen([GRAIN, "connect", os.path.join(STATE, "control.sock")], stdin=subprocess.PIPE,
                                 stdout=open(path("recover.stdout"), "ab"), stderr=open(path("recover.stderr"), "ab"))
        LIVE.append(owner)
        owner.stdin.write(b"attach soft\nrecover\n"); owner.stdin.flush()
        time.sleep(3)
        return owner if owner.poll() is None else None
    owner = wait_for("owner connection to the restarted controller", owner_connected, 600, 2)
    # Recovery fences the uncertain send rather than settling it: the journaled
    # record is sendStarted with no outcome (decision class crash-after-send) and
    # the "provider reservation fenced" note; the "uncertain:crash-after-send"
    # outcome string belongs to the LATER audited class-settle
    # (provider_meter_class_inner), which this journey never drives.
    def recovered():
        j = journal()
        attempt = j.get("providerAttempt")
        decision = ((attempt or {}).get("decision") or {}).get("class") or {}
        return (j.get("connection") == "fenced" and attempt is not None
                and attempt.get("sendStarted") is True and attempt.get("outcome") is None
                and decision.get("kind") == "crash-after-send")
    wait_for("owner recovery", recovered, 900)
    # the connector prints the controller's replies on stdout, its own errors on stderr;
    # the attach-time recovery runs signed queries first, so its reply can trail the
    # journal's fence by a while
    def attach_replies():
        return open(path("recover.stdout")).read() + open(path("recover.stderr")).read()
    for _ in range(300):
        if "provider reservation remains held after fence" in attach_replies(): break
        time.sleep(1)
    refused_attach = attach_replies()
    row("the owner reconnects to the fenced task", "attach refused: attach-time recovery keeps the provider hold fenced",
        " | ".join(line for line in refused_attach.splitlines() if "fence" in line)[:240],
        "provider reservation remains held after fence" in refused_attach)
    j = journal()
    attempt, hold = j["providerAttempt"], j.get("providerHold") or {}
    row("recovery records the provider attempt as uncertain and keeps the hold",
        "sendStarted true, outcome null, hold reserveConfirmed, connection fenced",
        f"sendStarted={attempt.get('sendStarted')} outcome={attempt.get('outcome')} hold={hold.get('reserve')}/{hold.get('reserveConfirmed')} "
        f"connection={j.get('connection')} decision={(((attempt.get('decision') or {}).get('class') or {}).get('kind'))}"
        f" note={[n for n in j.get('unresolvedExternal') or [] if 'fenced' in str(n)][:1]}",
        attempt.get("sendStarted") is True and attempt.get("outcome") is None and hold.get("reserveConfirmed") is True)
    time.sleep(30)
    held, _ = mini_query("purse-held", PROVIDER, PURSE, 101)
    h = held["grain"]
    row("the purse still holds the uncertain attempt's reservation", f"reserved {PROVIDER_RESERVE}",
        f"g={h['generation']} s={h['status']} remaining={h['remaining']} reserved={h['reserved']}",
        h["reserved"] == str(PROVIDER_RESERVE))
    row("NO second provider send (the provider's own request log, 30 s after recovery)",
        "3 requests (one per sent prompt: user, pool, the uncertain pool call)",
        f"upstream_requests={upstream_requests()}", upstream_requests() == 3)

    # -- a pool hold cannot be settled as a user call
    held_grain, held_root = grain_of("purse-held-route")
    row("the uncertain call's hold records the pool route", "route 2 (pool) while held",
        f"route={held_grain.get('route')} s={held_grain['status']} reserved={held_grain['reserved']}",
        held_grain.get("route") == "2")
    settle_nonce = [61000]
    def settle_as(label, before_route, op_route, charge, offline=False):
        settle_nonce[0] += 1
        grain = {"task": str(PURSE), "subject": str(PROVIDER), "capability": "101", "schemaVersion": "1",
                 "expectedTargetRoot": held_root,
                 "context": {"operationId": str(settle_nonce[0]), "payload": "settle the pool hold as a user call"},
                 "before": {"generation": held_grain["generation"], "status": held_grain["status"],
                            "remaining": held_grain["remaining"], "reserved": held_grain["reserved"],
                            "route": before_route},
                 "operation": {"type": "settle", "charge": str(charge), "route": op_route},
                 "publications": [], "observeCapability": "101"}
        intent = {"grain": grain, "grants": [{"kind": "object", "target": str(PURSE), "capability": "101"}],
                  "intentNonce": str(settle_nonce[0])}
        if offline:
            # The Host's own authoring, offline: a refusal here is by name and
            # submits nothing (through `mini serve` it would close the session).
            source, out = path(f"{label}-intent.json"), path(f"{label}.bin")
            json.dump(intent, open(source, "w"))
            done = subprocess.run([HOST, CONFIG, "author", "grain-intent", source, out], capture_output=True)
            open(path(f"{label}.stderr"), "wb").write(done.stdout + done.stderr)
            result = {"type": "authored" if done.returncode == 0 else "author-refused", "exit": done.returncode}
        else:
            result = mini_submit(label, intent, PROVIDER, kind="grain-intent")
        text = open(path(f"{label}.stderr"), "rb").read().decode("utf-8", "replace")
        after, _ = grain_of(label + "-after")
        unchanged = (after["reserved"], after["remaining"], after.get("route")) == \
            (held_grain["reserved"], held_grain["remaining"], "2")
        return result, text, after, unchanged
    r1, t1, h1, same1 = settle_as("settle-pool-as-user-by-name", "2", "user", USER_FEE, offline=True)
    row("settling the pool hold while naming the user route", "refused by name at authoring: route-mismatch; hold unchanged",
        f"{r1.get('type')} exit={r1.get('exit')} | {[l for l in t1.splitlines() if 'route' in l][:1]} reserved={h1['reserved']} route={h1.get('route')}",
        r1.get("type") == "author-refused" and "route-mismatch" in t1 and same1)
    def prepare_refusal(label, text):
        # The kernel refuses at prepare: nothing is signed or submitted, and the
        # client retains the Host's refusal frame.
        try: frame = json.load(open(path(f"{label}-attempt/pre-submit-refusal.json")))
        except (OSError, ValueError): frame = {}
        reason = next((l.strip() for l in text.splitlines() if l.startswith("refused:")), "")
        return frame.get("stage") == "prepare", reason
    r2, t2, h2, same2 = settle_as("settle-pool-claiming-user-before", "1", "user", USER_FEE)
    at2, why2 = prepare_refusal("settle-pool-claiming-user-before", t2)
    row("settling the pool hold from a forged before.route = user",
        "refused at prepare by the receiver's old-value guard on field 4 (the recorded route); hold unchanged",
        f"{why2[:160]} reserved={h2['reserved']} route={h2.get('route')}",
        at2 and "guard-rejected 4" in why2 and same2)
    r3, t3, h3, same3 = settle_as("settle-pool-at-the-user-fee", "2", "pool", USER_FEE)
    at3, why3 = prepare_refusal("settle-pool-at-the-user-fee", t3)
    row(f"settling the pool hold for the user fee ({USER_FEE} < pool fee {POOL_FEE})",
        "refused at prepare by the purse's route law (law-denied); hold unchanged",
        f"{why3[:60]} ... pool clause: {'pair 2,3 delta <= -' + str(POOL_FEE) in why3} reserved={h3['reserved']} route={h3.get('route')}",
        at3 and why3.startswith("refused: law-denied") and same3)
finally:
    subprocess.run(["systemctl", "--user", "stop", UNIT + ".service"], capture_output=True)
    try: connector.stdin.close()
    except Exception: pass
    serve.stop()
    upstream.send_signal(signal.SIGCONT); upstream.terminate(); upstream.wait(timeout=30)

host = Host()
r, _ = refill(host, FRIEND, CAPS[FRIEND][0], FRIEND, 1_000_000, 1_000_000)
row("a refill while the purse holds the uncertain reservation", "refused undisclosed (built to hit purseRefused (the edge needs reserved = 0))",
    show(r), refused_with(r, "purseRefused"))
host.stop()

REFILLED = REFILL
led2, p3 = ledger(), purse()
row("ledger identity on this Store: -well_h = -well_0 + credited - burned into purses",
    f"-well_h = {-int(led0['well'])} + 0 - {REFILLED}",
    f"-well_h={-int(led2['well'])} -well_0={-int(led0['well'])} friend={balance(led2, FRIEND)}",
    -int(led2["well"]) == -int(led0["well"]) + 0 - REFILLED and balance(led2, FRIEND) == FRIEND_BALANCE - REFILLED)
row("purse_never_mints on this Store: budget_h <= budget_0 + sum burns; the gap is the user fee plus the metered pool charge",
    f"budget {budget(p1)} + {REFILLED} - {USER_FEE} - {METERED_CHARGE}",
    f"budget_h={budget(p3)} remaining={p3['remaining']} reserved={p3['reserved']}",
    budget(p3) == budget(p1) + REFILLED - USER_FEE - METERED_CHARGE)
audit = subprocess.run([HOST, CONFIG, "audit"], capture_output=True)
audit_text = (audit.stdout + audit.stderr).decode("utf-8", "replace").strip().splitlines()
row("operator audit re-admits every record (NativeHostReplay, incl. the refill)", "exit 0",
    f"exit={audit.returncode} {audit_text[-1] if audit_text else ''}", audit.returncode == 0)

json.dump({"config": CONFIG, "keys": path("keys"), "purse": PURSE, "friend": FRIEND,
           "friendCapability": CAPS[FRIEND][0]}, open(path("handoff.json"), "w"))
rows_path = path("rows.tsv")
with open(rows_path, "w") as out:
    out.write("verdict\tstep\texpected\tobserved\n")
    for name, expected, observed, verdict in ROWS:
        out.write(f"{verdict}\t{name}\t{expected}\t{observed}\n")
passed = sum(1 for r in ROWS if r[3] == "PASS")
verdict = f"J-PAY-6 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - started:.1f} s)"
print(verdict)
print(verdict, file=sys.stderr)
print(rows_path)
sys.exit(0 if passed == len(ROWS) else 1)
PY
