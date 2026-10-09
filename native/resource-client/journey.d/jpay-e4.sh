#!/usr/bin/env bash
# J-PAY-E4 (PAY.md §11.9 JOIN-SOLANA): a friend enrols themselves by paying, end to end on
# fixtures — `mini join --solana` → a fixture transfer carrying that memo → the real tick script
# (deploy/pay/mini-pay-watcher) → the observer's self-enrollment through ops 117-120 on the
# Host's OPERATOR socket → the enrollment view → the roster renderer (dry run) → `join --wait`.
#
# Follows the journey hook contract (journey.sh header): executed with HOST, MINI, STORE,
# VERIFIER and JOURNEY_STEP_DIR exported; it starts its OWN supervised private Host
# and fixed public relay on its OWN fresh Store and stops both. Exit 0 = PASS.
# The verdict `J-PAY-E4 PASS n/n` is the last stderr line and the line before the last stdout
# line; the last stdout line is the deciding artifact (rows.tsv).
#
# Also required: PAY_WATCHER_BIN (default native/pay-watcher/target/release/pay-watcher);
# INFRA_EDGE = a copy of dregg-infra `edge/mini` (render-authorized-keys.sh, mini-closed,
# shell/{render-shell-key,mini-socket-proxy,mini-shell-ssh}), used read-only; python3 with
# PyNaCl (an attacker's memo is built without our client); ssh-keygen; jq.
#
# No real Solana: every transfer is a fixture endpoint pair built with P1b's generator
# (native/pay-watcher/fixtures/generate.py: enrol_tx, the enrollment address, mint and
# Token-2022 accounts), the memo text being the one `join --solana` printed. VERIFIER must
# have `verify-sshsig` (P3b-1 or later).
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR INFRA_EDGE; do
  if [ -z "${!name:-}" ]; then echo "jpay-e4: $name is required" >&2; exit 2; fi
done
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
TREE=$(CDPATH='' cd -- "$HERE/../../.." && pwd)
export PAY_WATCHER_BIN=${PAY_WATCHER_BIN:-$TREE/native/pay-watcher/target/release/pay-watcher}
export PAY_FIXTURES=$TREE/native/pay-watcher/fixtures
export PAY_TICK_SCRIPT=$TREE/deploy/pay/mini-pay-watcher
for tool in python3 jq ssh-keygen xxd flock; do
  command -v "$tool" >/dev/null || { echo "jpay-e4: $tool is required" >&2; exit 2; }
done
python3 -c 'import nacl.signing' 2>/dev/null || { echo "jpay-e4: PyNaCl is required" >&2; exit 2; }
[ -x "$PAY_WATCHER_BIN" ] || { echo "J-PAY-E4 FAIL setup: pay-watcher binary missing at $PAY_WATCHER_BIN" >&2; exit 1; }
for f in render-authorized-keys.sh mini-closed shell/render-shell-key shell/mini-socket-proxy shell/mini-shell-ssh; do
  [ -f "$INFRA_EDGE/$f" ] || { echo "jpay-e4: INFRA_EDGE lacks $f" >&2; exit 2; }
done
DIR="$JOURNEY_STEP_DIR/jpay-e4"
if [ -e "$DIR" ]; then echo "jpay-e4: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
# The genesis clock is chosen by the one candidate helper, never written here.
. "$(dirname -- "$0")/lib/genesis-params.sh"
resolve_params_sh "$(CDPATH='' cd -- "$(dirname -- "$0")/../../.." && pwd)" || exit 2
exec python3 - "$DIR" <<'PY'
import base64, hashlib, http.client, json, os, re, shutil, signal, struct, subprocess, sys, time
import nacl.signing

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
WATCHER, FIXTURES = os.environ["PAY_WATCHER_BIN"], os.environ["PAY_FIXTURES"]
TICK_SCRIPT, EDGE = os.environ["PAY_TICK_SCRIPT"], os.environ["INFRA_EDGE"]
sys.path.insert(0, FIXTURES)
sys.dont_write_bytecode = True   # never leave __pycache__ in the tree's fixtures
import generate as gen   # P1b's fixture vocabulary (generate.py runs nothing on import)

ROWS, STARTED = [], time.time()
EMBER, FLOAT, OBSERVER = 7, 20, 30
FACTORY_CONTROL, OBSERVER_CAP, PAY_CONTROL, ENROL_CAP = 53, 4030, 4031, 4032
SUBJECTS = [EMBER, FLOAT, OBSERVER]
def acct(s): return 100 + s
WEEK = 50_000_000                  # 50 DREGG a node week at 6 decimals, exact (the tariff unit is the week)
BIRTH_FEE = 3 + 2 + 2 * 1           # the factory tariff below; join must print the same price
PRICE = BIRTH_FEE + WEEK            # explicit bare entry: creditPerAtomic 1, starter zero
STARTER = 105 * 3 + 8 * 2 + 16 * 1  # source recommendation for this exact genesis tariff
COLD_WEEKS = 2
FLOOR = 1_000_000
LOGIN = "mini@box.example"

def path(*names): return os.path.join(DIR, *names)
def fail(message):
    print(f"J-PAY-E4 FAIL: {message}", file=sys.stderr); sys.exit(1)
def row(name, ok, observed):
    observed = " ".join(str(observed).split())
    ROWS.append(("PASS" if ok else "FAIL", name, observed))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{observed}", file=sys.stderr)
def run(argv, env=None, check=False, timeout=900):
    result = subprocess.run([str(a) for a in argv], capture_output=True, text=True, env=env, timeout=timeout)
    if check and result.returncode != 0:
        fail(f"{' '.join(map(str, argv[:3]))} exit {result.returncode}: {result.stderr[-600:]}")
    return result
def mini(*words, check=False): return run([MINI, *words], check=check)
def b58decode(text):
    n = 0
    for c in text: n = n * 58 + gen.ALPHABET.index(c)
    raw = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    return b"\0" * (len(text) - len(text.lstrip("1"))) + raw
def hexof(b58): return b58decode(b58).hex()

ENROL_HEX, MINT_HEX = hexof(gen.ENROL), hexof(gen.MINT)
PROGRAM_HEX = hexof(gen.TOKEN_2022)
EXTRA = [gen.b58(gen.key(f"book {i}")) for i in range(2, 8)]
BOOK = [gen.ENROL, gen.BOOK0] + EXTRA          # row 0 = the enrollment address

# ------------------------------------------------------------ genesis (E3's shape, via mini)
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
            "initialBalance": "100", "accountPredicate": {"type": "all", "predicates": []}}
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
                           "controlCapability": str(PAY_CONTROL), "enrolCapability": str(ENROL_CAP)}}
with open(path("genesis.json"), "w") as out: json.dump(genesis, out)
subprocess.run(["sh", os.environ["GENESIS_PARAMS_SH"], "fill-source", path("genesis.json")], check=True)
mini("bootstrap", "--host", HOST, "--config", path("operator.json"), "--source", path("genesis.json"),
     "--dir", path("deployment"), check=True)
CONFIG = path("deployment", "pinned-config.json")
BIRTH_CONTEXT = path("published-birth-context.json")
json.dump({"type":"minidregg-participant-birth-context-v1", "genesis":genesis,
           "template":profile["template"]}, open(BIRTH_CONTEXT,"w"))

# ------------------------------------------------------------ supervised private Host and public relay
os.makedirs(path("public"), mode=0o700)
os.makedirs(path("operator"), mode=0o700)
SOCKET, OPSOCK = path("public", "mini.sock"), path("operator", "mini.sock")
server = relay = None
def start_server():
    global server, relay
    log = path("serve.log")
    seen = open(log).read().count("mini: serving " + OPSOCK) if os.path.exists(log) else 0
    server = subprocess.Popen([MINI, "serve-operator", "--host", HOST, "--config", CONFIG,
                               "--socket", OPSOCK],stdout=open(log,"ab"),stderr=subprocess.STDOUT,
                               start_new_session=True)
    for _ in range(1200):
        if open(log).read().count("mini: serving " + OPSOCK)>seen and os.path.exists(OPSOCK): break
        if server.poll() is not None: fail("private operator supervisor exited")
        time.sleep(0.1)
    else: fail("private operator socket did not appear")
    relay=subprocess.Popen([MINI,"serve-public-proxy","--socket",SOCKET,
                            "--upstream",OPSOCK,"--config",CONFIG],
                            stdout=open(path("relay.log"),"ab"),stderr=subprocess.STDOUT,
                            start_new_session=True)
    for _ in range(1200):
        if relay.poll() is not None: fail("public relay exited")
        if os.path.exists(SOCKET):
            checked=mini("profile","--host",HOST,"--config",CONFIG,"--socket",SOCKET)
            if checked.returncode==0:return
        time.sleep(0.1)
    fail("public relay did not become readable")
def stop_server():
    global server,relay
    for process in [relay,server]:
        if process is not None and process.poll() is None:
            os.killpg(process.pid,signal.SIGTERM);process.wait(timeout=60)
    server=relay=None
import atexit
atexit.register(lambda:stop_server())
start_server()

WS = {s: path("ws", str(s)) for s in SUBJECTS}
os.makedirs(path("ws"))
for s in SUBJECTS:
    mini("workspace", "--action", "init", "--host", HOST, "--config", CONFIG, "--socket", SOCKET,
         "--key", path("keys", f"{s}.key"), "--subject", s, "--dir", WS[s], "--no-prerotation", check=True)
mini("workspace", "--action", "import", "--dir", WS[FLOAT], "--name", "account", "--kind", "account",
     "--target", acct(FLOAT), "--observe-capability", 1000 + FLOAT, "--operation-capability",
     1000 + FLOAT, check=True)
OBS = WS[OBSERVER]

tariff = {"version": "2", "asset": "0", "mint": MINT_HEX, "tokenProgram": PROGRAM_HEX, "decimals": "6",
          "creditPerAtomic": "1", "maxPerObservation": "100000000000", "minTickSlots": "1",
          "nodeWeekRate": str(WEEK), "enrolIndex": None, "journalFloor": str(FLOOR), "slashCallerPermille":"500"}
json.dump({"control": str(FACTORY_CONTROL), "book": BOOK, "tariff": tariff}, open(path("book.json"), "w"))
b1 = mini("pay", "book", "--dir", WS[EMBER], "--source", path("book.json"))
a0 = mini("pay", "address", "--dir", WS[FLOAT])
json.dump({"control": str(FACTORY_CONTROL), "book": [], "tariff": dict(tariff, version="3", enrolIndex="0")},
          open(path("tariff-on.json"), "w"))
b2 = mini("pay", "book", "--dir", WS[EMBER], "--source", path("tariff-on.json"))
row("bootstrap: 8-row book (row 0 = the enrollment address), the float takes index 0, the tariff names index 0",
    b1.returncode == 0 and a0.returncode == 0 and a0.stdout.startswith(f"index 0 → {gen.ENROL}") and b2.returncode == 0,
    f"{b1.stdout.strip()} | {a0.stdout.splitlines()[0] if a0.stdout else a0.stderr[-120:]} | {b2.stdout.strip() or b2.stderr[-160:]}")

def enrolment_view():
    r = mini("enrollment-view", "--socket", SOCKET)
    if r.returncode != 0: fail(f"enrollment-view: {r.stderr[-300:]}")
    return json.loads(r.stdout)
def ledger_well():
    """The issuer well and the float's balance, read with the service stopped (pay-ledger)."""
    stop_server()
    out = path(f"ledger-{time.time_ns()}.json")
    run([HOST, CONFIG, "pay-ledger", out], check=True)
    start_server()
    led = json.load(open(out))
    bal = {r["account"]: int(r["balance"]) for r in led["payers"]}
    return int(led["well"]), bal

# ------------------------------------------------------------ the friend's side: join --solana
PIN = path("enrol-pinned.json")
json.dump({"type": "minidregg-enrol-pin-v1", "enrolAddress": gen.ENROL, "login": LOGIN}, open(PIN, "w"))
os.makedirs(path("join"))
def join(name, *extra, pin=PIN):
    return mini("join", "--solana", "--host", HOST, "--config", CONFIG, "--socket", SOCKET,
                "--enrol", pin, "--dir", path("join", name), "--name", name,
                "--starter-credit", "0", *extra)
def printed(result, key):
    for line in result.stdout.splitlines():
        if line.startswith(key + " ") or line.startswith(key + "\t"):
            return line[len(key):].strip()
    return None

# The pin the operator has not filled in. deploy/pay/enrol-terms.json is the one source of the real
# address (render-enrol writes the pin from it), so the unset pin is built here, not shipped.
TEMPLATE = path("enrol-unset.json")
json.dump({"type": "minidregg-enrol-pin-v1", "enrolAddress": "EMBER_ENROL_ADDRESS", "login": LOGIN}, open(TEMPLATE, "w"))
t = join("template", pin=TEMPLATE)
row("join --solana with an unset pin (EMBER_ENROL_ADDRESS) refuses; no memo printed",
    t.returncode != 0 and "EMBER_ENROL_ADDRESS is unset" in t.stderr and "memo" not in t.stdout,
    t.stderr.strip()[-160:])

alice = join("alice")
memo = printed(alice, "memo") or ""
url = printed(alice, "solana-pay") or ""
amount_line = printed(alice, "amount") or ""
row("join --solana (alice): address, 400-byte memo, amount = birth fee + one node week, Solana Pay URL",
    alice.returncode == 0 and printed(alice, "address") == gen.ENROL and printed(alice, "memo-bytes") == "400"
    and len(memo) == 400 and amount_line.startswith(f"{PRICE / 1e6:.6f}".rstrip("0") + " DREGG")
    and f"({PRICE} atomic units)" in amount_line
    and url.startswith(f"solana:{gen.ENROL}?amount=") and f"&spl-token={gen.MINT}&memo=enrol%3Av1%3A" in url
    and "wallets also drop the memo" in alice.stdout,
    f"exit={alice.returncode} amount {amount_line} memo-bytes {printed(alice, 'memo-bytes')} "
    f"{(alice.stderr or '').strip()[-160:]}")
JA = json.load(open(path("join", "alice", "join.json"))) if alice.returncode == 0 else fail(alice.stderr)

# The memo byte equality: the Host's own codec reads the printed memo back, and the fields it
# reads re-encode (PayEnrolMemo.encode, done here in Python) to the very same 400 bytes.
open(path("alice-memo.bin"), "wb").write(memo.encode())
run([HOST, CONFIG, "inspect", "pay-enrol-memo", path("alice-memo.bin"), path("alice-memo.json")], check=True)
parsed = json.load(open(path("alice-memo.json")))
reencoded = ("enrol:v1:" + parsed.get("miniKey", "") + ":" +
             base64.b64encode(bytes.fromhex(parsed.get("sshBlob", ""))).decode().rstrip("=") + ":" +
             parsed.get("miniSig", "") + ":" + parsed.get("sshSig", ""))
alice_pub = open(path("join", "alice", "mini.pub"), "rb").read().hex()
alice_ssh_line = open(path("join", "alice", "ssh", "id_ed25519.pub")).read().split()
row("memo byte equality: the Host's inspect pay-enrol-memo accepts it; its fields re-encode to the same 400 bytes; "
    "the Mini key is alice's own",
    parsed.get("accepted") is True and reencoded.encode() == memo.encode() and parsed["miniKey"] == alice_pub
    and parsed["sshBlob"] == base64.b64decode(alice_ssh_line[1]).hex(),
    f"accepted={parsed.get('accepted')} reencoded==printed {reencoded.encode() == memo.encode()} "
    f"subject={parsed.get('subject')}")

os.makedirs(path("fido"))
open(path("fido", "id.pub"), "w").write("sk-ssh-ed25519@openssh.com AAAAGnNrLXNzaC1lZDI1NTE5QG9wZW5zc2guY29tAAAAIG07ssw/nVQyEp4fbo6x0DefttH5CdsmuUI28/nc/UkKAAAABHNzaDo= fido\n")
open(path("fido", "id"), "w").write("")
f = join("fido", "--ssh-key", path("fido", "id"))
row("join --solana refuses a FIDO (sk-) ssh key by name; nothing printed (control: alice above)",
    f.returncode != 0 and "fidoKeyRefused" in f.stderr and printed(f, "memo") is None, f.stderr.strip()[-140:])

json.dump({"type": "minidregg-enrol-pin-v1", "enrolAddress": gen.BOOK0, "login": LOGIN}, open(path("enrol-wrong.json"), "w"))
w = join("wrongpin", pin=path("enrol-wrong.json"))
row("join --solana refuses when the published address is not the box's enrollment row (control: alice)",
    w.returncode != 0 and "differs from the published enrolAddress" in w.stderr, w.stderr.strip()[-140:])

def wait(name, *extra):
    return mini("join", "--wait", "--host", HOST, "--config", CONFIG, "--socket", SOCKET,
                "--dir", path("join", name), "--birth-context", BIRTH_CONTEXT, *extra)
early = wait("alice", "--timeout", "0")
row("join --wait before any payment: not enrolled yet (exit 4)", early.returncode == 4 and "not enrolled yet" in early.stderr,
    early.stderr.strip()[-120:])

# ------------------------------------------------------------ fixture ticks (P1b's generator)
HISTORY = []          # (signature bytes, slot, tx body), newest last
TIP = [2000]
def pay(label, amount, memos=(), inner=()):
    TIP[0] += 100
    signature = gen.sig(f"e4-{label}")
    body = gen.enrol_tx(signature, TIP[0] - 50, amount, memos=list(memos), inner_memos=list(inner))
    HISTORY.append((signature, TIP[0] - 50, body, label))
    return signature
def endpoint(tip):
    ep = gen.Endpoint()
    ep.put("getSlot/finalized.json", gen.envelope(tip))
    ep.put(f"getBlockTime/{tip}.json", gen.envelope(gen.block_time(tip)))
    for owner, acct_ in ((gen.ENROL, gen.ENROL_TA), (gen.BOOK0, gen.ATA0)):
        ep.put(f"getTokenAccountsByOwner/{owner}.{gen.MINT}.json",
               gen.envelope({"context": {"slot": tip}, "value": [gen.token_account_entry(acct_, owner=owner)]}))
    for owner in EXTRA:
        ep.put(f"getTokenAccountsByOwner/{owner}.{gen.MINT}.json",
               gen.envelope({"context": {"slot": tip}, "value": []}))
    newest_first = [(s, slot) for (s, slot, _, _) in reversed(HISTORY) if slot < tip]
    # The watcher's enrollment cursor: whichever signature it holds, the listing above it.
    for until in [None] + [s for s, _ in newest_first]:
        rows_ = newest_first if until is None else newest_first[:[s for s, _ in newest_first].index(until)]
        suffix = f".until.{gen.b58(until)}" if until else ""
        ep.put(f"getSignaturesForAddress/{gen.ENROL_TA}{suffix}.json",
               gen.envelope(gen.listing(*[(s, slot, None) for s, slot in rows_])))
    for s, _, body, _ in HISTORY:
        ep.tx(s, body)
    ep.sigs(gen.ATA0, [])
    return ep
STATE = path("watcher-state")
def tick(tag, tip=None):
    tip = tip or TIP[0] + 10
    dirs = []
    for side in ("a", "b"):
        d = path("ticks", tag, side)
        for rel, body in endpoint(tip).files.items():
            gen.dump(os.path.join(d, rel), body)
        dirs.append(d)
    env = dict(os.environ, MINI=MINI, PAY_WATCHER=WATCHER, PAY_STATE=STATE,
               PAY_OBSERVER_WS=OBS, PAY_OBSERVER_CAPABILITY=str(OBSERVER_CAP),
               PAY_ENROL_INDEX="0", PAY_JOURNAL_FLOOR=str(FLOOR),
               PAY_ENROL_CAPABILITY=str(ENROL_CAP), PAY_OPERATOR_SOCKET=OPSOCK,
               PAY_RPC_FIXTURES=" ".join(dirs))
    env.pop("PAY_RPC_ENDPOINTS", None)
    result = run(["sh", TICK_SCRIPT], env=env)
    open(path(f"tick-{tag}.out"), "w").write(result.stdout + result.stderr)
    for name in ("observations", "events"):
        src = os.path.join(STATE, "tick", f"{name}.json")
        if os.path.exists(src): shutil.copyfile(src, path(f"tick-{tag}.{name}.json"))
    return result
def lines(result, first):
    return [l.split("\t") for l in result.stdout.splitlines() if l.split("\t")[0] == first]
def summary(result):
    found = [l for l in result.stdout.splitlines() if l.startswith("pay observe:")]
    return found[-1] if found else (result.stdout + result.stderr).strip()[-240:]
def entry(view, key):
    return next((e for e in view.get("entries", []) if e["miniKey"] == key), None)
def journal_of(view, signature):
    return next((j for j in view.get("journal", []) if j["signature"] == signature.hex()), None)

well0, bal0 = ledger_well()
A1 = pay("alice", PRICE, memos=[memo])
t1 = tick("alice")
ev = enrolment_view()
ea = entry(ev, alice_pub)
hour = ev["clock"]["hour"]
row("tick: alice's transfer (exactly the price, her memo) → self-enrolled through ops 117-120 on the operator socket",
    t1.returncode == 0 and len(lines(t1, "enrolled")) == 1 and "enrolled 1" in summary(t1)
    and ea is not None and ea["sshBlob"] == base64.b64decode(alice_ssh_line[1]).hex()
    and ea["lease"] == {"expiresAt": hour + 168} and ea["index"] == 1,
    f"{summary(t1)} entry={json.dumps(ea, sort_keys=True)[:200] if ea else None} hour={hour}")
well1, bal1 = ledger_well()
run([HOST, CONFIG, "pay-enrol-ids", alice_pub, path("alice-ids.json")], check=True)
alice_account = json.load(open(path("alice-ids.json")))["account"]
row("the enrollment mints creditFor(amount) once; the float nets zero; alice's new account holds amount - price = 0",
    well0 - well1 == PRICE and bal1.get(str(acct(FLOAT))) == bal0.get(str(acct(FLOAT)))
    and bal1.get(alice_account) == 0,
    f"well {well0}->{well1} float {bal0.get(str(acct(FLOAT)))}->{bal1.get(str(acct(FLOAT)))} "
    f"account {alice_account}={bal1.get(alice_account)}")

# The roster renderer (dregg-infra, read-only) in MINI_ROOT, --view required, --dry-run.
import tempfile
R = tempfile.mkdtemp(prefix="je4-")   # sockaddr_un: the staged socket path must stay short
os.symlink(R, path("root"))
LIB, NODE, CUR = f"{R}/usr/local/lib/mini", f"{R}/var/lib/mini/store/node", f"{R}/var/lib/mini/candidate/current"
for d in (f"{R}/etc/mini", f"{LIB}/infra/friends", f"{NODE}/public", f"{NODE}/deployment", f"{CUR}/bin"):
    os.makedirs(d, exist_ok=True)
for rel in ("render-authorized-keys.sh", "mini-closed", "shell/render-shell-key", "shell/mini-socket-proxy",
            "shell/mini-shell-ssh"):
    shutil.copyfile(os.path.join(EDGE, rel), f"{LIB}/{os.path.basename(rel)}"); os.chmod(f"{LIB}/{os.path.basename(rel)}", 0o755)
os.symlink(MINI, f"{CUR}/bin/mini"); os.symlink(HOST, f"{CUR}/bin/minidregg-host")
open(f"{NODE}/state.json", "w").write("{}")
shutil.copyfile(CONFIG, f"{NODE}/deployment/pinned-config.json")
os.symlink(SOCKET, f"{NODE}/public/mini.sock")
shutil.copyfile(path("public", "mini.config"), f"{NODE}/public/mini.config")
run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", "ember", "-f", path("ember-ssh")], check=True)
shutil.copyfile(path("ember-ssh.pub"), f"{LIB}/infra/friends/ember.pub")
open(f"{R}/etc/mini/authorized_keys", "w").write("")
renv = dict(os.environ, MINI_ROOT=R)
rend = run(["bash", f"{LIB}/render-authorized-keys.sh", "--on-box", "--view", "required", "--dry-run"], env=renv)
open(path("render-dry-run.out"), "w").write(rend.stdout + rend.stderr)
comment = "k" + hashlib.sha256(bytes.fromhex(alice_pub)).hexdigest()[:12]
added = [l for l in rend.stdout.splitlines() if l.startswith("+restrict") and alice_ssh_line[1] in l]
row("render-authorized-keys.sh --view required --dry-run would add alice's proxy line (mini enrollment-view)",
    rend.returncode == 0 and len(added) == 1 and added[0].endswith(f"ssh-ed25519 {alice_ssh_line[1]} {comment}")
    and "mini-socket-proxy" in added[0] and "self-enrolled 1" in rend.stdout,
    (added[0][:60] + "…" + added[0][-40:]) if added else (rend.stdout + rend.stderr).strip()[-200:])

ok = wait("alice", "--timeout", "30", "--interval", "1")
ids = json.load(open(next(os.path.join(dp, f) for dp, _, fs in os.walk(path("join", "alice")) for f in fs if f == "ids.json")))
row("join --wait: enrolled; the subject is the kernel's derived one; lease and the ssh login line",
    ok.returncode == 0 and f"enrolled subject {ea['subject']}" in ok.stdout and ids["subject"] == ea["subject"]
    and f"until box hour {hour + 168}" in ok.stdout and f"ssh -i {JA['sshKeyFile']} {LOGIN}" in ok.stdout,
    " | ".join(ok.stdout.strip().splitlines()[:3]) or ok.stderr[-160:])

ALICE_WS = path("join", "alice", "workspace")
again = wait("alice", "--timeout", "0")
shell_entry = mini("shell", "--workspace", ALICE_WS, "--home", path("join","alice","home"), "--line", "whoami")
read_account = mini("workspace", "--action", "read", "--dir", ALICE_WS, "--name", "account", "--ephemeral", "true")
row("paid join creates a usable workspace; repeated wait preserves it and member reads own account",
    again.returncode == 0 and read_account.returncode == 0 and shell_entry.returncode == 0 and str(ea["subject"]) in shell_entry.stdout
    and json.load(open(os.path.join(ALICE_WS,"workspace.json")))["subject"] == ea["subject"],
    f"repeat={again.returncode} shell-subject={ea['subject']} read={read_account.returncode} {read_account.stderr[-120:]}")

# ------------------------------------------------------------ refusals, each with its control
def nacl_memo(label, ssh_signer_dir=None, blob_of_dir=None):
    """An attacker's memo, built without our client (PyNaCl + ssh-keygen, as J-PAY-E3)."""
    mini_key = nacl.signing.SigningKey.generate()
    signer = ssh_signer_dir or path(f"ssh-{label}")
    if not os.path.exists(signer):
        os.makedirs(signer)
        run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", label, "-f", os.path.join(signer, "key")], check=True)
    named = blob_of_dir or signer
    blob = base64.b64decode(open(os.path.join(named, "key.pub")).read().split()[1])
    mint, address = bytes.fromhex(MINT_HEX), bytes.fromhex(ENROL_HEX)
    message = os.path.join(signer, f"message-{label}")
    open(message, "wb").write(mint + address + mini_key.verify_key.encode())
    run(["ssh-keygen", "-Y", "sign", "-n", "dregg-enrol@v1", "-f", os.path.join(signer, "key"), message], check=True)
    armour = open(message + ".sig").read()
    ssh_sig = base64.b64decode("".join(l for l in armour.splitlines() if not l.startswith("-----")))[-64:]
    mini_sig = mini_key.sign(b"DREGG/PAY/ENROL/POSSESSION/v1" + mint + address + blob).signature
    return mini_key, ("enrol:v1:" + mini_key.verify_key.encode().hex() + ":" +
                      base64.b64encode(blob).decode().rstrip("=") + ":" + mini_sig.hex() + ":" + ssh_sig.hex())

def journalled_row(name, label, amount, memos, reason, control):
    signature = pay(label, amount, memos=memos)
    w0, _ = ledger_well()
    t = tick(label)
    view = enrolment_view()
    j = journal_of(view, signature)
    w1, _ = ledger_well()
    row(name, t.returncode == 0 and j is not None and j["reason"] == reason and j["amount"] == amount
        and w1 == w0 and len(view["entries"]) == len_entries[0] and len(lines(t, "journalled")) == 1,
        f"journal {j} well {w0}->{w1} entries={len(view['entries'])} (control: {control}) {summary(t)}")
    return t
len_entries = [1]

journalled_row("memo-less transfer → journalled memoMissing, not enrolled, nothing minted", "nomemo", PRICE, [],
               "memoMissing", "alice's memo enrolled")

bob = join("bob")
bob_memo = printed(bob, "memo")
bad = bob_memo[:9 + 64 + 1 + 68 + 1] + ("0" if bob_memo[143] != "0" else "1") + bob_memo[144:]
journalled_row("a memo whose mini-sig fails → journalled miniSigInvalid", "bob-badsig", PRICE, [bad],
               "miniSigInvalid", "bob's unaltered memo, next row")
pay("bob", PRICE, memos=[bob_memo])
tb = tick("bob")
bob_pub = open(path("join", "bob", "mini.pub"), "rb").read().hex()
len_entries[0] = len(enrolment_view()["entries"])
row("control: bob's unaltered memo → enrolled (index 2)", tb.returncode == 0 and len(lines(tb, "enrolled")) == 1
    and (entry(enrolment_view(), bob_pub) or {}).get("index") == 2, summary(tb))

# Mallory binds dave's PUBLIC ssh key to her own Mini key; she can only sign with her own ssh key.
os.makedirs(path("ssh-dave"))
run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", "dave", "-f", path("ssh-dave", "key")], check=True)
_, squat = nacl_memo("mallory", blob_of_dir=path("ssh-dave"))
journalled_row("a memo naming someone else's ssh key (dave's public key) → journalled sshSigInvalid "
               "(else anyone could bind a public ssh key for the entry fee)", "squat", PRICE, [squat], "sshSigInvalid",
               "dave's own memo, next row")
dave = join("dave", "--ssh-key", path("ssh-dave", "key"))
pay("dave", PRICE, memos=[printed(dave, "memo")])
td = tick("dave")
len_entries[0] = len(enrolment_view()["entries"])
row("control: dave's own memo with his own ssh key → enrolled", td.returncode == 0 and len(lines(td, "enrolled")) == 1,
    summary(td))

carol = join("carol")
carol_memo = printed(carol, "memo")
journalled_row("under-payment (the price - 1 atomic unit) → journalled belowPrice: the client's price is the kernel's",
               "carol-short", PRICE - 1, [carol_memo], "belowPrice", "carol at exactly the price, next row")
pay("carol", PRICE, memos=[carol_memo])
tc = tick("carol")
len_entries[0] = len(enrolment_view()["entries"])
row("control: carol at exactly the printed price → enrolled", tc.returncode == 0 and len(lines(tc, "enrolled")) == 1,
    summary(tc))

# The same payment replayed: alice's decided transfer reaches the kernel again (receipts lost).
receipt = os.path.join(OBS, "pay", "receipts", f"{A1.hex()}.{ENROL_HEX}")
original = os.readlink(receipt)
# Lose the deciding attempt and its receipt (a restored backup without them): the client can no
# longer know, so only the kernel's nullifier answers.
shutil.move(original, path("lost-attempt"))
os.remove(receipt)
replay_file = path("replay-observations.json")
obs1 = json.load(open(path("tick-alice.observations.json")))
TIP[0] += 100
json.dump({"tip": {"slot": TIP[0], "blockTime": gen.block_time(TIP[0])}, "observations":
           [o for o in obs1["observations"] if o["signature"] == A1.hex()]}, open(replay_file, "w"))
w0, _ = ledger_well()
rp = mini("pay", "observe", "--dir", OBS, "--capability", OBSERVER_CAP, "--enrol-capability", ENROL_CAP,
          "--operator-socket", OPSOCK, "--from", replay_file)
w1, _ = ledger_well()
row("the same payment replayed (attempt and receipt lost) → the kernel refuses alreadyConsumed: already decided, "
    "nothing minted",
    rp.returncode == 0 and len(lines(rp, "already-decided")) == 1 and w1 == w0 and os.path.islink(receipt)
    and len(enrolment_view()["entries"]) == len_entries[0],
    f"{(lines(rp, 'already-decided') or [['none']])[0][:3]} well {w0}->{w1} (control: the original enrolled, "
    f"{original.split('/')[-1]}) {summary(rp)}")
shutil.move(path("lost-attempt"), original)   # the audit below counts the original decision

ea0 = entry(enrolment_view(), alice_pub)
pay("alice-again", 2 * WEEK + 500, memos=[memo])
ta = tick("alice-again")
ev = enrolment_view()
ea2 = entry(ev, alice_pub)
row("a second payment with alice's memo → renewed: lease extends by 2 weeks from its end, one entry, same subject",
    ta.returncode == 0 and len(lines(ta, "renewed")) == 1 and ea2["subject"] == ea0["subject"]
    and ea2["lease"]["expiresAt"] == ea0["lease"]["expiresAt"] + 336
    and sum(1 for e in ev["entries"] if e["miniKey"] == alice_pub) == 1,
    f"{summary(ta)} expiresAt {ea0['lease']['expiresAt']}->{ea2['lease']['expiresAt']}")

# The renewal's 500-unit remainder funds actual first use by the paid member.
open_law = path("open-law.json")
json.dump({"type":"all","predicates":[]}, open(open_law,"w"))
_, before_birth = ledger_well()
context_path = os.path.join(ALICE_WS,"birth-context.json")
original_context = open(context_path,"rb").read()
wrong_context = json.loads(original_context)
wrong_context["genesis"]["domain"] = "8502"
json.dump(wrong_context,open(context_path,"w"))
try:
    wrong_birth = mini("workspace", "--action", "create", "--dir", ALICE_WS, "--name", "foreign-note",
                       "--storage", "content", "--predicate", open_law)
finally:
    open(context_path,"wb").write(original_context)
_, after_wrong_birth = ledger_well()
row("paid member cannot substitute a foreign deployment genesis for app/resource birth",
    wrong_birth.returncode != 0 and before_birth == after_wrong_birth,
    f"exit={wrong_birth.returncode} balances-unchanged={before_birth == after_wrong_birth} {wrong_birth.stderr[-160:]}")
born = mini("workspace", "--action", "create", "--dir", ALICE_WS, "--name", "paid-note",
            "--storage", "content", "--predicate", open_law)
_, after_birth = ledger_well()
birth_source_path = os.path.join(ALICE_WS,"sources","create-paid-note.json")
birth_source = json.load(open(birth_source_path)) if os.path.exists(birth_source_path) else {}
read_note = mini("workspace", "--action", "read", "--dir", ALICE_WS, "--name", "paid-note", "--ephemeral", "true")
row("paid member creates and reads content using only their enrolled account and factory grants",
    born.returncode == 0 and read_note.returncode == 0
    and birth_source.get("birth",{}).get("feePayer") == alice_account
    and before_birth.get(alice_account,0) - after_birth.get(alice_account,0) == BIRTH_FEE,
    f"create={born.returncode} read={read_note.returncode} account={before_birth.get(alice_account)}->{after_birth.get(alice_account)} {born.stderr[-180:]}")

renew = mini("join", "--renew", "--host", HOST, "--config", CONFIG, "--socket", SOCKET, "--enrol", PIN,
             "--dir", path("join", "alice"), "--starter-credit", "0")
row("join --renew prints the same memo with one node week's amount",
    renew.returncode == 0 and printed(renew, "memo") == memo and f"({WEEK} atomic units)" in (printed(renew, "amount") or ""),
    printed(renew, "amount") or renew.stderr[-160:])

erin = join("erin", "--ssh-key", JA["sshKeyFile"])
journalled_row("a second Mini key for alice's ssh key (signed by that key) → journalled sshKeyTaken (ssh_key_unique)",
               "erin", PRICE, [printed(erin, "memo") or "x"], "sshKeyTaken", "alice's first key enrolled")

# An ordinary report carrying an enrollment-index record: the client routes it away; the kernel
# refuses it if it ever arrives (enrol_index_not_ordinary). Driven raw over the public socket.
CONFIG_BYTES = open(path("public", "mini.config"), "rb").read()
def sock(op, payload=b""):
    import socket as so
    s = so.socket(so.AF_UNIX, so.SOCK_STREAM); s.connect(SOCKET)
    frame = bytes([1]) + struct.pack("<I", len(CONFIG_BYTES)) + CONFIG_BYTES + bytes([op]) + payload
    s.sendall(struct.pack("<I", len(frame)) + frame)
    data = b""
    while True:
        chunk = s.recv(65536)
        if not chunk: break
        data += chunk
        if len(data) >= 4 and len(data) >= 4 + struct.unpack("<I", data[:4])[0]: break
    s.close()
    body = data[4:4 + struct.unpack("<I", data[:4])[0]]
    return body[0], body[1:]
def cli_file(kind, data, verb):
    src, out = path(f"raw-{time.time_ns()}.in"), path(f"raw-{time.time_ns()}.out")
    open(src, "wb" if isinstance(data, bytes) else "w").write(data)
    run([HOST, CONFIG, verb, kind, src, out], check=True)
    return out
sig_ord = pay("ordinary-to-enrol", PRICE)
obs_view = json.load(open(cli_file("pay-view", sock(107)[1], "inspect")))
rec = {"index": 0, "address": ENROL_HEX, "signature": sig_ord.hex(), "slot": TIP[0] - 50,
       "blockTime": gen.block_time(TIP[0] - 50), "amount": PRICE, "mint": MINT_HEX, "tokenProgram": PROGRAM_HEX,
       "memo": None, "memoError": None}
TIP[0] += 100
command = {"observer": str(OBSERVER), "capability": str(OBSERVER_CAP), "nonce": "777001",
           "expectedAuthorityRoot": obs_view["authorityRoot"], "expectedPayRoot": obs_view["payRoot"],
           "tip": {"slot": TIP[0], "blockTime": gen.block_time(TIP[0])}, "observations": [rec]}
cmd = open(cli_file("pay-observation", json.dumps(command), "author"), "rb").read()
op, plan = sock(108, cmd)
signing = nacl.signing.SigningKey(open(path("keys", f"{OBSERVER}.key"), "rb").read())
detail = ""
if op == 108:
    header = bytes.fromhex(json.load(open(cli_file("pay-plan", plan, "inspect")))["header"]["canonical"])
    op, ingress = sock(109, struct.pack("<I", len(plan)) + plan + signing.sign(header).signature)
    op, result = sock(110, ingress)
    out = json.load(open(cli_file("outcome", result, "inspect")))
    detail = bytes.fromhex(out.get("detail", "")).decode("utf-8", "replace")
else:
    detail = plan.decode("utf-8", "replace")
row("an ordinary report carrying an enrollment-index deposit → refused enrolIndexNeedsReceiver (the client never sends one)",
    "enrolIndexNeedsReceiver" in detail, detail[-120:])
# The same transfer, through the tick: the self-enrollment receiver journals it (memoMissing).
tm = tick("ordinary-to-enrol")
row("control: the same deposit through the tick → journalled memoMissing via the self-enrollment receiver",
    tm.returncode == 0 and (journal_of(enrolment_view(), sig_ord) or {}).get("reason") == "memoMissing", summary(tm))

# Self-enrollment unconfigured (no C_enrol / operator socket): the record waits, undecided.
pay("frank-waits", PRICE, memos=[printed(join("frank"), "memo")])
env = dict(os.environ); env.pop("PAY_RPC_ENDPOINTS", None)
cfg = path("frank-watcher.json")
mini("pay", "watch-config", "--dir", OBS, "--out", cfg, "--enrol-index", "0", "--journal-floor", FLOOR, check=True)
os.makedirs(path("frank-out"))
TIPF = TIP[0] + 10
for side in ("a", "b"):
    for rel, body in endpoint(TIPF).files.items(): gen.dump(path("frank-fx", side, rel), body)
run([WATCHER, "--config", cfg, "--out", path("frank-out"), "--rpc-fixture", path("frank-fx", "a"),
     "--rpc-fixture", path("frank-fx", "b")], env=env)
un = mini("pay", "observe", "--dir", OBS, "--capability", OBSERVER_CAP, "--from", path("frank-out", "observations.json"))
tf = tick("frank")
row("without --enrol-capability/--operator-socket an enrollment record is left undecided (exit 3, no receipt); "
    "the configured tick then enrols it",
    un.returncode == 3 and len(lines(un, "enrol-unconfigured")) == 1 and len(lines(tf, "enrolled")) == 1,
    f"{summary(un)} | {summary(tf)}")


# ------------------------------------------------------------ actual public cold-entry HTTP
# Keep this after the legacy refusals and entry-count checks. The bootstrap owns
# only its loopback listener; its Host connection is the same pinned public
# socket. No SSH transport/socket is supplied to the prepayment client.
bootstrap_server = None
def stop_bootstrap():
    global bootstrap_server
    if bootstrap_server is not None and bootstrap_server.poll() is None:
        os.killpg(bootstrap_server.pid, signal.SIGTERM)
        try: bootstrap_server.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(bootstrap_server.pid, signal.SIGKILL)
            bootstrap_server.wait(timeout=10)
    bootstrap_server = None
atexit.register(stop_bootstrap)

PUBLIC_CONFIG = path("public", "mini.config")
PUBLIC_METADATA = path("bootstrap-metadata.json")
def file_sha256(filename):
    digest = hashlib.sha256()
    with open(filename, "rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""): digest.update(chunk)
    return digest.hexdigest()
json.dump({"sshLogin": LOGIN, "clientBundleUrl": "https://box.example/fixture-mini",
           "clientBundleSha256": file_sha256(MINI)},
          open(PUBLIC_METADATA, "w"))
bootstrap_log = path("bootstrap.log")
bootstrap_server = subprocess.Popen(
    [MINI, "enrollment-bootstrap", "--host", HOST, "--config", PUBLIC_CONFIG,
     "--socket", SOCKET, "--listen", "127.0.0.1:0", "--metadata", PUBLIC_METADATA],
    stdout=open(bootstrap_log, "wb"), stderr=subprocess.STDOUT, start_new_session=True)
# Let the OS pick and retain a free port: no reserve-close-bind race.
bootstrap_port = None
for _ in range(600):
    log = open(bootstrap_log).read()
    match = re.search(r"enrollment bootstrap listening on 127\.0\.0\.1:(\d+)", log)
    if match:
        bootstrap_port = int(match.group(1)); break
    if bootstrap_server.poll() is not None:
        fail(f"enrollment-bootstrap exited: {log[-600:]}")
    time.sleep(0.1)
if bootstrap_port is None: fail("enrollment-bootstrap did not publish its bound loopback port")
BOOTSTRAP_URL = f"http://127.0.0.1:{bootstrap_port}/mini/v1"
json.dump({"url": BOOTSTRAP_URL, "pid": bootstrap_server.pid, "publicSocket": SOCKET},
          open(path("bootstrap-fixture.json"), "w"))

def http_get(route):
    # Direct loopback connection ignores ambient HTTP proxy settings. Bound the
    # read as the public adapter does, and keep response headers in the evidence.
    connection = http.client.HTTPConnection("127.0.0.1", bootstrap_port, timeout=5)
    started = time.monotonic()
    try:
        connection.request("GET", "/mini/v1" + route)
        response = connection.getresponse()
        raw = response.read(16 * 1024 + 1)
        if response.status != 200 or len(raw) > 16 * 1024:
            fail(f"bootstrap {route}: status={response.status} bytes={len(raw)}")
        value = json.loads(raw)
        return value, dict(response.getheaders()), time.monotonic() - started
    finally: connection.close()

public_metadata, metadata_headers, metadata_seconds = http_get("/metadata")
row("cold HTTP metadata pins the Host, domain and login without exposing deployment configuration",
    public_metadata.get("type") == "minidregg-enrollment-bootstrap-v1"
    and public_metadata.get("hostSha256") == file_sha256(HOST)
    and str(public_metadata.get("domain")) == str(operator["domain"])
    and public_metadata.get("sshLogin") == LOGIN
    and public_metadata.get("memoVersions") == ["enrol:v1"]
    and not any(k in public_metadata for k in ("config", "storageRoot", "signatureBinary", "operatorSocket"))
    and metadata_headers.get("Cache-Control") == "no-store" and metadata_seconds < 5,
    f"url={BOOTSTRAP_URL} host={public_metadata.get('hostSha256')} no-cache={metadata_headers.get('Cache-Control')} seconds={metadata_seconds:.3f}")

cold_args = ["join", "--solana", "--host", HOST, "--config", PUBLIC_CONFIG,
             "--bootstrap-url", BOOTSTRAP_URL, "--enrol", PIN,
             "--dir", path("join", "cold-http"), "--name", "cold-http",
             "--weeks", str(COLD_WEEKS)]
assert "--socket" not in cold_args and "--remote" not in cold_args
cold_join = mini(*cold_args)
open(path("cold-http-join.out"), "w").write(cold_join.stdout + cold_join.stderr)
if cold_join.returncode != 0: fail(f"cold HTTP join: {cold_join.stderr[-600:]}")
cold_record = json.load(open(path("join", "cold-http", "join.json")))
cold_quote = cold_record.get("quote", {})
cold_key = cold_record["miniKey"]
cold_memo = printed(cold_join, "memo") or ""
cold_amount = int(cold_quote.get("atomicAmount", "0"))
row("cold HTTP join without a socket retains the source quote: two exact weeks plus 347 spendable credit",
    cold_record.get("bootstrapUrl") == BOOTSTRAP_URL
    and cold_record.get("bootstrapMetadata") == public_metadata
    and cold_quote.get("type") == "minidregg-pay-enrollment-quote-v1"
    and cold_quote.get("miniKey") == cold_key and cold_quote.get("mode") == "enrol"
    and cold_quote.get("priceReserved") is False
    and int(cold_quote.get("requestedWeeks", "0")) == COLD_WEEKS
    and int(cold_quote.get("grantedWeeks", "0")) == COLD_WEEKS
    and all(int(cold_quote.get(k, "-1")) == STARTER for k in
            ("recommendedStarterCredit", "requestedStarterCredit", "spendableRemainder"))
    and STARTER == 347 and int(cold_quote.get("birthFee", "-1")) == BIRTH_FEE
    and int(cold_quote.get("membershipCredit", "0")) == COLD_WEEKS * WEEK
    and int(cold_quote.get("roundingCredit", "-1")) == 0
    and cold_amount == int(cold_record["amountAtomic"]) == BIRTH_FEE + COLD_WEEKS * WEEK + STARTER
    and f"({cold_amount} atomic units)" in (printed(cold_join, "amount") or "")
    and len(cold_memo) == 400,
    f"atomic={cold_amount} birth={cold_quote.get('birthFee')} weeks={cold_quote.get('grantedWeeks')} starter={cold_quote.get('spendableRemainder')}")

cold_signature = gen.sig("e4-cold-http")
cold_route = f"/enrollment/{cold_key}?signature={cold_signature.hex()}"
cold_before, _, _ = http_get(cold_route)
cold_early = mini("join", "--wait", "--host", HOST, "--config", PUBLIC_CONFIG,
                  "--bootstrap-url", BOOTSTRAP_URL, "--dir", path("join", "cold-http"),
                  "--signature", gen.b58(cold_signature), "--timeout", "0")
# Signature diagnosis is exact and separate from key admission: an already
# journaled memo-less payment must not look like an unknown payment.
missing_signature = gen.sig("e4-nomemo")
# The prior direct status and wait consume this client's two-status burst.
# Respect the public polling budget before testing a distinct exact refusal.
time.sleep(10.1)
cold_refusal, _, _ = http_get(f"/enrollment/{cold_key}?signature={missing_signature.hex()}")
cold_refusal_wait = mini("join", "--wait", "--host", HOST, "--config", PUBLIC_CONFIG,
                         "--bootstrap-url", BOOTSTRAP_URL, "--dir", path("join", "cold-http"),
                         "--signature", gen.b58(missing_signature), "--timeout", "0")
row("cold HTTP wait distinguishes notObserved from the exact journaled payment before admission",
    cold_before.get("state") == "notObserved" and cold_before.get("entry") is None
    and cold_before.get("paymentDecision") is None
    and cold_early.returncode == 4 and "not enrolled yet" in cold_early.stderr
    and cold_refusal.get("state") == "notObserved" and cold_refusal.get("entry") is None
    and (cold_refusal.get("paymentDecision") or {}).get("signature") == missing_signature.hex()
    and (cold_refusal.get("paymentDecision") or {}).get("reason") == "memoMissing"
    and cold_refusal_wait.returncode == 3 and "memoMissing" in cold_refusal_wait.stderr
    and not os.path.exists(path("join", "cold-http", "workspace")),
    f"unknown={cold_early.returncode} exact-refusal={cold_refusal_wait.returncode} state={cold_before.get('state')}")

cold_well_before, cold_bal_before = ledger_well()
entries_before_cold = len(enrolment_view()["entries"])
# The float occupies row0; five existing members occupy rows1..5. This
# additional member must fit row6 rather than silently rely on an exhausted book.
if 1 + entries_before_cold >= len(BOOK): fail("cold HTTP fixture needs one unallocated book row")
actual_cold_signature = pay("cold-http", cold_amount, memos=[cold_memo])
assert actual_cold_signature == cold_signature
cold_tick = tick("cold-http")
cold_view = enrolment_view()
cold_entry = entry(cold_view, cold_key)
cold_status, cold_headers, cold_seconds = http_get(cold_route)
row("the real fixture tick admits the HTTP-quoted payment with the exact duration and available book row",
    cold_tick.returncode == 0 and len(lines(cold_tick, "enrolled")) == 1
    and cold_entry is not None
    and len(cold_view["entries"]) == entries_before_cold + 1
    and cold_entry["index"] == 1 + entries_before_cold < len(BOOK)
    and cold_entry["lease"]["expiresAt"] == cold_view["clock"]["hour"] + 168 * COLD_WEEKS
    and cold_status.get("type") == "minidregg-enrollment-status-v1"
    and cold_status.get("miniKey") == cold_key and cold_status.get("state") == "enrolled"
    and cold_status.get("entry") == cold_entry and cold_status.get("paymentDecision") is None
    and cold_headers.get("Cache-Control") == "no-store" and cold_seconds < 5,
    f"{summary(cold_tick)} entry={cold_entry} HTTP-seconds={cold_seconds:.3f}")

# Status still comes from HTTP. The explicit local socket is the fixture's
# already-admitted workspace transport, never a prepayment quote dependency.
cold_wait = mini("join", "--wait", "--host", HOST, "--config", PUBLIC_CONFIG,
                 "--bootstrap-url", BOOTSTRAP_URL, "--socket", SOCKET,
                 "--dir", path("join", "cold-http"), "--signature", gen.b58(cold_signature),
                 "--birth-context", BIRTH_CONTEXT, "--timeout", "30", "--interval", "1")
open(path("cold-http-wait.out"), "w").write(cold_wait.stdout + cold_wait.stderr)
cold_workspace = path("join", "cold-http", "workspace")
cold_read = mini("workspace", "--action", "read", "--dir", cold_workspace,
                 "--name", "account", "--ephemeral", "true")
run([HOST, PUBLIC_CONFIG, "pay-enrol-ids", cold_key, path("cold-http-ids.json")], check=True)
cold_ids = json.load(open(path("cold-http-ids.json")))
cold_well_after, cold_bal_after = ledger_well()
row("HTTP paid wait constructs the member workspace and preserves all 347 starter credit",
    cold_wait.returncode == 0 and cold_read.returncode == 0
    and f"enrolled subject {cold_ids['subject']}" in cold_wait.stdout
    and cold_bal_after.get(cold_ids["account"]) == STARTER
    and cold_well_before - cold_well_after == cold_amount
    and cold_bal_after.get(str(acct(FLOAT))) == cold_bal_before.get(str(acct(FLOAT)))
    and os.path.exists(os.path.join(cold_workspace, "birth-context.json")),
    f"wait={cold_wait.returncode} read={cold_read.returncode} starter={cold_bal_after.get(cold_ids['account'])} well={cold_well_before}->{cold_well_after} {cold_wait.stderr[-180:]}")

# ------------------------------------------------------------ restart, audit
before = enrolment_view()
stop_server(); start_server()
after = enrolment_view()
cold_read = mini("workspace", "--action", "read", "--dir", ALICE_WS, "--name", "paid-note", "--ephemeral", "true")
row("cold restart: paid member still reads their created content", cold_read.returncode == 0,
    f"read={cold_read.returncode} {cold_read.stderr[-120:]}")
row("restart: the enrollment view is identical (entries, leases, journal)", before == after,
    f"entries={len(after['entries'])} journal={len(after['journal'])}")
au = mini("pay", "audit", "--dir", OBS, "--operator-socket", OPSOCK)
enrols = [l for l in au.stdout.splitlines() if l.startswith("enrol\t")]
row("pay audit (online): every self-enrollment decision replays through op 120",
    au.returncode == 0 and "FINDING" not in au.stdout and len(enrols) == 13, f"{len(enrols)} enrol rows; {au.stdout.strip().splitlines()[-1] if au.stdout else au.stderr[-160:]}")
stop_bootstrap()
stop_server()
off = mini("pay", "audit", "--dir", OBS, "--offline", "true")
led = [l for l in off.stdout.splitlines() if l.startswith(("ledger", "host-audit"))]
row("audit (offline): -well_now = -well_genesis + Σ enrolment credit; the Host re-admits every record",
    off.returncode == 0 and any("identity holds" in l for l in led) and "FINDING" not in off.stdout,
    " | ".join(led) or off.stderr[-200:])

with open(path("rows.tsv"), "w") as out:
    out.write("verdict\tstep\tobserved\n")
    for verdict, name, observed in ROWS: out.write(f"{verdict}\t{name}\t{observed}\n")
passed = sum(1 for v, _, _ in ROWS if v == "PASS")
verdict = f"J-PAY-E4 {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - STARTED:.1f} s)"
print(verdict); print(path("rows.tsv")); print(verdict, file=sys.stderr)
sys.exit(0 if passed == len(ROWS) else 1)
PY
