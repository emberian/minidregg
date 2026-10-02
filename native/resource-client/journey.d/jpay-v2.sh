#!/usr/bin/env bash
# J-PAY-V2: real matched Host/Store receiving with synthetic Solana RPC fixtures.
# Run with absolute HOST MINI STORE VERIFIER PAY_WATCHER_BIN and a fresh
# JOURNEY_STEP_DIR; optional FAMILY_MANIFEST is recorded in evidence.
# Requires source181-186, checked empty-report chain tips, v2 observer decisions,
# and the paid-context/claim client. Core-only Hosts refuse early.
# No network RPC, fake Host, or seeded pay mutations. Uses E3/E4 signed bootstrap
# and the real deploy/pay/mini-pay-watcher with two independent fixture paths.
# The transparent fault relay only drops already-received real replies.
# Runtime qualification remains pending until this hook actually passes.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jpay-v2: $name is required" >&2; exit 2; fi
done
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
TREE=$(CDPATH='' cd -- "$HERE/../../.." && pwd)
export PAY_WATCHER_BIN=${PAY_WATCHER_BIN:-$TREE/native/pay-watcher/target/release/pay-watcher}
export PAY_FIXTURES=$TREE/native/pay-watcher/fixtures
export PAY_TICK_SCRIPT=$TREE/deploy/pay/mini-pay-watcher
for tool in python3 jq ssh-keygen flock; do
  command -v "$tool" >/dev/null || { echo "jpay-v2: $tool is required" >&2; exit 2; }
done
python3 -c 'import nacl.signing' 2>/dev/null || { echo "jpay-v2: PyNaCl is required" >&2; exit 2; }
[ -x "$PAY_WATCHER_BIN" ] || { echo "J-PAY-V2 FAIL setup: pay-watcher binary missing at $PAY_WATCHER_BIN" >&2; exit 1; }
[ ! -e "$JOURNEY_STEP_DIR/jpay-v2" ] || { echo "jpay-v2: refusing existing run" >&2; exit 2; }
mkdir -p "$JOURNEY_STEP_DIR"
DIR=$(mktemp -d /tmp/jpay-v2.XXXXXX)
ln -s "$DIR" "$JOURNEY_STEP_DIR/jpay-v2"
exec python3 - "$DIR" <<'PY'
import atexit, base64, glob, hashlib, json, os, shutil, signal, socket, struct, subprocess, sys, threading, time
import nacl.signing

DIR = sys.argv[1]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
WATCHER, FIXTURES = os.environ["PAY_WATCHER_BIN"], os.environ["PAY_FIXTURES"]
TICK_SCRIPT = os.environ["PAY_TICK_SCRIPT"]
sys.path.insert(0, FIXTURES)
sys.dont_write_bytecode = True   # never leave __pycache__ in the tree's fixtures
import generate as gen   # P1b's fixture vocabulary (generate.py runs nothing on import)

ROWS, STARTED, COMPLETED = [], time.time(), False
EMBER, FLOAT, OBSERVER = 7, 20, 30
FACTORY_CONTROL, OBSERVER_CAP, PAY_CONTROL, ENROL_CAP = 53, 4030, 4031, 4032
SUBJECTS = [EMBER, FLOAT, OBSERVER]
def acct(s): return 100 + s
NODE_RATE = 5952380
STARTER = 347  # an explicit positive requested allowance; prices come only from source182
WEEKS = 2
FLOOR = 1_000_000
LOGIN = "mini@box.example"

def path(*names): return os.path.join(DIR, *names)
def fail(message):
    print(f"J-PAY-V2 FAIL: {message}", file=sys.stderr); sys.exit(1)
def row(name, ok, observed):
    observed = " ".join(str(observed).split())
    ROWS.append(("PASS" if ok else "FAIL", name, observed))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{observed}", file=sys.stderr)
def finish():
    if not COMPLETED:
        ROWS.append(("FAIL", "journey completed", "interrupted or refused; inspect logs"))
    with open(path("rows.tsv"),"w") as out:
        out.write("status\tcheck\tobserved\n")
        for cells in ROWS: out.write("\t".join(cells)+"\n")
    binaries = {k: {"path":os.environ[k], "sha256":hashlib.sha256(open(os.environ[k],"rb").read()).hexdigest()}
                for k in ("HOST","MINI","STORE","VERIFIER","PAY_WATCHER_BIN")}
    result = {"type":"mini-paid-v2-journey-v1","completed":COMPLETED,
              "passed":sum(r[0]=="PASS" for r in ROWS),"total":len(ROWS),
              "elapsedSeconds":time.time()-STARTED,"binaries":binaries,
              "familyManifest":os.environ.get("FAMILY_MANIFEST"),"checks":ROWS}
    json.dump(result,open(path("result.json"),"w"),indent=2)
    verdict=f"J-PAY-V2 {'PASS' if COMPLETED and all(r[0]=='PASS' for r in ROWS) else 'FAIL'} {result['passed']}/{len(ROWS)}"
    print(verdict,file=sys.stderr);print(verdict);print(path("rows.tsv"))
atexit.register(finish)
def require(name, ok, observed):
    row(name,ok,observed)
    if not ok: raise RuntimeError(name)
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
json.dump(genesis, open(path("genesis.json"), "w"))
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
          "creditPerAtomic": "1", "maxPerObservation": "100000000000", "minTickSlots": "150",
          "nodeHourRate": str(NODE_RATE), "enrolIndex": None, "journalFloor": str(FLOOR), "slashCallerPermille":"500"}
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


# ------------------------------------------------------------ bounded real public wire
CONFIG_BYTES = open(CONFIG,"rb").read()
HOST_SHA = hashlib.sha256(open(HOST,"rb").read()).digest()
def read_exact(stream,n):
    parts=b""
    while len(parts)<n:
        piece=stream.recv(n-len(parts))
        if not piece: raise RuntimeError("transport closed before full frame")
        parts+=piece
    return parts
def read_frame(stream):
    size=struct.unpack("<I",read_exact(stream,4))[0]
    if not 0<size<=16*1024*1024: raise RuntimeError("fixture transport frame bound")
    return read_exact(stream,size)
def wire(op,payload=b"",sock=None):
    envelope=b"\x02"+struct.pack("<I",len(CONFIG_BYTES))+CONFIG_BYTES+HOST_SHA+bytes([op])+payload
    with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as stream:
        stream.settimeout(120);stream.connect(sock or SOCKET)
        stream.sendall(struct.pack("<I",len(envelope))+envelope)
        reply=read_frame(stream)
    return reply[0],reply[1:]
def source_json(op,value,label):
    payload=json.dumps(value,separators=(",",":")).encode()
    actual,data=wire(op,payload)
    open(path(label+".request.json"),"wb").write(payload)
    open(path(label+".response.bin"),"wb").write(data)
    if actual!=op: fail(f"source op{op} refused: {data[-240:]!r}")
    result=json.loads(data)
    json.dump(result,open(path(label+".json"),"w"),indent=2)
    return result
def status(record,signature=None,label="status"):
    request={"identityKey":record["miniKey"]}
    if signature is not None:
        request.update(signature=signature.hex(),originalRecipient=record["enrolAddress"])
    return source_json(181,request,label)
def ids(record,label):
    output=path(label+"-ids.json")
    run([HOST,CONFIG,"pay-enrol-ids",record["miniKey"],output],check=True)
    return json.load(open(output))
def original_id(record,signature):
    return (b"soltx:"+signature+bytes.fromhex(record["enrolAddress"])).hex()

# ------------------------------------------------------------ E4's two independent RPC fixture paths
HISTORY, TIP = [], [2000]
def pay(label,record):
    TIP[0]+=300
    signature=gen.sig(f"v2-{label}")
    body=gen.enrol_tx(signature,TIP[0]-50,int(record["amountAtomic"]),memos=[record["memo"]])
    HISTORY.append((signature,TIP[0]-50,body,label))
    return signature
def endpoint(tip):
    ep=gen.Endpoint()
    ep.put("getSlot/finalized.json",gen.envelope(tip))
    ep.put(f"getBlockTime/{tip}.json",gen.envelope(gen.block_time(tip)))
    for owner,account in ((gen.ENROL,gen.ENROL_TA),(gen.BOOK0,gen.ATA0)):
        ep.put(f"getTokenAccountsByOwner/{owner}.{gen.MINT}.json",
               gen.envelope({"context":{"slot":tip},"value":[gen.token_account_entry(account,owner=owner)]}))
    for owner in EXTRA:
        ep.put(f"getTokenAccountsByOwner/{owner}.{gen.MINT}.json",
               gen.envelope({"context":{"slot":tip},"value":[]}))
    newest=[(s,slot) for s,slot,_,_ in reversed(HISTORY) if slot<tip]
    for until in [None]+[s for s,_ in newest]:
        rows=newest if until is None else newest[:[s for s,_ in newest].index(until)]
        suffix=f".until.{gen.b58(until)}" if until else ""
        ep.put(f"getSignaturesForAddress/{gen.ENROL_TA}{suffix}.json",
               gen.envelope(gen.listing(*[(s,slot,None) for s,slot in rows])))
    for signature,_,body,_ in HISTORY: ep.tx(signature,body)
    ep.sigs(gen.ATA0,[])
    return ep
STATE=path("watcher-state")
def tick(tag):
    dirs=[]
    for side in ("a","b"):
        target=path("ticks",tag,side)
        for relative,value in endpoint(TIP[0]+10).files.items():
            gen.dump(os.path.join(target,relative),value)
        dirs.append(target)
    env=dict(os.environ,MINI=MINI,PAY_WATCHER=WATCHER,PAY_STATE=STATE,
             PAY_OBSERVER_WS=OBS,PAY_OBSERVER_CAPABILITY=str(OBSERVER_CAP),
             PAY_ENROL_INDEX="0",PAY_JOURNAL_FLOOR=str(FLOOR),
             PAY_ENROL_CAPABILITY=str(ENROL_CAP),PAY_OPERATOR_SOCKET=OPSOCK,
             PAY_RPC_FIXTURES=" ".join(dirs),PAY_ENROL_ROUNDS="0")
    env.pop("PAY_RPC_ENDPOINTS",None)
    result=run(["sh",TICK_SCRIPT],env=env)
    open(path("tick-"+tag+".log"),"w").write(result.stdout+result.stderr)
    for name in ("observations","events"):
        src=os.path.join(STATE,"tick",name+".json")
        if os.path.exists(src): shutil.copyfile(src,path(f"tick-{tag}.{name}.json"))
    return result

# ------------------------------------------------------------ native v2 caller custody
PIN=path("enrol-v2.json")
json.dump({"type":"minidregg-enrol-pin-v2","enrolAddress":gen.ENROL,"mint":gen.MINT,
           "tokenProgram":gen.TOKEN_2022,"decimals":"6","login":LOGIN},open(PIN,"w"))
os.makedirs(path("join"),mode=0o700)
def join(name):
    return mini("join","--memo-version","v2","--solana","--host",HOST,"--config",CONFIG,
                "--socket",SOCKET,"--enrol",PIN,"--dir",path("join",name),"--name",name,
                "--weeks",WEEKS,"--starter-credit",STARTER,"--birth-context",BIRTH_CONTEXT)
def wait(name,signature):
    return mini("join","--memo-version","v2","--wait","--host",HOST,"--config",CONFIG,
                "--socket",SOCKET,"--dir",path("join",name),"--signature",gen.b58(signature),
                "--timeout","0","--birth-context",BIRTH_CONTEXT)

missing=source_json(181,{"identityKey":public[OBSERVER]},"missing-tip-status")
require("fresh genesis has no authenticated chain evidence",
        missing["chainFreshness"]=="missing" and missing["asOf"] is None,missing)
op,data=wire(182,json.dumps({"kind":"purchase","identityKey":public[OBSERVER],
    "sshKey":public[OBSERVER],"freshNext":"01"*32,"mode":"enrol","weeks":"1",
    "starter":"0","expiryHour":"1"}).encode())
require("source182 refuses a quote with missing chain evidence",op==255,
        {"op":op,"detail":data[-220:].decode(errors="replace")})
early=join("alice")
require("native v2 entry preserves preparation but refuses missing chain evidence",
        early.returncode!=0 and "missing" in early.stderr and not os.path.exists(path("join","alice","join.json")),
        early.stderr[-250:])
well0,bal0=ledger_well()
heartbeat=tick("empty-heartbeat")
after_heartbeat=source_json(181,{"identityKey":public[OBSERVER]},"fresh-tip-status")
well_h,bal_h=ledger_well()
require("real empty watcher report installs exact fresh tip without mint",
        heartbeat.returncode==0 and "heartbeat\t" in heartbeat.stdout
        and after_heartbeat["chainFreshness"]=="fresh"
        and int(after_heartbeat["asOf"]["slot"])==TIP[0]+10
        and int(after_heartbeat["asOf"]["blockTime"])==gen.block_time(TIP[0]+10)
        and (well_h,bal_h)==(well0,bal0),heartbeat.stdout[-300:])
alice=join("alice")
require("fresh source182 creates a signed v2 payment from retained native preparation",
        alice.returncode==0,alice.stderr[-250:] or alice.stdout[-250:])
JA=json.load(open(path("join","alice","join.json")))
AQ=JA["quote"]["split"]
require("native payment retains source amount, explicit weeks and starter",
        JA["memo"].startswith("enrol:v2:") and len(JA["memo"])==485
        and int(AQ["weeks"])==WEEKS and int(AQ["minimumStarterCredit"])==STARTER
        and JA["amountAtomic"]==AQ["amountAtomic"],AQ)
A=pay("alice",JA);ta=tick("alice")
SA=status(JA,A,"alice-consumed")
AP=SA["payment"];alice_ids=ids(JA,"alice")
well_a,bal_a=ledger_well()
require("real watcher deposits v2 and source consumes original memo exactly once",
        ta.returncode==0 and AP["state"]=="consumedV2" and AP["authorization"]=="originalMemo"
        and int(AP["weeks"])==WEEKS and AP["amountAtomic"]==JA["amountAtomic"]
        and SA["paymentLocator"]["claimId"]==original_id(JA,A)
        and SA["entry"]["subject"]==alice_ids["subject"],{"tick":ta.stdout[-220:],"status":SA})
require("first admission conserves source quote and keeps requested duration and starter",
        well_h-well_a==int(AQ["mintedCredit"])
        and int(AP["mintedCredit"])==int(AQ["mintedCredit"])
        and int(AP["birthFee"])+int(AP["membershipCredit"])+int(AP["creditedRemainder"])==int(AP["mintedCredit"])
        and bal_a[alice_ids["account"]]==int(AP["creditedRemainder"])>=STARTER
        and int(SA["entry"]["leaseUntil"])==int(SA["asOf"]["hour"])+168*WEEKS
        and bal_a[str(acct(FLOAT))]==bal_h[str(acct(FLOAT))],AP)
aw=wait("alice",A)
require("native v2 wait imports an admitted member workspace",aw.returncode==0,aw.stderr[-350:] or aw.stdout[-250:])

bob=join("bob")
require("second friend obtains source quote before tariff changes",bob.returncode==0,bob.stderr[-250:])
JB=json.load(open(path("join","bob","join.json")))
changed=dict(tariff,version="4",enrolIndex="0",creditPerAtomic="2")
json.dump({"control":str(FACTORY_CONTROL),"book":[],"tariff":changed},open(path("tariff-v4.json"),"w"))
change=mini("pay","book","--dir",WS[EMBER],"--source",path("tariff-v4.json"))
require("ordinary signed pay book changes current pricing",change.returncode==0,change.stderr[-220:] or change.stdout)
well_before,bal_before=ledger_well()
B=pay("bob-stale-terms",JB);tb=tick("bob-pending")
SB=status(JB,B,"bob-pending")
well_pending,bal_pending=ledger_well()
require("stale terms remain an exact pending origin with no mint or enrollment",
        tb.returncode==0 and SB["payment"]["state"]=="pendingV2"
        and SB["payment"]["reason"]=="termsStale" and SB["leaseState"]=="notEnrolled"
        and SB["payment"]["amountAtomic"]==JB["amountAtomic"]
        and SB["paymentLocator"]["claimId"]==original_id(JB,B)
        and (well_pending,bal_pending)==(well_before,bal_before),
        {"tick":tb.stdout[-220:],"status":SB})
bw=wait("bob",B)
locator_path=path("join","bob","payment-"+hashlib.sha256(JB["memo"].encode()).hexdigest()+".locator.json")
locator=json.load(open(locator_path))
require("native wait retains exact pending locator without publishing membership",
        bw.returncode!=0 and locator=={"signature":B.hex(),"originalRecipient":JB["enrolAddress"],
            "identityKey":JB["miniKey"]} and not os.path.exists(path("join","bob","workspace","workspace.json"))
        and len(HISTORY)==2,bw.stderr[-350:])

# One bounded transparent listener. It drops a reply only AFTER saving the full
# real Host response, never synthesizing a result or mutating the pay Store.
FAULT=path("fault.sock")
FAULT_STOP=threading.Event();FAULT_DROP=threading.Event();FAULT_CALLS=[];FAULT_ERRORS=[]
def fault_loop(listener):
    while not FAULT_STOP.is_set():
        try:client,_=listener.accept()
        except socket.timeout:continue
        except OSError:
            if FAULT_STOP.is_set():return
            raise
        try:
            with client:
                client.settimeout(120);frame=read_frame(client)
                n=struct.unpack("<I",frame[1:5])[0]
                op=frame[5+n+(32 if frame[0]==2 else 0)]
                FAULT_CALLS.append(op)
                if op not in (181,182,183,184,185,186): raise RuntimeError(f"unexpected fixture op{op}")
                with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as upstream:
                    upstream.settimeout(120);upstream.connect(SOCKET)
                    upstream.sendall(struct.pack("<I",len(frame))+frame);reply=read_frame(upstream)
                number=len(FAULT_CALLS)
                open(path(f"fault-{number}-op{op}.request.bin"),"wb").write(frame)
                open(path(f"fault-{number}-op{op}.response.bin"),"wb").write(reply)
                if op==185 and FAULT_DROP.is_set():
                    FAULT_DROP.clear();continue
                client.sendall(struct.pack("<I",len(reply))+reply)
        except Exception as error:
            FAULT_ERRORS.append(repr(error))
listener=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM)
listener.bind(FAULT);listener.listen(4);listener.settimeout(.2)
fault_thread=threading.Thread(target=fault_loop,args=(listener,),daemon=True);fault_thread.start()
def stop_fault():
    FAULT_STOP.set();listener.close();fault_thread.join(timeout=3)
atexit.register(stop_fault)
def claim_args(name,action,*extra):
    return ["pay-claim","--action",action,"--join-dir",path("join",name),
            "--host",HOST,"--config",CONFIG,"--socket",FAULT,*map(str,extra)]
def current_claim_quote(label,nonce):
    now=status(JB,B,label+"-status")
    output=path(label+".bin")
    result=mini(*claim_args("bob","quote","--mode","enrol","--weeks",WEEKS,
                 "--starter-credit",STARTER,"--expiry-hour",int(now["asOf"]["hour"])+1,
                 "--nonce",nonce,"--output",output))
    require(label+" is source-authored unsigned preparation",result.returncode==0,result.stderr[-250:] or output)
    sidecar=json.load(open(output+".quote.json"))
    require(label+" preserves immutable origin and makes no extra transfer",
            sidecar["originClaimId"]==original_id(JB,B)
            and sidecar["quote"]["split"]["amountAtomic"]==JB["amountAtomic"]
            and int(sidecar["quote"]["split"]["weeks"])==WEEKS,sidecar["quote"]["split"])
    return output,sidecar["quote"]
before_rotate,QR=current_claim_quote("before-rotation",601)
successor=JB["miniKeyFile"]+".next"
successor_public=open(JB["nextPublicFile"],"rb").read().hex()
mini("keygen","--secret",path("after-next.key"),"--public",path("after-next.pub"),"--no-prerotation",check=True)
json.dump({"publicKey":open(path("after-next.pub"),"rb").read().hex()},open(path("next-digest.json"),"w"))
run([HOST,CONFIG,"author","signing-key-next-digest",path("next-digest.json"),path("next-digest.txt")],check=True)
next_digest=int(open(path("next-digest.txt")).read().strip()).to_bytes(32,"little").hex()
rotation={"expectedAuthorityRoot":QR["authorityRoot"],"expectedPayRoot":QR["payRoot"],
          "identityKey":JB["miniKey"],"expectedEpoch":QR["owner"]["authorityEpoch"],
          "nonce":"602","successorKey":successor_public,"successorNextKeyDigest":next_digest}
json.dump(rotation,open(path("rotation.json"),"w"))
run([HOST,CONFIG,"author","pay-claim-rotation",path("rotation.json"),path("rotation.bin")],check=True)
ROTATE=path("rotate-operation")
FAULT_DROP.set()
lost_rotation=mini(*claim_args("bob","rotate","--key",successor,"--command",path("rotation.bin"),
                               "--operation-record",ROTATE))
require("pending rotation crosses real185 then loses only its reply",
        lost_rotation.returncode!=0 and not FAULT_DROP.is_set() and os.path.exists(os.path.join(ROTATE,"operation.json")),
        lost_rotation.stderr[-300:])
# Preserve fixture custody privately but remove the original key path used by lookup.
os.rename(JB["miniKeyFile"],JB["miniKeyFile"]+".retired-evidence")
call_mark=len(FAULT_CALLS)
rotate_lookup=mini(*claim_args("bob","lookup","--operation-record",ROTATE))
require("exact rotation lookup survives missing old key and changed current custody",
        rotate_lookup.returncode==0 and FAULT_CALLS[call_mark:]==[186],rotate_lookup.stderr[-250:] or rotate_lookup.stdout[-250:])
after_rotate,QC=current_claim_quote("after-rotation",603)
still_pending=status(JB,B,"bob-after-rotation")
require("pending rotation preserves stable identity and moves current custody before first admission",
        still_pending["leaseState"]=="notEnrolled" and still_pending["payment"]["state"]=="pendingV2"
        and still_pending["payment"]==SB["payment"]
        and QC["owner"]["identityKey"]==JB["miniKey"]
        and QC["owner"]["authorizingKey"]==successor_public
        and int(QC["owner"]["authorityEpoch"])==int(QR["owner"]["authorityEpoch"])+1,QC["owner"])
ACCEPT=path("accept-operation")
FAULT_DROP.set()
lost_accept=mini(*claim_args("bob","accept","--key",successor,"--command",after_rotate,"--operation-record",ACCEPT))
require("explicit current quote accept crosses real185 then loses only its reply",
        lost_accept.returncode!=0 and not FAULT_DROP.is_set() and os.path.exists(os.path.join(ACCEPT,"operation.json")),
        lost_accept.stderr[-300:])
after=status(JB,B,"bob-consumed")
well_after,bal_after=ledger_well()
BP=after["payment"];bob_ids=ids(JB,"bob")
require("current quote consumes once: exact weeks, spendable extra-week remainder, rotated authority",
        BP["state"]=="consumedV2" and BP["authorization"]=="acceptCurrentQuote"
        and BP["amountAtomic"]==JB["amountAtomic"]
        and isinstance(BP["acceptedRequest"],str) and len(BP["acceptedRequest"])>0
        and int(BP["weeks"])==WEEKS
        and well_pending-well_after==int(QC["split"]["mintedCredit"])
        and bal_after[bob_ids["account"]]==int(QC["split"]["creditedRemainder"])
        and int(BP["creditedRemainder"])>=int(BP["membershipCredit"])//WEEKS
        and int(after["entry"]["leaseUntil"])==int(after["asOf"]["hour"])+168*WEEKS
        and bal_after[str(acct(FLOAT))]==bal_pending[str(acct(FLOAT))]
        and int(BP["birthFee"])+int(BP["membershipCredit"])+int(BP["creditedRemainder"])==int(BP["mintedCredit"])
        and after["entry"]["subject"]==bob_ids["subject"],BP)
os.rename(successor,successor+".retired-evidence")
call_mark=len(FAULT_CALLS)
lookups=[mini(*claim_args("bob","lookup","--operation-record",ACCEPT)) for _ in range(2)]
well_replayed,bal_replayed=ledger_well()
require("duplicate exact lookup does not replan, sign, submit, or mint",
        all(r.returncode==0 for r in lookups) and FAULT_CALLS[call_mark:]==[186,186]
        and (well_replayed,bal_replayed)==(well_after,bal_after),{"ops":FAULT_CALLS[call_mark:],"well":well_replayed})
renew=source_json(182,{"kind":"purchase","identityKey":JB["miniKey"],"sshKey":JB["sshKey"],
    "mode":"renew","weeks":"1","starter":"0","expiryHour":str(int(after["asOf"]["hour"])+1)},"bob-registry-renewal")
require("post-admission source owner comes from registry with stable subject and rotated key",
        renew["owner"]["identityKey"]==JB["miniKey"]
        and renew["owner"]["authorizingKey"]==successor_public
        and renew["owner"]["authorityEpoch"]==QC["owner"]["authorityEpoch"]
        and after["entry"]["subject"]==bob_ids["subject"],renew["owner"])
require("fault relay generated no result and observed only fixed public paid operations",
        not FAULT_ERRORS,{"ops":FAULT_CALLS,"errors":FAULT_ERRORS})
stop_server();start_server()
cold=status(JB,B,"bob-cold-reopen")
require("cold Store reopen preserves exact consumed origin and enrollment",cold==after,cold)
online_audit=mini("pay","audit","--dir",OBS,"--operator-socket",OPSOCK)
require("online audit attributes original observer and independent claim mint once",
        online_audit.returncode==0 and f"observer credit {AP['mintedCredit']}" in online_audit.stdout
        and f"independent claim credit {BP['mintedCredit']}" in online_audit.stdout,
        online_audit.stderr[-350:] or online_audit.stdout[-500:])
retained=[json.load(open(p)) for p in glob.glob(os.path.join(OBS,"attempts","pay-enrol-*","enrol-status-v2.json"))]
require("later claim mint preserves original pending observer evidence",
        any(v["paymentLocator"]["claimId"]==original_id(JB,B) and v["payment"]["state"]=="pendingV2" for v in retained),retained)
stop_server()
offline_audit=mini("pay","audit","--dir",OBS,"--offline","true")
require("offline audit fully readmits once and conserves observer plus independent claim mint",
        offline_audit.returncode==0 and "fully re-admitted" in offline_audit.stdout
        and "identity holds on fully audited image" in offline_audit.stdout
        and f"independent claim credit {BP['mintedCredit']}" in offline_audit.stdout,
        offline_audit.stderr[-350:] or offline_audit.stdout[-700:])
provenance_paths=glob.glob(os.path.join(OBS,"pay","audit-*","provenance.json"))
require("offline audit retains source image and executable/config provenance",len(provenance_paths)==1,provenance_paths)
provenance=json.load(open(provenance_paths[0]))
require("offline accounting binds the exact source image and retained outputs",
        provenance["hostSha256"]==hashlib.sha256(open(HOST,"rb").read()).hexdigest()
        and provenance["configSha256"]==hashlib.sha256(open(CONFIG,"rb").read()).hexdigest()
        and all(provenance[k].isdigit() for k in ("domain","semantics","expectedSeed","auditedHeight","worldRoot")),provenance)
COMPLETED=True
sys.exit(0 if all(r[0]=="PASS" for r in ROWS) else 1)
PY
