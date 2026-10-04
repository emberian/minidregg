#!/usr/bin/env bash
# J-JOB-MONEY (COMPUTE §2.6, lane C3 K-JOB-MONEY; rebound by J-JOB): a job's money -- the
# caller's escrow, the provider's bond, and the payout or slash -- as conservation-checked Book
# turns on a fresh private Store. The Book holds a job's credit in the account whose id is the job
# cell's id (`pay-job`'s bookHeld); the job cell's escrow + bond is the law's view of it, and every
# row checks the two agree.
#
# Hook contract: HOST, MINI, STORE, VERIFIER and JOURNEY_STEP_DIR exported; it bootstraps its own
# fresh Store and service (newparticipant-acceptance.sh, the J0 fixture) and stops what it starts.
# Run it from a short root (SUN_LEN). Exit 0 = PASS; the last stdout line is rows.tsv.
#
# The job law is C1's (deploy/shell/templates/job/law.job): a job is a declared cell born in A's
# room `lab`, ordered by its caller (born unfunded), and its money moves only by the job-money
# receiver (ops 160-163), which pins the job law (notJobLaw otherwise). The terminal states are
# reached by the law's own edges, never hand-set: upheld by timeout (an answer, no truth, the
# clock past finalAt), slashed by the stall. The money turns are `mini job --action
# fund|claim|settle`; the plan (op 160) names a refused decision, so every refusal row names its
# reason (the submission, op 162, is blind as MR requires).
#
# Who: A = the sponsor (7, account 7) is caller and operator; P = 21 (account 121) is invited into
# lab; S = 22 (account 122) is enrolled but holds no grant on the jobs.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jjob-money: $name is required" >&2; exit 2; fi
done
DIR="$JOURNEY_STEP_DIR/jjob-money"
if [ -e "$DIR" ]; then echo "jjob-money: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
set +e
python3 - "$DIR" "$HERE" <<'PY'
import json, os, re, socket, struct, subprocess, sys, time
DIR, HERE = sys.argv[1], sys.argv[2]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
W = os.path.join(DIR, "w")
ROWS = []
PRICE, BOND = 10000, 10000
SHARE = BOND * 500 // 1000
started = time.time()
def path(*p): return os.path.join(DIR, *p)
def row(name, expected, got, ok):
    got = " ".join(str(got).split())[:400]
    ROWS.append((name, expected, got, "PASS" if ok else "FAIL"))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{got[:220]}", file=sys.stderr)
def run(*args, env=None):
    return subprocess.run(list(args), capture_output=True, text=True, env=env)
def last_line(r): return ((r.stderr or "").strip().splitlines() or [""])[-1]
def last_json(text):
    for line in reversed((text or "").strip().splitlines()):
        try: return json.loads(line)
        except Exception: continue
    return {}
def stop():
    pid = os.path.join(W, "public", "server.pid")
    if os.path.exists(pid):
        try: os.kill(int(open(pid).read().strip()), 15)
        except Exception: pass
def finish(code):
    stop()
    with open(path("rows.tsv"), "w") as out:
        out.write("verdict\tstep\texpected\tobserved\n")
        for name, expected, observed, verdict in ROWS: out.write(f"{verdict}\t{name}\t{expected}\t{observed}\n")
    passed = sum(1 for r in ROWS if r[3] == "PASS")
    ok = passed == len(ROWS) and code == 0
    verdict = f"J-JOB-MONEY {'PASS' if ok else 'FAIL'} {passed}/{len(ROWS)} ({time.time() - started:.1f} s)"
    print(verdict); print(verdict, file=sys.stderr); print(path("rows.tsv"))
    sys.exit(0 if ok else 1)
def fail(message):
    print(f"J-JOB-MONEY FAIL: {message}", file=sys.stderr); finish(1)

# ---------------------------------------------------------------- the Store
keys = {}
for who in ("p", "s"):
    r = run(MINI, "keygen", "--secret", path(f"{who}.key"), "--public", path(f"{who}.pub"))
    if r.returncode: fail(f"keygen {who}: {last_line(r)}")
    keys[who] = open(path(f"{who}.pub"), "rb").read().hex()
def enrollment(subject, who):
    return {"key": {"keyId": str(7000 + subject), "keyEpoch": "2", "algorithm": "1", "subject": str(subject),
                    "publicKey": keys[who], "activeFrom": "0", "activeUntil": "1000000", "nextKeyDigest": None},
            "accountId": str(100 + subject), "spendCapabilityId": str(1000 + subject),
            "controlCapabilityId": str(2000 + subject), "factoryObserveCapabilityId": str(3000 + subject),
            "initialBalance": "1000000", "accountPredicate": {"type": "all", "predicates": []}}
json.dump([enrollment(21, "p"), enrollment(22, "s")], open(path("extra.json"), "w"))
env = dict(os.environ, NEWPARTICIPANT_OWNER_BUDGET="4000000", EXTRA_GENESIS_ENROLLMENTS=path("extra.json"))
r = run("sh", os.path.join(HERE, "newparticipant-acceptance.sh"), HOST, MINI, STORE, VERIFIER, W, env=env)
open(path("fixture.err"), "w").write(r.stdout + r.stderr)
if r.returncode: fail(f"fixture: {last_line(r)}")
CONFIG = os.path.join(W, "deployment", "pinned-config.json")
SOCK = os.path.join(W, "public", "mini.sock")
A = os.path.join(W, "sponsor"); P = path("p-ws"); S = path("s-ws")
for who, ws, subject in (("p", P, 21), ("s", S, 22)):
    r = run(MINI, "workspace", "--action", "init", "--host", HOST, "--config", CONFIG, "--socket", SOCK,
            "--key", path(f"{who}.key"), "--subject", str(subject), "--dir", ws)
    if r.returncode: fail(f"init {who}: {last_line(r)}")
for ws, account, cap in ((A, 7, 41), (P, 121, 1021), (S, 122, 1022)):
    run(MINI, "workspace", "--action", "import", "--dir", ws, "--name", "purse", "--kind", "account",
        "--target", str(account), "--observe-capability", str(cap), "--operation-capability", str(cap))
cfg = open(CONFIG, "rb").read()
def op(code, payload):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.connect(SOCK)
    body = bytes([1]) + struct.pack("<I", len(cfg)) + cfg + bytes([code]) + payload
    s.sendall(struct.pack("<I", len(body)) + body)
    def exact(n):
        out = b""
        while len(out) < n:
            chunk = s.recv(n - len(out))
            if not chunk: raise RuntimeError("short reply")
            out += chunk
        return out
    n = struct.unpack("<I", exact(4))[0]; reply = exact(n); s.close()
    return reply[0], reply[1:]
def kinded(kind, body): return struct.pack("<H", len(kind)) + kind.encode() + body
def outcome(data):
    code, view = op(8, kinded("outcome", data))
    v = json.loads(view)
    return v
def restart():
    log = open(os.path.join(W, "public", "serve2.log"), "ab")
    if os.path.exists(SOCK): os.unlink(SOCK)
    proc = subprocess.Popen([MINI, "serve", "--host", HOST, "--config", CONFIG, "--socket", SOCK],
                            stdout=log, stderr=log, stdin=subprocess.DEVNULL, start_new_session=True)
    open(os.path.join(W, "public", "server.pid"), "w").write(str(proc.pid))
    for _ in range(1200):
        if os.path.exists(SOCK): return
        time.sleep(0.1)
    fail("service did not come back")
def book(*jobs):
    """The operator's reads of the Book (pay-ledger, pay-job) with the service stopped."""
    stop(); time.sleep(2)
    out = path(f"ledger-{time.time_ns()}.json")
    r = run(HOST, CONFIG, "pay-ledger", out)
    led = json.load(open(out)) if r.returncode == 0 else {"error": last_line(r)}
    views = []
    for j in jobs:
        o = path(f"job-{j}-{time.time_ns()}.json")
        r = run(HOST, CONFIG, "pay-job", str(j), o)
        views.append(json.load(open(o)) if r.returncode == 0 else {"error": last_line(r)})
    restart()
    return led, views
def credit(ws):
    r = run(MINI, "pay", "status", "--dir", ws, "--account", "purse")
    m = re.search(r"credit (-?\d+)", r.stdout)
    return int(m.group(1)) if m else None
def job(ws, action, *flags):
    r = run(MINI, "job", "--action", action, "--dir", ws, *flags)
    open(path(f"cli-{len(ROWS):03d}-{action}.log"), "w").write(r.stdout + "\n---\n" + r.stderr)
    return r.returncode, last_json(r.stdout), ("" if r.returncode == 0 else (last_line(r) or r.stdout.strip()[-300:]))
def money(j): return f"state={j.get('state')} escrow={j.get('escrow')} provider={j.get('provider')} bond={j.get('bond')} held={j.get('held')} bookHeld={j.get('bookHeld')}"
def agrees(j): return j.get("held") == j.get("bookHeld")
def clock(): return int(json.loads(run(MINI, "clock", "--action", "view", "--workspace", A).stdout)["now"])
def tick(now): return run(MINI, "clock", "--action", "tick", "--workspace", os.path.join(W, "clock"), "--now", str(now)).returncode == 0
def named(err, name): return "refused" in err and name in err

def raw_op(code, payload):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.connect(SOCK)
    body = bytes([1]) + struct.pack("<I", len(cfg)) + cfg + bytes([code]) + payload
    s.sendall(struct.pack("<I", len(body)) + body)
    def exact(n):
        out = b""
        while len(out) < n:
            chunk = s.recv(n - len(out))
            if not chunk: raise RuntimeError("short reply")
            out += chunk
        return out
    n = struct.unpack("<I", exact(4))[0]; reply = exact(n); s.close()
    return reply[0], reply[1:]
def authority_root():
    code, view = raw_op(107, b"")
    kind = b"pay-view"
    code, inspected = raw_op(8, struct.pack("<H", len(kind)) + kind + view)
    return json.loads(inspected)["authorityRoot"]

def explain(ws, prefix):
    """The operator's explanation (minidregg-host job-money-explain, the receiver's own
    preparation on the Store as it is) of this workspace's newest money command for prefix.
    A public money submission is blind (MR); the operator names the refusal locally."""
    jobs = os.path.join(ws, "jobs")
    dirs = sorted((d for d in os.listdir(jobs) if d.startswith(prefix)), key=lambda d: os.path.getmtime(os.path.join(jobs, d)))
    if not dirs: return "no command retained"
    # the decision now: the command re-pinned to the current authority root (its own root may
    # have moved since; a refused turn moved nothing of the job's or the Book's)
    command = json.load(open(os.path.join(jobs, dirs[-1], "command.json")))
    command["expectedAuthorityRoot"] = authority_root()
    src = path(f"explain-{time.time_ns()}.json")
    json.dump(command, open(src, "w"))
    out = path(f"explain-{time.time_ns()}.bin")
    r = run(HOST, CONFIG, "author", "job-money", src, out)
    if r.returncode: return "author failed: " + last_line(r)
    stop(); time.sleep(2)
    r = run(HOST, CONFIG, "job-money-explain", out)
    restart()
    return (r.stdout.strip() or last_line(r))[-300:]

tick(clock() + 1000)
open(path("open.json"), "w").write('{"type":"all","predicates":[]}\n')
run(MINI, "workspace", "--action", "create", "--dir", A, "--name", "lab", "--storage", "declared", "--predicate", path("open.json"))
def propose_submit(ws, pid, request):
    json.dump(request, open(path(f"{pid}.json"), "w"))
    r1 = run(MINI, "workspace", "--action", "propose", "--dir", ws, "--request", path(f"{pid}.json"), "--proposal-id", pid)
    r2 = run(MINI, "workspace", "--action", "submit", "--dir", ws, "--intent", os.path.join(ws, "proposals", pid, "intent.json"),
             "--attempt", os.path.join(ws, "attempts", pid))
    try: o = json.load(open(os.path.join(ws, "attempts", pid, "outcome.json")))
    except Exception: o = {}
    return r1, r2, o
propose_submit(A, "invite-p", {"type": "minidregg-workspace-proposal-v1", "action": "delegate", "name": "lab",
               "recipient": "21", "verbs": ["observe", "mutate"], "maxCost": "500000", "room": True})
run(MINI, "workspace", "--action", "publish-delegation", "--dir", A, "--proposal-id", "invite-p", "--attempt", os.path.join(A, "attempts", "invite-p"))
r = run(MINI, "workspace", "--action", "import", "--dir", P, "--name", "lab", "--from-ref", os.path.join(A, "proposals", "invite-p", "recipient-reference.json"))
row("setup: the Store, the room lab (A), P invited (under lab), accounts A 7, P 121, S 122",
    "P imported the invite", f"import rc={r.returncode}", r.returncode == 0)

# ---------------------------------------------------------------- two jobs, posted before any tariff
posted = {}
for name in ("j1", "j2"):
    rc, out, err = job(A, "post", "--name", name, "--room", "lab", "--program", "42", "--input", "5",
                       "--price", str(PRICE), "--deadline", "400", "--window", "100", "--account", "purse")
    posted[name] = (rc, out, err)
J1 = json.load(open(os.path.join(A, "refs", "j1.json")))["target"]
J2 = json.load(open(os.path.join(A, "refs", "j2.json")))["target"]
why = explain(A, "j1.fund")
row("A posts j1 and j2 (born in lab, ordered unfunded); the fund before a valid tariff is refused",
    "born and ordered; fund refused undisclosed; explained: tariffInvalid", f"j1={J1} j2={J2} {posted['j1'][2][:100]} | {why}",
    all(posted[n][0] != 0 for n in posted) and "tariffInvalid" in why)
tariff = {"control": "53", "book": [], "tariff": {"version": "1", "asset": "0", "mint": "85" * 32,
          "tokenProgram": "06" * 32, "decimals": "6", "creditPerAtomic": "1", "maxPerObservation": "2000000000",
          "minTickSlots": "1500", "nodeWeekRate": "999999840", "enrolIndex": None, "journalFloor": "1000000",
          "slashCallerPermille": "500"}}
json.dump(tariff, open(path("tariff.json"), "w"))
r = run(MINI, "pay", "book", "--dir", A, "--source", path("tariff.json"))
row("the operator installs the tariff (credit asset 0, slash split 500 permille)", "pay book confirmed",
    (r.stdout + r.stderr).strip()[-140:], r.returncode == 0)
led0, (j0,) = book(J1)
a0, p0 = credit(A), credit(P)
row("j1 before funding: state 0, escrow 0, provider 0, bond 0; the Book holds nothing for it",
    "state 0 escrow 0 provider 0 bond 0 held 0 bookHeld 0", money(j0),
    (j0.get("state"), j0.get("escrow"), j0.get("provider"), j0.get("bond"), j0.get("held"), j0.get("bookHeld")) == ("0", "0", "0", "0", "0", "0"))

# ---- refusal poles before funding: each named by the plan, and nothing moves
run(MINI, "workspace", "--action", "import", "--dir", S, "--name", "j1", "--kind", "object", "--target", str(J1),
    "--observe-capability", "3022", "--operation-capability", "3022")
# The public submission is blind (every refusal `undisclosed`); each row names the branch through
# the operator's explanation of the retained command, taken while nothing has moved.
def pole(label, built, ws, prefix, rc, err):
    why = explain(ws, prefix)
    row(label, f"refused undisclosed; explained: {built}", f"rc={rc} {err[:100]} | {why}", rc != 0 and built in why)
rc, out, err = job(S, "fund", "--name", "j1", "--account", "purse", "--amount", str(PRICE))
pole("S funds A's job with its own account", "notCaller", S, "j1.fund-", rc, err)
rc, out, err = job(A, "fund", "--name", "j1", "--account", "purse", "--amount", str(PRICE - 1000))
pole("A funds 9 000 against a 10 000 price (the joint commit does not balance)", "unbalanced", A, "j1.fund-", rc, err)
rc, out, err = job(P, "claim", "--job", str(J1), "--room", "lab", "--bond", str(BOND), "--account", "purse", "--name", "j1")
pole("P claims an unfunded job", "notFunded", P, "j1.claim-", rc, err)
rc, out, err = job(A, "settle", "--name", "j1")
pole("A settles an open job", "notTerminal", A, "j1.settle-", rc, err)
led_p, (j_p,) = book(J1)
row("the refused turns moved nothing", "ledger and job unchanged", f"well={led_p.get('well')} total={led_p.get('total')} {money(j_p)}",
    led_p == led0 and j_p == j0)

# ---- FUND
rc, out, err = job(A, "fund", "--name", "j1", "--account", "purse")
row("A funds j1 with the price (into the job's held account and its escrow field, one joint turn)", "confirmed",
    f"rc={rc} {out.get('type')} {err}", rc == 0)
fund_dir = sorted((d for d in os.listdir(os.path.join(A, "jobs")) if d.startswith("j1.fund-")),
                  key=lambda d: os.path.getmtime(os.path.join(A, "jobs", d)))
ingress = open(os.path.join(A, "jobs", fund_dir[-1], "ingress.bin"), "rb").read() if fund_dir else b""
code, data = op(163, ingress)
looked = outcome(data) if code == 163 else {"type": f"op{code}"}
row("receipt-only lookup of that fund (op 163)", "confirmed replayed", f"{looked.get('type')} {looked.get('confirmation')}",
    looked.get("type") == "confirmed" and looked.get("confirmation") == "replayed")
code, data = op(162, ingress)
again = outcome(data) if code == 162 else {"type": f"op{code}"}
row("the same signed fund submitted again", "confirmed replayed (no second deposit)", f"{again.get('type')} {again.get('confirmation')}",
    again.get("type") == "confirmed" and again.get("confirmation") == "replayed")
rc, out, err = job(A, "fund", "--name", "j1", "--account", "purse")
pole("A funds j1 a second time (a fresh command)", "alreadyFunded", A, "j1.fund-", rc, err)
led1, (j1,) = book(J1)
a1 = credit(A)
row("Book after the fund: A -10 000 into j1's held account; well and total unchanged",
    "A -10000, bookHeld 10000", f"A {a0} -> {a1} bookHeld={j1.get('bookHeld')} well {led0.get('well')} -> {led1.get('well')} total {led0.get('total')} -> {led1.get('total')}",
    a1 == a0 - PRICE and j1.get("bookHeld") == str(PRICE) and led1.get("well") == led0.get("well") and led1.get("total") == led0.get("total"))
row("j1 after the fund: escrow = price; the cell and the Book agree", "state 0 escrow 10000 held 10000 = bookHeld", money(j1),
    (j1.get("state"), j1.get("escrow"), j1.get("held")) == ("0", str(PRICE), str(PRICE)) and agrees(j1))

# ---- CLAIM
rc, out, err = job(P, "claim", "--job", str(J1), "--room", "lab", "--bond", str(BOND - 1000), "--account", "purse", "--name", "j1")
pole("P claims with a 9 000 bond against a 10 000 price", "bondBelowPrice", P, "j1.claim-", rc, err)
rc, out, err = job(S, "claim", "--job", str(J1), "--bond", str(BOND), "--account", "purse", "--name", "j1")
pole("S claims j1 (no grant covering the job: not a member)", "notMember", S, "j1.claim-", rc, err)
rc, out, err = job(P, "claim", "--job", str(J1), "--room", "lab", "--bond", str(BOND), "--account", "purse", "--name", "j1")
row("P claims j1, bonding 10 000 (moved into the held account in the same turn)", "confirmed", f"rc={rc} {err}", rc == 0)
led2, (j2v,) = book(J1)
p2 = credit(P)
row("Book after the claim: P -10 000 into the held account; well and total unchanged", "P -10000, bookHeld 20000",
    f"P {p0} -> {p2} bookHeld={j2v.get('bookHeld')} well {led1.get('well')} -> {led2.get('well')} total {led1.get('total')} -> {led2.get('total')}",
    p2 == p0 - BOND and j2v.get("bookHeld") == str(PRICE + BOND) and led2.get("well") == led1.get("well") and led2.get("total") == led1.get("total"))
row("j1 after the claim: state 1, provider 21 on account 121, bond 10 000, held 20 000 = bookHeld",
    "state 1 provider 21 providerAcct 121 bond 10000 held 20000", money(j2v) + f" providerAcct={j2v.get('providerAcct')}",
    (j2v.get("state"), j2v.get("provider"), j2v.get("providerAcct"), j2v.get("bond"), j2v.get("held")) == ("1", "21", "121", str(BOND), str(PRICE + BOND)) and agrees(j2v))

# ---- money is not an ordinary write's to move
r1, r2, o = propose_submit(A, "write-escrow", {"type": "minidregg-workspace-proposal-v1", "action": "invoke",
    "targets": [{"name": "j1", "payload": {"type": "scalar", "actions": [
        {"type": "write", "key": {"type": "object", "field": "8"}, "expected": str(PRICE), "value": "0"}]}}]})
why = o.get("explain") or o.get("reason") or last_line(r2)
row("A zeroes claimed j1's escrow by an ordinary write (no money slot)", "refused: the job law's clause 14 (escrow moves only on fund or close)",
    f"{o.get('type')} {why}", o.get("type") != "confirmed" and "law-denied" in str(why) and "field 8 delta == 0" in str(why))

# ---- upheld by timeout: an answer, no truth, the window passes
rc, out, err = job(P, "answer", "--name", "j1", "--output", "5", "--steps", "1")
final_at = int(out.get("finalAt", "0"))
tick(final_at + 1)
rc2, out2, err2 = job(A, "check", "--name", "j1")
row("P answers; nobody checks; past finalAt the job is upheld by timeout (the law's edge, not a hand-set state)",
    "upheld (timeout)", f"answer rc={rc} check rc={rc2} {out2.get('verdict')} {out2.get('why')} {err}{err2}",
    rc == 0 and rc2 == 0 and out2.get("verdict") == "upheld")
led3, (j3v,) = book(J1)

# ---- SETTLE: upheld
run(MINI, "workspace", "--action", "import", "--dir", S, "--name", "j1x", "--kind", "object", "--target", str(J1),
    "--observe-capability", "1022", "--operation-capability", "1022")
rc, out, err = job(S, "settle", "--name", "j1x")
row("S settles j1 naming a capability that is not on the job", "refused undisclosed (built to hit capabilityRejected: authorization, after preparation)",
    f"rc={rc} {err[:160]}", rc != 0 and "undisclosed" in err)
rc, out, err = job(A, "settle", "--name", "j1")
row("A settles j1 (upheld): the payouts leave the held account, a pure function of the job", "confirmed", f"rc={rc} {err}", rc == 0)
rc, out, err = job(P, "settle", "--name", "j1")
pole("P settles j1 again (a fresh command)", "alreadySettled", P, "j1.settle-", rc, err)
led4, (j4v,) = book(J1)
a4, p4 = credit(A), credit(P)
row("Book after the upheld settle: P paid exactly price + bond; A nothing back; well and total unchanged",
    "P +20000 (net +price), A unchanged", f"P {p2} -> {p4} A {a1} -> {a4} well {led3.get('well')} -> {led4.get('well')} total {led3.get('total')} -> {led4.get('total')}",
    p4 == p2 + PRICE + BOND and a4 == a1 and led4.get("well") == led3.get("well") and led4.get("total") == led3.get("total"))
row("j1 closed and empty, in the cell and in the Book", "state 6 escrow 0 bond 0 held 0 bookHeld 0", money(j4v),
    (j4v.get("state"), j4v.get("escrow"), j4v.get("bond"), j4v.get("held"), j4v.get("bookHeld")) == ("6", "0", "0", "0", "0"))

# ---- j2: fund, claim, the stall, the slash
rc1, _, e1 = job(A, "fund", "--name", "j2", "--account", "purse")
rc2, _, e2 = job(P, "claim", "--job", str(J2), "--room", "lab", "--bond", str(BOND), "--account", "purse", "--name", "j2")
row("A funds and P claims j2 (10 000 each)", "confirmed confirmed", f"{rc1} {rc2} {e1}{e2}", rc1 == 0 and rc2 == 0)
answer_by = int(json.loads(run(MINI, "job", "--action", "show", "--dir", A, "--name", "j2").stdout.strip().splitlines()[-1])["fields"]["answerBy"])
tick(max(clock(), answer_by) + 1)
rc, out, err = job(A, "check", "--name", "j2")
row("P never answers; past answerBy the check decides the stall", "slashed", f"rc={rc} {out.get('verdict')} {out.get('why')} {err}",
    rc == 0 and out.get("verdict") == "slashed")
led5, (k5,) = book(J2)
a5, p5 = credit(A), credit(P)
rc, out, err = job(A, "settle", "--name", "j2")
row("settle j2 (slashed)", "confirmed", f"rc={rc} {err}", rc == 0)
led6, (k6,) = book(J2)
a6, p6 = credit(A), credit(P)
row("Book after the slash: A gets escrow + half the bond, P nothing; the other half is burned into the well",
    f"A +{PRICE + SHARE}, P +0, well +{BOND - SHARE}, total unchanged",
    f"A {a5} -> {a6} P {p5} -> {p6} well {led5.get('well')} -> {led6.get('well')} total {led5.get('total')} -> {led6.get('total')}",
    a6 == a5 + PRICE + SHARE and p6 == p5 and int(led6["well"]) == int(led5["well"]) + (BOND - SHARE) and led6.get("total") == led5.get("total"))
row("the slash's legs: dheld + dcirculating + dwell = 0; j2 closed and empty", f"held -{PRICE + BOND}",
    f"held {k5.get('held')} -> {k6.get('held')} well +{int(led6['well']) - int(led5['well'])} " + money(k6),
    int(k6["held"]) - int(k5["held"]) + (a6 - a5) + (p6 - p5) + (int(led6["well"]) - int(led5["well"])) == 0
    and k6.get("state") == "6" and k6.get("bookHeld") == "0")

# ---- a forgery: job-shaped fields on an ordinary declared object pay nothing
run(MINI, "workspace", "--action", "create", "--dir", A, "--name", "forged", "--storage", "declared", "--predicate", path("open.json"),
    "--fields", "0-15")
fields = [(0, 3), (1, 42), (2, 5), (3, 7), (4, 7), (5, PRICE), (8, PRICE), (9, 21), (10, 121), (11, BOND)]
acts = [{"type": "create", "key": {"type": "object", "field": str(f)}, "value": str(v)} for f, v in fields]
r1, r2, o = propose_submit(A, "forge", {"type": "minidregg-workspace-proposal-v1", "action": "invoke",
    "targets": [{"name": "forged", "payload": {"type": "scalar", "actions": acts}}]})
FORGED = json.load(open(os.path.join(A, "refs", "forged.json")))["target"]
ledf, (f0,) = book(FORGED)
row("A writes upheld, funded job fields onto an ordinary declared object (its law admits anything)",
    "confirmed; the cell claims 20 000 held, the Book holds 0", f"{o.get('type')} " + money(f0),
    o.get("type") == "confirmed" and f0.get("held") == str(PRICE + BOND) and f0.get("bookHeld") == "0")
rc, out, err = job(A, "settle", "--name", "forged")
pole("settle the forged job: the Book holds nothing for it", "heldMismatch", A, "forged.settle-", rc, err)
# The pin on its own: an ordered, unfunded job-shaped cell under `all []` (not the job law). The
# money decision accepts A's fund (A is its caller, the Book has room); the receiver's pin refuses.
run(MINI, "workspace", "--action", "create", "--dir", A, "--name", "forged2", "--storage", "declared", "--predicate", path("open.json"),
    "--fields", "0-15")
order2 = [(0, 0), (1, 42), (2, 5), (3, 7), (4, 7), (5, PRICE), (6, 999999), (7, 999999), (8, 0), (9, 0), (10, 0), (11, 0)]
propose_submit(A, "forge2", {"type": "minidregg-workspace-proposal-v1", "action": "invoke",
    "targets": [{"name": "forged2", "payload": {"type": "scalar", "actions": [
        {"type": "create", "key": {"type": "object", "field": str(f)}, "value": str(v)} for f, v in order2]}}]})
rc, out, err = job(A, "fund", "--name", "forged2", "--account", "purse")
pole("fund an ordered job-shaped cell whose law is all [] (the receiver pins C1's job law)", "notJobLaw", A, "forged2.fund-", rc, err)
ledg, _ = book()
row("the forgery minted and moved nothing", "ledger unchanged", f"well={ledg.get('well')} total={ledg.get('total')}",
    {k: v for k, v in ledg.items()} == {k: v for k, v in ledf.items()})

# ---- the identities on this Store
RETIRED = BOND - SHARE
row("ledger identity: -well_h = -well_0 + credited - refilled - retired", f"-well_h = {-int(led0['well'])} - {RETIRED}",
    f"-well_h={-int(ledg['well'])}", -int(ledg["well"]) == -int(led0["well"]) - RETIRED)
row("totals: the Book's total in credit (well included) never moved", f"{led0.get('total')}", f"{ledg.get('total')}",
    ledg.get("total") == led0.get("total"))
stop(); time.sleep(3)
a = run(HOST, CONFIG, "audit")
open(path("audit.out"), "w").write(a.stdout + a.stderr)
row("cold reopen: the operator audit re-admits every record (every job-money turn included)", "audited",
    (a.stdout.strip() or a.stderr.strip())[-200:], a.returncode == 0 and "audited" in a.stdout)
finish(0)
PY
rc=$?
exit $rc
