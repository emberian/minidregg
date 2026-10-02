#!/usr/bin/env bash
# J-JOB (COMPUTE, the floor): one friend posts a Nock job in a room, another
# friend's node runs it, the answer comes back, and a WRONG answer costs the
# provider its bond -- adjudicated by one `ran` turn: the kernel re-executes the
# job's program on its own sample and compares the outputs exactly.
#
# Hook contract (journey.sh header): HOST, MINI, STORE, VERIFIER and
# JOURNEY_STEP_DIR exported; it bootstraps its OWN fresh Store and service under
# JOURNEY_STEP_DIR (newparticipant-acceptance.sh, the J0 fixture) and stops what
# it starts. Run it from a SHORT root (the socket path must fit SUN_LEN).
# Also needs: NOCK_RUN (the untrusted nockvm runner) and JOB_PROGRAMS, a
# directory holding collatz.jam and liar.jam (minimal jam bytes of
# deploy/shell/templates/job/programs/*.hoon, compiled by the pinned hoonc).
# Exit 0 = PASS. The last stdout line is rows.tsv; the verdict is the last stderr line.
#
# Who: A = the sponsor (subject 7, account 7) is the caller and the operator;
# P = subject 21 (account 121) the provider, invited into A's room `lab`;
# S = subject 22 (account 122) enrolled on the Store but not a member of `lab`.
# The program is collatz (input: job field 2; the one write it names is the
# truth, field 15: the Collatz step count of the input). Every turn is the
# client's own (`mini job ...`, `mini workspace ...`); no field is hand-set.
#
# Jobs: j1 P answers correctly -> A checks (the ran truth turn) -> upheld ->
# settle pays P price + bond; settle again replays the receipt. j2 P answers
# wrong -> check: mismatch -> slashed -> settle splits the bond (half to A, half
# burned, per the tariff). j3 P claims and never answers; the clock passes
# answerBy -> check: the stall -> slashed. j4 A tries to forge the truth (a bare
# write; a write carrying the run claim of ANOTHER program) and to move the
# escrow by an ordinary write: each refused by the clause the Host names; then
# the honest check upholds. j5 a non-member cannot post into the room or claim;
# A voids j5 and settle returns the escrow. Cold reopen + operator audit.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR NOCK_RUN JOB_PROGRAMS; do
  if [ -z "${!name:-}" ]; then echo "jjob: $name is required" >&2; exit 2; fi
done
DIR="$JOURNEY_STEP_DIR/jjob"
if [ -e "$DIR" ]; then echo "jjob: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
set +e
python3 - "$DIR" "$HERE" <<'PY'
import json, os, re, socket, struct, subprocess, sys, time
DIR, HERE = sys.argv[1], sys.argv[2]
HOST, MINI, STORE, VERIFIER = (os.environ[k] for k in ("HOST", "MINI", "STORE", "VERIFIER"))
NOCK_RUN, PROGS = os.environ["NOCK_RUN"], os.environ["JOB_PROGRAMS"]
W = os.path.join(DIR, "w")
ROWS = []
def path(*p): return os.path.join(DIR, *p)
def load(): return f"{os.getloadavg()[0]:.1f}"
def row(job, name, expected, got, ok, secs=None):
    got = " ".join(str(got).split())[:400]
    ROWS.append((job, name, expected, got, "PASS" if ok else "FAIL", "" if secs is None else f"{secs:.2f}", load()))
    print(f"{'PASS' if ok else 'FAIL'}\t{job}\t{name}\t{got[:200]}", file=sys.stderr)
def fail(message):
    print(f"J-JOB FAIL: {message}", file=sys.stderr); finish(1)
def run(*args, env=None, stdin=None):
    return subprocess.run(list(args), capture_output=True, text=True, env=env, input=stdin)
def last_json(text):
    for line in reversed(text.strip().splitlines()):
        try: return json.loads(line)
        except Exception: continue
    return None
def last_line(r): return ((r.stderr or "").strip().splitlines() or [""])[-1]

# ---------------------------------------------------------------- the Store: A, P, S
keys = {}
for who in ("p", "s"):
    r = run(MINI, "keygen", "--secret", path(f"{who}.key"), "--public", path(f"{who}.pub"))
    if r.returncode: fail(f"keygen {who}: {last_line(r)}")
    keys[who] = open(path(f"{who}.pub"), "rb").read().hex()
def enrollment(subject, who):
    return {"key": {"keyId": str(7000 + subject), "keyEpoch": "2", "algorithm": "1", "subject": str(subject),
                    "publicKey": keys[who], "activeFrom": "0", "activeUntil": "1000000"},
            "accountId": str(100 + subject), "spendCapabilityId": str(1000 + subject),
            "controlCapabilityId": str(2000 + subject), "factoryObserveCapabilityId": str(3000 + subject),
            "initialBalance": "1000000", "accountPredicate": {"type": "all", "predicates": []}}
json.dump([enrollment(21, "p"), enrollment(22, "s")], open(path("extra-enrollments.json"), "w"))
env = dict(os.environ, NEWPARTICIPANT_OWNER_BUDGET="4000000", EXTRA_GENESIS_ENROLLMENTS=path("extra-enrollments.json"))
t = time.time()
r = run("sh", os.path.join(HERE, "newparticipant-acceptance.sh"), HOST, MINI, STORE, VERIFIER, W, env=env)
open(path("fixture.err"), "w").write(r.stdout + r.stderr)
if r.returncode: fail(f"fixture: {last_line(r)}")
CONFIG = os.path.join(W, "deployment", "pinned-config.json")
SOCK = os.path.join(W, "public", "mini.sock")
A = os.path.join(W, "sponsor"); P = path("p-ws"); S = path("s-ws")
def stop():
    pid = os.path.join(W, "public", "server.pid")
    if os.path.exists(pid):
        try: os.kill(int(open(pid).read().strip()), 15)
        except Exception: pass
def finish(code):
    stop()
    with open(path("rows.tsv"), "w") as f:
        f.write("verdict\tjob\trow\texpected\tgot\tseconds\tload\n")
        for job, name, exp, got, v, secs, ld in ROWS: f.write(f"{v}\t{job}\t{name}\t{exp}\t{got}\t{secs}\t{ld}\n")
    passed = sum(1 for r in ROWS if r[4] == "PASS")
    verdict = f"J-JOB {'PASS' if passed == len(ROWS) and code == 0 else 'FAIL'} {passed}/{len(ROWS)}"
    print(verdict); print(path("rows.tsv")); print(verdict, file=sys.stderr)
    sys.exit(0 if passed == len(ROWS) and code == 0 else 1)
row("setup", "fresh Store: A (7) sponsors; P (21) and S (22) enrolled at genesis with accounts 121, 122",
    "bootstrapped", f"{time.time() - t:.0f}s", True, time.time() - t)
for who, ws, subject, account in (("p", P, 21, 121), ("s", S, 22, 122)):
    r = run(MINI, "workspace", "--action", "init", "--host", HOST, "--config", CONFIG, "--socket", SOCK,
            "--key", path(f"{who}.key"), "--subject", str(subject), "--dir", ws)
    if r.returncode: fail(f"init {who}: {last_line(r)}")
for ws, account, cap in ((A, 7, 41), (P, 121, 1021), (S, 122, 1022)):
    r = run(MINI, "workspace", "--action", "import", "--dir", ws, "--name", "purse", "--kind", "account",
            "--target", str(account), "--observe-capability", str(cap), "--operation-capability", str(cap))
    if r.returncode: fail(f"import purse {ws}: {last_line(r)}")

cfg = open(CONFIG, "rb").read()
def frame(b): return struct.pack("<I", len(b)) + b
def op(code, payload):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.connect(SOCK)
    s.sendall(frame(bytes([1]) + struct.pack("<I", len(cfg)) + cfg + bytes([code]) + payload))
    def exact(n):
        out = b""
        while len(out) < n:
            chunk = s.recv(n - len(out))
            if not chunk: raise RuntimeError("short reply")
            out += chunk
        return out
    n = struct.unpack("<I", exact(4))[0]; body = exact(n); s.close()
    if body[0] != code: raise RuntimeError(f"op {code} answered {body[0]}: {body[1:300]!r}")
    return json.loads(body[1:].decode())
def pair(a, b): return struct.pack("<I", len(a)) + a + b

# The operator's tariff: credit asset 0, slash split 500 permille (half the bond to the caller).
tariff = {"control": "53", "book": [], "tariff": {"version": "1", "asset": "0", "mint": "85" * 32,
          "tokenProgram": "06" * 32, "decimals": "6", "creditPerAtomic": "1",
          "maxPerObservation": "2000000000", "minTickSlots": "1500", "nodeHourRate": "5952380",
          "enrolIndex": None, "journalFloor": "1000000", "slashCallerPermille": "500"}}
json.dump(tariff, open(path("tariff.json"), "w"))
r = run(MINI, "pay", "book", "--dir", A, "--source", path("tariff.json"))
row("setup", "A (the operator) installs the tariff: asset 0, slash split 500 permille", "pay book confirmed",
    (r.stdout + r.stderr).strip()[-160:], r.returncode == 0)
def clock_view():
    r = run(MINI, "clock", "--action", "view", "--workspace", A)
    return int(json.loads(r.stdout)["now"])
def tick(now):
    r = run(MINI, "clock", "--action", "tick", "--workspace", os.path.join(W, "clock"), "--now", str(now))
    return r.returncode == 0
T0 = clock_view() + 1000
row("setup", f"tick the clock to {T0}", f"now {T0}", f"tick={tick(T0)} now={clock_view()}", clock_view() == T0)

# The room: A creates `lab` and invites P (a room invite: P's grant is `under lab`).
open(path("open.json"), "w").write('{"type":"all","predicates":[]}\n')
r = run(MINI, "workspace", "--action", "create", "--dir", A, "--name", "lab", "--storage", "declared",
        "--predicate", path("open.json"))
lab_ok = r.returncode == 0
def propose_submit(ws, pid, request):
    json.dump(request, open(path(f"{pid}.request.json"), "w"))
    r1 = run(MINI, "workspace", "--action", "propose", "--dir", ws, "--request", path(f"{pid}.request.json"),
             "--proposal-id", pid)
    if r1.returncode: return r1, None
    r2 = run(MINI, "workspace", "--action", "submit", "--dir", ws, "--intent",
             os.path.join(ws, "proposals", pid, "intent.json"), "--attempt", os.path.join(ws, "attempts", pid))
    try: outcome = json.load(open(os.path.join(ws, "attempts", pid, "outcome.json")))
    except Exception: outcome = None
    return r2, outcome
invite = {"type": "minidregg-workspace-proposal-v1", "action": "delegate", "name": "lab", "recipient": "21",
          "verbs": ["observe", "mutate"], "maxCost": "500000", "room": True}
r, outcome = propose_submit(A, "invite-p", invite)
r3 = run(MINI, "workspace", "--action", "publish-delegation", "--dir", A, "--proposal-id", "invite-p",
         "--attempt", os.path.join(A, "attempts", "invite-p"))
r4 = run(MINI, "workspace", "--action", "import", "--dir", P, "--name", "lab", "--from-ref",
         os.path.join(A, "proposals", "invite-p", "recipient-reference.json"))
row("setup", "A creates the room lab and invites P (a room invite: under lab); P imports it",
    "room created; invite confirmed; P imported", f"create rc={r.returncode} invite={outcome and outcome.get('type')} import rc={r4.returncode} {last_line(r4)[:120]}",
    lab_ok and outcome is not None and outcome.get("type") == "confirmed" and r4.returncode == 0)

# The programs: collatz (the job program) and liar (names the truth field, always answers 9).
def abi(fuel): return {"evaluator": "nock", "version": "5", "context": "live", "arm": "2", "fuel": str(fuel),
    "sample": [{"target": "0", "slot": "resource/field/2/before", "key": "input", "type": "nat"}],
    "outputs": [{"key": "truth", "target": "0", "field": "15", "type": "nat"}], "libraries": []}
PID = {}
for name in ("collatz", "liar"):
    jam = open(os.path.join(PROGS, f"{name}.jam"), "rb").read()
    v = op(131, pair(jam, json.dumps(abi(5000000)).encode()))
    json.dump(v, open(path(f"{name}.check.json"), "w"))
    r = run(MINI, "workspace", "--action", "create", "--dir", A, "--name", name, "--storage", "nock",
            "--predicate", path("open.json"), "--program", path(f"{name}.check.json"))
    PID[name] = v.get("programId")
    row("setup", f"program {name} born (ABI: reads job field 2 as input, writes field 15 truth)",
        "admissible; born", f"verdict={v.get('verdict')} rc={r.returncode} programId={str(PID[name])[:24]}...",
        v.get("verdict") == "admissible" and r.returncode == 0)

# ---------------------------------------------------------------- reading the Book
def ledger():
    out = path(f"ledger-{time.time_ns()}.json")
    r = run(HOST, CONFIG, "pay-ledger", out)
    return json.load(open(out)) if r.returncode == 0 else {"error": last_line(r)}
def jobview(job):
    out = path(f"job-{job}-{time.time_ns()}.json")
    r = run(HOST, CONFIG, "pay-job", str(job), out)
    return json.load(open(out)) if r.returncode == 0 else {"error": last_line(r)}
def bal(led, account):
    for k in ("accounts", "payers", "balances"):
        for e in led.get(k, []) or []:
            if isinstance(e, dict) and e.get("account") == str(account): return int(e.get("balance", "0"))
    return None
def account_balance(ws):
    r = run(MINI, "pay", "status", "--dir", ws, "--account", "purse")
    m = re.search(r"credit (-?\d+)", r.stdout)
    return int(m.group(1)) if m else None
def well(led): return int(led["well"]) if "well" in led else None
def total(led): return int(led["total"]) if "total" in led else None

# ---------------------------------------------------------------- the client
def job(ws, action, *flags):
    t = time.time()
    r = run(MINI, "job", "--action", action, "--dir", ws, *flags)
    secs = time.time() - t
    out = last_json(r.stdout)
    open(path(f"cli-{len(ROWS):03d}-{action}.log"), "w").write(r.stdout + "\n---\n" + r.stderr)
    err = "" if r.returncode == 0 else (last_line(r) or r.stdout.strip()[-300:])
    return r.returncode, out or {}, err, secs
TRANSCRIPT = []
def say(who, line, result):
    TRANSCRIPT.append(f"{who}$ {line}\n  -> {json.dumps(result) if isinstance(result, dict) else result}")
def post(name, inp, price=1000, deadline=600, window=100, ws=A, room="lab"):
    flags = ["--name", name, "--room", room, "--program", PID["collatz"], "--input", str(inp), "--price", str(price),
             "--deadline", str(deadline), "--window", str(window), "--account", "purse"]
    rc, out, err, secs = job(ws, "post", *flags)
    say("A" if ws == A else "S", f"job post {room} collatz --input {inp} --price {price} --deadline {deadline} --name {name}", out or err)
    return rc, out, err, secs

PRICE, BOND = 1000, 1000
jobs = {}
def stage_ledger(label):
    stop(); time.sleep(2)
    led = ledger()
    restart()
    return led
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

led0 = stage_ledger("start")
json.dump(led0, open(path("ledger-0.json"), "w"))
a0, p0 = account_balance(A), account_balance(P)
row("setup", "the Book before any job: A's and P's credit, the well, the total", "readable",
    f"A={a0} P={p0} well={well(led0)} total={total(led0)}", a0 is not None and p0 is not None and total(led0) is not None)

# ================================================================ j1: a correct answer
rc, out, err, secs = post("j1", 6)
J1 = out.get("job")
row("j1", "A posts collatz(6) in lab at price 1000 (birth, order, fund: escrow moves into the job's held account)",
    "posted; escrow 1000", f"rc={rc} job={J1} escrow={out.get('escrow')} {err}", rc == 0 and out.get("escrow") == "1000", secs)
a1 = account_balance(A)
rc, out, err, secs = job(P, "claim", "--job", str(J1), "--room", "lab", "--bond", str(BOND), "--account", "purse", "--name", "j1")
say("P", f"job claim {J1} --room lab --bond {BOND}", out or err)
row("j1", "P claims j1, bonding 1000 (P's under-lab grant admits the job; the bond moves into the held account)",
    "claimed", f"rc={rc} {out.get('type')} {err}", rc == 0 and out.get("type") == "job-claimed", secs)
p1 = account_balance(P)
rc, out, err, secs = job(P, "answer", "--name", "j1")
say("P", "job answer j1   (P's node runs collatz on the job's sample: op 134)", out or err)
row("j1", "P's node runs collatz on the job's sample and posts the output", "answered output 8",
    f"rc={rc} output={out.get('output')} steps={out.get('steps')} {err}", rc == 0 and out.get("output") == "8", secs)
rc, out, err, secs = job(A, "check", "--name", "j1")
say("A", "job check j1   (the ran truth turn: the kernel re-executes and compares)", out or err)
row("j1", "A checks: the truth turn carries the run claim; the kernel re-executes collatz; truth 8 = output 8",
    "upheld", f"rc={rc} truth={out.get('truth')} output={out.get('output')} verdict={out.get('verdict')} kernelSteps={out.get('kernelSteps')} {err}",
    rc == 0 and out.get("verdict") == "upheld" and out.get("truth") == "8", secs)
rc, out, err, secs = job(A, "settle", "--name", "j1")
say("A", "job settle j1", out or err)
p2 = account_balance(P)
row("j1", "A settles: the provider is paid price + bond out of the held account", f"P +{PRICE + BOND}",
    f"rc={rc} P {p1} -> {p2} state={out.get('fields', {}).get('stateName')} escrow={out.get('fields', {}).get('escrow')} bond={out.get('fields', {}).get('bond')} {err}",
    rc == 0 and p1 is not None and p2 == p1 + PRICE + BOND, secs)
receipt1 = out.get("outcome")
rc, out, err, secs = job(A, "settle", "--name", "j1")
row("j1", "A settles j1 again: the retained ingress resubmitted answers the original receipt", "confirmed replayed",
    f"rc={rc} {json.dumps(out.get('outcome'))[:200]} {err}",
    rc == 0 and (out.get("outcome") or {}).get("confirmation") == "replayed", secs)
rc, out, err, secs = job(A, "show", "--name", "j1")
f = out.get("fields", {})
row("j1", "j1 closed: truth 8, output 8, escrow 0, bond 0", "state 6",
    f"state={f.get('stateName')} truth={f.get('truth')} output={f.get('output')} escrow={f.get('escrow')} bond={f.get('bond')}",
    f.get("state") == "6" and f.get("truth") == "8" and f.get("escrow") == "0" and f.get("bond") == "0", secs)

t = time.time()
r, outcome = propose_submit(A, "undeclared-j1", {"type": "minidregg-workspace-proposal-v1", "action": "invoke",
    "targets": [{"name": "j1", "payload": {"type": "scalar", "actions": [
        {"type": "create", "key": {"type": "object", "field": "16"}, "value": "1"}]}}]})
why = (outcome or {}).get("explain") or (outcome or {}).get("reason") or (outcome or {}).get("detail") or last_line(r)
row("j1", "A creates field 16 on the CLOSED job (a field the cell never declared; K-FIELD-CLOSURE)",
    "refused by name: undeclaredField 16", f"rc={r.returncode} {why}", r.returncode != 0 and "undeclaredField 16" in str(why), time.time() - t)

# ================================================================ j2: a wrong answer
rc, out, err, secs = post("j2", 7)
J2 = out.get("job")
row("j2", "A posts collatz(7) at price 1000", "posted", f"rc={rc} job={J2} {err}", rc == 0, secs)
rc, out, err, secs = job(P, "claim", "--job", str(J2), "--room", "lab", "--bond", str(BOND), "--account", "purse", "--name", "j2")
row("j2", "P claims j2, bonding 1000", "claimed", f"rc={rc} {err}", rc == 0, secs)
a2, pb2 = account_balance(A), account_balance(P)
led2 = stage_ledger("j2-claimed")
rc, out, err, secs = job(P, "answer", "--name", "j2", "--output", "17", "--steps", "1")
say("P", "job answer j2 17   (wrong: collatz(7) is 16)", out or err)
row("j2", "P posts a WRONG output (17; collatz(7) = 16)", "answered", f"rc={rc} output={out.get('output')} {err}", rc == 0, secs)
rc, out, err, secs = job(A, "check", "--name", "j2")
say("A", "job check j2", out or err)
row("j2", "A checks: the kernel's truth 16 differs from 17", "slashed",
    f"rc={rc} truth={out.get('truth')} output={out.get('output')} verdict={out.get('verdict')} {err}",
    rc == 0 and out.get("verdict") == "slashed" and out.get("truth") == "16", secs)
rc, out, err, secs = job(A, "settle", "--name", "j2")
say("A", "job settle j2", out or err)
a3, pb3 = account_balance(A), account_balance(P)
row("j2", "settle the slash: A gets escrow + half the bond, P gets nothing back", f"A +{PRICE + BOND // 2}, P +0",
    f"rc={rc} A {a2} -> {a3} P {pb2} -> {pb3} {err}",
    rc == 0 and a3 == a2 + PRICE + BOND // 2 and pb3 == pb2, secs)
led3 = stage_ledger("j2-settled")
row("j2", "conservation: the Book's total is unchanged; the well grew by exactly the burned half",
    f"total equal; well +{BOND - BOND // 2}", f"total {total(led2)} -> {total(led3)} well {well(led2)} -> {well(led3)}",
    total(led2) == total(led3) and well(led3) is not None and well(led3) == well(led2) + (BOND - BOND // 2))

# ================================================================ j3: the stall
now = clock_view()
rc, out, err, secs = post("j3", 6, deadline=40)
J3 = out.get("job")
row("j3", "A posts collatz(6) with a 40-second deadline", "posted", f"rc={rc} job={J3} answerBy={out.get('answerBy')} {err}", rc == 0, secs)
answer_by = int(out.get("answerBy", "0"))
rc, out, err, secs = job(P, "claim", "--job", str(J3), "--room", "lab", "--bond", str(BOND), "--account", "purse", "--name", "j3")
row("j3", "P claims j3 and never answers", "claimed", f"rc={rc} {err}", rc == 0, secs)
rc, out, err, secs = job(A, "check", "--name", "j3")
row("j3", "before answerBy, A's check has nothing to decide", "refused (claimed, not past answerBy)",
    f"rc={rc} {err[:200]}", rc != 0, secs)
row("j3", f"the clock passes answerBy ({answer_by})", f"now > {answer_by}", f"tick={tick(answer_by + 1)} now={clock_view()}", clock_view() > answer_by)
pb4, a4 = account_balance(P), account_balance(A)
rc, out, err, secs = job(A, "check", "--name", "j3")
say("A", "job check j3   (past answerBy, no answer: the stall)", out or err)
row("j3", "A checks: no answer by answerBy is the stall", "slashed", f"rc={rc} verdict={out.get('verdict')} why={out.get('why')} {err}",
    rc == 0 and out.get("verdict") == "slashed", secs)
rc, out, err, secs = job(A, "settle", "--name", "j3")
a5, pb5 = account_balance(A), account_balance(P)
row("j3", "settle the stall: A gets escrow + half the bond", f"A +{PRICE + BOND // 2}, P +0",
    f"rc={rc} A {a4} -> {a5} P {pb4} -> {pb5} {err}", rc == 0 and a5 == a4 + PRICE + BOND // 2 and pb5 == pb4, secs)

# ================================================================ j4: forging the truth
rc, out, err, secs = post("j4", 6)
J4 = out.get("job")
row("j4", "A posts collatz(6)", "posted", f"rc={rc} job={J4} {err}", rc == 0, secs)
rc, out, err, secs = job(P, "claim", "--job", str(J4), "--room", "lab", "--bond", str(BOND), "--account", "purse", "--name", "j4")
rc2, out2, err2, secs2 = job(P, "answer", "--name", "j4")
row("j4", "P claims j4 and answers correctly (8)", "answered 8", f"claim rc={rc} answer rc={rc2} output={out2.get('output')} {err}{err2}",
    rc == 0 and rc2 == 0 and out2.get("output") == "8", secs + secs2)
def truth_write(pid, value, claim=None):
    req = {"type": "minidregg-workspace-proposal-v1", "action": "invoke",
           "targets": [{"name": "j4", "payload": {"type": "scalar", "actions": [
               {"type": "create", "key": {"type": "object", "field": "15"}, "value": str(value)}]}}]}
    if claim: req["run"] = claim
    t = time.time()
    r, outcome = propose_submit(A, pid, req)
    why = (outcome or {}).get("explain") or (outcome or {}).get("reason") or last_line(r)
    return r.returncode, outcome, why, time.time() - t
law = [l.rstrip(";") for l in open(os.path.join(HERE, "..", "..", "deploy", "shell", "templates", "job", "law.job.shell")).read().splitlines() if not l.startswith("--")]
rc, outcome, why, secs = truth_write("forge-bare", 9)
say("A", "invoke j4 create 15 9   (a bare write of the truth field)", why)
row("j4", "A writes truth 9 with no run claim (caller_cannot_forge_truth's pole)", "refused: clause 22 (ran PROGRAM)",
    f"rc={rc} {why}", rc != 0 and "law-denied" in str(why) and f"ran {PID['collatz']}" in str(why), secs)
d = op(134, json.dumps({"programId": PID["liar"], "caller": "7", "room": "0", "targets": [str(J4)],
                         "values": [["0", "resource/field/2/before", "6"]]}).encode())
liar_claim = {"programId": PID["liar"], "sample": d.get("sample"), "output": d.get("output"), "steps": d.get("steps")}
rc, outcome, why, secs = truth_write("forge-liar", 9, liar_claim)
say("A", "invoke j4 create 15 9 --run liar   (a re-executed run, of the WRONG program)", why)
row("j4", "A writes truth 9 carrying liar's run claim (re-executed and matching -- but not the job's program)",
    "refused: clause 22 (ran PROGRAM is the job's program)", f"rc={rc} dry={d.get('verdict')} {why}",
    rc != 0 and "law-denied" in str(why) and f"ran {PID['collatz']}" in str(why), secs)
req = {"type": "minidregg-workspace-proposal-v1", "action": "invoke",
       "targets": [{"name": "j4", "payload": {"type": "scalar", "actions": [
           {"type": "write", "key": {"type": "object", "field": "8"}, "expected": "1000", "value": "0"}]}}]}
t = time.time(); r, outcome = propose_submit(A, "forge-escrow", req)
why = (outcome or {}).get("explain") or (outcome or {}).get("reason") or last_line(r)
row("j4", "A zeroes the escrow of a claimed job by an ordinary write (money without the receiver)",
    "refused: clause 14 (escrow moves only on fund or close)", f"rc={r.returncode} {why}",
    r.returncode != 0 and "law-denied" in str(why) and "field 8 delta == 0" in str(why), time.time() - t)
rc, out, err, secs = job(A, "check", "--name", "j4")
row("j4", "the honest check: truth 8 = output 8", "upheld", f"rc={rc} verdict={out.get('verdict')} {err}",
    rc == 0 and out.get("verdict") == "upheld", secs)
rc, out, err, secs = job(A, "settle", "--name", "j4")
row("j4", "settle j4", "closed", f"rc={rc} {err}", rc == 0, secs)

# ================================================================ j5: a non-member
rc, out, err, secs = post("j5", 6)
J5 = out.get("job")
row("j5", "A posts collatz(6) (open, funded)", "posted", f"rc={rc} job={J5} {err}", rc == 0, secs)
# S is enrolled on the Store and holds an account, but holds no grant under lab.
ctx = json.load(open(os.path.join(W, "sponsor-birth-context.json")))
ctx.update({"sourceCapabilities": ["1022"], "feePayer": "122",
            "grants": [{"kind": "object", "target": "10", "capability": "3022"},
                       {"kind": "account", "target": "122", "capability": "1022"}]})
json.dump(ctx, open(path("s-birth-context.json"), "w"))
run("rm", "-rf", S)
r = run(MINI, "workspace", "--action", "init", "--host", HOST, "--config", CONFIG, "--socket", SOCK,
        "--key", path("s.key"), "--subject", "22", "--birth-context", path("s-birth-context.json"),
        "--namespace-root", path("s-namespace"), "--dir", S)
run(MINI, "workspace", "--action", "import", "--dir", S, "--name", "purse", "--kind", "account",
    "--target", "122", "--observe-capability", "1022", "--operation-capability", "1022")
lab_target = json.load(open(os.path.join(A, "refs", "lab.json")))["target"]
# S names lab by its id with the only object grant it holds (its factory observe grant).
run(MINI, "workspace", "--action", "import", "--dir", S, "--name", "lab", "--kind", "object",
    "--target", str(lab_target), "--observe-capability", "3022", "--operation-capability", "3022")
rc, out, err, secs = post("s1", 6, ws=S)
row("j5", "S (not a member of lab) posts a job into lab", "refused (a birth into a room needs a grant on the room)",
    f"rc={rc} {out.get('type')} {err[:200]}", rc != 0, secs)
rc, out, err, secs = job(S, "claim", "--job", str(J5), "--room", "lab", "--bond", str(BOND), "--account", "purse", "--name", "j5")
say("S", f"job claim {J5} --room lab   (S holds no grant under lab)", out or err)
why = explain(S, "j5.claim-")
say("operator", "minidregg-host CONFIG job-money-explain <S's claim command>", why)
row("j5", "S (not a member) claims j5 with its own account; the operator's explanation names the reason",
    "refused (blind submission); explained: notMember", f"rc={rc} {err[:120]} | {why}", rc != 0 and "notMember" in why, secs)
void = {"type": "minidregg-workspace-proposal-v1", "action": "invoke",
        "targets": [{"name": "j5", "payload": {"type": "scalar", "actions": [
            {"type": "write", "key": {"type": "object", "field": "0"}, "expected": "0", "value": "5"}]}}]}
a6 = account_balance(A)
t = time.time(); r, outcome = propose_submit(A, "void-j5", void)
row("j5", "A voids j5 (the caller, any time in state 0)", "confirmed", f"{(outcome or {}).get('type')} {last_line(r)[:120]}",
    outcome is not None and outcome.get("type") == "confirmed", time.time() - t)
rc, out, err, secs = job(A, "settle", "--name", "j5")
a7 = account_balance(A)
row("j5", "settle the void: the escrow returns to A", f"A +{PRICE}", f"rc={rc} A {a6} -> {a7} {err}", rc == 0 and a7 == a6 + PRICE, secs)

# ================================================================ the Book over the run, and the audit
stop(); time.sleep(3)
ledN = ledger()
json.dump(ledN, open(path("ledger-N.json"), "w"))
views = {n: jobview(j) for n, j in (("j1", J1), ("j2", J2), ("j3", J3), ("j4", J4), ("j5", J5))}
json.dump(views, open(path("jobs-N.json"), "w"))
held = sum(int(v.get("bookHeld", "0")) for v in views.values())
row("book", "every job closed: no credit left in any held account; the cells say the same",
    "bookHeld 0 for j1..j5", " ".join(f"{n}:{v.get('bookHeld')}/{v.get('held')}" for n, v in views.items()),
    held == 0 and all(v.get("held") == "0" for v in views.values()))
burned = 2 * (BOND - BOND // 2)
row("book", "ledger identity over the run: total unchanged; the well grew by exactly the two burned halves",
    f"total {total(led0)}; well +{burned}", f"total {total(led0)} -> {total(ledN)} well {well(led0)} -> {well(ledN)}",
    total(ledN) == total(led0) and well(ledN) == well(led0) + burned)
a = run(HOST, CONFIG, "audit")
open(path("audit.out"), "w").write(a.stdout + a.stderr)
row("audit", "cold reopen: the operator audit re-admits every record (money turns and ran truth turns included)",
    "audited", (a.stdout.strip() or a.stderr.strip())[-200:], a.returncode == 0 and "audited" in a.stdout)
open(path("transcript.txt"), "w").write("\n".join(TRANSCRIPT) + "\n")
finish(0)
PY
rc=$?
exit $rc
