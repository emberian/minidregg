#!/usr/bin/env bash
# J-NOCK-3P (COMPUTE.md C2, K-RUN-PIN): a pinned program's claim is good at every
# height where the fields it reads are unchanged.
#
# Journey hook contract (journey.sh header): HOST, MINI, STORE, VERIFIER and
# JOURNEY_STEP_DIR exported; it bootstraps its OWN fresh Store and service under
# JOURNEY_STEP_DIR (newparticipant-acceptance.sh, the J0 fixture), never touches
# the journey's service, and stops what it starts. Exit 0 = PASS. The last stdout
# line is the deciding artifact (rows.tsv); the verdict is the last stderr line.
#
# Also needs: NOCK_TEMPLATES (forge.jam, minimal bytes) and NOCK_RUN (the untrusted
# nockvm runner, ABI v3 `--sample-json`; the Host speaks program ABI v4).
#
# Rows: forge is born as a library cell; the pinned forge is the N16 shape, the
# one-byte program `[0 1]` over that library, ABI v4 `context: pinned`, reading
# fields 2-4 and writing fields 5-7. A door ABI that says `pinned` is refused
# `abiShape` (a door's sample is its own state and event number, which every poke
# advances, so no poke claim can be reused); a v3 ABI is refused `abiVersion`.
# The runner's `--emit-sample` equals the kernel's sample byte for byte under both
# contexts, and with a `noun` input. One claim, computed at height h0, is admitted
# at h1 > h0 and again at h2 > h1 (other admissions in between). A `noun` output
# is written as the jam atom of the product's noun and read back by a `noun`
# sample slot. Once field 3 (inv/wood) is written, the same claim is refused
# `sampleStale` naming `inv/wood`. Control: a LIVE forge claim goes stale at the
# next height with no field changed. The declared maximum (ABI v4 carries NC-2's per-slot `max`
# beside `context`): at the maximum admitted, one above refused `fieldOverMax` by name.
# Cold reopen + audit re-admits every record.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR NOCK_TEMPLATES NOCK_RUN; do
  if [ -z "${!name:-}" ]; then echo "jnock3p: $name is required" >&2; exit 2; fi
done
DIR="$JOURNEY_STEP_DIR/jnock3p"
if [ -e "$DIR" ]; then echo "jnock3p: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
W="$DIR/world"
# The forge library's birth costs its ~566 KB intent against the owner budget (J-NOCK-2b).
NEWPARTICIPANT_OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-4000000} \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W" \
  >"$DIR/bootstrap.out" 2>"$DIR/bootstrap.err" || { echo "jnock3p: bootstrap failed: $(tail -1 "$DIR/bootstrap.err")" >&2; exit 1; }
stop() { if [ -s "$W/public/server.pid" ]; then kill "$(cat "$W/public/server.pid")" 2>/dev/null || true; fi; }
trap stop EXIT
set +e
python3 - "$DIR" "$W" <<'PY'
import json, os, re, socket, struct, subprocess, sys, time
DIR, W = sys.argv[1], sys.argv[2]
MINI, NOCK_RUN, TPL = os.environ["MINI"], os.environ["NOCK_RUN"], os.environ["NOCK_TEMPLATES"]
CONFIG = os.path.join(W, "deployment", "pinned-config.json")
SOCK = os.path.join(W, "public", "mini.sock")
WS = os.path.join(W, "sponsor")
SUBJECT = 7
ROWS = []
def path(n): return os.path.join(DIR, n)
def row(name, ok, detail):
    ROWS.append((name, "PASS" if ok else "FAIL", detail))
    print(f"{'PASS' if ok else 'FAIL'}\t{name}\t{detail}", file=sys.stderr)

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
    if body[0] != code: raise RuntimeError(f"op {code} answered {body[0]}: {body[1:200]!r}")
    return json.loads(body[1:].decode())
def pair(a, b): return struct.pack("<I", len(a)) + a + b
def mini(*args):
    return subprocess.run([MINI, "workspace", *args], capture_output=True, text=True)
def last_line(r, attempt_dir=None):
    last = (r.stderr.strip().splitlines() or [""])[-1]
    if attempt_dir:
        retained = os.path.join(attempt_dir, "reply.frame")
        if "retained encoded Host outcome" in last and os.path.exists(retained):
            last = open(retained, "rb").read().decode("latin1").replace("\xff", " | ")
    m = re.search(r"([0-9a-f]{40,})", last)
    if m:
        try: last = bytes.fromhex(m.group(1)).decode("latin1").replace("\xff", " | ")
        except ValueError: pass
    return last

# --- Urbit jam (Theory.Noun.jamAux): atoms are ints, cells 2-tuples ---------
def mat(n):
    if n == 0: return [1]
    b = n.bit_length(); c = b.bit_length()
    return [0] * c + [1] + [(b >> i) & 1 for i in range(c - 1)] + [(n >> i) & 1 for i in range(b)]
def jam(noun):
    out, table = [], {}
    def go(n):
        key = ("a", n) if isinstance(n, int) else ("c", n)
        if key in table:
            p = table[key]
            if isinstance(n, int) and n.bit_length() <= p.bit_length(): out.extend([0] + mat(n))
            else: out.extend([1, 1] + mat(p))
            return
        table[key] = len(out)
        if isinstance(n, int): out.extend([0] + mat(n))
        else: out.extend([1, 0]); go(n[0]); go(n[1])
    go(noun)
    atom = sum(bit << i for i, bit in enumerate(out))
    return atom.to_bytes((atom.bit_length() + 7) // 8, "little")
def atom_of(b): return int.from_bytes(b, "little")
def cord(s): return int.from_bytes(s.encode(), "little")
def core(battery): return ((1, (battery, (0, 0))), 0)   # [[1 gate] 0], gate [battery [0 0]]
# In the gate the sample is axis 6; with ONE target, the first ABI slot's value is axis 109.
NOUNOUT = core((((1, cord("blob")), ((0, 109), (1, 7))), (1, 0)))   # ~[['blob' [iron 7]]]
NOUNCOPY = core((((1, cord("copy")), (0, 109)), (1, 0)))           # ~[['copy' blob]]
N16 = (0, 1)                                                       # the program over [forge]

forge = open(os.path.join(TPL, "forge.jam"), "rb").read()
open(path("permit-all.json"), "w").write('{"type":"all","predicates":[]}\n')
IRON, WOOD, SWORD = 2, 3, 4                  # read by the pinned forge
OUT = {"inv/iron": 5, "inv/wood": 6, "inv/sword": 7}  # written by it
BLOB, COPY = 9, 10
def slot(f, k, t="nat"): return {"target": "0", "slot": f"resource/field/{f}/before", "key": k, "type": t}
def out(k, f, t="nat"): return {"key": k, "target": "0", "field": str(f), "type": t}
INV_SAMPLE = [slot(IRON, "inv/iron"), slot(WOOD, "inv/wood"), slot(SWORD, "inv/sword")]
def abi(context, sample, outputs, libraries=(), fuel=1000000, version="5"):
    return {"evaluator": "nock", "version": version, "context": context, "arm": "2", "fuel": str(fuel),
            "sample": sample, "outputs": outputs, "libraries": list(libraries)}

def check(name, jam_bytes, a):
    v = op(131, pair(jam_bytes, json.dumps(a).encode()))
    json.dump(v, open(path(f"{name}.check.json"), "w"))
    return v
def birth(name, jam_bytes, a):
    v = check(name, jam_bytes, a)
    r = mini("--action", "create", "--dir", WS, "--name", name, "--storage", "nock",
        "--predicate", path("permit-all.json"), "--program", path(f"{name}.check.json"))
    open(path(f"{name}.birth.err"), "w").write(r.stderr)
    return v, r.returncode
counter = [0]
def submit(label, targets, run=None):
    counter[0] += 1
    pid = re.sub(r"[^A-Za-z0-9-]+", "-", label).strip("-") + f"-{counter[0]}"
    req = {"type": "minidregg-workspace-proposal-v1", "action": "invoke", "targets": targets}
    if run is not None: req["run"] = run
    json.dump(req, open(path(f"{pid}.request.json"), "w"))
    r = mini("--action", "propose", "--dir", WS, "--request", path(f"{pid}.request.json"),
        "--proposal-id", pid)
    if r.returncode != 0:
        return r.returncode, "propose: " + last_line(r)
    attempt = os.path.join(WS, "attempts", pid)
    r = mini("--action", "submit", "--dir", WS, "--intent", os.path.join(WS, "proposals", pid, "intent.json"),
        "--attempt", attempt)
    open(path(f"{pid}.submit.err"), "w").write(r.stderr)
    last = last_line(r, attempt)
    outcome = os.path.join(attempt, "outcome.json")
    if "exact outcome evidence was retained" in last and os.path.exists(outcome):
        o = json.load(open(outcome))
        last = "outcome " + o.get("type", "?") + " | " + bytes.fromhex(o.get("phase", "")).decode("latin1") \
            + " | " + bytes.fromhex(o.get("detail", "")).decode("latin1")
    return r.returncode, last
def scalar(actions): return [{"name": "jobs", "payload": {"type": "scalar", "actions": actions}}]
def create(f, v): return {"type": "create", "key": {"type": "object", "field": str(f)}, "value": str(v)}
def write(f, v, e): return {"type": "write", "key": {"type": "object", "field": str(f)}, "value": str(v), "expected": str(e)}
def read_fields():
    r = mini("--action", "read", "--dir", WS, "--name", "jobs")
    open(path(f"jobs.read.{counter[0]}.json"), "w").write(r.stdout)
    vals = {}
    try:
        for e in json.loads(r.stdout)["cell"]["entries"]:
            vals[e["key"]["field"]] = e["value"]
    except Exception: pass
    return vals
def install(name, predicate):
    req = {"type": "minidregg-workspace-proposal-v1", "action": "install-policy", "name": "jobs",
           "predicate": predicate}
    json.dump(req, open(path(f"{name}.request.json"), "w"))
    r2 = mini("--action", "propose", "--dir", WS, "--request", path(f"{name}.request.json"), "--proposal-id", name)
    if r2.returncode != 0: return r2.returncode, last_line(r2)
    r3 = mini("--action", "submit", "--dir", WS, "--intent", os.path.join(WS, "proposals", name, "intent.json"),
        "--attempt", os.path.join(WS, "attempts", name))
    return r3.returncode, last_line(r3)
def dry(program, values, targets=None):
    req = {"programId": program, "caller": str(SUBJECT), "room": "0", "targets": targets or [JOBS],
           "values": [["0", f"resource/field/{f}/before", str(v)] for f, v in values]}
    return op(134, json.dumps(req).encode())
def runner(jam_path, sample_hex, name):
    open(path(f"{name}.sample.jam"), "wb").write(bytes.fromhex(sample_hex or ""))
    nr = subprocess.run([NOCK_RUN, "--program", jam_path, "--sample", path(f"{name}.sample.jam"),
        "--fuel", "100000000", "--jets", "off"], capture_output=True, text=True)
    open(path(f"{name}.nock-run.json"), "w").write(nr.stdout)
    try: return json.loads(nr.stdout)
    except Exception: return {}

# 1. births: forge as a library (live ABI, its own reads); the pinned forge in N16 shape
P = {}
v, rc = birth("forgelib", forge, abi("live", INV_SAMPLE, [out(k, f) for k, f in
    {"inv/iron": IRON, "inv/wood": WOOD, "inv/sword": SWORD}.items()]))
P["forgelib"] = v.get("programId")
row("forge born as a library cell (ABI v4, live)", rc == 0 and v.get("verdict") == "admissible",
    f"rc={rc} programId={P['forgelib']} jamBytes={v.get('jamBytes')}")
open(path("pinforge.jam"), "wb").write(jam(N16))
v, rc = birth("pinforge", jam(N16), abi("pinned", INV_SAMPLE, [out(k, f) for k, f in OUT.items()],
    libraries=[P["forgelib"]]))
P["pinforge"] = v.get("programId")
row("the pinned forge is born: `[0 1]` over the forge library (N16 shape), context pinned",
    rc == 0 and v.get("verdict") == "admissible" and v.get("jamBytes") == str(len(jam(N16))),
    f"rc={rc} programId={P['pinforge']} jamBytes={v.get('jamBytes')} reads fields 2-4, writes 5-7")
for name, noun, a in [
    ("nounout", NOUNOUT, abi("pinned", [slot(IRON, "inv/iron")], [out("blob", BLOB, "noun")])),
    ("nouncopy", NOUNCOPY, abi("pinned", [slot(BLOB, "blob", "noun")], [out("copy", COPY, "noun")]))]:
    open(path(f"{name}.jam"), "wb").write(jam(noun))
    v, rc = birth(name, jam(noun), a)
    P[name] = v.get("programId")
    row(f"{name} born (raw Nock core, pinned, a `noun` slot)", rc == 0 and v.get("verdict") == "admissible",
        f"rc={rc} programId={P[name]} verdict={v.get('verdict')}/{v.get('reason')}")

# 2. refusals at op 131, by name
door_pinned = dict(abi("pinned", [], [out("count", 4)]), arm="23", door={"peek": "22", "state": "2", "event": "3"})
v = check("door-pinned", jam(N16), door_pinned)
row("a door ABI that says pinned: refused abiShape (a door's sample is its state + event, advanced by every poke)",
    v.get("verdict") == "refused" and v.get("reason") == "abiShape", f"{v.get('verdict')}/{v.get('reason')}")
v = check("abi-v3", jam(N16), abi("live", INV_SAMPLE, [], version="3"))
row("an ABI v3 record (K-RUN-PIN's or NC-2's, both superseded by v4): refused abiVersion", v.get("verdict") == "refused" and v.get("reason") == "abiVersion",
    f"{v.get('verdict')}/{v.get('reason')}")

# 3. differential: op 133 (kernel sampleOf) vs nock-run --emit-sample, both contexts and a noun input
def k_sample(program, ctx, values):
    req = {"programId": program, "context": {"height": str(ctx[0]), "caller": str(ctx[1]), "room": "0"},
           "targets": ["10"], "values": [["0", f"resource/field/{f}/before", str(x)] for f, x in values]}
    return bytes.fromhex(op(133, json.dumps(req).encode()).get("sample", ""))
def r_sample(name, sj):
    json.dump(sj, open(path(f"{name}.runner-sample.json"), "w"))
    subprocess.run([NOCK_RUN, "--program", os.path.join(TPL, "forge.jam"), "--sample-json",
        path(f"{name}.runner-sample.json"), "--fuel", "1", "--emit-sample", path(f"{name}.runner-sample.jam")],
        capture_output=True, text=True)
    p = path(f"{name}.runner-sample.jam")
    return open(p, "rb").read() if os.path.exists(p) else b""
inv_inputs = [["target/0", 10], ["inv/iron", 3], ["inv/wood", 2], ["inv/sword", 0]]
vals = [(IRON, 3), (WOOD, 2), (SWORD, 0)]
kp1, kp2 = k_sample(P["pinforge"], (212, 1103), vals), k_sample(P["pinforge"], (999, 7), vals)
rp = r_sample("pinned", {"context": "pinned", "inputs": inv_inputs})
kl = k_sample(P["forgelib"], (212, 1103), vals)
rl = r_sample("live", {"context": "live", "height": 212, "caller": 1103, "room": 0, "inputs": inv_inputs})
blob = jam((3, 7))
kn = k_sample(P["nouncopy"], (212, 1103), [(BLOB, atom_of(blob))])
rn = r_sample("noun", {"context": "pinned", "inputs": [["target/0", 10], ["blob", {"noun": blob.hex()}]]})
row("runner --emit-sample = kernel sampleOf, byte for byte: pinned (at heights 212 and 999), live, noun input",
    kp1 and kp1 == kp2 == rp and kl and kl == rl and kl != kp1 and kn and kn == rn,
    f"pinned {kp1.hex()} live {kl.hex()} noun {kn.hex()} runner {rp.hex()}|{rl.hex()}|{rn.hex()}")

# 4. the job cell: fields 2-4 filled, the law: every mutation is one of the three programs' checked product
r = mini("--action", "create", "--dir", WS, "--name", "jobs", "--storage", "declared",
    "--predicate", path("permit-all.json"))
JOBS = json.load(open(os.path.join(WS, "refs", "jobs.json")))["target"] if r.returncode == 0 else None
rc, last = submit("fill", scalar([create(IRON, 3), create(WOOD, 2), create(SWORD, 0)]))
LAW = {"type": "any", "predicates": [
    {"type": "not", "predicate": {"type": "eq", "slot": "request/verb", "value": "2"}},
    {"type": "ran", "program": P["pinforge"]}, {"type": "ran", "program": P["nounout"]},
    {"type": "ran", "program": P["nouncopy"]}]}
rc2, last2 = install("law", LAW)
row("job cell filled (iron 3, wood 2, sword 0) under the law `ran pinforge | ran nounout | ran nouncopy`",
    JOBS is not None and rc == 0 and rc2 == 0, f"jobs={JOBS} fill rc={rc} law rc={rc2} {last2[:120]}")

# 5. the claim, computed once at height h0
d0 = dry(P["pinforge"], vals)
json.dump(d0, open(path("pinforge.dry0.json"), "w"))
rn0 = runner(os.path.join(TPL, "forge.jam"), d0.get("sample"), "pinforge")
CLAIM = {"programId": P["pinforge"], "sample": d0.get("sample"), "output": rn0.get("out_hex", ""),
         "steps": d0.get("steps")}
json.dump(CLAIM, open(path("claim.json"), "w"))
H0 = int(d0.get("height", "-1"))
row("op 134 at h0: the kernel's pinned sample, steps and writes; nockvm on that sample gets the kernel's output",
    d0.get("verdict") == "ok" and rn0.get("status") == "ok" and rn0.get("out_hex") == d0.get("output")
    and d0.get("writes") == [["0", str(f), "1"] for f in OUT.values()],
    f"h0={H0} lean steps={d0.get('steps')} nockvm items={rn0.get('steps')} writes={d0.get('writes')}")

# 6. other admissions move the height: the noun output, written as a jam atom
dn = dry(P["nounout"], [(IRON, 3)])
json.dump(dn, open(path("nounout.dry.json"), "w"))
rnn = runner(path("nounout.jam"), dn.get("sample"), "nounout")
want = atom_of(jam((3, 7)))
rc, last = submit("nounout", scalar([create(BLOB, want)]),
    {"programId": P["nounout"], "sample": dn.get("sample"), "output": rnn.get("out_hex", ""), "steps": dn.get("steps")})
f = read_fields()
row("a `noun` output: the product's noun [3 7] is written as its jam atom (and nockvm agrees)",
    rc == 0 and dn.get("writes") == [["0", str(BLOB), str(want)]] and f.get(str(BLOB)) == str(want)
    and rnn.get("out_hex") == dn.get("output"),
    f"rc={rc} jamAtom([3 7])={want} field9={f.get(str(BLOB))} {last[:120]}")
dc = dry(P["nouncopy"], [(BLOB, want)])
json.dump(dc, open(path("nouncopy.dry.json"), "w"))
rnc = runner(path("nouncopy.jam"), dc.get("sample"), "nouncopy")
rc, last = submit("nouncopy", scalar([create(COPY, want)]),
    {"programId": P["nouncopy"], "sample": dc.get("sample"), "output": rnc.get("out_hex", ""), "steps": dc.get("steps")})
f = read_fields()
row("a `noun` sample slot cues that field back to [3 7]; copying it writes the same atom (noun_output_roundtrip)",
    rc == 0 and f.get(str(COPY)) == str(want) and rnc.get("out_hex") == dc.get("output"),
    f"rc={rc} field10={f.get(str(COPY))} {last[:120]}")

# 7. the one claim, admitted at h1 > h0 ...
d1 = dry(P["pinforge"], vals)
H1 = int(d1.get("height", "-1"))
rc, last = submit("pinned-at-h1", scalar([create(f, 1) for f in OUT.values()]), CLAIM)
f = read_fields()
row("the claim computed at h0 is admitted at h1 > h0 (sampleStale does not fire)",
    rc == 0 and H1 > H0 and d1.get("sample") == CLAIM["sample"] and all(f.get(str(x)) == "1" for x in OUT.values()),
    f"rc={rc} h0={H0} h1={H1} fields={f} {last[:120]}")
# ... and again at h2 > h1
d2 = dry(P["pinforge"], vals)
H2 = int(d2.get("height", "-1"))
rc, last = submit("pinned-at-h2", scalar([write(f, 1, 1) for f in OUT.values()]), CLAIM)
row("the SAME claim is admitted again at h2 > h1",
    rc == 0 and H2 > H1 and d2.get("sample") == CLAIM["sample"], f"rc={rc} h2={H2} {last[:120]}")

# 8. write field 3 (inv/wood): the claim is stale, and the refusal names the field
rc, last = install("open", {"type": "all", "predicates": []})
rcw, lastw = submit("wood", scalar([write(WOOD, 5, 2)]))
rc, last = submit("pinned-after-wood", scalar([write(f, 1, 1) for f in OUT.values()]), CLAIM)
row("after inv/wood is written, the same claim is refused sampleStale naming inv/wood",
    rcw == 0 and rc != 0 and 'sampleStale (some "inv/wood")' in last, f"wood rc={rcw} rc={rc} last={last[:220]}")

# 9. control: a LIVE forge claim goes stale at the next height with no field changed
vl = [(IRON, 3), (WOOD, 5), (SWORD, 0)]
dl = dry(P["forgelib"], vl)
rl = runner(os.path.join(TPL, "forge.jam"), dl.get("sample"), "forgelib")
live_claim = {"programId": P["forgelib"], "sample": dl.get("sample"), "output": rl.get("out_hex", ""),
              "steps": dl.get("steps")}
rcx, _ = submit("unrelated", scalar([create(11, 1)]))
rc, last = submit("live-next-height", scalar([write(IRON, 1, 3), write(WOOD, 1, 5), write(SWORD, 1, 0)]), live_claim)
row("control (live): the claim computed one admission earlier, no field changed, is refused sampleStale none",
    dl.get("verdict") == "ok" and rcx == 0 and rc != 0 and "sampleStale none" in last,
    f"h={dl.get('height')} unrelated rc={rcx} rc={rc} last={last[:220]}")

# 9b. the declared maximum (NC-2's `SampleSlot.max`, carried by ABI v4 beside `context`): a slot value
# AT its maximum is admitted; the same value under a program that declares one less is refused
# `fieldOverMax` by name, at prepare, before any sample is built. Fields now: iron 3, wood 5, sword 0.
def mslot(f, k, m): return dict(slot(f, k), max=str(m))
MAXOUT = {"inv/iron": 12, "inv/wood": 13, "inv/sword": 14}
for name, ceil in [("maxforge", (3, 5, 3)), ("tightforge", (2, 5, 3))]:
    v, rc = birth(name, jam(N16), abi("pinned", [mslot(IRON, "inv/iron", ceil[0]), mslot(WOOD, "inv/wood", ceil[1]),
        mslot(SWORD, "inv/sword", ceil[2])], [out(k, f) for k, f in MAXOUT.items()], libraries=[P["forgelib"]]))
    P[name] = v.get("programId")
vm = [(IRON, 3), (WOOD, 5), (SWORD, 0)]
dm = dry(P["maxforge"], vm)
json.dump(dm, open(path("maxforge.dry.json"), "w"))
rm = runner(os.path.join(TPL, "forge.jam"), dm.get("sample"), "maxforge")
max_claim = {"programId": P["maxforge"], "sample": dm.get("sample"), "output": rm.get("out_hex", ""),
             "steps": dm.get("steps")}
max_writes = scalar([create(int(w[1]), int(w[2])) for w in dm.get("writes") or []])
rc, last = submit("at-max", max_writes, max_claim)
f = read_fields()
row("fieldOverMax pole, at the maximum: iron = 3 under `max 3` (wood = 5 under `max 5`) is admitted",
    P["maxforge"] is not None and dm.get("verdict") == "ok" and rc == 0
    and all(f.get(str(x)) is not None for x in MAXOUT.values()),
    f"rc={rc} writes={dm.get('writes')} fields12-14={[f.get(str(x)) for x in MAXOUT.values()]} {last[:120]}")
tight_claim = dict(max_claim, programId=P["tightforge"])
rc, last = submit("over-max", scalar([write(int(w[1]), int(w[2]), int(w[2])) for w in dm.get("writes") or []]),
    tight_claim)
row("fieldOverMax pole, above it: iron = 3 under `max 2` is refused fieldOverMax by name",
    P["tightforge"] is not None and rc != 0 and "fieldOverMax" in last, f"rc={rc} last={last[:220]}")

# 10. cold reopen + operator audit: every record (both pinned admissions included) re-admits
pid = open(os.path.join(W, "public", "server.pid")).read().strip()
subprocess.run(["kill", pid]); time.sleep(3)
a = subprocess.run([os.environ["HOST"], CONFIG, "audit"], capture_output=True, text=True)
open(path("audit.out"), "w").write(a.stdout + a.stderr)
row("cold reopen: the operator audit re-admits every record, both pinned admissions included",
    a.returncode == 0 and "audited" in a.stdout,
    next((l for l in a.stdout.splitlines() if l.startswith("audited")), (a.stdout + a.stderr).strip()[-200:]))

with open(path("rows.tsv"), "w") as fh:
    for name, status, detail in ROWS: fh.write(f"{status}\t{name}\t{detail}\n")
passed = sum(1 for r in ROWS if r[1] == "PASS")
verdict = f"J-NOCK-3P {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)}"
print(verdict); print(path("rows.tsv"))
print(verdict, file=sys.stderr)
sys.exit(0 if passed == len(ROWS) else 1)
PY
rc=$?
exit $rc
