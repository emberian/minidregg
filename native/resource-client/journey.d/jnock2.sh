#!/usr/bin/env bash
# J-NOCK-2b (NOCK.md K-NOCK-CELL): a friend's Nock program becomes a program cell.
#
# Journey hook contract (journey.sh header): HOST, MINI, STORE, VERIFIER and
# JOURNEY_STEP_DIR exported; it bootstraps its OWN fresh Store and service under
# JOURNEY_STEP_DIR (newparticipant-acceptance.sh, the J0 fixture), never touches
# the journey's service, and stops what it starts. Exit 0 = PASS. The last stdout
# line is the deciding artifact (rows.tsv); the verdict is the last stderr line.
#
# Also needs: NOCK_TEMPLATES (a directory holding NOCK-RUNNER's forge.jam and
# noop.jam, minimal bytes) and NOCK_RUN (the untrusted runner, read-only use).
#
# Rows: forge's check is admissible and names its content address; its birth
# (storage nock, the sponsor's own law) is admitted at that address; the Host
# shows it back byte for byte; the same record again meets an occupied
# identifier; hoonc's padded jam is refused nonCanonical (check AND birth); a jam
# that does not cue is refused noCue (check AND birth); an ABI naming a missing
# library is refused missingLibrary / nockLibrary (check AND birth); fuel 0 is
# refused; an ABI naming the stored forge as a library is admissible; the
# kernel's sample for a two-target command equals the runner's sample byte for
# byte, and the runner, fed the kernel's sample, computes forge's writes.
set -euo pipefail
umask 077
for name in HOST MINI STORE VERIFIER JOURNEY_STEP_DIR NOCK_TEMPLATES NOCK_RUN; do
  if [ -z "${!name:-}" ]; then echo "jnock2: $name is required" >&2; exit 2; fi
done
DIR="$JOURNEY_STEP_DIR/jnock2"
if [ -e "$DIR" ]; then echo "jnock2: refusing to reuse $DIR" >&2; exit 2; fi
mkdir -p "$DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
W="$DIR/world"
# A program jam is ~566 KB (NOCK-RUNNER A6: hoonc ships the stdlib in every
# trap). Observing a birth intent costs its byte length against the owner
# capability's maxCost (the template ownerBudget, 100000 by default), so this
# world is bootstrapped with a budget a program birth fits under.
NEWPARTICIPANT_OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-4000000} \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W" \
  >"$DIR/bootstrap.out" 2>"$DIR/bootstrap.err" || { echo "jnock2: bootstrap failed: $(tail -1 "$DIR/bootstrap.err")" >&2; exit 1; }
stop() { if [ -s "$W/public/server.pid" ]; then kill "$(cat "$W/public/server.pid")" 2>/dev/null || true; fi; }
trap stop EXIT
set +e
python3 - "$DIR" "$W" <<'PY'
import hashlib, json, os, re, socket, struct, subprocess, sys, time
DIR, W = sys.argv[1], sys.argv[2]
MINI, NOCK_RUN, TPL = os.environ["MINI"], os.environ["NOCK_RUN"], os.environ["NOCK_TEMPLATES"]
CONFIG = os.path.join(W, "deployment", "pinned-config.json")
SOCK = os.path.join(W, "public", "mini.sock")
WS = os.path.join(W, "sponsor")
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
def cord(s): return int.from_bytes(s.encode(), "little")

forge = open(os.path.join(TPL, "forge.jam"), "rb").read()
noop = open(os.path.join(TPL, "noop.jam"), "rb").read()
def slot(t, f, k): return {"target": str(t), "slot": f"resource/field/{f}/before", "key": k, "type": "nat"}
def out(k, t, f): return {"key": k, "target": str(t), "field": str(f), "type": "nat"}
FORGE_ABI = {"version": "4", "context": "live", "arm": "2", "fuel": "1000000",
  "sample": [slot(0, 1, "inv/iron"), slot(0, 2, "inv/wood"), slot(1, 3, "inv/sword")],
  "outputs": [out("inv/iron", 0, 1), out("inv/wood", 0, 2), out("inv/sword", 1, 3)],
  "libraries": []}
def check(jam, abi, name):
    t0 = time.monotonic()
    v = op(131, pair(jam, json.dumps(abi).encode()))
    dt = time.monotonic() - t0
    json.dump(v, open(path(f"{name}.check.json"), "w"))
    return v, dt
def birth(name, verdict_name):
    r = subprocess.run([MINI, "workspace", "--action", "create", "--dir", WS, "--name", name,
        "--storage", "nock", "--predicate", path("permit-all.json"),
        "--program", path(f"{verdict_name}.check.json")], capture_output=True, text=True)
    open(path(f"{name}.birth.out"), "w").write(r.stdout); open(path(f"{name}.birth.err"), "w").write(r.stderr)
    outcome = os.path.join(WS, "attempts", f"create-{name}", "outcome.json")
    o = json.load(open(outcome)) if os.path.exists(outcome) else None
    last = (r.stderr.strip().splitlines() or [""])[-1]
    retained = os.path.join(WS, "sources", f"create-{name}.current", "reply.frame")
    if "retained encoded Host outcome" in last and os.path.exists(retained):
        last = open(retained, "rb").read().decode("latin1").replace("\xff", " | ")
    # The client now names the retained frame of a refused authoring generation.
    named = re.search(r"retained (\S+/reply\.frame)", last)
    if named and os.path.exists(named.group(1)):
        last = open(named.group(1), "rb").read().decode("latin1").replace("\xff", " | ")
    m = re.search(r"([0-9a-f]{40,})", last)
    if m:
        last = bytes.fromhex(m.group(1)).decode("latin1").replace("\xff", " | ")
    return r.returncode, o, last
open(path("permit-all.json"), "w").write('{"type":"all","predicates":[]}\n')

# 1. forge: admissible, content-addressed
v, dt = check(forge, FORGE_ABI, "forge")
P, C = v.get("programId"), v.get("cellId")
row("forge check admissible", v.get("verdict") == "admissible" and v.get("present") is False
    and v.get("jamBytes") == str(len(forge)),
    f"verdict={v.get('verdict')} programId={P} cellId={C} jamBytes={v.get('jamBytes')} check {dt:.2f}s")
# 2. forge birth under the sponsor's own law
rc, o, last = birth("forge", "forge")
ref = json.load(open(os.path.join(WS, "refs", "forge.json"))) if os.path.exists(os.path.join(WS, "refs", "forge.json")) else {}
row("forge birth admitted at its content address", rc == 0 and ref.get("target") == C,
    f"rc={rc} ref.target={ref.get('target')} cellId={C} last={last[:160]}")
# 3. show: the stored bytes are forge's bytes
s = op(132, P.encode())
json.dump({k: (v2 if k != "jam" else f"<{len(v2)//2} bytes>") for k, v2 in s.items()}, open(path("forge.show.json"), "w"))
same = s.get("present") is True and bytes.fromhex(s.get("jam", "")) == forge
row("forge show = forge.jam byte for byte", same and s.get("cellId") == C,
    f"present={s.get('present')} cellId={s.get('cellId')} jam sha256={hashlib.sha256(bytes.fromhex(s.get('jam',''))).hexdigest()[:16]} forge sha256={hashlib.sha256(forge).hexdigest()[:16]} codeDigest={s.get('codeDigest')}")
# 4. the same record again
v2, _ = check(forge, FORGE_ABI, "forge-again")
rc, o, last = birth("forge-again", "forge-again")
row("same record again: one cell, second birth refused as occupied",
    v2.get("present") is True and v2.get("cellId") == C and rc != 0 and "already present" in last,
    f"check present={v2.get('present')} same id={v2.get('cellId') == C}; birth rc={rc} last={last[:200]}")
# 5. hoonc's padded jam
padded = forge + b"\x00" * 5
v, dt = check(padded, FORGE_ABI, "padded")
rc, o, last = birth("padded", "padded")
row("padded jam refused nonCanonical (check and birth)",
    v.get("verdict") == "refused" and v.get("reason") == "nonCanonical" and rc != 0
    and "initialPayload" in last,
    f"check={v.get('verdict')}/{v.get('reason')} ({dt:.2f}s); birth rc={rc} last={last[:200]}")
# 6. a jam that does not cue
nocue = forge[:1000]
v, _ = check(nocue, FORGE_ABI, "nocue")
rc, o, last = birth("nocue", "nocue")
row("truncated jam refused noCue (check and birth)",
    v.get("verdict") == "refused" and v.get("reason") == "noCue" and rc != 0
    and "initialPayload" in last,
    f"check={v.get('verdict')}/{v.get('reason')}; birth rc={rc} last={last[:200]}")
# 7. an ABI naming a missing library
lib_abi = dict(FORGE_ABI, libraries=["12345"])
v, _ = check(noop, lib_abi, "missinglib")
rc, o, last = birth("missinglib", "missinglib")
row("missing library refused (check missingLibrary, birth nockLibrary)",
    v.get("verdict") == "refused" and v.get("reason") == "missingLibrary" and rc != 0
    and "nockLibrary" in last,
    f"check={v.get('verdict')}/{v.get('reason')}; birth rc={rc} last={last[:200]}")
# 8. fuel 0
v, _ = check(noop, dict(FORGE_ABI, fuel="0"), "fuelzero")
row("fuel 0 refused", v.get("verdict") == "refused" and v.get("reason") == "fuelZero",
    f"check={v.get('verdict')}/{v.get('reason')}")
# 9. a present library is admissible
v, _ = check(noop, dict(FORGE_ABI, libraries=[P]), "withlib")
row("ABI naming stored forge as a library is admissible", v.get("verdict") == "admissible",
    f"check={v.get('verdict')}/{v.get('reason')} programId={v.get('programId')}")
# 10. sampleOf on a two-target command vs the runner
TARGETS = [10, 11]
req = {"programId": P, "context": {"height": "212", "caller": "1103", "room": str(cord("tale"))},
       "targets": [str(t) for t in TARGETS],
       "values": [["0", "resource/field/1/before", "3"], ["0", "resource/field/2/before", "2"],
                  ["1", "resource/field/3/before", "0"]]}
smp = op(133, json.dumps(req).encode())
json.dump(smp, open(path("sample.json"), "w"))
kernel_sample = bytes.fromhex(smp.get("sample", ""))
open(path("kernel-sample.jam"), "wb").write(kernel_sample)
sj = {"context": "live", "height": 212, "caller": 1103, "room": "tale",
      "inputs": [["target/0", 10], ["target/1", 11], ["inv/iron", 3], ["inv/wood", 2], ["inv/sword", 0]]}
json.dump(sj, open(path("runner-sample.json"), "w"))
r = subprocess.run([NOCK_RUN, "--program", os.path.join(TPL, "forge.jam"), "--sample-json", path("runner-sample.json"),
    "--fuel", "100000", "--emit-sample", path("runner-sample.jam"), "--emit-subject-formula", path("runner-sf.jam")],
    capture_output=True, text=True)
runner_sample = open(path("runner-sample.jam"), "rb").read() if os.path.exists(path("runner-sample.jam")) else b""
row("kernel sampleOf = runner sample, byte for byte", smp.get("verdict") == "sample" and kernel_sample == runner_sample and len(kernel_sample) > 0,
    f"kernel {kernel_sample.hex()} runner {runner_sample.hex()} (rc={r.returncode})")
r2 = subprocess.run([NOCK_RUN, "--program", os.path.join(TPL, "forge.jam"), "--sample", path("kernel-sample.jam"),
    "--fuel", "100000", "--writes"], capture_output=True, text=True)
open(path("runner-on-kernel-sample.json"), "w").write(r2.stdout)
try: res = json.loads(r2.stdout)
except Exception: res = {}
row("runner on the kernel's sample computes forge's writes", res.get("status") == "ok",
    f"status={res.get('status')} result={res.get('result')} writes={res.get('writes')}")
# 11. a sample the ABI cannot fill refuses
bad = dict(req, values=req["values"][:2])
smp2 = op(133, json.dumps(bad).encode())
row("absent slot refuses the sample", smp2.get("verdict") == "refused" and smp2.get("reason") == "sampleUnavailable",
    f"{smp2}")

# 12. replay: stop the service; the operator audit re-admits every accepted
# record (the forge birth included: its canonical check and library check run
# again through the ordinary birth replay) on a cold reopen.
pid = open(os.path.join(W, "public", "server.pid")).read().strip()
subprocess.run(["kill", pid]); time.sleep(3)
a = subprocess.run([os.environ["HOST"], CONFIG, "audit"], capture_output=True, text=True)
open(path("audit.out"), "w").write(a.stdout + a.stderr)
row("cold reopen: operator audit re-admits every record, the program birth included",
    a.returncode == 0 and "audited" in a.stdout, (a.stdout.strip() or a.stderr.strip())[-200:])

with open(path("rows.tsv"), "w") as f:
    for name, status, detail in ROWS: f.write(f"{status}\t{name}\t{detail}\n")
passed = sum(1 for r in ROWS if r[1] == "PASS")
verdict = f"J-NOCK-2b {'PASS' if passed == len(ROWS) else 'FAIL'} {passed}/{len(ROWS)}"
print(verdict); print(path("rows.tsv"))
print(verdict, file=sys.stderr)
sys.exit(0 if passed == len(ROWS) else 1)
PY
rc=$?
exit $rc
