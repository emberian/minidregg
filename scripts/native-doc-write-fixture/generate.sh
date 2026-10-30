#!/usr/bin/env bash
# generate.sh -- regenerate Fixtures/NativeDocWriteFixtureData.lean from a real native run.
#
#   scripts/native-doc-write-fixture/generate.sh WORLD [VERIFIER] [ATTEMPT]
#
# WORLD is the root of a FRESH scratch world on which
#   native/resource-client/doc-write-native-acceptance.py --bin BIN --root WORLD
# ran with a native Host and clients built from ONE candidate (never a live world).
# ATTEMPT (default a2) is the retained document write that is the fixture. VERIFIER
# (default: the candidate's, from WORLD/state.json) is the binary behind the transcript;
# on a machine that cannot run the candidate's, one built from native/credential-signature-verifier.
# FIXTURE_LEAN_PATH_EXTRA adds module search roots (a tree whose Fixtures oleans are not built yet).
#
# It re-runs the admission in Lean (the same scripts/native-accepted-fixture/replay.lean, `doc`
# mode) against the Store prefix it was admitted at (signatures by the linked native kernel, every check
# recorded by scripts/native-accepted-fixture/verify-shim.c), submits every check the kernel verified to
# the verifier binary (each `verified`: the transcript), and refuses unless the Lean admission's record is
# byte for byte the Host's appended record, its world root the Host's, and its projection the
# hand-written Fixtures/NativeDocWriteFixtureAuthority.lean. Then it writes the data module.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
world=$(cd "${1:?usage: generate.sh WORLD [VERIFIER] [ATTEMPT]}" && pwd)
attempt=${3:-a2}
export PATH=$HOME/.elan/bin:$PATH
work=$(mktemp -d "${TMPDIR:-/tmp}/native-doc-write-fixture.XXXXXX")
trap 'rm -rf "$work"' EXIT
verifier=${2:-$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["bin"])' "$world/state.json")/minidregg-credential-signature-verifier}
[ -x "$verifier" ] || { echo "generate: no verifier at $verifier" >&2; exit 2; }
settings=$world/w/deployment/pinned-config.json

python3 - "$world" "$attempt" "$work" <<'PY'
import json, pathlib, sqlite3, sys
world, attempt, work = pathlib.Path(sys.argv[1]), sys.argv[2], pathlib.Path(sys.argv[3])
db = sqlite3.connect(f"file:{world}/w/store/forward-link.sqlite3?mode=ro", uri=True)
(seed,) = db.execute("select bytes from durable_seed").fetchone()
records = dict(db.execute("select height, record from durable_log"))
dir_ = world / "w/sponsor/attempts" / attempt
outcome = json.loads((dir_ / "outcome.json").read_text())
assert outcome["type"] == "confirmed" and outcome["confirmation"] == "installed", outcome
height = int(outcome["acceptedCount"]) - 1
d = work / "first"; d.mkdir()
(d / "seed.bin").write_bytes(seed)
for i in range(1, height + 1): (d / f"rec-{i}.bin").write_bytes(records[i])
(d / "call.bin").write_bytes((dir_ / "call.bin").read_bytes())
(d / "host-record.bin").write_bytes(records[height + 1])
(work / "meta.json").write_text(json.dumps({"height": height, "worldRoot": outcome["worldRoot"]}))
PY
height=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["height"])' "$work/meta.json")
ulimit -s unlimited 2>/dev/null || true
cd "$root"
cc -shared -fPIC -O1 -I "$(lake env lean --print-prefix)/include" -o "$work/verify-shim.so" "$root/scripts/native-accepted-fixture/verify-shim.c" -ldl
extra=$(lake env printenv LEAN_PATH)${FIXTURE_LEAN_PATH_EXTRA:+:$FIXTURE_LEAN_PATH_EXTRA}
  VERIFY_LOG=$work/verify.log MINI_KERNELS_LIB=$root/.lake/native/libmini_kernels_lean.so lake env env LEAN_PATH="$extra" lean --load-dynlib="$work/verify-shim.so" --load-dynlib=.lake/native/libmini_kernels_lean.so --run "$root/scripts/native-accepted-fixture/replay.lean" \
  "$work/first" "$settings" "$verifier" "$height" doc \
  >"$work/first.out" 2>"$work/first.err" || { cat "$work/first.err" >&2; echo "generate: replay failed" >&2; exit 1; }
echo "replay: $(head -1 "$work/first.out")"

python3 - "$world" "$work" "$root/Fixtures/NativeDocWriteFixtureData.lean" "$verifier" "$attempt" <<'PY'
import json, pathlib, sys, hashlib
world, work, out, verifier, attempt = sys.argv[1:6]
world, work = pathlib.Path(world), pathlib.Path(work)
meta = json.loads((work / "meta.json").read_text())
state = json.loads((world / "state.json").read_text())
lines_out = (work / "first.out").read_text().splitlines()
fo = lines_out[0].split()
assert fo[:2] == ["ACCEPTED", "record=same"], f"the Lean admission's record is not the Host's: {fo}"
assert fo[2] == f"root={meta['worldRoot']}", f"world root {fo[2]} != Host {meta['worldRoot']}"
def parse(text):
    res = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"): continue
        parts = line.split(" = ")
        res.append((parts[0].strip(), parts[1].strip()) if len(parts) == 2 else ("malformed", line))
    return res
authority_path = pathlib.Path(out).with_name("NativeDocWriteFixtureAuthority.lean")
authority_module = authority_path.read_text()
authority = parse(authority_module[authority_module.index('def text : String := "') + len('def text : String := "'):authority_module.rindex('"')])
projection = [tuple(l[len("PROJECTION "):].split(" = ", 1)) for l in lines_out if l.startswith("PROJECTION ")]
keys = list(dict.fromkeys([k for k, _ in authority] + [k for k, _ in projection]))
a, p = dict(authority), dict(projection)
diff = [f"  {k}: authority {a.get(k, '(absent)')}, run {p.get(k, '(absent)')}" for k in keys if a.get(k) != p.get(k)]
if diff or len(projection) != len(authority):
    print(f"generate: REFUSED: the run's projection differs from the authority {authority_path}:", file=sys.stderr)
    print("\n".join(diff), file=sys.stderr)
    print("Fix the implementation, or change the authority in its own reviewed commit (Authority-Change: <reason>).", file=sys.stderr)
    sys.exit(1)
def verified_triples(log, verifier):
    """Every check the re-run asked the linked kernel (verify-shim.c's log: KEY FRAME SIGNATURE
    VERDICT) that the kernel verified (verdict 0, `CredentialSignatureIO.nativeVerified`), each
    re-submitted to the pinned verifier binary, which must answer exactly `verified`."""
    import subprocess, tempfile
    out = []
    for line in (log.read_text().splitlines() if log.exists() else []):
        key, frame, signature, verdict = line.split()
        if verdict != "0": continue
        with tempfile.TemporaryDirectory() as d:
            paths = []
            for name, value in (("key", key), ("frame", frame), ("signature", signature)):
                p = pathlib.Path(d) / name; p.write_bytes(bytes.fromhex(value)); paths.append(str(p))
            r = subprocess.run([verifier, "verify", *paths], capture_output=True, text=True)
        assert (r.returncode, r.stdout, r.stderr) == (0, "verified\n", ""), (key, frame, signature, r)
        out.append((key, frame, signature))
    return out
triples, seen = [], set()
for t in verified_triples(work / "verify.log", verifier):
    if t not in seen: seen.add(t); triples.append(t)
assert triples, "the re-run asked the kernel nothing"
cfg = json.loads((world / "w/deployment/pinned-config.json").read_text())
# Fields the fixture's config does not carry: they must be unset. grainBirthTariff and
# completionCustodianKey ARE carried (they enter the runtime parameters, hence the profile).
for k in ("disabledEvaluators", "birthSlack", "jointConsensus", "fnGateway", "objectiveInvocation"):
    assert cfg.get(k) is None, f"pinned config sets {k}; the fixture's config does not read it"
d = work / "first"
height = meta["height"]
rd = lambda p: p.read_bytes().hex()
lines = [
"/- GENERATED by scripts/native-doc-write-fixture/generate.sh -- do not edit; regenerate.",
f"Candidate: {state['bin']} (host sha256 {state['hostSha256']}), world doc-write-native-acceptance.py,",
f"document write `{attempt}` (doc append) at Store height {height + 1}.",
f"Verifier behind the transcript: sha256 {hashlib.sha256(open(verifier,'rb').read()).hexdigest()}.",
"The consumer is Fixtures.NativeDocWriteFixture. -/",
"namespace Minidregg.Fixtures.NativeDocWriteFixtureData", "",
"/-! The deployment's pinned config (w/deployment/pinned-config.json). -/",
]
for lean, key in (("pinDomain","domain"),("pinFactoryId","factoryId"),("pinResourceBookId","resourceBookId"),
    ("pinAuthorityCellId","authorityCellId"),("pinFederation","federation"),("pinIssuer","issuer"),
    ("pinOwnerBudget","ownerBudget"),("pinLifetime","lifetime"),("pinTariffBase","tariffBase"),
    ("pinTariffPerBirth","tariffPerBirth"),("pinTariffPerGrant","tariffPerGrant"),
    ("pinTariffPerInitialPayloadByte","tariffPerInitialPayloadByte"),("pinCollector","collector"),
    ("pinAsset","asset"),("pinGenesisHeight","genesisHeight"),("pinExpectedSeed","expectedSeed")):
    lines.append(f"def {lean} : Nat := {int(cfg[key])}")
grain, custodian = cfg.get("grainBirthTariff"), cfg.get("completionCustodianKey")
lines += ["def pinGrainBirthTariff : Option (Nat × Nat) := " +
          ("none" if grain is None else f"some ({int(grain['base'])}, {int(grain['perBirth'])})"),
          "def pinCompletionCustodianKeyHex : Option String := " +
          ("none" if custodian is None else f'some "{custodian}"')]
lines += ["", "/-! The Store prefix of the document write (its own seed and log frames). -/",
          f'def seedHex : String := "{rd(d / "seed.bin")}"',
          "def recordHexes : List String := ["]
lines += [f'  "{rd(d / f"rec-{i}.bin")}"' + ("," if i < height else "") for i in range(1, height + 1)]
lines += ["]", "", "/-! The write, and the record and world root the Host reported after it. -/",
          f'def callHex : String := "{rd(d / "call.bin")}"',
          f'def hostRecordHex : String := "{rd(d / "host-record.bin")}"',
          f"def hostWorldRoot : Nat := {int(meta['worldRoot'])}",
          "", "/-! Every (publicKey, frame, signature) the verifier answered `verified` on during the admission. -/",
          "def verifiedTriples : List (String × String × String) := ["]
lines += [f'  ("{k}", "{f}", "{s}")' + ("," if i < len(triples) - 1 else "") for i, (k, f, s) in enumerate(triples)]
lines += ["]", "", "end Minidregg.Fixtures.NativeDocWriteFixtureData", ""]
pathlib.Path(out).write_text("\n".join(lines))
print(f"generate: wrote {out} ({len(triples)} triples, {height} records)")
PY
