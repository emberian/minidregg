#!/usr/bin/env bash
# generate.sh -- regenerate Assurance/NativeAcceptedFixtureData.lean from a real native run.
#
#   scripts/native-accepted-fixture/generate.sh WORLD [FIRST] [REFUSED]
#
# WORLD is the root of a FRESH scratch world on which
#   native/resource-client/objective-native-acceptance.py all --bin BIN --root WORLD
# ran with a native Host and clients built from THIS tree (never a live world).
# FIRST (default objective-first) is the accepted call, REFUSED (default
# dishonest-r01-source-is-package) a refused one admitted right after it.
#
# It re-runs both admissions in Lean (replay.lean) against the Store prefix each was
# admitted at, with the world's own verifier binary behind verify-logger.py, and
# refuses unless the accepted call's record is byte for byte the Host's appended
# record, its world root the Host's, and the refused call refused with the Host's
# reason. Then it writes the data module: the Store prefix, the two calls, the Host's
# record and root, the pinned config, and the transcript (every triple the verifier
# answered, each `verified`). Commit it with the module it feeds; the gate
# scripts/check-native-transcripts.sh re-verifies the transcript.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
world=$(cd "${1:?usage: generate.sh WORLD [FIRST] [REFUSED]}" && pwd)
first=${2:-objective-first}
refused=${3:-dishonest-r01-source-is-package}
export PATH=$HOME/.elan/bin:$PATH
work=$(mktemp -d "${TMPDIR:-/tmp}/native-accepted-fixture.XXXXXX")
trap 'rm -rf "$work"' EXIT
verifier=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["bin"])' "$world/state.json")/minidregg-credential-signature-verifier
[ -x "$verifier" ] || { echo "generate: no verifier at $verifier" >&2; exit 2; }
settings=$world/w/deployment/pinned-config.json

python3 - "$world" "$first" "$refused" "$work" <<'PY'
import json, pathlib, sqlite3, sys
world, first, refused, work = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3], pathlib.Path(sys.argv[4])
db = sqlite3.connect(f"file:{world}/w/store/forward-link.sqlite3?mode=ro", uri=True)
(seed,) = db.execute("select bytes from durable_seed").fetchone()
records = dict(db.execute("select height, record from durable_log"))
attempts = world / "w/sponsor/attempts"
outcome = json.loads((attempts / first / "outcome.json").read_text())
assert outcome["type"] == "confirmed" and outcome["confirmation"] == "installed", outcome
height = int(outcome["acceptedCount"]) - 1
for name, label, h in (("first", first, height), ("refused", refused, height + 1)):
    d = work / name; d.mkdir()
    (d / "seed.bin").write_bytes(seed)
    for i in range(1, h + 1): (d / f"rec-{i}.bin").write_bytes(records[i])
    (d / "call.bin").write_bytes((attempts / label / "call.bin").read_bytes())
(work / "first" / "host-record.bin").write_bytes(records[height + 1])
(work / "meta.json").write_text(json.dumps({"height": height, "worldRoot": outcome["worldRoot"]}))
PY
height=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["height"])' "$work/meta.json")
ulimit -s unlimited
cd "$root"
for name in first refused; do
  h=$height; [ "$name" = refused ] && h=$((height + 1))
  REAL_VERIFIER=$verifier VERIFY_LOG=$work/$name-verify.jsonl \
    lake env lean --run "$here/replay.lean" "$work/$name" "$settings" "$here/verify-logger.py" "$h" \
    >"$work/$name.out" 2>"$work/$name.err" || { cat "$work/$name.err" >&2; echo "generate: replay of $name failed" >&2; exit 1; }
  echo "replay $name: $(cat "$work/$name.out")"
done

python3 - "$world" "$first" "$refused" "$work" "$root/Assurance/NativeAcceptedFixtureData.lean" "$verifier" <<'PY'
import json, pathlib, sqlite3, sys, hashlib
world, first, refused, work, out, verifier = sys.argv[1:7]
world, work = pathlib.Path(world), pathlib.Path(work)
meta = json.loads((work / "meta.json").read_text())
fo = (work / "first.out").read_text().split()
assert fo[:2] == ["ACCEPTED", "record=same"], f"first: the Lean admission's record is not the Host's: {fo}"
assert fo[2] == f"root={meta['worldRoot']}", f"first: world root {fo[2]} != Host {meta['worldRoot']}"
host_reason = None
for r in (world / "results").glob("*.json"):
    d = json.loads(r.read_text())
    if str(d.get("attempt", "")).endswith("/" + refused) and d.get("refused"):
        host_reason = d.get("detail")
ro = (work / "refused.out").read_text().split()
assert ro[0] == "REFUSED", f"refused call was not refused in Lean: {ro}"
assert host_reason and host_reason.endswith("Reject." + ro[1].split(".")[-1]), f"Lean reason {ro[1]} != Host reason {host_reason}"
triples, seen = [], set()
for name in ("first", "refused"):
    for line in (work / f"{name}-verify.jsonl").read_text().splitlines():
        d = json.loads(line)
        assert (d["code"], d["stdout"], d["stderr"]) == (0, "verified\n", ""), d
        t = (d["key"], d["frame"], d["signature"])
        if t not in seen: seen.add(t); triples.append(t)
cfg = json.loads((world / "w/deployment/pinned-config.json").read_text())
for k in ("disabledEvaluators", "birthSlack", "grainBirthTariff", "completionCustodianKey", "jointConsensus", "fnGateway"):
    assert cfg.get(k) is None, f"pinned config sets {k}; the fixture's config does not read it"
d = work / "first"
height = meta["height"]
rd = lambda p: p.read_bytes().hex()
lines = [
"/- GENERATED by scripts/native-accepted-fixture/generate.sh -- do not edit; regenerate.",
f"World: {world} (objective-native-acceptance.py all), accepted call `{first}` at",
f"Store height {height + 1}, refused call `{refused}` (Host: {host_reason}).",
f"Verifier: {verifier} (sha256 {hashlib.sha256(open(verifier,'rb').read()).hexdigest()}).",
"The consumer is Assurance.NativeAcceptedFixture. -/",
"namespace Minidregg.Assurance.NativeAcceptedFixtureData", "",
"/-! The deployment's pinned config (w/deployment/pinned-config.json). -/",
]
for lean, key in (("pinDomain","domain"),("pinFactoryId","factoryId"),("pinResourceBookId","resourceBookId"),
    ("pinAuthorityCellId","authorityCellId"),("pinFederation","federation"),("pinIssuer","issuer"),
    ("pinOwnerBudget","ownerBudget"),("pinLifetime","lifetime"),("pinTariffBase","tariffBase"),
    ("pinTariffPerBirth","tariffPerBirth"),("pinTariffPerGrant","tariffPerGrant"),
    ("pinTariffPerInitialPayloadByte","tariffPerInitialPayloadByte"),("pinCollector","collector"),
    ("pinAsset","asset"),("pinGenesisHeight","genesisHeight"),("pinExpectedSeed","expectedSeed")):
    lines.append(f"def {lean} : Nat := {int(cfg[key])}")
lines.append(f'def pinObjectivePolicyHex : String := "{cfg["objectiveInvocation"]}"')
lines += ["", "/-! The Store prefix of the accepted call (its own seed and log frames). -/",
          f'def seedHex : String := "{rd(d / "seed.bin")}"',
          "def recordHexes : List String := ["]
lines += [f'  "{rd(d / f"rec-{i}.bin")}"' + ("," if i < height else "") for i in range(1, height + 1)]
lines += ["]", "", "/-! The accepted call, and the record and world root the Host reported after it. -/",
          f'def firstCallHex : String := "{rd(d / "call.bin")}"',
          f'def firstRecordHex : String := "{rd(d / "host-record.bin")}"',
          f"def firstWorldRoot : Nat := {int(meta['worldRoot'])}",
          "", "/-! The refused call. -/",
          f'def refusedCallHex : String := "{rd(work / "refused" / "call.bin")}"',
          "", "/-! Every (publicKey, frame, signature) the verifier answered `verified` on during the two admissions. -/",
          "def verifiedTriples : List (String × String × String) := ["]
lines += [f'  ("{k}", "{f}", "{s}")' + ("," if i < len(triples) - 1 else "") for i, (k, f, s) in enumerate(triples)]
lines += ["]", "", "end Minidregg.Assurance.NativeAcceptedFixtureData", ""]
pathlib.Path(out).write_text("\n".join(lines))
print(f"generate: wrote {out} ({len(triples)} triples, {height} records)")
PY
