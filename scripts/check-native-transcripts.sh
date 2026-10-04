#!/usr/bin/env bash
# check-native-transcripts.sh -- every recorded verifier transcript is still the verifier's.
#
# A `CredentialSignatureIO.Transcript` answers for the native Ed25519 verifier
# inside a Lean fixture that evaluates a real admission (Assurance.NativeAcceptedFixture
# names the first native Objective acceptance through one). This gate is what that
# substitution rests on:
#   * scripts/NativeTranscripts.lean lists EVERY transcript in the research umbrella
#     (and refuses a Transcript.mk hidden in any other definition);
#   * each triple is re-submitted to the pinned verifier built from this tree
#     (native/credential-signature-verifier, `verify KEY FRAME SIGNATURE`): the
#     answer must be exactly `verified`;
#   * control, per triple: the same triple with the signature's last byte flipped
#     must read exactly `invalid` (a verifier that says yes to everything fails here);
#   * at least one transcript must exist (the fixture's);
#   * self-test, every run: one recorded answer is flipped -- the first triple, its
#     signature's last byte changed, presented as if the transcript recorded it as
#     `verified` -- and the checker must FAIL on exactly that triple. A checker that
#     cannot go red on a forged answer is not a gate.
# Requires AxiomCensusResearch built (lake-build); builds the verifier with cargo
# into $CARGO_TARGET_DIR (default <repo>/target-gates, shared with the journey gate).
set -uo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root" || exit 2
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$root/target-gates}
rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
die() { echo "native-transcripts: FAIL: $*"; exit 1; }
mkdir -p "$root/build-logs"
(cd native/credential-signature-verifier && cargo "+$rust" build --release --locked -j "${LOCAL_GATES_CARGO_JOBS:-6}") \
  >"$root/build-logs/transcripts-cargo.log" 2>&1 || die "cargo build native/credential-signature-verifier (build-logs/transcripts-cargo.log)"
verifier=$CARGO_TARGET_DIR/release/minidregg-credential-signature-verifier
[ -x "$verifier" ] || die "no verifier at $verifier"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/native-transcripts.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
lake env lean scripts/NativeTranscripts.lean >"$tmp/list.txt" 2>"$tmp/list.err" \
  || { cat "$tmp/list.txt" "$tmp/list.err"; die "scripts/NativeTranscripts.lean refused (see above)"; }
summary=$(grep -a '^TRANSCRIPTS' "$tmp/list.txt") || die "no TRANSCRIPTS summary line"
transcripts=$(cut -f2 <<<"$summary"); triples=$(cut -f4 <<<"$summary")
[ "$transcripts" -ge 1 ] && [ "$triples" -ge 1 ] || die "no transcript in the tree ($summary); the fixture's is missing"
cat >"$tmp/check.py" <<'PY'
import subprocess, sys, os
verifier, tmp = sys.argv[1], sys.argv[2]
bad = 0; seen = 0
def answer(k, f, s):
    paths = []
    for name, data in (("key", k), ("frame", f), ("signature", s)):
        p = os.path.join(tmp, name + ".bin"); open(p, "wb").write(data); paths.append(p)
    r = subprocess.run([verifier, "verify"] + paths, capture_output=True)
    return r.returncode, r.stdout.decode(errors="replace"), r.stderr.decode(errors="replace")
for line in sys.stdin:
    if not line.startswith("TRIPLE\t"): continue
    _, const, idx, k, f, s = line.rstrip("\n").split("\t")
    k, f, s = bytes.fromhex(k), bytes.fromhex(f), bytes.fromhex(s)
    seen += 1
    got = answer(k, f, s)
    mutated = s[:-1] + bytes([s[-1] ^ 1])
    ctl = answer(k, f, mutated)
    ok = got == (0, "verified\n", "") and ctl == (0, "invalid\n", "")
    print(f"{'PASS' if ok else 'FAIL'}\t{const}[{idx}]\tverified={got!r}\tflipped={ctl!r}\tframe={len(f)}B")
    bad += not ok
print(f"native-transcripts: {seen} triple(s), {bad} failing")
sys.exit(1 if bad or not seen else 0)
PY
# self-test: a forged recorded answer must turn the checker red
python3 - "$tmp/list.txt" "$tmp/forged.txt" <<'PY'
import sys
for line in open(sys.argv[1]):
    if line.startswith("TRIPLE\t"):
        tag, const, idx, k, f, s = line.rstrip("\n").split("\t")
        forged = s[:-2] + "%02x" % (int(s[-2:], 16) ^ 0x80)
        open(sys.argv[2], "w").write("\t".join([tag, "SELFTEST-forged-" + const, idx, k, f, forged]) + "\n")
        break
else:
    sys.exit("self-test: no triple to forge")
PY
python3 "$tmp/check.py" "$verifier" "$tmp" <"$tmp/forged.txt" >"$tmp/forged.log" 2>&1
forged_rc=$?
if [ "$forged_rc" = 1 ] && grep -q "^FAIL	SELFTEST-forged-" "$tmp/forged.log" && grep -q "1 triple(s), 1 failing" "$tmp/forged.log"; then
  echo "native-transcripts: self-test PASS (a forged recorded answer is refused: $(grep -m1 '^FAIL' "$tmp/forged.log" | cut -f1-3))"
else
  cat "$tmp/forged.log"; die "self-test: a forged recorded answer was NOT refused (exit $forged_rc)"
fi
python3 "$tmp/check.py" "$verifier" "$tmp" <"$tmp/list.txt"
rc=$?
[ "$rc" = 0 ] || die "a transcript triple is not the verifier's answer (above)"
echo "native-transcripts: PASS ($transcripts transcript(s), $triples triple(s); verifier $(sha256sum "$verifier" | cut -c1-16))"
