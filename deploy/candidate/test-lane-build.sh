#!/usr/bin/env bash
# lane-build.sh pack, run for real on a synthetic repo with stub role binaries and PATH shims for the
# toolchain version probes: no Lean, no Rust build. Needs git, jq, python3, readelf, sha256sum.
#   deploy/candidate/test-lane-build.sh [SCRATCH_DIR]      (default: a fresh mktemp -d)
# Cases: (1) a lane whose roles were built at HEAD packages, consent pinned; (2) a compiled input that
# changed after the Rust build is REFUSED naming the file; (3) a missing consent artifact is REFUSED;
# (4) a tracked change left uncommitted is REFUSED.
set -euo pipefail
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
S=${1:-$(mktemp -d)}
[ ! -e "$S/lane" ] || { echo "test-lane-build: $S/lane exists" >&2; exit 64; }
for t in git jq python3 readelf sha256sum; do command -v "$t" >/dev/null || { echo "need $t" >&2; exit 66; }; done
mkdir -p "$S/lane/src/native/resource-client/src" "$S/lane/src/deploy/candidate" "$S/lane/artifacts" "$S/lane/logs" "$S/lane/native-out" "$S/shim"
cd "$S/lane/src"
git init -q
cp "$HERE/package.py" deploy/candidate/
# Keep the synthetic archive complete for the packager's current shipping contract.
python3 - <<'SOURCE'
from pathlib import Path
import runpy
for member, _ in runpy.run_path("deploy/candidate/package.py")["SCRIPTS"].values():
    path = Path(member)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("{}\n" if path.suffix == ".json" else f"stub {member}\n")
SOURCE
echo 'channel = "stub-1"' | sed 's/^/[toolchain]\n/' >rust-toolchain.toml
echo "leanprover/lean4:v0.0.0" >lean-toolchain
printf '# synthetic workspace lock; no Rust build\nversion = 4\n' >Cargo.lock
echo "pub fn f() {}" >native/resource-client/src/lib.rs
: >.minidregg-native-snapshot
echo ".minidregg-native-snapshot" >.gitignore
G=(git -c user.name=t -c user.email=t@t -c commit.gpgsign=false)
"${G[@]}" add -A; "${G[@]}" commit -q -m base
# shims for the version probes pack makes
for t in lean lake cargo cc; do printf '#!/bin/sh\necho "stub-%s 0.0"\n' "$t" >"$S/shim/$t"; chmod +x "$S/shim/$t"; done
cat >"$S/shim/rustc" <<'RUSTC'
#!/bin/sh
cat <<'VERSION'
rustc stub 0.0
commit-hash: 0000000000000000000000000000000000000000
host: x86_64-unknown-linux-gnu
release: 0.0.0
LLVM version: 0.0.0
VERSION
RUSTC
chmod +x "$S/shim/rustc"
# pack consumes flags recorded by the builder, not the packager's environment.
printf '%s\n' '--remap-path-prefix=/synthetic=/minidregg' >"$S/lane/logs/rust-build.flags"
export PATH="$S/shim:$PATH" LANE_DIR="$S/lane"
for n in minidregg-host minidregg-client-consent $(python3 "$HERE/package.py" --rust-roles | awk '{print $3}'); do
  echo "stub binary $n" >"$S/lane/artifacts/$n"
done
echo "stub manifest" >"$S/lane/native-out/manifest.txt"
printf '%s\n' '-O0 -DSYNTHETIC_BUILD' >"$S/lane/native-out/compile-args.txt"
git rev-parse HEAD | tee "$S/lane/logs/host-build.commit" >"$S/lane/logs/rust-build.commit"
fails=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fails=$((fails + 1)); }

if "$HERE/lane-build.sh" pack "$S/cand1" >"$S/1.out" 2>"$S/1.err"; then
  jq -e '.binaries.consent.path == "bin/minidregg-client-consent" and
    (.clients["x86_64-unknown-linux-gnu"].consent | type == "object") and
    (.outputs["bin/minidregg-host"].build |
      .flags.rust.RUSTFLAGS == "--remap-path-prefix=/synthetic=/minidregg" and
      .flags.native.compileArgs == "-O0 -DSYNTHETIC_BUILD\n" and
      (.rustcVerbose | contains("commit-hash:")))' "$S/cand1/provenance.json" >/dev/null \
    && [ -f "$S/cand1/bin/clients/x86_64-unknown-linux-gnu/minidregg-client-consent" ] && ok "(1) built-at-HEAD lane packages with the consent pair" \
    || bad "(1) packaged, but the consent pair is not pinned: $(cat "$S/1.err")"
else bad "(1) pack failed: $(cat "$S/1.err")"; fi

echo "pub fn g() {}" >>native/resource-client/src/lib.rs
"${G[@]}" commit -q -am "change a compiled input after the build"
if "$HERE/lane-build.sh" pack "$S/cand2" >"$S/2.out" 2>"$S/2.err"; then bad "(2) packaged roles built before a compiled input changed"
elif grep -q 'native/resource-client/src/lib.rs' "$S/2.err" && [ ! -e "$S/cand2" ]; then ok "(2) a compiled input changed after the build: refused, names the file, no output"
else bad "(2) refused for the wrong reason: $(cat "$S/2.err")"; fi

git rev-parse HEAD | tee "$S/lane/logs/host-build.commit" >"$S/lane/logs/rust-build.commit"
mv "$S/lane/artifacts/minidregg-client-consent" "$S/consent.keep"
if "$HERE/lane-build.sh" pack "$S/cand3" >"$S/3.out" 2>"$S/3.err"; then bad "(3) packaged without the consent artifact"
elif grep -q 'missing .*minidregg-client-consent' "$S/3.err" && [ ! -e "$S/cand3" ]; then ok "(3) missing consent artifact: refused by name, no output"
else bad "(3) refused for the wrong reason: $(cat "$S/3.err")"; fi
mv "$S/consent.keep" "$S/lane/artifacts/minidregg-client-consent"

echo "// edit" >>native/resource-client/src/lib.rs
if "$HERE/lane-build.sh" pack "$S/cand4" >"$S/4.out" 2>"$S/4.err"; then bad "(4) packaged a dirty tree"
elif grep -q 'uncommitted' "$S/4.err"; then ok "(4) a dirty tree: refused"
else bad "(4) refused for the wrong reason: $(cat "$S/4.err")"; fi
[ "$fails" = 0 ] && echo "test-lane-build: all cases passed" || { echo "test-lane-build: $fails FAILED" >&2; exit 1; }
