#!/usr/bin/env bash
# scripts/build-mini-kernels.sh -- the Rust kernels the compiled Lean calls through @[extern]
# (native/mini-kernels; HOT-PATH 2d). Produces, under .lake/native/:
#   libmini_kernels.a          the Rust kernels (cargo staticlib)
#   mini_kernels_lean.o        the Lean ByteArray shim (native/mini-kernels/shim), compiled with leanc
#   link-inputs.txt            those two, one per line: link inputs of EVERY Lean executable and
#                              shared library (the lakefile's moreLinkArgs; build-native-host.sh appends
#                              them to its response file; channel-lib/build.sh links them)
#   libmini_kernels_lean.so    the shim, the kernels AND the compiled objects of the seam's module
#                              closure (Init + Spec, Fast, Native, Midstate, Core, Kmac256,
#                              CredentialSignatureKernel), for `lean --load-dynlib`
#                              at elaboration and `lean --run`: the interpreter resolves an
#                              `@[extern]` declaration by its module's compiled wrapper
#                              (`l_..._cshake256Kernel___boxed`), never by the C symbol, so
#                              evaluating anything that hashes or verifies needs these objects
#                              loaded (the lakefile passes the path to every lean).
# Two stages, because Lake passes --load-dynlib to the very lean that compiles the seam modules:
# stage 1 is the shim and the kernels alone (enough for lean to start); the module objects are then
# built by Lake and stage 2 relinks the library with them. Re-run after editing any of those modules
# (a stale library makes interpreted or compiled evaluation use the old kernel). Idempotent.
set -euo pipefail
root=$(cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$root"
export PATH=$HOME/.cargo/bin:$HOME/.elan/bin:$PATH
out=$root/.lake/native
mkdir -p "$out"
target=${CARGO_TARGET_DIR:-$root/target}
cargo build --release --locked -p mini-kernels --target-dir "$target" >"$out/cargo.log" 2>&1 || {
  echo "build-mini-kernels: cargo build failed; see $out/cargo.log" >&2; tail -n 20 "$out/cargo.log" >&2; exit 1; }
cp -f "$target/release/libmini_kernels.a" "$out/libmini_kernels.a"
prefix=$(lean --print-prefix)
leanc -c -O2 -fPIC -o "$out/mini_kernels_lean.o" native/mini-kernels/shim/mini_kernels_lean.c
printf '%s\n' "$out/mini_kernels_lean.o" "$out/libmini_kernels.a" > "$out/link-inputs.txt"
case "$(uname -s)" in
  Darwin) undefined=(-Wl,-undefined,dynamic_lookup) ;;
  *) undefined=(-Wl,--allow-shlib-undefined) ;;
esac
link_dynlib() {
  leanc -shared -o "$out/libmini_kernels_lean.so.tmp" "$out/mini_kernels_lean.o" "$@" "$out/libmini_kernels.a" \
    -L"$prefix/lib/lean" -lleanshared "${undefined[@]}" -Wl,-rpath,"$prefix/lib/lean"
  mv -f "$out/libmini_kernels_lean.so.tmp" "$out/libmini_kernels_lean.so"
}
[ -f "$out/libmini_kernels_lean.so" ] || link_dynlib
# The seam module closure (Init + these), as Lake's own export objects: the code generator names a
# declaration `lp_minidregg_...` (the package prefix), and that is the wrapper the interpreter looks
# up when lean runs under Lake's module setup (a bare `lean FILE` has no package and looks for `l_...`:
# check these modules with `lake build`/`lake env lean`, never bare `lean`).
seam=(Theory.Sp800185Cshake256Spec Theory.Sp800185Cshake256Fast Theory.Sp800185Cshake256Native
  Theory.Sp800185Cshake256Midstate
  Theory.Sp800185Cshake256Core Compiler.Sp800185Kmac256 Compiler.CredentialSignatureKernel)
targets=()
for module in "${seam[@]}"; do targets+=("$module:o.export"); done
lake build "${targets[@]}" >"$out/lake.log" 2>&1 || {
  echo "build-mini-kernels: lake build of the seam objects failed; see $out/lake.log" >&2; tail -n 20 "$out/lake.log" >&2; exit 1; }
objects=()
for module in "${seam[@]}"; do
  object=".lake/build/ir/${module//.//}.c.o.export"
  [ -f "$object" ] || { echo "build-mini-kernels: missing seam object $object" >&2; exit 1; }
  objects+=("$object")
done
link_dynlib "${objects[@]}"
shasum -a 256 "$out/libmini_kernels.a" "$out/mini_kernels_lean.o" "$out/libmini_kernels_lean.so" | tee "$out/SHA256SUMS"
