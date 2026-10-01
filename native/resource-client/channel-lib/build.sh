#!/usr/bin/env bash
# usage: native/resource-client/channel-lib/build.sh [OUT.so]   (from any directory)
#
# Links libminidregg-channel.so: the compiled objects of Kernel.DomainEpochExport and its whole import
# closure (this workspace's and its packages'; the toolchain's own modules come from libleanshared), the
# C shim, and the toolchain's shared Lean runtime. `mini relay --lean-lib` dlopens it. Build the module
# objects first (the closure is these eight; build.sh refuses if it grows past Init + this workspace):
#   lake build Compiler.Sp800185Cshake256Core:o.export Pred.HashEqDigest:o.export Theory.Channel.Cell:o.export \
#     Theory.Channel.Lease:o.export Theory.Channel.Trace:o.export Theory.Channel:o.export \
#     Kernel.DomainEpoch:o.export Kernel.DomainEpochExport:o.export
# A missing object refuses the link by name; nothing is compiled here except the shim.
set -euo pipefail
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
cd "$root"
export PATH=$HOME/.elan/bin:$PATH
out=${1:-$root/.lake/build/lib/libminidregg-channel.so}
prefix=$(lean --print-prefix)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake env lean --run "$here/closure.lean" Kernel.DomainEpochExport >"$tmp/oleans"
# The runtime closure is Init + this workspace's channel modules. Anything else (Lean, Std, Mathlib,
# Batteries, ...) means a heavy import crept back in: refuse by name rather than ship a 490 MB member.
# mdc_init (shim.c) initialises only the runtime, which is correct exactly when `Lean` is not reached.
grep -v -e "^$prefix/lib/lean/Init/" -e "^$prefix/lib/lean/Init.olean$" -e "^$root/.lake/build/lib/lean/" "$tmp/oleans" >"$tmp/foreign" || true
if [ -s "$tmp/foreign" ]; then
  echo "refused: the channel runtime closure reaches $(wc -l <"$tmp/foreign") modules outside Init and this workspace, e.g.:" >&2
  head -5 "$tmp/foreign" >&2
  exit 1
fi
grep -v "^$prefix/" "$tmp/oleans" | sed 's|/build/lib/lean/|/build/ir/|; s|\.olean$|.c.o.export|' >"$tmp/objs"
missing=0
while read -r o; do [ -f "$o" ] || { echo "missing object: $o" >&2; missing=1; }; done <"$tmp/objs"
[ "$missing" = 0 ] || exit 1
echo "closure: $(wc -l <"$tmp/oleans") modules, $(wc -l <"$tmp/objs") package objects" >&2
leanc -c -O2 -fPIC -o "$tmp/shim.o" "$here/shim.c"
mkdir -p "$(dirname "$out")"
leanc -shared -o "$out.tmp" "$tmp/shim.o" @"$tmp/objs" -L"$prefix/lib/lean" \
  -lInit_shared -lleanshared_1 -lleanshared_2 -lleanshared -Wl,-rpath,"$prefix/lib/lean"
mv -f "$out.tmp" "$out"
sha256sum "$out"
