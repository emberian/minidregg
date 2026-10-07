#!/usr/bin/env bash
# check-kernel-transport.sh -- the kernel facet is handed out only by the routes that commit
# through `ActivitySeatEnd.finish` / `SeatStore.checkInert` (scripts/KernelTransportCensus.lean).
#
# Every invariant theorem of the protected coordinates (`domain_holds_forever`, the checkpoint and
# upgrade invariants) is stated over `Step`; it describes the deployment only while the definitions
# using `Config.kernelTransport` / `ControlFacet.objectKernel` are exactly the census rows.
#
# Before the real run it tests the instrument, every time (copies in a temp dir; the tree is never
# edited): each plant below is appended to a copy of the census and the run MUST fail naming it:
#   (a) a new route passing `config.kernelTransport`;
#   (b) a route building the facet by hand: `config.sourceGate (some .objectKernel)`;
#   (c) a route decoding a facet: `ControlFacet.ofNat 2`;
#   (d) an allowed row renamed to a definition that does not use it: the run must fail as STALE.
# Requires Kernel.NativeHost and Kernel.NativeHostReplay built (it never builds).
#
# usage: scripts/check-kernel-transport.sh [--no-self-test]
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
census=scripts/KernelTransportCensus.lean
run() { lake env lean "$1" 2>&1; }

if [ "${1:-}" != "--no-self-test" ]; then
  tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
  plant() {  # NAME EXPECT-SUBSTRING LEAN-TEXT
    local name=$1 expect=$2 text=$3 copy="$tmp/Plant_$1.lean"
    python3 - "$census" "$copy" "$text" <<'PY'
import sys
src, dst, text = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(src).read()
anchor = 'open KernelTransportCensus in\nrun_cmd do'
assert s.count(anchor) == 1, 'census anchor moved'
open(dst, 'w').write(s.replace(anchor, text + '\n\n' + anchor))
PY
    if out=$(run "$copy"); then
      echo "check-kernel-transport: INSTRUMENT BROKEN: plant $name did not fail"; echo "$out" | tail -5; exit 1
    fi
    if ! grep -q "$expect" <<<"$out"; then
      echo "check-kernel-transport: INSTRUMENT BROKEN: plant $name failed without naming '$expect'"; echo "$out" | tail -5; exit 1
    fi
    echo "check-kernel-transport: plant $name red (as it must be)"
  }
  plant route  'Minidregg.KTPlant.route uses' \
    'def Minidregg.KTPlant.route (c : Minidregg.Kernel.NativeHost.Config) := c.kernelTransport'
  plant byhand 'Minidregg.KTPlant.byHand uses' \
    'def Minidregg.KTPlant.byHand (c : Minidregg.Kernel.NativeHost.Config) :=
  { c.transport with sourceGate := c.sourceGate (some .objectKernel) }'
  plant decode 'Minidregg.KTPlant.decode uses' \
    'def Minidregg.KTPlant.decode : Minidregg.Kernel.NativeHost.ControlFacet := Minidregg.Kernel.NativeHost.ControlFacet.ofNat 2'
  # (d) stale: point an allowed row at a definition that does not use it
  copy="$tmp/Stale.lean"
  python3 - "$census" "$copy" <<'PY'
import sys
s = open(sys.argv[1]).read()
old = '``Minidregg.Kernel.NativeHost.seatSubmitLoaded,'
assert s.count(old) == 1, 'seat row moved'
open(sys.argv[2], 'w').write(s.replace(old, '``Minidregg.Kernel.NativeHost.Config.transport,'))
PY
  if out=$(run "$copy"); then echo "check-kernel-transport: INSTRUMENT BROKEN: stale row passed"; exit 1; fi
  grep -q 'census is stale' <<<"$out" || { echo "check-kernel-transport: INSTRUMENT BROKEN: stale not named"; exit 1; }
  echo "check-kernel-transport: plant stale red (as it must be)"
fi

out=$(run "$census") || { echo "$out"; echo "check-kernel-transport: RED"; exit 1; }
echo "$out" | grep 'kernel-transport census'
echo "check-kernel-transport: GREEN"
