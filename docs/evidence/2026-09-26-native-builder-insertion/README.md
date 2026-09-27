# Native builder inserted-closure regression (2026-09-27 UTC)

`scripts/build-native-host.sh` SHA-256
`1ea0380d1c4642ddd469018ecf93f78d4a0100f300b1c80ae9b7fb4e44f91f96`
adds an explicit inserted-module allowlist to guarded suffix reuse. It
recomputes the native import closure, requires the reused prefix to retain
its exact order, requires the old modules to remain present, checks the exact
set of declared insertions, and refuses changed package requirements. It
checks baseline source, Lean/C artifact, package artifact, toolchain, and
binary hashes before compiling the entire new suffix. New modules before
the restart and undeclared changes are refused. `bash -n`, `shellcheck`, and
Bash 3.2 option parsing passed.

The private positive regression cloned the completed own-R source and used
the certified provider-metering Mac build as baseline:

```sh
MINIDREGG_CYCLE_DIR=/tmp/minidregg-overnight-20260926 \
MINIDREGG_NATIVE_JOBS=2 MINIDREGG_LEAN_THREADS=2 \
scripts/build-native-host.sh \
  --incremental-suffix-from /tmp/minidregg-provider-metering-op6-native \
    /tmp/minidregg-overnight-20260926/build-local-provider-metering-op6 \
    Kernel.FnOriginOutbox \
  --allow-unchanged-restart \
  --allow-inserted-module Kernel.FnCatalogOwnRProgress \
  --allow-suffix-change Host.FnInboxView \
  --allow-suffix-change Host.Main \
  --output /tmp/minidregg-overnight-20260926/build-insert-positive-ownr \
  --binary /tmp/minidregg-overnight-20260926/minidregg-host-insert-positive-ownr
```

The guard validated 157 reused prefix modules and 2,933 package objects;
15 suffix modules compiled, 3,105 objects linked, and all 172 source hashes
and four output artifacts were reverified. The [source manifest](positive-source-sha256.txt)
is byte-identical (SHA-256 `f7b62df2a539f96e9b2fa3c0025ae0554bf3936bc976caa0bc8c1cf96479399e`)
to the independent [full own-R build](../2026-09-26-mini-provider-ownr/README.md).
See the [positive manifest](positive-manifest.txt), [validation](positive-validation.txt),
[changed sources](positive-changed-source-sha256.txt), [artifacts](positive-artifact-sha256.txt),
and [module order](positive-source-modules.txt). The linked binary SHA differs
from the full build; this check supports source and artifact provenance, not
byte-identical executables or a runtime acceptance claim.

Three private negative invocations all exited 65 before compilation:

- [Restart after insertion/reorder](refuse-early-restart.log): `Host.FnInboxView`
  was too late to reuse the preceding reordered prefix.
- [Undeclared insertion](refuse-undeclared-insertion.log): declaring
  `Kernel.NotInClosure` did not match the actual new module.
- [Changed reused source](refuse-changed-reused-source.log): a comment appended
  to private `Compiler/PredCompile.lean` changed a prefix source. The same
  shell restored the private file and verified its original SHA-256
  `46d082cbbe605df7472a5181f90d180f172a6ef960ec1af78921a39fc5b0c052`.

The [refusal verdict](refusals-verdict.txt) is `three_refusals_PASS`. No
release image or live service used the experimental mode in this regression.
