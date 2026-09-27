# Qualified fn own-R stable binding image (2026-09-27 UTC)

This image follows the [strict injection-prefix image](../2026-09-26-mini-provider-ownr-prefix/README.md)
with a single `Host.Main` change, SHA-256
`4623088c835ce931663256f47564f2c8d0e288e1cd3ad61a48063f03a4ba4141`.
The retained control binding now uses the stable configured `pin.fnBinary`
instead of a temporary private executable path. The source hunk was
narrow-compiled in an independent qualified snapshot and root committed the
corresponding composite source as `2b6db7d`.

The guarded Main-only suffix build checked the successful prefix baseline,
171 unchanged imported modules, 2,933 package modules, source hashes, Lean
artifacts, and toolchain. It compiled `Host.Main`, linked 3,105 response
objects, and rechecked all 172 source modules and recorded output artifacts.
The no-argument `usage_exit=1` is expected.

The Mac executable is
`/tmp/minidregg-overnight-20260926/minidregg-host-provider-ownr-stable`,
SHA-256 `c37a35073b9d19ac342d91ba0a071b3a732f51b0f5f0991fc995ec64573edcff`.
See the [manifest](mac-manifest.txt), [source hashes](mac-source-sha256.txt),
[artifact hashes](mac-artifact-sha256.txt), and
[incremental validation](mac-incremental-validation.txt). This is a fn-only
source cut, separate from the composite grain birth image. Old accepted tag9
history bound to the vanished temporary executable remains fail-closed; the
fresh A runtime gate uses a new Store.
