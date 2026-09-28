# GitWeb human journey helper: focused source check

The new `native/spk-host/src/bin/gitweb-human-journey.rs` was checked in an
isolated private snapshot of committed SPK source `8d7a3f8` plus only this new
bin. Exact helper SHA-256:
`71170393aed441bb86a411765785dc976aeed74b66328f45064b3a0861112991`.
The companion operator command contract at
`scripts/gitweb-shared-journey/README.md` had SHA-256
`be06effecc9f73db8b3f82ca633d9f29d074350a7d7a44bcfa0fc15ae98efaee`.
The builder compared 95/95 committed source files before the focused gate.

On Persvati, the isolated snapshot ran:

```text
cargo check --locked --offline --bin gitweb-human-journey
cargo clippy --locked --offline --bin gitweb-human-journey -- -D warnings
```

Both passed. The original logs are copied here as `check.log` and
`clippy.log`, each SHA-256
`97c29315c2a903d01076239f8242c099764cee004d2b55f8d931521239f7e107`.
The builder's original private location was
`/home/ember/build/minidregg-spk-host-gitweb-check-evidence/`. Earlier
compiler/style failures remain there as r1/r2 logs and were not reclassified.

This is a source check only. No release binary, native Unix-entrance component
probe, resident START, Git request, Mini dispatch, human view, or fn export is
claimed. The first live mutating Git request remains gated on a source-matched
component probe and the installed resident app/tickets.
