# Private resident SPK INSTALL component gate — 2026-09-27

This source cut adds a two-phase operator INSTALL path. `install-prepare`
verifies an operator-private copy of the signed SPK under a bounded unit,
compares it with Mini's source-authored descriptor, and submits exactly one
current-image BEGIN (50/51→22) and claim (52/53→26). It retains the original
ingress, committed claim frame, receipt identity, and a private prepared marker.
The separately root-only `deploy/spk-host/spk-ingest` publishes the same raw
SHA-256. `install-complete` reparses the protected published image, freshly
inspects the retained committed claim, compares signed package/bridge/schema
fields, signs Mini's `materialized` report, and submits exactly one completion
(44/45→38). No INSTALL path starts the app or binds HTTP. An uncertain native
send retains its attempt directory and refuses automatic retry.

The new `deploy/spk-host/spk-install-phase` runs each operator phase as a
stopped, private, offline transient unit with the exact pinned host binary,
operator-owned config/journal, `MemoryMax=1G`, `RuntimeMaxSec=900`,
`TasksMax=16`, `CPUQuota=100%`, and read-only system files except the journal.
This bound covers Bread's whole-block XZ parse memory, which the archive output
limit alone does not bound. It checks the exact `systemd-run --wait` unit verdict.
The root ingest remains a separate action; a preexisting immutable matching
image may be reused only after the same physical verifier passes. The phase
wrapper passed `bash -n` and `shellcheck` locally.
Because the unit uses `PrivateTmp=yes`, INSTALL refuses direct source, image,
Host, config, socket, and signer paths under `/tmp` or `/var/tmp`. A selected
deployment must keep the Mini operator socket and any helper paths referenced
by its config reachable inside that unit, for example under protected `/run`
and `/var/lib`; no selected deployment config was run in this cut.

Source SHA-256 of the root-reviewed INSTALL-only commit. The shared working
tree also has later resident/API changes in `main.rs` and `lib.rs`; those were
excluded from this commit and are not covered by this table.

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/install_service.rs` | `2f04150e2b85f07bfa557cca58c9e613dfa1567d38cb7165b3d6e2b24051ea21` |
| `native/spk-host/src/descriptor_native.rs` | `64cd51e0a73234f96859e6879bf6a26ffc1f7a9e3b17db16a7c5a386c51e7cab` |
| `native/spk-host/src/claim_descriptor.rs` | `8b465dbece92e9044e19519842043530b9dad2d4e16c5151fb1d2b43c10f42fd` |
| `native/spk-host/src/claim_native.rs` | `c0f302b18aecb92fc18249fc1d6b42afeb90920a75846dae8352eb0bc53d8497` |
| `native/spk-host/src/completion_native.rs` | `0c6214fd4877e9f37d252f491a16fc9a26eb4363213fd0987dc76d7abdf6fdd6` |
| `native/spk-host/src/materialize.rs` | `9ff8ec603bb083efcd346ffa2f88feaed8121abfbf8f4d577678d1c3684d0602` |
| `native/spk-host/src/main.rs` | `cb57c866d9f96392f4f444c747bac10993a248527ba131d83e07e1e534148d74` |
| `native/spk-host/src/lib.rs` | `8703b378ba5089bbc25022e41b9f7c10e32723ce9c35a797440b1dbb336863b7` |
| `deploy/spk-host/spk-install-phase` | `7a182adc4ad4eec710dde08de10192d5bbfb6076572d1248f30205a920597c1c` |

Private Persvati snapshot:
`/tmp/mini-spk-install-source-20260927/native/spk-host` with locked Cargo
dependencies and two build jobs, reusing only the earlier qualifier target
cache. Before the final cancellation/preflight edits, full library nextest was
80/80 PASS (`nextest.log`, SHA-256 `44de5245b7fc05da5fecce47aef0efdad27541c3dd5d8db1fbdce81052b89d2a`).
After the edits, focused INSTALL/agent/caller EOF tests were 8/8 PASS
(`focused.log`, SHA-256 `fc37b66e4df1e87f201442ae479a81631e031cb42d7c2de10b0da6148d290ec2`),
the final protected-ancestor INSTALL change passed its focused test 1/1
(`install-focused.log`, SHA-256 `e0ae0740d4d0b33d7251e8483a2e907e94c2377fd5dd31bc55fe2acae3c733f6`),
and strict `cargo clippy --locked --all-targets -- -D warnings` passed on that
earlier source (`clippy-r3.log`, SHA-256 `2df865c169bb03e0739f8bab482929912dbdc52d2b5ee11ef595b3104d7cae9f`).
The later `PrivateTmp` path refusal and its test have not yet been rerun on
Linux because Persvati fell below the shared 8 GiB disk floor.
The snapshot included staged agent API modules; their latest reverse-client
changes are a later cut and are not covered by these logs.

One physical read-only check used the exact root-owned GitWeb image at
`/var/lib/minidregg/spk/packages/sha256-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`:
image directory owner/mode `0:555`, package and manifest `0:444`. A private
operator UID 1000 helper called `verify_installed_spk(image, app_uid=1001)` in
`mini-spk-verify-image-20260927` with `MemoryMax=1G`, `RuntimeMaxSec=120`,
`PrivateNetwork=yes`, `ProtectSystem=strict`. It returned raw SHA-256
`2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`,
length `14045864`, signed AppID
`6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash`, version `10`.
The unit reported success/status 0, 175.3 MiB peak, then unloaded with MainPID
0. Log `/tmp/mini-spk-install-source-20260927/verify-image-unit.log` SHA-256
`dd266d56e1d0db1e55aa13266bcf4789779c5dc49979d2c90d1f0e8c3ab040c4`.
The helper was private snapshot code, not a product route.

No Mini INSTALL/START admission or app execution occurred in this cut. The
certified `bf04c29` native Host does not include the later generic SPK
descriptor author/inspector; a new source-qualified native binary and a fresh
Store configured with `completionCustodianKey` at genesis are required for the
actual lifecycle acceptance. A lost op38 reply remains a held completion with
no HTTP exposure; audited recovery is a separate liveness task.
