# Event28 session enrollment custody client

This source cut adds four private Mini commands: `session-enrollment-plan`,
`session-enrollment-seal`, `session-enrollment-submit`, and
`session-enrollment-lookup`. Mini retains the exact Host-authored Request and
Plan, signs each ordered source header using an explicitly approved private
key path, and retains the exact event28 Ingress. It writes a durable submit
marker before its sole op84 send. A lost response can only use op85 with the
retained Ingress; op85 is receipt-only. Operator transport accepts op82/84/85
only with bounded nonempty payloads and op83 only with a bounded nonempty
LE32 pair. The public socket refuses all four.

The plan command takes `--host`, `--config`, `--operator-socket`, a private
source `--request` JSON, and a new private `--dir`. Seal takes `--attempt`
and a private `--approval` JSON with type
`minidregg-session-enrollment-approval-v1`, exact `requestSha256`,
`planSha256`, `planInspectionSha256`, and `signers` in source slot order. Each
signer supplies the slot `role`, `index`, `keyId`, `keyEpoch`,
`headerSha256`, private `keyPath`, and `publicKey`. Submit and lookup take
only `--attempt`; the retained attempt selects every native byte and socket.

The isolated Rust snapshot was the committed `e1a36c0` resource-client source
with only `main.rs`, `transport.rs`, and new `session_enrollment.rs` overlaid.
On Persvati, under two capped user units, these commands passed:

```sh
cargo nextest run --locked --offline -E 'test(/session_enrollment/)'
cargo clippy --locked --offline --all-targets -- -D warnings
```

The [nextest log](nextest.log) shows 4/4 focused tests passing; the
[Clippy log](clippy.log) shows the strict all-target gate completed. `cargo
fmt` and `git diff --check` also passed locally. The three source and two
log SHA-256 values are in [SHA256SUMS](SHA256SUMS).

The matching Host event28 author/inspect and op82–85 source gate was reported
direct-Lean green by its owner, but a combined native build and event28 Store
acceptance are still pending. This cut did not touch the live r3 Store. Source
observation headers use the participant command subject; participant app,
manifest, and ticket observe capabilities must be admitted before an
enrollment can be signed and accepted. Separate local key paths do not waive
that source condition.
