# Sealed fresh STOP claim to checked physical fence

This source cut joins the sealed `FreshStopClaim` to the existing checked hostd fence. `fence_exact` is callable only with the type constructed after a fresh installed/CAS-winner op26 STOP response and the current verified `inspect-stop-claim` comparison. It projects the **prior running** generation, unit, image, invocation ID and control group, compares the retained Running journal and root volume witness, fsyncs the exact private attempt marker, and invokes `fence_and_stop_manager_checked`. The hostd hook repeats the identity and volume checks under its journal lock before any manager action and retains Fenced on uncertainty. The new STOP operation generation is never used as the physical target generation.

The source was copied into an isolated hbox crate snapshot at `/tank/dregg-build/mini-spk-v3-stop-agent`; the shared tree was not modified for the test. Exact source dependencies: `lifecycle_v3_stop_native.rs` SHA-256 `0e9f7e6e48ad02dab3f255479e6961c18d86b5a9cf92e0c9a8f59ab2a1896ab4`, sealed `lifecycle_v3_stop_claim_native.rs` `e2449d98792875835b4cfe86778e3a83a8c71721beeb2e222c4829ba61670b4c`, and checked `hostd.rs` `4e4b807f7ca8f8252f515125548602cf893c3cbbd94f99999f3f75259c134189`.

The bounded commands in that snapshot were:

```sh
CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-stop-agent/target CARGO_BUILD_JOBS=2 cargo nextest run --offline --locked --lib -E 'test(/stop_target_/)'
CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-stop-agent/target CARGO_BUILD_JOBS=2 cargo clippy --offline --locked --all-targets -- -D warnings
```

The first returned 3/3 PASS (run `cdc13573-777b-40ce-9153-f97050984d6b`); strict Clippy passed. Exact retained logs are `nextest.log` and `clippy.log`. `rustfmt --edition 2021 --check native/spk-host/src/lifecycle_v3_stop_native.rs` was clean. `SHA256SUMS` pins this source and the logs.

This is a source and focused-component gate, **not** a physical STOP acceptance. There is no source-matched linked Host/SPK-host pair or callable STOP entry, and no systemd action was run. The initial `fence_exact` path requires a retained Running journal. A crash after the exact marker or Fenced write remains fail-closed until a separate recovery-only path can reopen the same incarnation and audit or resume its already-fenced stop; historical op27 receipt lookup cannot mint a new fresh fence. The complete one-Store acceptance recipe remains in `docs/evidence/2026-09-27-spk-lifecycle-stop-acceptance/PLAN.md`.
