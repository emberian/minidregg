# Agent payer-signature custody source checkpoint — 2026-09-27

This adds a controller-only `mini agent-payer-sign` command. It requires the exact private original reserve attempt, its retained native confirmation, a paid Plan, a separate operator approval, and the controller's private seed. Before signing, the pinned Host re-inspects the reserve and paid Plans, authors the expected paid request from the original request/context/receipt index, and reproduces the supplied paid Plan byte-for-byte through private op48 at the current verified image. The client compares the complete source-projected context, fixed selectors, full HTTP bytes, reserve receipt/index, approval and ordered payer signing headers. It signs only `payerSlots`, not resident `appSlots`, and does not assemble op49 or submit op46.

Frozen source SHA-256:

| Path | SHA-256 |
| --- | --- |
| `native/resource-client/src/agent_payer.rs` | `ac8eb1723d50f9423fac5d50cb58ffd8f119c4b64a23840806e72c6e7c55e4cd` |
| `native/resource-client/src/agent_reserve.rs` | `669d5a34c4b0832a886cd33151ac51d70600510efb71924417883ced9410fa79` |
| `native/resource-client/src/main.rs` | `ba6aa1e41743c9641d395807bf15953adef0fd9e233bc465b5cc53c97014f28b` |
| `native/resource-client/README.md` | `b7313f3f7d562ee01be5f428b2eca6a540727982c48e1fbf1dbb80e217f90a8b` |

From the repository root, focused `CARGO_BUILD_JOBS=2 cargo nextest run --locked --manifest-path native/resource-client/Cargo.toml -E 'test(agent_payer::tests) or test(agent_reserve::tests)'` passed 6/6 ([log](focused-nextest.log), SHA-256 `c1294a9bb78b5f73c215a22958c30aeeebe3929e281526e9bd8342638901a4f1`). `CARGO_BUILD_JOBS=2 cargo clippy --locked --manifest-path native/resource-client/Cargo.toml --all-targets -- -D warnings` passed ([log](strict-clippy.log), SHA-256 `9e50580e5e3c2f290457e58f14b40de9329ac0c7a20b5becb3547234ea03eb00`). Targeted `git diff --check` passed.

The helper rechecks the original reserve pin, selected Host image, config, paid Plan and approval after detached signing and before publishing `payer-signatures.json`. A partial payer directory has no native mutation and remains evidence; a retry uses a new directory and reselects op48 from the same exact retained inputs.

This is a source and focused custody check. No linked Host op48 paid-plan fixture or actual payer signature was exercised. Current op48 re-selection is a required fail-closed step; a historical reserve receipt alone cannot authorize paid dispatch.
