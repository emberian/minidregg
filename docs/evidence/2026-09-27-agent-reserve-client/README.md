# Agent reserve custody client source checkpoint — 2026-09-27

This checkpoint adds a private, four-phase `mini agent-reserve-plan`, `agent-reserve-seal`, `agent-reserve-submit`, and `agent-reserve-lookup` route for the source-owned paid AgentGrain reserve protocol. It consumes Host op58's exact plan and Host op59's exact canonical op2 call bytes; Rust does not construct the command or decide authorization. The controller must independently compare the inspected request, fixed selectors, and context with its protected dispatch task before issuing the private signing approval. A durable submit marker is written before op2; an unknown reply cannot trigger automatic repost.

Frozen source SHA-256:

| Path | SHA-256 |
| --- | --- |
| `native/resource-client/src/agent_reserve.rs` | `a833409ca90c6f758428477657167dd46117d32fd2e4fc99592d6a3ad503e2b5` |
| `native/resource-client/src/main.rs` | `306237b6c1ad29f9d6110a3dbd1017c0937012c1500fc1356c5004f009bb064d` |
| `native/resource-client/README.md` | `554580e21c1d7cfade342bf1ad6c794f1c7d05d2ff967166dc072f8100a273e3` |

From the repository root, `CARGO_BUILD_JOBS=2 cargo nextest run --locked --manifest-path native/resource-client/Cargo.toml -E 'test(agent_reserve::tests)'` passed 4/4 focused tests ([log](focused-nextest.log), SHA-256 `e72baa03758eeb258e6426e3a6c80bd78d45873d010ee5689fd53d0d841c3b3d`). `CARGO_BUILD_JOBS=2 cargo clippy --locked --manifest-path native/resource-client/Cargo.toml --all-targets -- -D warnings` passed ([log](strict-clippy.log), SHA-256 `a41051563a4cb5fc1b1bcdd9aa0ba28ca80f7736d629d90cc138218756e8e3a9`). `git diff --check` passed for the modified client files.

These tests cover exact receipt fields/index arithmetic, approval-to-plan/header binding, durable owner-private retention of source-generated files, and a lost op2 reply that leaves one marker and the exact call. They do **not** establish native interoperability: a linked, source-qualified Host containing op58/59 and a private controller fixture have not yet exercised all four phases. No reserve was submitted by this checkpoint.
