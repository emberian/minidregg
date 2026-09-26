# Upstream Hermes ACP initialization in a gated Linux worker

Persvati, 2026-09-26. Raw safe output: [HERMES-GATED-INIT-2026-09-26.log](HERMES-GATED-INIT-2026-09-26.log), SHA-256 `725d101a15cc088934f5fdf62bfd4f5bf1fda6a9c7a74b6d9fd9b75ef915dd32`.

The exact deployed `launch-gate.rs` source (`65a4ad217a43b103e70dfa41e91a804d7e0e11ce27d376577569f5c65aa68e96`) and `bwrap` launcher (`09b76dd5cb04a3e0668921483842996c9b19600225490a300a0ab6a5ae1ee6bd`) ran [probe-hermes-acp.sh](probe-hermes-acp.sh) (`785216fb3113b89c9a66609fd9b8a531dd0de137733ee8c2e848807b5e07dc18`). The worker used upstream Hermes Agent 0.21.3 with its ACP and MCP dependencies, a keyless `grain-runtime` broker binary (`023be6b425b47312777b1e23855aab7478a1b992d18256c43de9990e06aee18f`), no network namespace access, and a matching transient controller unit. The raw log records the upstream project and lock hashes.

`hermes-acp --check` passed; the actual ACP process accepted `initialize` at protocol v1; after connector stop the worker unit was inactive. This is an executable and confinement component probe. It did not start a signed Mini grain, open an upstream session, call a model/provider, or publish a resource. Those are covered only by separate native acceptance evidence.
