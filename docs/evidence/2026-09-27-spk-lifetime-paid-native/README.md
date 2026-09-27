# SPK lifetime paid assembly component gate

This cut adds a v3 reverse reserve/payer client, stable resident app/grant signer custody, and a source-owned op78/79 paid assembler. It does not submit op76, mark a send, or deliver an HTTP request. The v2 route remains separate.

Private Linux build source: `/tank/dregg-build/mini-spk-v3-agent/native/spk-host` on hbox, with only the five listed SPK files copied from the shared tree for this check. Target: `/tank/dregg-build/mini-spk-v3-agent/target`; two Cargo jobs. `cargo nextest run --locked --lib -E 'test(agent_api_lifetime_reverse_v3::tests::) | test(agent_api_lifetime_custody_v3::tests::) | test(agent_api_lifetime_paid_native_v3::tests::)'`: 8/8 PASS. `cargo clippy --locked --all-targets -- -D warnings`: PASS. No Store, native submit, app launch, or live socket was used.

Source SHA-256:
- `agent_api_lifetime_reverse_v3.rs` 1c0ea10e91ed75468f4477f9436109819da0d31653f9630a0bc928710682c6de
- `agent_api_lifetime_custody_v3.rs` e44ad90d9f1ecb1e9dd0bc2391b943a41db6680394e51d692cee38e39d3f70c4
- `agent_api_lifetime_paid_native_v3.rs` 1608ceebca2a9ecf24ecc27fc64ca4cf154ff8196e8bd24cabbd67f182ca5800
- `agent_api_native.rs` 52e3020106e3b68a6bb695f0a8921df6cbcb3a03ea0e2106a1608b0ea3fd7325
- `lib.rs` 199def2865643d2db7073fe039c10f52225198811c5d274bdba6a9f95b7a3af8

The signer split is app slots and grant observation under resident protected keys, all ordered payer slots under controller custody. The controller's signed post-reserve purse physical root is checked against the exact source op78 plan before op79 assembly. The retained paid ingress has no delivery authority; fresh installed op76, durable mark-send ACK, and the physical fd3 path remain separate work.
