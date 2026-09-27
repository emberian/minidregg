# Claim planning and fn namespace signature custody

This source cut adds private Host op52/53 for descriptor-bound claim-v2 planning and detached assembly. The configured `residentClaimManagement` fixes the app, package manifest, management subject/key, and capabilities; a request supplies only the original BEGIN index and query nonce. Op26 still performs fresh native admission. It also changes private op43 to accept exactly one raw 64-byte Ed25519 signature. Lean constructs the canonical credential envelope from the retained source signing header and rechecks the current namespace plan before returning ingress.

The owner-private resource-client broker accepts op52/53 with bounded request/pair frames and op43 only with a nonempty bounded plan plus exactly 64 signature bytes. The public socket refuses these operations.

| Source | SHA256 |
| --- | --- |
| `Host/FnConsumerNamespacePlan.lean` | `8d6f185ce82dec49ad3275fa003bb0844a63e9c30d800f8da3072e2afa9dd4c0` |
| `Host/ApplicationLifecycleClaimOperator.lean` | `435297893e70868e8f8df64c6fe8bd8407b87e14b1ba4b4782c92c943e722342` |
| `Host/Json.lean` | `6c137c78e2ad88f77b02ffdd255e8d9aae01adeb03aa6ebca52bfcb211748b72` |
| `Host/Main.lean` | `82c7f74f6ba8f1e9918784473545803c6b68ca5ae3b78f1d31d569151d018a4f` |
| `native/resource-client/src/transport.rs` | `bf67094de08d62b650cd29e44afa5949807b99e5e394127116055e2c2321b80a` |

Private writable Persvati overlay `/tmp/minidregg-operator-followup-check` compiled Plan → ClaimOperator → Json → Main serially against the certified read-only `24ecf8a` Host snapshot, plus the source-matched BEGIN operator OLean from the prior cut. All four direct Lean commands exited 0; Plan, ClaimOperator, and Main logs are empty, Json contains only existing axiom/linter warnings. OLean hashes in that order: `de5ef6ee`, `52cc54f6`, `2f111bf5`, `ab3b04ff`.

The focused `namespace_and_lifecycle_authoring_routes_stay_private_and_bounded` nextest test passed 1/1. `rustfmt --check --edition 2021 native/resource-client/src/transport.rs` passed. Whole-crate `cargo fmt --check` currently reports only concurrent uncommitted formatting in `native/resource-client/src/fn_namespace.rs`, which this cut does not edit. This is source-only evidence; no linked Host or physical claim is asserted.
