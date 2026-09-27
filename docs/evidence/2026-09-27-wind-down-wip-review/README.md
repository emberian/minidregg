# Frozen grain-runtime controller source review (2026-09-27)

This is a read-only review of a frozen, uncommitted source cut. It is not a native acceptance result or an adopted source commit. The broader 13-file WIP is preserved as reconstructible patches at `8846d4e`.

Reviewed source SHA-256:

| File | SHA-256 |
| --- | --- |
| `native/grain-runtime/src/main.rs` | `9d9356533bdf19e8da92c62596bc6cdb29f3610725eb90442d93d87789b261c4` |
| `native/grain-runtime/src/application_api_tools.rs` | `a81fa1d99244fc8f1c6b35571f59fbe72968c2d5b56d52796bc78721c7ac9b81` |
| `native/grain-runtime/src/dispatch_custody.rs` | `5b14bd3abb70868980c827bd4a70b0d17b4d0beed4cb51bab1364e8a24280e08` |

Inspected `lifetime_purse_signers`, `dispatch_reserve_v3`, `dispatch_sign_payer_v3`, `dispatch_mark_send_v3`, `dispatch_settle_definite`, `poll_lifetime_application_api`, `verified_lifetime_definite_reply`, `recover_v3_dispatch_reserve`, `recover`, and `exchange_once_guarded`; also checked the resource-client `approve_slot` signer check. The three payer slots require ordered roles 4/8/1 at index 0 with pinned key ID/epoch and exact header digests; the client checks that the private key derives the pinned public key. The forward fingerprint and dispatch attempt are durable before public reserve. Mark-send saves the committed receipt in both the dispatch and forward attempts before fd3 delivery. Definite settlement saves the response hash before native settlement; restart verifies the exact settlement against the current image and restores the forward hash. A definite API reply requires the committed receipt, settled hash, and no unresolved native hold. Transport errors after a first request byte are uncertain and do not trigger resubmission.

No concrete crash-ordering or custody bypass was found in this inspected path. Pre-send and inspection crash windows can leave conservative held/uncertain attempts requiring reconciliation; they do not prove retry availability. This was a source review, not an independent crash-injection or native integration run. The source owner reported `cargo nextest` 125/125 and strict all-target Clippy PASS in `/tmp/mini-grain-v3-controller-nextest-final-r2.log`; those checks were not rerun for this review.
