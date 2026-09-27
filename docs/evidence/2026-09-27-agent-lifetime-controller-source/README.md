# Lifetime agent controller source checkpoint

The grain controller now has a separate v3 route for event27 lifetime grants and event26 paid dispatch. The v2 route and its fixed generation pins remain intact. The v3 controller retains stable ticket/grant lineage from `binding-v3`, derives fresh app/session roots and parent/purse generations from the source-owned op80 plan plus signed task reads, and journals the per-operation fingerprint before the forward request. It issues one exact lifetime reserve, uses receipt-only lookup after uncertainty, and returns the full source plan so the resident can independently inspect it.

For paid dispatch, the controller reauthors the exact op78 plan and signs only the three ordered payer target/observation/authority slots under its protected purse key. `mark-send-v3` pairs that retained plan with the resident's exact ingress through `inspect-agent-lifetime-paid-ingress`, separately inspects the op76 committed payload, checks full ticket/grant/reserve/HTTP/receipt lineage, and saves ingress/frame hashes and the four-field receipt before ACK. A definite `http-v3` reply requires the durable committed receipt and confirmed native purse settlement; recovery restores the latter only from the retained exact settlement. A lost or uncertain send remains held without resubmission.

Frozen source SHA-256:

| File | SHA-256 |
| --- | --- |
| `native/grain-runtime/src/main.rs` | `9d9356533bdf19e8da92c62596bc6cdb29f3610725eb90442d93d87789b261c4` |
| `native/grain-runtime/src/application_api_tools.rs` | `a81fa1d99244fc8f1c6b35571f59fbe72968c2d5b56d52796bc78721c7ac9b81` |
| `native/grain-runtime/src/dispatch_custody.rs` | `5b14bd3abb70868980c827bd4a70b0d17b4d0beed4cb51bab1364e8a24280e08` |

From `native/grain-runtime`, `cargo nextest run -p minidregg-grain-runtime` passed **125/125**; the exact log is `nextest.log`. `cargo clippy --all-targets -- -D warnings` and `git diff --check` passed at these source hashes; their bounded observed verdict is in `clippy-verdict.txt`. The tests include a cross-side SPK fingerprint golden vector, three-slot payer shape, larger exact v3 reverse response, and definite-reply marker refusal/acceptance. They do not constitute native v3 acceptance.

Still required for a hosted native journey: a source-qualified Linux Host including the two-input paid-ingress CLI, the resident's fresh op76 installed-permit and op79 split-signature integration, a same-Store event27→op80 reserve→op78 paid→op76 installed→mark-send→fd3→settle fixture, and hard-EOF/restart evidence. The committed-frame inspector is structural; only the resident's fresh installed op76 result can permit physical delivery. No paid provider or live Store was used for this checkpoint.
