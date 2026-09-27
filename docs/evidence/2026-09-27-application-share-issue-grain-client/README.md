# Event-22 grain-backed share custody checkpoint

The event-22 client is separate from the older event-15 bare share client.
`grain-share-issue-prepare` authors a strict source Request, compares its full
canonical bytes to an operator-private approval, requests one current-image
plan on the operator socket (op56), checks the returned plan's exact Request
and ordered birth-then-app signing headers, signs each with its separately
pinned key, and assembles the ingress through source op57. The approval binds
the issuer, delegate capability, ticket/participant, payer, full funding and
source capability lists, and tool/parent selectors. Every signer entry pins
role, index, key ID/epoch, public key and exact signing-header SHA-256. The
Host/config/approval bytes are pinned before authoring and checked again
through signing and assembly. Event-22 JSON inspection is bounded; submit and
lookup recheck the retained Host/config/approval/ingress pins after the native
call and before trusting the inspected receipt.

`grain-share-issue-submit` marks one durable op54 attempt before transmission.
It never resends an uncertain issue. `grain-share-issue-lookup` sends only op55
with the retained exact ingress, reconstructs an outcome from a synced reply
frame after a crash, and anchors the first confirmed four-field receipt across
later lookups. The separate `grain-share-issue-receipt-lookup` accepts only the
exact ingress and four pinned original receipt fields for recipient recovery.
The public broker currently **refuses op55** until native event-22 replay and
recipient acceptance are qualified; that CLI is staged source code only.

In the separate, still-uncommitted grain-runtime integration, `ShareIssuePin.kind` is required: `bareEvent15` selects the
existing op29 recipient path, while `grainBackedEvent22` cannot fall back to
op29. Existing private event-15 reference configs must explicitly add
`"kind":"bareEvent15"`; no committed reference JSON was migrated or claimed
as event-22 evidence.

Source SHA-256 at this checkpoint:

| File | SHA-256 |
| --- | --- |
| `native/resource-client/src/grain_share_issue.rs` | `fd5d03d9a89e5d1995e35b6bc5859c6e86dd78e4ca9fee88b38c2d906be9331f` |
| `native/resource-client/src/share_issue.rs` (visibility-only helper reuse) | `878863e81c9c590dd6843352db34786edd7969f6a99a91baebe792875c1c2444` |
| `native/resource-client/src/share_issue_receipt.rs` | `59578880ed12f7b970c3af5f7840c146090438c3f3fd837940ea4cf6658940cb` |
| `native/resource-client/src/main.rs` | `5059dbcac9d49490c2c28b319f80e32397da71aa899c49b01c6cc230319c6c82` |
| `native/grain-runtime/src/shared_app_refs.rs` (separate working-tree integration; not included in this client commit) | `9b535ff3b201db79b111239f861dfd97e21ed00fca5feeec9d306b3eafd3aa47` |

Local private-target `cargo check -p minidregg-resource-client` passed before
the final pin-readback addition. The preceding full package Nextest passed
**81/81** (run ID `5a563ed9-ff29-473e-8199-db8fbb66299d`). After that
addition, focused `cargo nextest run -p minidregg-resource-client -E
'test(/grain_share_issue/)'` passed **4/4** (run ID
`7d147f95-a1f5-430e-bd80-dfcee43cbe5f`) using the private target: exact
Request/selector approval, birth/app slot order, frame-only crash recovery
with changed historical receipt refusal, and post-operation pin mismatch
refusal.
`rustfmt --check` and `git diff --check` passed. The integrated grain-runtime
carrier-kind test passed **1/1** in Hermes's bounded run `c06faf61`.

This is client source qualification, not a linked Host or accepted native
ticket. The event-22 Host routes, historical verifier, public read-only op55
broker release, and fresh same-factory-law Store fixture have independent gates.
