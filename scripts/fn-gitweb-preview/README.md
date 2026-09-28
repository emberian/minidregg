# Selected GitWeb file preview over fn

`join.sh` joins existing source-owned Mini commands. It does not read a raw
GitWeb volume as publication authority. A separate app/runtime step must place
the operator-chosen public version payload in one Mini content atom and return a
signed current resource query. `prepare` reopens that exact query with the
pinned Lean Host, compares the native view bytes to the retained signed read,
then compares the Host-decoded atom payload to the exported payload file. The Host
constructs the owner-signed release. The chosen
Git commit and path are retained as provenance, not treated as a Mini grant.
The payload may contain a source-authored commit/path/blob header followed by
the exact file bytes; `selectedFileSha256` hashes the **whole atom payload**,
not just the raw Git blob. The source owner must explicitly choose public
disclosure. Recipient-only content needs a separate encrypted profile.

Use a private `CONTRACT.json` with absolute paths and canonical decimal strings:
`host`, `mini`, `sourceConfig`, `recipientConfig`, `exportResult`,
`gitRawFile`, `gitRawFileSha256`, `gitBlob`, `sourceResource`, `selectedFile`,
`selectedFileSha256`, `sourceViewBin`, `sourceSignedQuery`,
`sourceSignedQueryHex`, `sourceAtom`, `ownerKey`, `sourceDelegateCapability`,
`destinationDomain`, `destinationSemantics`, `destinationTarget`, `group`,
`messageId`, `destinationPolicyRoot`, `destinationKeysetRoot`, `ownerEpoch`,
`ownerSubject`, `ownerNonce`, `ownerExpiresAt`, `from`, `date`, `subject`,
`gitCommit`, `gitPath`, `privatePostConfig`, `fnBinary`, `fnBinarySha256`, `fnScope`,
`fnControl`, `recipientCapability`, `recipientAuthorityRoot`,
`recipientTargetRoot`, `recipientSocket`, `recipientOperatorSocket`,
`gatewayKey`, `recipientQueryIntent`, and `recipientQueryKey`. The recipient
roots must come from a fresh signed recipient
query. Pin a source-matched Mini Host/client and an **isolated** qualified fn
node with a bounded article profile. `group` is a routing label, not privacy.
The currently qualified format-8 fn image for an isolated node is
`/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host`
(SHA-256 `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505`).
Current fn dev format 9 and its widened `hybrid-author` have no qualified image;
the existing selected publisher uses protected NNTP POST. Never repoint the
protected live node at a new Store or silently upgrade its profile.

Run each phase only after inspecting the retained result:

```sh
scripts/fn-gitweb-preview/join.sh prepare CONTRACT.json NEW-PRIVATE-STATE
scripts/fn-gitweb-preview/join.sh publish CONTRACT.json PRIVATE-STATE
scripts/fn-gitweb-preview/join.sh receive CONTRACT.json PRIVATE-STATE
scripts/fn-gitweb-preview/join.sh cover-plan CONTRACT.json PRIVATE-STATE
scripts/fn-gitweb-preview/join.sh cover-advance CONTRACT.json PRIVATE-STATE APPROVAL.json
scripts/fn-gitweb-preview/join.sh ack CONTRACT.json PRIVATE-STATE
scripts/fn-gitweb-preview/join.sh verify CONTRACT.json PRIVATE-STATE
```

The preparation phase makes no Store or fn write. Publication uses event14
op24/25 and the existing publisher's durable no-blind-repost marker. `receive`
uses a native authenticated fn consumer projection and recipient op20/21;
reentry performs exact lookup, not a second submit. `cover-plan` and
`cover-advance` use the registered gateway's event17 first-match record;
the gateway key signs only the source-issued header after an exact private
approval. `ack` requires both Mini receipts, then the Host re-polls before
acknowledging the fn cursor. Event20 registration and event19 neutral progress
must already be admitted where needed. A final signed recipient resource query
must name the exact destination target and recipient capability, then show the
owner packet under the accepted event13 transaction ID, which the source codec
defines as the recipient AtomId. The atom must be live and inline object schema
11. Its source selection already bound the chosen atom payload. Fn acceptance alone never proves
source publication or recipient installation.

The state directory is mode 0700. An interrupted poll keeps its partial files;
the next `receive` makes a fresh bounded poll attempt and never submits the
partial candidate. Once a recipient attempt directory exists, `receive` invokes
op21 lookup only. Its **latest** outcome must confirm the same original receipt;
an earlier confirmation cannot overrule a later absent or uncertain lookup.
`recipient-confirmed.json` is recreated only after that full check; a failed
latest lookup removes the convenience copy while retaining all original outcome
files. Coverage planning, coverage signing, ACK, and final verification recheck
the latest recipient outcome before proceeding.
Repeated `ack` calls use new numbered output files and re-enter the native
Host's current fn position/coverage check; a lost ACK reply is never interpreted
from a caller marker. Repeated `verify` calls make new signed readbacks. Each
phase allows at most eight retained attempts and then requires operator review.
The query and binary payload hex are passed to jq through private files so a
large selected version does not exceed the platform's single-argument limit.

`test-join-recovery.sh` exercises these shell recovery/refusal paths with fake
Host and Mini commands, including a 100 KiB binary readback. It tests command
routing and retained files; it is not native event14, fn, or recipient admission
evidence. No GitWeb-selected Mini Store or fn node has been mutated by this
preview script yet.

The existing GitWeb private app run produced commit
`27c7e7dbe3c66cc5d8381748d0b0e5fbae05bafc` and a README with SHA-256
`fa2447c2dc837cb77e517024df9363e276bd12eae115190fc2dc2c3c95e32403`.
It has **not** yet created a Mini content atom. Do not substitute the older
synthetic selected-release fixture for that app-produced version.
