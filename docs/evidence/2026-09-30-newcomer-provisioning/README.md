# Independent newcomer provisioning — 2026-09-30

A newcomer holding only an enrolled key created, wrote and read its own
ordinary resource on a fresh private Persvati Store with no sponsor step for
that resource. Before this, an enrolled key could not observe the factory, so
current birth authoring (op91) refused it
(`2026-09-28-newparticipant-runtime/`). The same run qualifies the repair of
the stale-factory-observation liveness bug and a cold reopen.

Source: branch `m3-provision`, commits `d0b8a44` (Lean: factory-observation
provisioning) and `252158c` (client: provisioning custody and versioned
authoring generations). The launcher is
[`provisioning-acceptance.sh`](../../../native/resource-client/provisioning-acceptance.sh),
SHA-256 `09b53464c597b6e8ac760440a80ac7fb905483d793c5dc419b66c0098c79a79e`.
It calls the unchanged `newparticipant-acceptance.sh` (`37f744d9…f07f`) for the
fresh bootstrap.

## Design

- **Factory observation** is a new source-owned operation,
  `Kernel/ParticipantFactoryProvisioning(.Receiver).lean`. The sponsor presents
  the factory control capability (program, `installPolicy`) under the factory's
  current law, which is the same request shape as key enrollment. The law sees
  `authority/operation/provision-factory-observe`. The effect is the existing
  root-issuance family. It issues one fresh root object capability with exactly
  `{observeObject}` on the deployed factory, held by an already enrolled
  subject, at current epochs, registered for revocation, single-use marker.
  Unenrolled holders, used ids, stale roots and replayed markers refuse. The
  operation runs on existing Stores and widens no genesis grant.
- **Payer and funding** needed no new semantics. The sponsor births an
  ordinary declared account owned by the newcomer, funded from the sponsor's
  account. The birth controller already admits an owner who is not the creator.
- **Client.** `mini workspace --action provision` (sponsor) does the grant
  first, then the account, and emits a birth context for the newcomer. The
  context is a hint only. The newcomer then uses `workspace init/create`
  unchanged.
- **op91 liveness.** Authoring now lives in immutable generations
  `sources/create-NAME.authoring/gNNNN` of one reserved request. A retained
  refusal is superseded by a fresh-observation generation only while no
  attempt is bound. After binding, exact custody is unchanged.

## Binaries (RAN: `sha256sum` on persvati)

| Item | SHA-256 |
| --- | --- |
| Host `bin/minidregg-host-m3-r1` (from `d0b8a44` sources) | `7778058ed2fa70dcb937078e5a0e7031055ae313797ffaa48910c5f2c9b15a2d` |
| Mini `bin/mini-m3-r2` (from `252158c`) | `a41d517dd964b012b143593872dd00ebdd1396da1b4629a298ba43ab3b72be9d` |
| SQLite Store helper (bake-off durable copy) | `ad03aede839259c1884383fc97f141a3fe106ba2f2cbae0df6f7916676fe193f` |
| Ed25519 verifier helper (bake-off durable copy) | `c84004123ae6f02654cb6749e4105e351199618aaefce5755a2a0bb10bd0892b` |
| Pre-generation client `mini-0007925` (stale case only) | `3e9cb1ca488995a0a591ea6db8f9b4b6b59d9629782daf6babb294620c74513d` |

Host build: `scripts/build-native-host.sh --incremental-suffix-from` the
qualified `e22d16b` snapshot/`build-r3`. The Host Lean sources at `abe988d` are
byte-identical to `e22d16b`. The build compiled 101 of 365 modules from
`Kernel.ParticipantFactoryProvisioning`. It declared 2 inserted modules and 4
changed modules and reused 264 earlier modules and 2,933 package objects after
the script's byte checks. It took 1,115 s (05:34:47–05:53:22 UTC). Manifest SHA-256
`f0a326e9a5cc8a4941129106c78aca75676bfee8b8252465a48c5d9f4f9ce38b`; changed
source list `275cf60f…7b65d`. Its six source hashes equal the committed files.

## Run (RAN: `run3`, fresh root, 2 min 10 s wall)

Private root `/home/ember/build/mini-product-20260930/m3-provision/run3`.
Accepted records in order:

| # | Operation | Who signs | Transaction ID |
| ---: | --- | --- | --- |
| 1 | key-only enrollment, subject `13490942843177498195` | sponsor + new key | `42263753…583069` |
| 2 | factory-observation grant, capability `13535419377716210439` | sponsor | `59797285…168647` |
| 3 | account `14656694703177287780` owned by newcomer, funded 1000 | sponsor | `10971446…411913` |
| 4 | newcomer birth `notes` (fee payer: its own account) | newcomer only | `39168266…575502` |
| 5 | newcomer write field 2 = 1 | newcomer only | `83267082…874116` |
| 6 | sponsor birth `tick`, makes earlier observations stale | sponsor | — |
| 7 | newcomer birth `stale-crash` after superseding generation 1 | newcomer only | `11289779…154808` |
| 8 | newcomer birth `stale-refused` after superseding generation 1 | newcomer only | `84698582…389180` |
| 9 | newcomer birth `after-reopen` after cold reopen | newcomer only | `61300260…170248` |

All 9 signing slots of the newcomer's `notes` plan name the newcomer's key
`16293993923627442984`. The retained birth source has creator = newcomer,
`feePayer` = its account, and `sourceCapabilities` = its account owner grant.

Asserted refusals, each at its recorded boundary:

- Before provisioning, the enrolled key cannot read the factory: `host refused
  query … observation refused`.
- Provisioning an unenrolled subject `4242424242` is refused at op92. The
  retained frame reads
  `provisioning preparation: …Reject.holderNotEnrolled`. No account birth was
  attempted for it.

Stale factory observation (the reported bug). The newcomer took a signed
factory observation, and the sponsor's accepted record 6 then made it stale.

- The pre-generation client (`mini-0007925`) with that observation retained
  refused twice with `current resource birth authoring refused; retained
  encoded Host outcome`. Its `reply.frame` starts with 255 (SHA-256 prefix
  `6baaae8652cbcad7`), and no attempt directory exists. Same-name create stays
  stuck.
- New client, crash state (observation retained, no reply). Generation 1
  retained the identical refusal (`6baaae86…`). Generation 2 authored with a
  fresh observation (reply opcode 91), and the birth was accepted (record 7) in
  one `create` call.
- New client, reported state. The old client's exact refusal frame was planted
  as generation 1. Generation 1 was kept byte-identical, generation 2 reply
  opcode 91 was produced, and the birth was accepted (record 8).

Cold reopen of the same Store. The service was stopped at verified PIDs
(server and Host child), then restarted. The new server reported serving
after 0.25 s. The first request after that (enrollment receipt-only lookup)
took 13.91 s. That is consistent with the Host opening the Store and replaying
all 8 records semantically, the new provisioning ingress among them, on first
use. The split between open and replay was not measured. Receipt-only
`provision-lookup` returned `replayed` with the same receipt for the grant
(acceptedCount 2) and for the account (3). The newcomer's signed read still
showed field 2 = 1. A new newcomer birth after reopen was accepted (record 9).
Both services were stopped, and no process naming the run root remains.

Step timings are in [`timings.tsv`](timings.tsv); each includes local socket
round trips and no SSH. Newcomer create took 6.8 s, write 1.9 + 3.4 s, read
1.6 s and provisioning 8.8 s. These are small-Store timings, not a growth
measurement.

Retained evidence hashes (`run3/evidence.sha256`): pinned config
`ba29e4a1…`, enrollment result `3509d16c…`, provision summary `db902faa…`,
newcomer birth context `c97916d0…`, `notes` reference `8b5c58bb…`. Private
keys, signatures, signed ingress and the Store stay under the run root.

## Boundaries

- The newcomer key was generated on the same host by the bootstrap script, and
  the sponsor, newcomer and namespace root share one machine. No second person
  or network transport was involved.
- Provisioning is a sponsor act. "No sponsor step" means none per resource
  after provisioning.
- The stale case is fault injection. It plants a genuine, Host-signed but
  stale observation (and, in 6b, the old client's real refusal frame) at the
  path a crash or a race leaves. It does not reproduce the timing race itself.
- The provisioning plan's own stale-plan supersession is source-read and
  compiled only. No runtime case forced it.
- A birth whose attempt is bound and then refused at prepare still stops at
  the existing exact-custody message. That case is outside op91 and unchanged.
- Earlier runs: `run1` passed with the pre-commit client. `run2` failed at the
  reopen step because the old script treated a stale socket file as ready; it
  was fixed in this launcher before `run3`, and `run2`'s services were stopped.
