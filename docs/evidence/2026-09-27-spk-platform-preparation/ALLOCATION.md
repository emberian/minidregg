# One-Store participant allocation

`scripts/spk-platform/allocation-v1.json` reserves coordinates for a single
fresh Store and one installed signed GitWeb app. It is a planning artifact,
not a Mini grant, signed ticket, account balance or physical permit. The v2
SPK launch descriptor will change the v1 package root; no v1 ticket in the
separate fee fixture is reusable here.

| Participant | Session/descriptor | Ticket/grant | Parent | Tool | Dispatch purse | Provider |
| --- | --- | --- | --- | --- | --- | --- |
| Alice Web, subject 8 | 8404/8405 | 8500 | — | — | — | — |
| Bob Web, subject 9 | 8406/8407 | 8501 | — | — | — | — |
| Alice API, subject 8 | 8410/8411 | 8510 | — | — | — | — |
| Hermes A, participant subject 10 | 8420/8421 | 8520/8530 | 7920 (subject 10) | 7930 (11) | 7940 (12) | 7950 (13) |
| Hermes B, participant subject 20 | 8422/8423 | 8521/8531 | 7921 (subject 20) | 7931 (21) | 7941 (22) | 7951 (23) |

Agent A and B need independent controller UIDs, Unix sockets, custody keys,
task accounts, source-signed reserve payers and resident routes. Within each
controller, the dispatch payer is deliberately **different** from the ticket
participant: A is participant 10/payer 12; B is participant 20/payer 22. The
Mini event-21 context binds both. `grain-runtime` route validation must check
its participant against the controller subject and its payer against the
dispatchTask subject. Equating participant with dispatch payer is a source
configuration bug, not a shortcut for this fixture.
Persistent grant resources 8530/8531 are separate from their event-22 tickets
and from event-21 generation-bound paid dispatch. The new event-27 issuance
and event-26 dispatch continuation must source-admit each grant before a
restart-stable agent permission can be exercised.

All eight new agent subjects require separately generated private Ed25519
seeds, current enrollments and account grants in the **fresh** genesis.
The key IDs and capability IDs in `allocation-v1.json` are reserved and
collision-checked against one another and existing fixture literals; they
do not claim valid delegation. The source bootstrap must birth each task as
an actual grain under the factory law, then admit precise owner/worker and
parent-witness delegation for its subject and generation. The original
workroom source only enrolls subjects 7/8 and the member overlay adds 9;
those sources cannot establish agent 10–23 by implication.

`scripts/spk-platform/agent-genesis-overlay.sh` now prepares a private
source overlay that adds all eight distinct Ed25519 enrollments and account
allocations before bootstrap, then adds their two parent, two tool, two
dispatch-purse and two provider grains to the first signed birth. Its
post-birth continuation signs an owner-capability resource query for each
new grain and retains the one birth receipt plus eight signed views. This
source is generated after the offline v2 SPK qualification gate; it has
not run in a Store. After each born-grain readback, the continuation asks
Mini to source-admit three distinct parent-witness delegations per
controller, using a fresh owner root and authority observation for every
child, then requires a holder-signed readback and retains each receipt.
It does not start grains, issue tickets or prove any agent API permission.

Each controller also reserves three distinct parent-witness child caps:
A 203/204/205 and B 303/304/305 for its tool, dispatch payer and provider.
The parent grain starts at generation 0 with its tool, dispatch-payer and
provider worker subjects each pinned to generation 1. Host.Json's plural
grain policy gives each named worker only the pinned-generation no-op witness
branch; it refuses an unnamed worker and stale generation. The overlay
compares the actual installed policy bytes against the source-authored
three-worker policy. That policy choice is separate from the controller's
current delegation of a child cap. The child reservations have no authority
until those source-authored delegation receipts and holder readbacks
actually exist; the initial worker policy alone does not grant a parent cap.

The first reservation in commit `259d15e` used agent A account IDs 10, 11
and 12. Mini genesis reserves those resource IDs for the factory, resource
book and authority catalogue. Before any Store was created, the reservation
was corrected to account resources 8010–8013 for A and 8020–8023 for B;
subjects, key IDs, task IDs and ticket coordinates did not change. Each
enrollment also reserves a separate factory-observe capability 610–617.
Mini's `NativeHostGenesis.Config.Valid` requires all account IDs and the
three deployment resource IDs to be pairwise distinct. These corrected
coordinates are still only planned input to that source admission.

The required sequence is source-authored fresh genesis and births, v2 signed
launch descriptor/installed manifest at app 8401, distinct current-image
session births, event-22 issue for each ticket scoped to the installed package,
and source-verified receipt/current-view capture. After the one-shot START
selects the signed create action on a virgin `/var`, the resident may enable
three fixed human entrances and two separate agent routes. Hermes's read-only
recipient checker will consume protected `ROOT/acceptance/agent-a` and
`agent-b` artifacts only after they exist, re-query op55, and compare current
signed app/manifest/snapshot/ticket views. A file manifest alone is not
authority. No such artifacts or Store have been created yet.

The app birth and package/snapshot births are a separate stage from package
installation. `scripts/application-current-birth/native-share-base.sh`
authors app 8401 and empty package 8402/snapshot 8403 content pages and
checks the two latter `.page.entries == []`. Thus the qualified v2
`launchRoot` belongs in a later source-admitted prospective INSTALL/BEGIN-v3
manifest and its completed installed cell. The embedded v1 `packageRoot`
inside the v2 descriptor is signed SPK package identity, not the installed
manifest root. Neither root may be fabricated into the empty initial birth.
