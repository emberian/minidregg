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
