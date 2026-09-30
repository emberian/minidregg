# Agent-fleet surface on Mini

This is the Mini equivalent of the operations an agent fleet uses on Bread
through the contributor's `dregg-sdk-net/src/bin/dregg-client-sign.rs`
(reviewed at breadstuffs `origin/pr/95`, `2389dcb10`): **join**, **send**,
**transfer**, **receipt lookup** (by turn hash and by agent head) and **event
topics** (publish; subscribe/poll by cursor). The client contract is
`mini fleet`; the journey is
[`native/resource-client/fleet-journey.sh`](../native/resource-client/fleet-journey.sh);
the measured run is in
[`docs/evidence/2026-09-30-fleet-surface/`](evidence/2026-09-30-fleet-surface/).

## What was built

One source-owned receiver, **`FleetTurn`**
([`Kernel/FleetTurn.lean`](../Kernel/FleetTurn.lean),
[`Kernel/FleetTurnReceiver.lean`](../Kernel/FleetTurnReceiver.lean)), wired as
a `NativeAdmission` constructor that `NativeHostReplay` re-admits on every
open.

A fleet turn is signed by the current holder of a `transfer` capability over
the **paying account** and is checked against that account's installed law.
In one CAS it

- always posts the pinned base tariff (`config.tariff.base`) from the paying
  account to the deployment collector, as a real
  `CanonicalResourceKernel.Operation.fee` in the one canonical Book;
- optionally posts one `Operation.transfer` from the paying account to any
  registered account (receiving needs no authority);
- optionally appends one event to a **topic stream owned by the paying
  account**;
- consumes its operation marker in the authority cell.

The request's `cost` is fee + transferred amount, so a spend grant's
`maxCost` caps what one turn can move. Operation identity is
`(subject, paying account, nonce)`: an exact repeat replays the original
receipt; a changed command under the same identity is a transaction conflict,
never a second effect.

**Topic streams are the tree's causal event log.** A stream is a sequence of
`eventHistory` cells — the typed append-only four-slot pages already
registered in `CanonicalCellRegistry` with their own cell law, which no native
receiver wrote before. The stream id is `H(domain, account, topic bytes)`; the
page cell id is `H(stream, page number)`; sequence `n` sits at page
`(n-1)/4`, slot `(n-1)%4`, admitted only as the stream's next position, with
the previous event's key as its only parent. The `VersionEventRecord` binds
the payload digest, the turn's transaction id and effect digest, the Book
roots around the turn, and the typed author (subject, account capability).
The payload bytes stay in the signed ingress, which the accepted journal
already retains; a poll reads them back by exact transaction id and returns
them only when they reproduce the committed digest.

Host operations on the public socket (`Host/Main.lean` stdio; allowlisted in
`native/resource-client/src/transport.rs`):

| op | meaning |
| --- | --- |
| 96 | plan: a signed observation of the paying account **by the turn's signer**, plus a draft; the Host fills the fee from the pinned tariff and, when the draft leaves it zero, the stream's next position, and returns the one signing header |
| 97 | detached assembly of plan + one raw Ed25519 signature |
| 98 | checked submit |
| 99 | receipt-only lookup of one retained ingress (never submits) |
| 100 | topic poll since a cursor, behind a signed observation of the account |
| 101 | agent head: newest accepted fleet turn paid by the account, behind a signed observation |
| 102 | exact receipt by transaction id |

Client (`native/resource-client/src/fleet.rs`, `mini fleet --action …`):
`join`, `send`/`publish`, `transfer`, `receipt --transaction|--head-of`,
`lookup --attempt`, `poll`. `workspace::create` gained one birth shape: an
account owned by another admitted subject, funded by one Book posting from
the sponsor's fee payer under the sponsor's spend grant.

## What already existed and was reused

- Key admission: `ParticipantKeyEnrollment` (`mini enroll`), sponsor factory
  grant plus proof of possession.
- Account creation, funding and grants: resource birth with `InitialFunding`
  legs, the creation tariff, owner and control grants (`ResourceBirth`,
  current-birth authoring).
- Signed observations and account views (`NativeObservationController`).
- Receipts: the four-field `Receipt` (transaction id, event id, accepted
  count, image boundary) and `historicalReceipt`, which seals the original
  accepted prefix; exact lookup by retained call bytes.
- Delegation (`workspace --action propose|submit|publish-delegation`) for a
  subscriber's observe-only grant.
- The `eventHistory` cell kind and its cell law, the Book and its
  conservation proofs, the authority marker discipline.

## Verb mapping

| Bread `dregg-client-sign` | Mini | Differences |
| --- | --- | --- |
| `join`: create the named profile on first use; faucet-materialize and fund the canonical cell `derive(ed25519 pk, "default")` | `mini fleet --action join`: sponsor-signed key admission with the new key's proof of possession (`mini enroll`), then a sponsor-authored birth of an **account owned by the new subject**, funded by a Book posting from the sponsor's account under the sponsor's spend grant; the owner and control grants go to the new subject; the agent workspace imports the account reference | No faucet and no keyless materialization: value comes from a real account under a real grant. Identity is admitted by a sponsor's factory grant, not by first use, so there is no trust-on-first-use window and no #91 brick (Bread's cell id is derivable from a public key and claimable by anyone who posts it first; Mini's account id is a reservation the sponsor's signed birth creates). Key and account are distinct resources. |
| `send`: one hybrid-signed `EmitEvent` on the signer's own cell, `topic = symbol(--topic)`, payload packed into event words and the memo; fee from the computron estimate; `--to` must equal the own cell | `mini fleet --action send --topic T --payload P [--to ACCOUNT --amount N]`: one `FleetTurn` with a topic event on the paying account's stream and, optionally, a payment to a service account in the same CAS | The topic is an append-only stream with an exact sequence and parent, not a symbol on a flat event list. The payload is bound by digest in the page and retained exactly in the journal (no 8-byte-lane packing). The fee is a Book posting to the collector, stated by the signer and required to equal the pinned tariff. `--to` means *pay* that account atomically with the event — the "send with fee to a service cell" Bread cannot express in one turn. There is no coordination-exempt fee class. |
| (no separate publish) | `mini fleet --action publish`: the same primitive without a payment | `send` and `publish` are one receiver; `publish` is a name for the unpaid form. |
| `transfer --to CELL --amount N`: `Effect::Transfer` from the own cell; exit 0 only when a receipt for exactly this turn hash is on chain at accepted finality | `mini fleet --action transfer --to ACCOUNT --amount N`: one `FleetTurn` with fee + transfer | The payer must hold amount + fee (checked on the Book after the fee posting). Confirmation is the exact receipt of this turn's transaction id, naming the original accepted prefix. There are no finality levels: one Store, and a commit is an accepted journal entry. |
| receipt by exact turn hash (`/api/starbridge/receipts?turn_hash=`) | `mini fleet --action receipt --transaction ID` (op 102); `mini fleet --action lookup --attempt DIR` (op 99, from the retained ingress) | The transaction id is derived from the signed command's identity, not from the server's answer; `lookup` re-derives it from the exact retained bytes and never resubmits. An unknown id answers `absent`, never a nearest match. |
| agent receipt head (`fetch_agent_receipt_head`, threaded as `previous_receipt_hash`; one retry onto the node-wide head) | `mini fleet --action receipt --head-of ACCOUNT` (op 101) | Mini does not thread a head into admission; ordering is the operation marker plus a CAS on the exact loaded image, so there is no chain-mismatch refusal to retry (#87, #93 do not arise). The head is a read, behind the account's observe grant. |
| (no verb in `dregg-client-sign`) | `mini fleet --action poll --topic T --since CURSOR` (op 100) | Reading an account's topics requires that account's observe grant. A second agent subscribes by holding a delegated observe-only grant; the topic label confers nothing. Each event returns its sequence, key, transaction id, receipt and exact payload; a missing or digest-mismatched payload fails the poll instead of being skipped. |

## What Bread has that Mini refuses on purpose

- **A faucet and unauthenticated funding.** `POST /api/faucet` accepts any
  `public_key` that derives the recipient; that is the #91 griefing brick.
  Mini funds only from an account whose holder signs.
- **A bearer token for ingress, including on argv** (review F9 and §5). The
  Mini socket is an owner-private local endpoint; authority is the signature
  and the grant, not a token.
- **Transfers that never expire** (`valid_until = i64::MAX / 2`). A Mini
  signature names the current authority root and logical height, so an
  unsubmitted plan dies at the next commit; see the costs below.
- **A coordination-exempt fee class** (F2/F4/F9). Every fleet turn pays the
  tariff.
- **Accepting tentative finality by flag.** There is one level.
- **Retrying onto another agent's head** (#93's `a4f1328b4`). There is no
  head in admission.

## Costs and open edges, measured or read

- **Every commit stales every other agent's plan (MEASURED; the
  fleet-throughput question).** The signing header binds the authority-cell
  root, and every admitted operation consumes its marker in that cell, so a
  plan signed before any other commit is refused at submit with
  `staleAuthority` (checked from the header's root before any signature is
  examined). With two agents publishing at once, 8 of 8 rounds refused one of
  the two. Since `4a33c88` a fleet submit reports this as the Host's typed
  `contention`, and `mini fleet` re-plans in a fresh attempt (at most 8
  times), so every turn lands: K=2, 16 of 16 admitted with 8 re-plans,
  0.186 admitted/s; K=4, 20 of 20 admitted with 30 re-plans (the k-th agent
  to land re-plans k − 1 times), 0.083 admitted/s. Throughput *falls* as
  agents are added, because each losing plan's ~15 Host requests are wasted
  on the one serialized Host process. Bread's per-agent receipt head makes
  contention per agent; Mini's is global. Narrowing what a signature binds
  (for example to the signer's key record and the spent grant, not the whole
  authority root), or moving operation markers out of the root the signature
  names, is the change that would make fleet turns commute. It changes what a
  signature attests, so it is ember's decision, not this lane's. The numbers
  are in [the evidence](evidence/2026-09-30-fleet-surface/README.md).
- **Receipt sealing is O(delta) (MEASURED, fixed in `fe433a1`).** Fleet submit
  first sealed its receipt by reopening the whole Store (`openExisting`, full
  re-verification of the journal); the K=2 probe grew from 26 to 46 s per
  round. It now seals from the session image, refreshed by the appended
  suffix: 7.6 to 13.3 s per round. The remaining growth is the per-request
  reread and decode of the whole durable image. The participant key
  enrollment submit (op 88) still reopens the Store per submit.
- **Journal scans (READ).** Receipt-by-transaction (op 102), the agent head
  (op 101) and poll's payload retrieval find records by a linear pass over
  `durable.image.accepted`. DATAMODEL §3.3 moves `journal : TxId ↦ (height,
  H(turn))` and `receipts : height ↦ digest` into indexed namespaces of the
  system cell (Wave B/C); ops 102 and 100 become exact index reads then. The
  agent head needs an index §3.3 does not list (`payer ↦ newest fleet turn`);
  it should be added with the journal index rather than kept as a scan.
- **Topic pages are cells, not an index.** They are already the typed
  append-only namespace §3.3 wants and do not move.
- **Stream head walk (READ).** Finding the next position walks pages from 0,
  bounded at 4096 pages (16,384 events per stream); a stream-head field would
  make it O(1).
- **One base fee for every fleet turn.** The fee reuses the pinned
  `tariff.base` (already in the runtime parameters). A separate fleet tariff
  pin would be a `Config` field and a re-pin.
- **Authoring errors end the Host session process (OBSERVED, pre-existing).** A
  refused `author` request (op 7) raises out of the stdio session and the
  broker reports the request uncertain; it is not specific to fleet kinds.
- **Per-turn cost (MEASURED; request count READ from the client path).** A
  fleet turn is 15 Host requests — author and inspect the draft, 7 for the
  signed account observation, then plan, assemble and submit, each with its
  inspection (authoring and inspection are Lean's, so the client never
  decodes a binary itself): 2.1 s for send or transfer uncontended on the
  final run.
- **Speaking needs spend authority.** Appending to an account's topic
  requires the `transfer` verb on it, because every turn pays from it. A
  "may publish but not spend" grant would need a new verb in
  `TypedAuthorization`.
