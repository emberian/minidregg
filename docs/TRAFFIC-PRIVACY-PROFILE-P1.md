# Traffic privacy, profile P1 — what it hides, from whom, at what cost

**Devnet quality. Privacy not audited.** This card describes the restricted
registered-cohort mix (`native/resource-client/src/{pq_mailbox,cohort_tcp}.rs`).
There is no proved observation game for it; the reduction from its checks to
an anonymity statement is an open cryptographic composition obligation.

## What it tries to hide

Which honest member sent which request. Precisely: an observer should not be
able to associate an honest member's contribution with an honest output among
**at least two** compatible honest contributions in the same epoch.

The anonymity set is the cohort: **W = 4 members** in the measured profile.
It is never larger than 4, and it shrinks:

- every member the adversary controls removes one from it;
- a member who is offline in an epoch is visibly absent (presence is public);
- two corrupt members of four leave a set of two, the minimum the profile claims.

## Who sees what

| Party | Sees |
|---|---|
| Anyone on the network | cohort membership, each member's IP and connection presence, the public schedule (epoch, phase, slot), fixed packet sizes, public faults. Not contents. |
| The **endpoint** (the Mini Host that executes the call) | **The plaintext signed call and its result**: the author's native signature, the objects touched, the full object graph. The mix hides the network path, not the call. |
| The **registrar** | which member submitted which packet, and the private pairing of every packet's successive hashes. **A registrar that colludes with anyone deanonymizes the epoch.** It is trusted, not decorative. |
| A relay | one batch in, one shuffled batch out, the registrar's published sorted hash sets. One honest relay's shuffle is what unlinks. |
| Every member | the same whole broadcast every epoch. Each can open only its own reply. |

## What you must trust

- an honest, **non-colluding registrar**;
- **at least one honest relay** shuffling whole batches, for every protected epoch;
- an honest mailbox receiver;
- **at least two honest members** with independently private keys and storage;
- the set of corrupt parties is fixed for the whole run (no adaptive corruption);
- nobody later learns old ML-KEM keys, the registrar's pairing records, or retained traffic. **Later key compromise is not covered**; retained mix output plus old keys can rebuild old routes.

Not covered at all: longitudinal intersection across changing cohorts, adaptive
corruption, a malicious intended recipient's own observations.

## Cryptography

- Each packet has four onion layers (three relays + receiver), each ML-KEM-768
  + XChaCha20-Poly1305, +1,160 bytes per layer. Pure ML-KEM, **no classical
  hybrid**.
- Link admission: each fixed link opens only for the roster's member or
  operator, by a signed challenge-bound enrollment (see "Enrollment" below).
- **Not post-quantum end to end.** Native Mini authority (call signatures,
  enrollment signatures) is classical **Ed25519**. Calling the stack
  post-quantum secure would be false.

## Cost (exact codec arithmetic, not provider bills)

Per epoch, for W members and payload P, all fixed links together carry
`P·(W² + 5W) + 17237·W + 1016` bytes, before TCP/IP.

At the measured profile **W = 4, P = 4096, one epoch per second**:

- 217,420 bytes per epoch over all links;
- per member: 8,985 B/s up, 16,492 B/s down (the whole broadcast);
- **≈ 66 GB per member per 30 days** (66.036 GB), ≈ 564 GB across all physical legs;
- the broadcast is O(W²·P): every member downloads every reply.

This is a fixed reservation whether or not you send anything: cover traffic
is the point.

## Latency

One epoch per second, two processing slots per stage: **10 seconds** from a
member's contribution to the broadcast that carries its reply (11 s after the
public origin). That is not one-second delivery. A reply that misses its
broadcast is fetched in a reserved repair epoch (E+3, then E+7), so a slow
call can take 13–17 s end to end. Application completion adds more.

## Failure-leak classes (what can still leak)

1. **Abort without attribution.** One malicious enrolled member can make an
   epoch fail (send nothing valid, or a packet that does not match its
   registered hashes). The whole epoch refuses; nobody learns who. Privacy is
   not a liveness guarantee.
2. **Intermediate unavailability.** If an upstream stage misses its readiness
   cutoff, a corrupt downstream relay sees a physical-unavailable record for
   that epoch. The final broadcast is covered; that intermediate observation is
   not erased.
3. **Timing under contention.** Variable native Host work could miss a
   public release. The single-host v12 run kept every send within 2.3 ms of
   schedule, but that is not a proof that timing is independent of secrets
   under arbitrary contention (v11 showed native I/O disturbing relay readiness).
4. **Presence.** Going offline is public and removes you from the set.
5. **Caller-side completion.** The authorized caller observes when its own
   result arrives; that timing is separate leakage.
6. **Capacity refusal is covered, not hidden from you.** A refused real
   request becomes a valid cover packet plus a private refusal record; the
   network sees cover.

## What one malicious enrolled member can do

- Abort any epoch it participates in, unattributably (class 1).
- Remove itself from the honest anonymity set (it knows its own packet).
- See the whole broadcast; open only its own reply.

It **cannot**: inject a second packet, replace or duplicate another member's
packet (each relay and the receiver check the registrar's exact hash sets and
refuse the whole epoch before any native effect), take another member's slot
(enrollment is bound to the roster key for that slot), or drain another
member's reply (one-time capabilities; duplicate drains refuse).

With the registrar's help it can do anything: the registrar is the trust anchor.

## Enrollment

The cohort is a public roster: for each member slot and each operator role, a
native Ed25519 key and an ML-KEM-768 link key. A link opens only when the sender
signs, with the roster's key for that exact slot, a transcript bound to a fresh
receiver challenge, the profile and the roster's digest, and both ML-KEM
encapsulations (to the receiver's roster key and to a per-connection ephemeral
key) succeed. Unauthenticated, wrong-key and replayed attempts are dropped and
the receiver keeps waiting for the real member. The registrar retains each
member's signed enrollment as admission evidence. No operator-chosen shared
secret is involved.

Still the registrar's (and the roster author's) to get right: who is on the
roster. The roster is public by design (P1 makes membership public).

## Evidence

- v12 (single host, 2026-10-03): all 768 fixed records within 100 ms of
  schedule (max lateness 2.276 ms), identical broadcast to all four members in
  all 64 epochs, identical public shape between an all-cover run and a run
  carrying real work, 16/16 exact outcomes for a **replayed read-only lookup**.
  Every role ran on one machine; that shows schedule shape and exactly-once
  delivery, not anonymity against anyone who can see the co-located processes.
- None yet: no run on two hosts and no run carrying a new effect is recorded in
  this repository (`docs/evidence/` has no traffic directory). The traffic lane was wound down
  on 2026-10-04 before its two-host run (swarm ledger, 03:55); the single-host v12 run
  above is all the evidence this card has.

Sources: `WHY-TRAFFIC-PRIVACY-20261003.txt` lines 18–39 and its cost section;
`PRIVACY-COMPOSITION-REVIEW-20261003.txt` profile P1; `PQ-MAILBOX.md`.
