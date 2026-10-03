# Native Generic Simplex agreement

This is an in-progress domain-log implementation. The current engine, inert
source-history validation cache, transferable COMMIT witness implementation and
streaming storage adapter compile. The four-logical-node native harness passes
with actual TCP, ML-DSA, selective Byzantine COMMIT delivery, durable certificate
recovery after restart, lost CAS replies and the streaming CAS helper. The source
participant and actual workdesk fixture are not yet qualified together.

The model is a fixed committee of n = 3f + 1 with at most f cumulatively Byzantine
members, authenticated reliable delivery and partial synchrony. The configured
timeout must cover the paper's timing bound and actual source validation. Fair
polling alone does not make missing historical source inputs available. Changing
membership, mobile faults and perpetual storage compaction are separate work.

## Durable decisions

GenericSimplex retains old views and ordered audit events. The native journal
replays exact inputs and releases newly enabled messages only after compare-and-
append plus exact readback. A peer cannot supply a source checked event.

A certificate contains distinct ML-DSA-65 signatures on durable COMMIT sends.
It does not require each signer to have locally output a commitment. A Byzantine
sender can supply the final COMMIT only to one honest replica. That replica must
transfer the original quorum evidence without obtaining a new quorum of local
output attestations.

The native COMMIT packet carries a transferable signature covered by its pairwise
MAC. The recipient verifies both, then retains the signature and the counted
delivery in one journal transaction. A recovered certificate imports those same
original COMMIT messages. The statement binds the exact committee context, view
and full block, with the COMMIT-SEND v2 domain separator.

The changed journal and wire schema are not an implicit migration path from the
old local-output profile. Reconfiguration must preserve existing liabilities; a
fresh file or epoch number is not proof that old certificates cannot complete.

## Native source consumer

GenericSimplexParticipant calls the real admission, historical replay and ordered
append receiver:

1. Ordinary ingress is admitted at the verified source tip to derive the complete
   canonical source record. It becomes an offer, with no source append.
2. Proposals and received evidence create pending historical-prefix validation
   work. Only the opaque native validation result creates checked.
3. A verified full certificate orders source records. The next source record is
   freshly derived from its original ingress and compared with the certified
   prefix before the existing physical append/readback operation.
4. Lost replies reload the actual source and reverify historical admission.
   Completion polling returns the source's verified receipt for the exact record.

The client artifact boundary is the existing canonical
`NativeHostCodec.SignedCall` in `call.bin`. `proposeCall` and the fixture's
`runCall` decode that exact frame; an invocation retains its existing signed
command and receives only the deployment's fixed domain/profile encoding.
Birth, install and capability calls retain their original inner ingress bytes.
The adapter performs no signing and does not grant admission. New invocations
retain the existing local synchronous step bound; historical replay and receipt
lookup use the original admission rather than applying today's local bound.
Internal refusal details are operator diagnostics. A shared Host submit hook
must preserve the existing public disclosure policy when mapping those results.

The four-store harness checks distinct configured source and agreement paths
and restores each journal to check its signer index. Its fixture must actually
create those independent stores under one exact consensus-profile genesis.
Changing a previous consensus-free world's configuration does not create that
genesis. After a completed append, the harness discards volatile participant
state, reloads all four stores, replays original admission and locates the exact
retained signed ingress receipt with only one new source record. This is a
software reopen within the driver, not an OS process-kill claim.

An inert empty protocol block changes BFT ancestry but not source history.
Validation may reuse equality of filtered source histories; certificate checks
and the BFT safe-parent rule still use the exact unfiltered block.

A descendant certificate can recover several missing source records one at a
time. The receiver checks that its current source prefix plus the exact next
record is a prefix of that full certificate. It never invents signatures on a
truncated block.

## Service and remaining joins

Fresh traffic, retries, validation and certificate work have separate finite
service opportunities. A retry round fixes its end so a growing outbox cannot
starve older messages. Scheduling cursors may reset after restart because the
journal retains obligations. This physical service API does not create source
funding, private custody qualification or permission to release a reservation.

The optional streaming CAS helper separates journal-file capacity from the
network frame bound. The Lean journal still loads into memory, and complete
logical ancestry still needs a bounded chunk/reassembly transport before it
exceeds a single protocol frame. No pruning or finite-lifetime guarantee follows
from the storage adapter.

Still required for integrated qualification: current-source compilation; the
actual four-node native source fixture; the shared Host propose/await hook; local
guard and receive-provenance extraction into the global consensus proof; source
funding and private recovery joins; and justified checkpoint/reconfiguration
liability retention. VerifiedCommit verifies real signatures at an IO boundary;
it is not itself a proof of cryptographic unforgeability or executable refinement.
