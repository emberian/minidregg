# Native Generic Simplex agreement

This is an in-progress domain-log implementation. The current engine, inert
source-history validation cache, transferable COMMIT witness implementation and
streaming storage adapter compile. The four-logical-node native harness passes
with actual TCP, ML-DSA, selective Byzantine COMMIT delivery, durable certificate
recovery after restart, lost CAS replies and the streaming CAS helper. The source
participant and four-store driver compile against the frozen 373-module receiver
cohort. The actual workdesk fixture has not run.

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
The adapter first checks the existing native decoder for the outer call family.
A birth/install/capability wrapper cannot smuggle signed invocation bytes into
generic historical replay and bypass the live invocation budget. The adapter
performs no signing and does not grant admission. New invocations
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

Current source consumer compilation passed against the frozen receiver cohort.
Still required for integrated qualification: the actual four-node signed source
action, shared Host propose/await hook, the final native-consumer binding to the
reachable-engine proof, source funding and private recovery joins, and justified
checkpoint/reconfiguration liability retention. VerifiedCommit verifies real signatures at an IO boundary;
it is not itself a proof of cryptographic unforgeability or executable refinement.


## Ordinary operator bridge

`Verify.GenericSimplexOperatorBridge.submit` accepts the original native
SignedCall and actual opened replicas. If any native verified source already
contains that ingress, it drives the other participants to the exact retained
record using recovered certificates. It does not propose the mutation again.
It returns a confirmation only after all four have the same exact source prefix
through that call and exact receipt. Later agreed records may have reached only
some participants without blocking lookup of the earlier completed call. An exception during possible progress produces a uniform uncertain
outcome and refreshes actual sources; it is never reported as a rollback.

`testing/generic-simplex-operator.py` speaks the existing four-byte little-endian
length plus opcode/payload protocol and its exact 12,102,760-byte Host body
bound (distinct from the crypto helper frame limit). The owner supplies
`MINI_AGREEMENT_BRIDGE_CONFIG`, whose JSON has:

- `readerCommand`: explicit argv for the matching native Host on source store 0.
- `submitCommand`: explicit argv prefix for the real fixture's `submit-call`;
  the bridge appends original-call path, native-outcome path, and service fuel.
- `clientArguments`: exact client launch argv accepted by this wrapper.
- `attempts`: existing owner-private directory for retained exact signed calls.
- `fuel` and `timeoutSeconds`: finite positive operator service bounds.

Only opcode 2 takes the agreement route. Opcodes 0, 1, 3 through 11, 91 and 144 use the
matching Host's existing read, lookup, preparation and authoring handlers.
Opcode91 retains the signed current factory-observation birth gate; opcode144
performs the actual current signing-key status check. Every
other opcode fails closed; it cannot fall through to another mutation family.
The matched Host must use the actual same consensus-profile genesis and source
store. This wrapper does not authorize changing an existing world's profile.

The bridge retains and fsyncs the original call before invoking the native
consumer. It takes response bytes only from that consumer's bounded private
outcome file. A process timeout closes the client connection and retains the call;
there is no automatic second semantic dispatch. Exact lookup/retry uses the
existing source receipt and agreement evidence.

Current qualification: seven Python framing/file/process-boundary checks pass,
including an actual child timeout with no redispatch. The Lean operator bridge, exact-prefix completion refinement and native
call-family guard compile against the passing source consumer and frozen receiver
cohort. The matched standalone reader and operator have run against the actual four
source stores: profile/seed agreement, wrong-pin rejection, refusal of direct
reader submission and both enrolled current signing keys passed.

A development mesh of four replicas in one process on one host has since committed two
application records and then stalled on the third (scout R2-3, 2026-10-03; recorded
outside this repository, and not reproduced here). Its diagnosis: two replicas reached
their view timeout before collecting a quorum of VOTEs, because one drive iteration took
15-27 s against a timeout that needs Delta below timeout/7, and the engine ran only while
a client request was open. That is lawful behaviour of the engine, not a safety fault.
The liveness fixes (standing replicas, a cheaper iteration, an adaptive timeout) are not
on main, so liveness is not established; the safety theorems are over the Lean engine model.
This local four-participant driver does not claim four independent processes or
failure domains. Operator service fuel is not a source-funded recovery grant.

The native call-family guard and general mismatch-refusal theorem passed their
scoped check before the first source action. The earlier compiled adapter lacked
this outer/inner family equality; no source mutation was run through it.
