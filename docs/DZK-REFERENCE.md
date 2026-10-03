# Distributed degree proof reference

The native private backend now has a concrete Appendix B distributed degree
proof: a dealer proves degree-bounded Shamir column values, parties receive the
private proof through the actual recipient-private delivery protocol, and a
holder can transfer its verified values and proof to another recipient.

This is a bounded classical random-oracle reference construction. It is not a
QROM/PQ qualification or a native admission/declassification authority.

## Construction and domain

The source follows Appendix B of ePrint 2024/1666 and the ACSS-Id use in
sections 4.1–4.2, pages 13–14. The local primary text SHA256 is
40360a415737d6cd6ac4068d08c8fe4df69496e8b970aff3dce5f1a2a3974df4.

- Roster n = 3f + 1, 4 <= n <= 16, polynomial count 1..128, degree d < n.
- ACSS-Id uses exactly degree f and L/(f+1) column polynomials.
- Evaluation point of holder i (zero-based native index) is GF128(i+1);
  reconstruction point alpha0 is GF128(0).
- GF(2^128) uses x^128+x^7+x^2+x+1, the backend's existing reference Field.
  Its arithmetic is not a constant-time online secret processor.
- Compression factor u = 2. Repeated degree ceil(d/2) ends at <=1.
  For each stage s=d_previous-d_next, f_previous=g0+X^s*g1.
  This includes odd-degree boundaries; no coefficient is truncated.
- Initial commitment opens (f0(alpha_i),f1(alpha_i),...,fN(alpha_i)).
  Later commitments open the two compression-block evaluations.
- Every real Merkle leaf is masked by an independent domain-separated 32-byte
  salt. Trees pad to the next power of two and bind the context/stage/index.
- Challenges are the low 128 bits of SHA256 over a dedicated domain, the exact
  protocol context and the entire ordered root prefix.
- One retained 32-byte OS-random seed expands into mask coefficients, leaf salts
  and the independent private-delivery key coefficients using separate domains.
  The seed stays in the owner-private WAL and is never transmitted.

The paper uses an extension G of size approximately 2^(n+kappa). The reference
uses existing GF128 for both polynomial and challenge arithmetic. It consequently
does NOT inherit a kappa=128 soundness claim. Appendix B's corrupted-prover
argument incurs all-subset, verifier, polynomial-count, compression-round and
Fiat–Shamir query/grinding factors. A conservative elementary accounting term
before hash/PRG/PrivSend costs is proportional to

    Q * n * 2^n * (N + 2*tau) / 2^128.

At n=16,N=128,tau<=4 that numerator has roughly 27 bits before Q. This expression
documents the finite-field loss; it is not an implementation-refinement or
simulation proof. Classical SHA256 binding/hiding and seed expansion, static
cumulative f corruption, authenticated confidential reliable channels, and the
PrivSend replacement's explicit assurance boundaries remain separate assumptions.
Do not advertise QROM or full PQ security from the use of hashes.

## Actual interfaces

Profile::new binds the full original Generation, n/f/dealer/count/degree and
algorithm version into context. Each private proof slot derives a child protocol
invocation from this context and its holder index. The original native custody
descriptor Generation remains unchanged.

Dzk::new(me,dealer,n,f,g,count,degree) creates one actual Bracha reliable
broadcast for the public proof and n actual PrivateSend instances, one per
holder's fixed-length private proof. Once all instances disperse, each party
requests delivery of each holder proof to that holder.

Delivered is constructed only after all n private instances disperse, the
public proof is reliably delivered and the local holder proof is delivered.
It certifies availability of bytes. A malicious dealer's invalid proof may be
Delivered and then Rejected; availability is never promoted to proof validity.

authorize_verification(holder,receiver) is a source/environment request event.
It requests actual PrivateSend delivery to the receiver. PrivateSend requires
f+1 completed authenticated request broadcasts. This is not a message carrying a
permission boolean; the native enrolled-credential/current-authority adapter
must authenticate and govern the originating request.

verify_private(holder,values) waits for the distributing phase and private
proof delivery to this verifier, then checks every Merkle opening, all challenge
relations and the final degree-bounded polynomial. It returns one of:

- Verification::Accepted(VerifiedShares), binding context, holder, receiver,
  exact values and the reliably broadcast public-proof hash.
- Verification::Rejected(RejectedProof), binding context, holder, receiver and
  the exact public/proof/value evidence hash.
- WouldBlock for unavailable distribution/private proof.

Evidence fields are private: callers can inspect getters but cannot construct
a fake VerifiedShares from a callback result.

transfer(receiver,values) verifies the sender's own holder proof and emits a
recipient-bound Transfer with values and the actual private proof. The receiver
requires the authenticated sender to equal the claimed holder, requires its own
recipient index, and verifies against the same delivered public proof. Early
transfers are bounded and retained until local distribution completes; malformed
transfers cannot create accepted points. transferred(holder) returns typed
reverified point evidence.

open_proof(holder,values) returns the actual public/private proof bytes, values
and typed verification result. It supplies evidence for ACSS accusations; it
does not itself grant public-release authority. ACSS must invoke it only under
its source-authorized complaint/open-proof phase, and evaluate the received
row polynomial/column points against the actual dZK instance.

## Persistence

dzk_store::Store uses the existing deterministic transition Journal:

- Dealer event retains exact polynomial coefficients and random seed.
- Source/environment delivery request, authenticated receive, and proof transfer
  events retain their exact canonical bytes.
- The event and exact resulting outbox are fsynced before publication.
- Reopen re-executes every event and compares the exact recorded outbox.
- Exact dealer retry returns retained packets; changed coefficients refuse.
- Identity binds party, full Generation and protocol context.
- Partial record, replay disagreement, wrong identity and uncertain IO refuse.

The WAL is owner-private. Its checksum protects honest crash storage and detects
tears; it is not authentication against malicious snapshot rollback. Independent
monotonic checkpoint/correlation custody is a receiving obligation.

## Receiving checks

The narrow command is:

    cargo nextest run --release --locked --lib -E 'test(/dzk/)'

The first five selected tests passed using an independently frozen source copy
and bounded Rust build seat. The expanded eight-test source additionally covers:

- Every degree 0..3 and malformed shares, opening salts and final polynomial.
- Actual compressed n=7,f=2 distribution with two parties withholding.
- Malicious dealer public proof Delivered but Rejected/OpenProof, no transfer.
- Real private proof delivery to a third-party verifier.
- Cross-generation/context, holder/sender and recipient substitution.
- Malformed transferred proof and early-transfer revalidation.
- Canonical wire framing and persisted recipient transfer/replay.
- Retained dealer randomness/outboxes, changed inputs/identity and torn WAL.

See the exact build receipt for the tested source hashes and final result.
ACSS-Id, triples, malicious multiplication and private evaluator installation are
distinct consumers; this dZK module alone does not complete them.

