import Kernel.GenericSimplexCertificateSafety
import Kernel.JointReceiver

namespace Minidregg.Kernel.GenericSimplexReceiverSafety
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GenericSimplexCertificateSafety
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
set_option autoImplicit false

/-- Counts are extracted from the actual opaque verifier result. The remaining
premise is ONLY cryptographic/durable sender origin for its honest signers, not
agreement, local commit, or a freely supplied signer set. -/
theorem verifiedCommit_attributed {tr : Trace} {faulty : Finset Nat}
    {context : GenericSimplexCodec.Context}
    (certificate : GenericSimplexIO.VerifiedCommit context)
    (size : context.config.parties = 3 * context.config.faults + 1)
    (honestOrigin : ∀ party ∈ certificate.signerIds, party ∉ faulty →
      ∃ time, Sent tr time party certificate.view .commit (some certificate.block)) :
    AttributedCommitSends tr (Finset.range context.config.parties) faulty
      context.config.faults certificate.view certificate.block := by
  refine ⟨certificate.signerIds.toFinset, ?_, ?_, ?_⟩
  · intro party member
    exact Finset.mem_range.mpr
      (certificate.signers_members party (List.mem_toFinset.mp member))
  · rw [List.toFinset_card_of_nodup certificate.signers_distinct]
    have quorum := certificate.quorum_size
    unfold Minidregg.Kernel.GenericSimplex.Config.quorum at quorum
    omega
  · intro party member honest
    exact honestOrigin party (List.mem_toFinset.mp member) honest

/-- Exact consumer join for two currently ordered native source records at the
same durable source prefix. Attribution MUST be produced by the signature origin
and actual engine refinement; the opaque VerifiedCommit alone does not supply it.
Full descendant certificates remain intact throughout. -/
theorem ordered_next_payload_unique {tr : Trace} {roster faulty : Finset Nat}
    {f : Nat} {context : GenericSimplexCodec.Context} {loaded : Durable}
    {leftIntent rightIntent : DataIntent ResourceBirthCodec.rootBytes}
    (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (left : JointReceiver.Ordered context loaded leftIntent)
    (right : JointReceiver.Ordered context loaded rightIntent)
    (leftOrigin : AttributedCommitSends tr roster faulty f
      left.commitment.view left.commitment.block)
    (rightOrigin : AttributedCommitSends tr roster faulty f
      right.commitment.view right.commitment.block) :
    JointReceiver.sourcePayload leftIntent = JointReceiver.sourcePayload rightIntent := by
  exact certified_next_record_unique rules size faultBound leftOrigin rightOrigin
    left.sourceOrdered right.sourceOrdered

/-- The native applied index selects the exact next record of the unchanged
certificate; it is not inferred from an unauthenticated caller payload. -/
theorem ordered_next_payload_at_index {context : GenericSimplexCodec.Context}
    {loaded : Durable} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (ordered : JointReceiver.Ordered context loaded intent) :
    (sourceHistory ordered.commitment.block)[(JointReceiver.sourcePrefix loaded).length]? =
      some (JointReceiver.sourcePayload intent) :=
  covered_next_at_exact_index ordered.sourceOrdered

#assert_axioms verifiedCommit_attributed
#assert_axioms ordered_next_payload_unique
#assert_axioms ordered_next_payload_at_index
end Minidregg.Kernel.GenericSimplexReceiverSafety
