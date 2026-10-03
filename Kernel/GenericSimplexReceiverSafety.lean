import Kernel.GenericSimplexEngineSafety
import Kernel.GenericSimplexLawfulBEq
import Kernel.JointReceiver

namespace Minidregg.Kernel.GenericSimplexReceiverSafety
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GenericSimplexCertificateSafety
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
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

/-- The real exporter guard implies the real retained COMMIT send. This proves
its executable audit check, not cryptographic unforgeability of external bytes. -/
theorem exportable_has_durable_send (state : Minidregg.Kernel.GenericSimplex.State)
    (view : Nat) (block : Minidregg.Kernel.GenericSimplex.Block)
    (admitted : GenericSimplexCodec.exportable state view block = true) :
    (.send ⟨state.self, view, .commit, some block⟩ : Minidregg.Kernel.GenericSimplex.AuditEvent)
      ∈ state.audit := by
  simp only [GenericSimplexCodec.exportable, Bool.and_eq_true] at admitted
  simpa using admitted.2

open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexEngineSafety
/-- Export eligibility at an actual reachable replica yields an actual global
SEND witness, via the retained local audit and its proved owner projection. -/
theorem reachable_exportable_sent {faulty : Finset Nat}
    {c : Minidregg.Kernel.GenericSimplex.Config}
    {checked : Network → Nat → Minidregg.Kernel.GenericSimplex.Block → Prop}
    {initialTime : Nat} {net : Network} (reachable : Reachable c faulty checked initialTime net)
    (party view : Nat) (block : Minidregg.Kernel.GenericSimplex.Block)
    (enrolled : party < c.parties) (honest : party ∉ faulty)
    (admitted : GenericSimplexCodec.exportable (net.localState party) view block = true) :
    ∃ time, Sent (auditTrace net) time party view .commit (some block) := by
  have projected := Minidregg.Kernel.GenericSimplexAuditProjection.reachable_projected
    (Minidregg.Kernel.GenericSimplexStructure.structuralAuditLaws c) reachable
  have globalSend := Minidregg.Kernel.GenericSimplexGlobalReceive.local_audit_in_global
    projected enrolled honest (exportable_has_durable_send _ view block admitted)
  rw [projected.identity party enrolled honest] at globalSend
  obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp globalSend
  exact ⟨index, by simp only [Sent, auditTrace, atIndex, Option.getD_some]⟩

/-- Actual executable reachability supplies the consensus contract. The only
signature-specific premise is the origin of the verifier's actual honest signers.
The full opaque descendant certificates and receiver prefix checks are consumed. -/
theorem actual_ordered_next_payload_unique {faulty : Finset Nat}
    {context : GenericSimplexCodec.Context} {loaded : Durable}
    {checked : Network → Nat → Minidregg.Kernel.GenericSimplex.Block → Prop}
    {initialTime : Nat} {net : Network}
    {leftIntent rightIntent : DataIntent ResourceBirthCodec.rootBytes}
    (reachable : Reachable context.config faulty checked initialTime net)
    (size : context.config.parties = 3 * context.config.faults + 1)
    (faultBound : faulty.card ≤ context.config.faults)
    (left : JointReceiver.Ordered context loaded leftIntent)
    (right : JointReceiver.Ordered context loaded rightIntent)
    (leftOrigin : ∀ party ∈ left.commitment.signerIds, party ∉ faulty →
      ∃ time, Sent (auditTrace net) time party left.commitment.view .commit (some left.commitment.block))
    (rightOrigin : ∀ party ∈ right.commitment.signerIds, party ∉ faulty →
      ∃ time, Sent (auditTrace net) time party right.commitment.view .commit (some right.commitment.block)) :
    JointReceiver.sourcePayload leftIntent = JointReceiver.sourcePayload rightIntent :=
  actual_certified_next_record_unique reachable size faultBound
    (verifiedCommit_attributed left.commitment size leftOrigin)
    (verifiedCommit_attributed right.commitment size rightOrigin)
    left.sourceOrdered right.sourceOrdered

#assert_axioms reachable_exportable_sent
#assert_axioms exportable_has_durable_send
#assert_axioms actual_ordered_next_payload_unique
#assert_axioms verifiedCommit_attributed
#assert_axioms ordered_next_payload_unique
#assert_axioms ordered_next_payload_at_index
end Minidregg.Kernel.GenericSimplexReceiverSafety
