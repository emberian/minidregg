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

/-- Counts are extracted from the actual opaque verifier result. A certificate names its
chain by a digest and carries none of it, so the chain is the caller's: `block` is the chain
the certificate's honest signers sent their COMMIT for. That premise is cryptographic and
durable sender origin (a signature on the statement comes from a COMMIT send for a chain with
that statement) together with the digest's collision-freedom among the chains correct
members send (one chain per statement). It is not agreement, local commit, or a freely
supplied signer set. -/
theorem verifiedCommit_attributed {tr : Trace} {faulty : Finset Nat}
    {context : GenericSimplexCodec.Context}
    (certificate : GenericSimplexIO.VerifiedCommit context)
    (block : Minidregg.Kernel.GenericSimplex.Block)
    (size : context.config.parties = 3 * context.config.faults + 1)
    (honestOrigin : ∀ party ∈ certificate.signerIds, party ∉ faulty →
      ∃ time, Sent tr time party certificate.view .commit (some block)) :
    AttributedCommitSends tr (Finset.range context.config.parties) faulty
      context.config.faults certificate.view block := by
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

/-- Any roster size: the native verifier's own `Config.quorum = n - f` signer count
is the certificate quorum, with no `n = 3f + 1` premise. `block` is the caller's chain,
under the same origin and digest premises as `verifiedCommit_attributed`. -/
theorem verifiedCommit_attributed_at {tr : Trace} {faulty : Finset Nat}
    {context : GenericSimplexCodec.Context}
    (certificate : GenericSimplexIO.VerifiedCommit context)
    (block : Minidregg.Kernel.GenericSimplex.Block)
    (honestOrigin : ∀ party ∈ certificate.signerIds, party ∉ faulty →
      ∃ time, Sent tr time party certificate.view .commit (some block)) :
    AttributedCommitSendsAt tr (Finset.range context.config.parties) faulty
      context.config.quorum certificate.view block := by
  refine ⟨certificate.signerIds.toFinset, ?_, ?_, ?_⟩
  · intro party member
    exact Finset.mem_range.mpr
      (certificate.signers_members party (List.mem_toFinset.mp member))
  · rw [List.toFinset_card_of_nodup certificate.signers_distinct]
    exact certificate.quorum_size
  · intro party member honest
    exact honestOrigin party (List.mem_toFinset.mp member) honest

/-- Exact consumer join for any roster size whose thresholds satisfy `Thresholds`. -/
theorem ordered_next_payload_unique_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r : Nat} {context : GenericSimplexCodec.Context} {loaded : Durable}
    {leftIntent rightIntent : DataIntent ResourceBirthCodec.rootBytes}
    (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Minidregg.Kernel.GenericSimplexQuorum.Thresholds roster.card f q c r)
    (faultBound : faulty.card ≤ f)
    (left : JointReceiver.Ordered context loaded leftIntent)
    (right : JointReceiver.Ordered context loaded rightIntent)
    (leftBlock rightBlock : Minidregg.Kernel.GenericSimplex.Block)
    (leftReads : sourceHistory leftBlock = left.history)
    (rightReads : sourceHistory rightBlock = right.history)
    (leftOrigin : AttributedCommitSendsAt tr roster faulty q
      left.commitment.view leftBlock)
    (rightOrigin : AttributedCommitSendsAt tr roster faulty q
      right.commitment.view rightBlock) :
    JointReceiver.sourcePayload leftIntent = JointReceiver.sourcePayload rightIntent := by
  exact certified_next_record_unique_at rules th faultBound leftOrigin rightOrigin
    (leftReads ▸ left.sourceOrdered) (rightReads ▸ right.sourceOrdered)

/-- Exact consumer join for two currently ordered native source records at the
same durable source prefix. Attribution MUST be produced by the signature origin
and actual engine refinement; the opaque VerifiedCommit alone does not supply it.
`leftBlock` and `rightBlock` are the chains the two certificates' honest signers sent, and
`leftReads`, `rightReads` say each token's history is that chain's application history: for
the native digest that is `chainDigest_history` and collision-freedom of the history digest
between the token's history and the chain's. -/
theorem ordered_next_payload_unique {tr : Trace} {roster faulty : Finset Nat}
    {f : Nat} {context : GenericSimplexCodec.Context} {loaded : Durable}
    {leftIntent rightIntent : DataIntent ResourceBirthCodec.rootBytes}
    (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (left : JointReceiver.Ordered context loaded leftIntent)
    (right : JointReceiver.Ordered context loaded rightIntent)
    (leftBlock rightBlock : Minidregg.Kernel.GenericSimplex.Block)
    (leftReads : sourceHistory leftBlock = left.history)
    (rightReads : sourceHistory rightBlock = right.history)
    (leftOrigin : AttributedCommitSends tr roster faulty f
      left.commitment.view leftBlock)
    (rightOrigin : AttributedCommitSends tr roster faulty f
      right.commitment.view rightBlock) :
    JointReceiver.sourcePayload leftIntent = JointReceiver.sourcePayload rightIntent := by
  exact certified_next_record_unique rules size faultBound leftOrigin rightOrigin
    (leftReads ▸ left.sourceOrdered) (rightReads ▸ right.sourceOrdered)

/-- The native applied index selects the exact next record of the history the token reads;
it is not inferred from an unauthenticated caller payload. -/
theorem ordered_next_payload_at_index {context : GenericSimplexCodec.Context}
    {loaded : Durable} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (ordered : JointReceiver.Ordered context loaded intent) :
    ordered.history[(JointReceiver.sourcePrefix loaded).length]? =
      some (JointReceiver.sourcePayload intent) :=
  covered_next_at_exact_index ordered.sourceOrdered

open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexEngineSafety
/-- Actual executable reachability supplies the consensus contract, for every admitted
roster `n ≥ 3f + 1`: the certificate quorum is the native verifier's own `Config.quorum`
(`verifiedCommit_attributed_at`). The signature-specific premises are the origin of the
verifier's actual honest signers (the chain each sent its COMMIT for) and that each token's
history is that chain's application history. -/
theorem actual_ordered_next_payload_unique {faulty : Finset Nat}
    {context : GenericSimplexCodec.Context} {loaded : Durable}
    {checked : Network → Nat → Minidregg.Kernel.GenericSimplex.Block → Prop}
    {initialTime : Nat} {net : Network}
    {leftIntent rightIntent : DataIntent ResourceBirthCodec.rootBytes}
    (reachable : Reachable context.config faulty checked initialTime net)
    (admitted : 3 * context.config.faults + 1 ≤ context.config.parties)
    (faultBound : faulty.card ≤ context.config.faults)
    (left : JointReceiver.Ordered context loaded leftIntent)
    (right : JointReceiver.Ordered context loaded rightIntent)
    (leftBlock rightBlock : Minidregg.Kernel.GenericSimplex.Block)
    (leftReads : sourceHistory leftBlock = left.history)
    (rightReads : sourceHistory rightBlock = right.history)
    (leftOrigin : ∀ party ∈ left.commitment.signerIds, party ∉ faulty →
      ∃ time, Sent (auditTrace net) time party left.commitment.view .commit (some leftBlock))
    (rightOrigin : ∀ party ∈ right.commitment.signerIds, party ∉ faulty →
      ∃ time, Sent (auditTrace net) time party right.commitment.view .commit (some rightBlock)) :
    JointReceiver.sourcePayload leftIntent = JointReceiver.sourcePayload rightIntent :=
  actual_certified_next_record_unique reachable admitted faultBound
    (verifiedCommit_attributed_at left.commitment leftBlock leftOrigin)
    (verifiedCommit_attributed_at right.commitment rightBlock rightOrigin)
    (leftReads ▸ left.sourceOrdered) (rightReads ▸ right.sourceOrdered)

#assert_axioms actual_ordered_next_payload_unique
#assert_axioms verifiedCommit_attributed
#assert_axioms ordered_next_payload_unique
#assert_axioms ordered_next_payload_at_index
#assert_axioms verifiedCommit_attributed_at
#assert_axioms ordered_next_payload_unique_at
end Minidregg.Kernel.GenericSimplexReceiverSafety
