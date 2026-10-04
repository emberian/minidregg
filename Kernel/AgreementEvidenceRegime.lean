/-
# Kernel.AgreementEvidenceRegime — a Generic Simplex COMMIT certificate is a witness for
ORDERING, never for AUTHORIZATION

The README's sentence "an agreement certificate alone does not authorize or physically
install a change" as a type, through `Theory/ResearchRegime.lean`.

* `AgreementClaim` separates the two things a joint change can claim: `ordered ctx view
  block` (a quorum COMMIT certificate for exactly this block at this view of this
  context exists) and `authorized ctx block` (the change in this block may be installed).
* `commitEvidence accepted` is the regime's verifier over the native certificate type
  `Compiler.GenericSimplexCodec.Certificate`. `accepted` is the native verdict on the exact
  certificate: in deployment `acceptedByNative`, which accepts exactly the certificates
  whose canonical bytes are those of a `GenericSimplexIO.VerifiedCommit` (the type whose
  only producer, `verifyCommitted`, pins the context and checks a quorum of ML-DSA-65
  signatures — an IO boundary, not a proof of unforgeability).
* A COMMIT certificate discharges an `ordered` claim when it binds exactly that
  (context, view, block) and is accepted; it discharges NO `authorized` claim
  (`commit_never_witnesses_authorization`). The signed statement is `commitmentBytes`
  (domain `MINI-SIMPLEX-COMMIT-SEND`), which says nothing about authority; the
  source-applied promise of `Kernel/JointSimplexBinding.lean` is a different statement.

So every honest `Publication` of an authorization claim settled from agreement evidence
renders at most at ballot strength (`authorization_never_rendered_as_witness`); the
witness badge for an install must come from a different verifier (a typed authorization
witness). Consistency between two `ordered` claims is not proved here: it is
`GenericSimplexCertificateSafety.attributed_commit_sends_prefix_consistent`, under
`LocalFaithful`, `roster.card = 3f + 1` and the fault bound.
-/
import Theory.ResearchRegime
import Theory.AssertAxioms
import Compiler.GenericSimplexIO

namespace Minidregg.Kernel.AgreementEvidenceRegime

open Minidregg.Theory Minidregg.Theory.Disputation Minidregg.Theory.OptimisticAdjudication
open Minidregg.Theory.ResearchRegime
open Minidregg.Compiler.GenericSimplexCodec Minidregg.Compiler.GenericSimplexIO
open Minidregg.Kernel.GenericSimplex

set_option autoImplicit false

/-- What a claim about a joint change asserts. -/
inductive AgreementClaim where
  /-- A quorum COMMIT certificate exists for exactly this block at this view of this
  context: the ORDER of the change is agreed. -/
  | ordered (context : Context) (view : Nat) (block : Block)
  /-- The change in this block is AUTHORIZED to install in this context. -/
  | authorized (context : Context) (block : Block)

/-- The commit-certificate verifier. `accepted` is the native verdict on the exact
certificate. No certificate discharges an authorization claim. -/
def certificateVerify (accepted : Certificate → Bool) : AgreementClaim → Certificate → Bool
  | .ordered context view block, cert =>
      decide (cert.context = context) && decide (cert.view = view) &&
        decide (cert.block = block) && accepted cert
  | .authorized _ _, _ => false

/-- The regime's evidence instance over the native certificate type. -/
@[reducible] def commitEvidence (accepted : Certificate → Bool) :
    Verifiable AgreementClaim Certificate :=
  ⟨certificateVerify accepted⟩

/-- The witness regime needs no refutation system: none is offered. -/
@[reducible] def noRefutation (accepted : Certificate → Bool) :
    @Refutable AgreementClaim Certificate Empty (commitEvidence accepted) where
  Refutes := fun _ r => r.elim
  refutes_sound := fun _ r => r.elim

/-- The deployment verdict: a certificate is accepted exactly when its canonical bytes
are those of a commit the native verifier returned. -/
def acceptedByNative (verified : List (Σ expected : Context, VerifiedCommit expected))
    (cert : Certificate) : Bool :=
  verified.any fun v => certificateStream.encode cert == v.2.bytes

/-- A publication about agreement evidence. -/
abbrev AgreementPublication (accepted : Certificate → Bool) (ι : Type) :=
  @Publication AgreementClaim Certificate Empty ι (commitEvidence accepted) (noRefutation accepted)

/-- **A COMMIT certificate never witnesses authorization**, whatever the native verifier
accepts. -/
theorem commit_never_witnesses_authorization (accepted : Certificate → Bool)
    (context : Context) (block : Block) :
    ¬ @upheld AgreementClaim Certificate (commitEvidence accepted)
        ⟨.authorized context block⟩ := by
  rintro ⟨cert, h⟩
  change certificateVerify accepted (.authorized context block) cert = true at h
  simp [certificateVerify] at h

/-- **An accepted certificate witnesses exactly its own order.** -/
theorem accepted_certificate_upholds_its_order (accepted : Certificate → Bool)
    (cert : Certificate) (h : accepted cert = true) :
    @upheld AgreementClaim Certificate (commitEvidence accepted)
      ⟨.ordered cert.context cert.view cert.block⟩ :=
  ⟨cert, by
    change certificateVerify accepted (.ordered cert.context cert.view cert.block) cert = true
    simp [certificateVerify, h]⟩

/-- **The authorization badge is unconstructible from agreement evidence.** Any honest
publication of an authorization claim, whatever regime it was settled in, is not rendered
as a witness: the honesty field would force a discharging certificate, and none exists. -/
theorem authorization_never_rendered_as_witness {ι : Type} (accepted : Certificate → Bool)
    (pub : AgreementPublication accepted ι) {context : Context} {block : Block}
    (hclaim : pub.claim = ⟨.authorized context block⟩) :
    pub.renderedAs ≠ Regime.witness := by
  letI := commitEvidence accepted
  letI := noRefutation accepted
  intro hw
  have hup := rendered_witness_is_true pub hw
  rw [hclaim] at hup
  exact commit_never_witnesses_authorization accepted context block hup

/-- **The ordering publication of an accepted certificate**, settled and rendered as a
witness. -/
def orderingPublication {ι : Type} (accepted : Certificate → Bool) (ballot : Ballot ι)
    (cert : Certificate) (h : accepted cert = true) : AgreementPublication accepted ι :=
  letI := commitEvidence accepted
  letI := noRefutation accepted
  { claim := ⟨.ordered cert.context cert.view cert.block⟩
    observed := fun r => r.elim
    ballot := ballot
    settledIn := Regime.witness
    renderedAs := Regime.witness
    settlement := accepted_certificate_upholds_its_order accepted cert h
    honest := le_refl _ }

/-- The signers of a certificate, as a ballot: carried iff a quorum of distinct
configured parties signed. An install agreed this way is a BALLOT verdict. -/
def signerBallot (cert : Certificate) : Ballot Nat where
  asserts := fun i => i ∈ cert.signers.map Attestation.signer
  aggregates := fun a => ∃ s : Finset Nat, (∀ i ∈ s, a i) ∧
    cert.context.config.quorum ≤ s.card

/-- **The honest typing of "the committee agreed to install"**: an authorization claim
settled by the signer ballot and rendered as a ballot — the strongest badge agreement
evidence alone licenses. -/
def installByAgreement (accepted : Certificate → Bool) (cert : Certificate)
    (h : (signerBallot cert).upholds) : AgreementPublication accepted Nat :=
  letI := commitEvidence accepted
  letI := noRefutation accepted
  { claim := ⟨.authorized cert.context cert.block⟩
    observed := fun r => r.elim
    ballot := signerBallot cert
    settledIn := Regime.ballot
    renderedAs := Regime.ballot
    settlement := h
    honest := le_refl _ }

/-! ## Keystones — a concrete certificate, every pole named.

The context is `default` and the certificate carries one signer under a quorum-one
configuration; `accepted₀` accepts exactly this certificate (the toy stands in for the
native verifier's verdict; `acceptedByNative` is the deployment one). -/

namespace Keystone

/-- A quorum-one configuration (one party, no faults). -/
def config₀ : GenericSimplex.Config := { (default : GenericSimplex.Config) with parties := 1, faults := 0 }

/-- The context. -/
def context₀ : Context := { (default : Context) with config := config₀ }

/-- The certificate: block `[[1]]` at view `1`, signed by party `0`. -/
def cert₀ : Certificate :=
  { context := context₀, view := 1, block := [[1]], signers := [⟨0, []⟩] }

/-- The native verdict, stood in: accept exactly `cert₀`. -/
def accepted₀ (cert : Certificate) : Bool := decide (cert = cert₀)

theorem accepted₀_cert₀ : accepted₀ cert₀ = true := by simp [accepted₀]

/-- The ordering publication, built from the real constructor. -/
def publication₀ : AgreementPublication accepted₀ Nat :=
  orderingPublication accepted₀ (signerBallot cert₀) cert₀ accepted₀_cert₀

/-- **The witness theorem bites on it**: its claim is upheld. -/
theorem publication₀_upheld :
    @upheld AgreementClaim Certificate (commitEvidence accepted₀) publication₀.claim :=
  letI := commitEvidence accepted₀
  letI := noRefutation accepted₀
  rendered_witness_is_true publication₀ rfl

/-- **Teeth (order)**: no accepted certificate orders that block at view `2`. -/
theorem other_view_not_upheld :
    ¬ @upheld AgreementClaim Certificate (commitEvidence accepted₀)
        ⟨.ordered context₀ 2 [[1]]⟩ := by
  rintro ⟨cert, h⟩
  change certificateVerify accepted₀ (.ordered context₀ 2 [[1]]) cert = true at h
  simp only [certificateVerify, accepted₀, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, hview⟩, -⟩, rfl⟩ := h
  simp [cert₀] at hview

/-- The signer ballot of `cert₀` carries (party `0` signed; quorum one). -/
theorem signerBallot_upholds : (signerBallot cert₀).upholds := by
  show ∃ s : Finset Nat, (∀ i ∈ s, i ∈ cert₀.signers.map Attestation.signer) ∧
    cert₀.context.config.quorum ≤ s.card
  refine ⟨{0}, ?_, ?_⟩
  · simp [cert₀]
  · simp [cert₀, context₀, config₀, GenericSimplex.Config.quorum]

/-- **The install agreed by the committee, honestly typed**: constructible at ballot
strength, and its claim is NOT upheld — agreement evidence carries no authorization. -/
theorem install_by_agreement_carries_no_authorization :
    ¬ @upheld AgreementClaim Certificate (commitEvidence accepted₀)
        (installByAgreement accepted₀ cert₀ signerBallot_upholds).claim :=
  commit_never_witnesses_authorization accepted₀ context₀ [[1]]

/-- **And it cannot be re-badged as a witness.** -/
theorem install_by_agreement_not_witness :
    (installByAgreement accepted₀ cert₀ signerBallot_upholds).renderedAs ≠ Regime.witness :=
  authorization_never_rendered_as_witness accepted₀ _ rfl

end Keystone

#assert_axioms commit_never_witnesses_authorization
#assert_axioms accepted_certificate_upholds_its_order
#assert_axioms authorization_never_rendered_as_witness
#assert_axioms Keystone.publication₀_upheld
#assert_axioms Keystone.other_view_not_upheld
#assert_axioms Keystone.signerBallot_upholds
#assert_axioms Keystone.install_by_agreement_carries_no_authorization
#assert_axioms Keystone.install_by_agreement_not_witness

end Minidregg.Kernel.AgreementEvidenceRegime
