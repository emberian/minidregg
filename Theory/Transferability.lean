/-
# `Theory.Transferability` — the transferability dial: public vs designated-verifier evidence

`Theory.Knowledge` has ONE verify relation, `Discharged p w := Verify p w = true`, not indexed by
who is checking. Every discharged witness therefore convinces everyone: Knowledge can only express
non-repudiable, transferable evidence. That is right for agreement certificates and wrong for
deniable agent authorization and private returns, where evidence should convince one designated
verifier and nobody else.

This module adds the missing axis.

* `VerifierIndexed` / `DischargedFor v s p` — a verify relation indexed by the checking party.
* The dial's two endpoints: `Transferable` (convinces every verifier: the PUBLIC pole) and
  `DesignatedFor v₀` (convinces `v₀` and is not transferable: the DESIGNATED-VERIFIER pole).
* `knowledge_is_public_pole` — Knowledge's `Discharged` is exactly the public pole of the dial
  (`publicMode_collapses_to_universal` is that collapse for the dial's `transferable` setting).
* `VerifierBlind` — the verdict does not depend on who checks. A blind check has an empty DV pole
  (`blind_no_designated`), and a blind check WITH a simulator is universally forgeable
  (`blind_simulator_forges`): deniability and public verifiability cannot coexist. That is the
  precise reason a DV-mode receipt needs a verifier-secret-dependent check.
* `DVKernel` — the designated-verifier portal (a verifier secret and a simulator with its law), and
  `designated_is_deniable` / `designated_not_transferable` on it.
* `DVReceiptMode` — what a DV-mode receipt for a private return needs, with an inhabitant
  (`Reference.referenceReceiptMode`) and its consequence (`DVReceiptMode.simulated_is_designated`).

The classification of Mini's concrete evidence objects lives beside the objects themselves
(`Compiler/GenericSimplexTransferability.lean` for the ML-DSA COMMIT certificate), since `Theory`
may not import the candidate.

**Port provenance (Mini, 2026-10-04).** Re-derived from breadstuffs
`metatheory/Dregg2/Authority/DesignatedVerifier.lean` (sha256 `664bb6b4b906c0a7b250ade469f2a6486b6277e7c273a795bd186773b14279b0`) on `Theory.Knowledge`
instead of `Dregg2.CryptoKernel` (which Bread imported but did not use). Bread's single class is
split into `VerifierIndexed` (the indexed check) and `DVKernel` (secret + simulator), so the public
pole can be stated without a simulator. Ported statements keep Bread's names; the `#guard` lines of
Bread's reference kernel are replaced by named theorems.
-/
import Theory.Knowledge
import Mathlib.Logic.Basic

namespace Minidregg.Theory.Transferability

open Minidregg.Theory

set_option autoImplicit false

/-! ## The verifier-indexed check -/

/-- A verify relation indexed by the checking party. -/
class VerifierIndexed (Verifier : Type*) (Statement : Type*) (Proof : Type*) where
  verifyFor : Verifier → Statement → Proof → Bool

variable {Verifier Statement Proof : Type*}

/-- Verifier `v` is convinced that `p` discharges `s`. -/
def DischargedFor [VerifierIndexed Verifier Statement Proof]
    (v : Verifier) (s : Statement) (p : Proof) : Prop :=
  VerifierIndexed.verifyFor v s p = true

instance [VerifierIndexed Verifier Statement Proof] (v : Verifier) (s : Statement) (p : Proof) :
    Decidable (DischargedFor v s p) :=
  inferInstanceAs (Decidable (_ = true))

/-- The PUBLIC pole: the transcript convinces every verifier (non-repudiable). -/
def Transferable (Verifier : Type*) {Statement Proof : Type*}
    [VerifierIndexed Verifier Statement Proof] (s : Statement) (p : Proof) : Prop :=
  ∀ v : Verifier, DischargedFor v s p

/-- The DESIGNATED-VERIFIER pole: convinces `v₀` and is not transferable. -/
def DesignatedFor [VerifierIndexed Verifier Statement Proof]
    (v₀ : Verifier) (s : Statement) (p : Proof) : Prop :=
  DischargedFor v₀ s p ∧ ¬ Transferable Verifier s p

/-- The dial. -/
inductive TransferDial (Verifier : Type*) where
  | transferable
  | designated (v₀ : Verifier)

/-- The proposition each dial setting demands of a transcript. -/
def DialHolds [VerifierIndexed Verifier Statement Proof]
    (dial : TransferDial Verifier) (s : Statement) (p : Proof) : Prop :=
  match dial with
  | .transferable => Transferable Verifier s p
  | .designated v₀ => DesignatedFor v₀ s p

/-- Public mode is the `∀ v` collapse. -/
theorem publicMode_collapses_to_universal [VerifierIndexed Verifier Statement Proof]
    (s : Statement) (p : Proof) :
    DialHolds (Verifier := Verifier) .transferable s p ↔ ∀ v : Verifier, DischargedFor v s p :=
  Iff.rfl

/-- Non-repudiation: a transferable transcript convinces any third party. -/
theorem public_convinces_any_third_party [VerifierIndexed Verifier Statement Proof]
    (s : Statement) (p : Proof) (h : Transferable Verifier s p) (w : Verifier) :
    DischargedFor w s p :=
  h w

/-- A designated transcript leaves some verifier unconvinced. -/
theorem designated_not_transferable [VerifierIndexed Verifier Statement Proof]
    {v₀ : Verifier} {s : Statement} {p : Proof} (h : DesignatedFor v₀ s p) :
    ∃ w : Verifier, ¬ DischargedFor w s p := by
  refine Classical.byContradiction fun hall => h.2 fun w => ?_
  exact Classical.byContradiction fun hw => hall ⟨w, hw⟩

/-- The two endpoints exclude each other on the same transcript. -/
theorem designated_excludes_public [VerifierIndexed Verifier Statement Proof]
    {v₀ : Verifier} {s : Statement} {p : Proof}
    (h : DialHolds (.designated v₀) s p) : ¬ DialHolds (Verifier := Verifier) .transferable s p :=
  h.2

/-! ## Knowledge is the public pole -/

/-- The verifier-indexed check induced by Knowledge's single `Verify`: every verifier runs the same
check. -/
@[reducible] def ofVerifiable (Verifier : Type*) (Statement : Type*) (Proof : Type*)
    [Verifiable Statement Proof] : VerifierIndexed Verifier Statement Proof :=
  ⟨fun _ s p => Verifiable.Verify s p⟩

/-- **Knowledge's `Discharged` is exactly the public pole.** Over any nonempty population of
verifiers, a witness discharges a statement in `Theory.Knowledge` iff it is transferable under the
induced indexed check. (Without a verifier the `∀` is vacuous; the nonemptiness premise is what
makes the right side say something.) -/
theorem knowledge_is_public_pole (Verifier : Type*) [Nonempty Verifier]
    [Verifiable Statement Proof] (s : Statement) (p : Proof) :
    Discharged s p ↔
      @Transferable Verifier Statement Proof (ofVerifiable Verifier Statement Proof) s p := by
  constructor
  · intro h v; exact h
  · intro h; exact h (Classical.choice ‹Nonempty Verifier›)

/-! ## Verifier-blind checks: no DV pole, and a simulator forges -/

/-- The verdict does not depend on who checks. -/
def VerifierBlind (Verifier Statement Proof : Type*) [VerifierIndexed Verifier Statement Proof] :
    Prop :=
  ∀ (v w : Verifier) (s : Statement) (p : Proof),
    VerifierIndexed.verifyFor v s p = VerifierIndexed.verifyFor w s p

/-- The Knowledge-induced check is blind. -/
theorem ofVerifiable_blind (Verifier : Type*) [Verifiable Statement Proof] :
    @VerifierBlind Verifier Statement Proof (ofVerifiable Verifier Statement Proof) :=
  fun _ _ _ _ => rfl

/-- **A blind check sends every accepted transcript to the public pole.** -/
theorem blind_discharged_transferable [VerifierIndexed Verifier Statement Proof]
    (hb : VerifierBlind Verifier Statement Proof) {v : Verifier} {s : Statement} {p : Proof}
    (h : DischargedFor v s p) : Transferable Verifier s p := by
  intro w
  unfold DischargedFor at *
  rw [hb w v]; exact h

/-- **A blind check has an empty designated-verifier pole.** -/
theorem blind_no_designated [VerifierIndexed Verifier Statement Proof]
    (hb : VerifierBlind Verifier Statement Proof) (v₀ : Verifier) (s : Statement) (p : Proof) :
    ¬ DesignatedFor v₀ s p :=
  fun h => h.2 (blind_discharged_transferable hb h.1)

/-- The contrapositive, as a design rule: designated-verifier evidence REQUIRES a check whose
verdict depends on the checker. -/
theorem designated_requires_dependence [VerifierIndexed Verifier Statement Proof]
    {v₀ : Verifier} {s : Statement} {p : Proof} (h : DesignatedFor v₀ s p) :
    ¬ VerifierBlind Verifier Statement Proof :=
  fun hb => blind_no_designated hb v₀ s p h

/-! ## The designated-verifier portal -/

/-- **The DV portal.** A verifier-indexed check with a verifier secret and a simulator that, from a
verifier's own secret, forges a transcript that verifier accepts. The simulator law is the crypto
obligation of a DV-NIZK / chameleon scheme, carried as a field (never a Lean theorem about a real
scheme). -/
class DVKernel (Verifier : Type*) (Statement : Type*) (Proof : Type*) (VSecret : outParam Type*)
    extends VerifierIndexed Verifier Statement Proof where
  vsecret : Verifier → VSecret
  simulate : VSecret → Statement → Proof
  simulate_verifies : ∀ (v : Verifier) (s : Statement),
    verifyFor v s (simulate (vsecret v) s) = true

variable {VSecret : Type*}

/-- The transcript verifier `v` simulates for statement `s` from its own secret. -/
def simOf [DVKernel Verifier Statement Proof VSecret] (v : Verifier) (s : Statement) : Proof :=
  DVKernel.simulate (Verifier := Verifier) (Statement := Statement) (Proof := Proof)
    (DVKernel.vsecret (Verifier := Verifier) (Statement := Statement) (Proof := Proof) v) s

theorem simOf_verifies [DVKernel Verifier Statement Proof VSecret] (v : Verifier)
    (s : Statement) : DischargedFor v s (simOf (Proof := Proof) (VSecret := VSecret) v s) :=
  DVKernel.simulate_verifies v s

/-- **Deniability:** for every statement, the designated verifier accepts a transcript it produced
itself from its own secret, so the transcript is no evidence to a third party. -/
theorem designated_is_deniable [DVKernel Verifier Statement Proof VSecret]
    (v₀ : Verifier) (s : Statement) :
    ∃ p : Proof, DischargedFor v₀ s p ∧ p = simOf (Proof := Proof) (VSecret := VSecret) v₀ s :=
  ⟨_, simOf_verifies v₀ s, rfl⟩

/-- **Deniability and public verifiability cannot coexist.** If a DV kernel's check is blind, any
verifier's simulation convinces EVERY verifier: whoever holds any verifier secret forges
transferable evidence for every statement. -/
theorem blind_simulator_forges [DVKernel Verifier Statement Proof VSecret]
    (hb : VerifierBlind Verifier Statement Proof) (v : Verifier) (s : Statement) :
    Transferable Verifier s (simOf (Proof := Proof) (VSecret := VSecret) v s) :=
  blind_discharged_transferable hb (simOf_verifies v s)

/-! ## What a DV-mode receipt needs -/

/-- **DV receipt mode for designated verifier `v₀`.** A private return may be receipted in DV mode
only if (1) the check is not blind, and (2) some outsider is unconvinced by every transcript `v₀`
can simulate. (2) is what makes `v₀`'s simulations, and therefore all of `v₀`'s evidence,
deniable towards that outsider. Producer-side soundness (only the prover or `v₀` can produce
accepted transcripts) is the cryptographic obligation of the concrete scheme, not stated here. -/
structure DVReceiptMode (Verifier Statement Proof VSecret : Type*)
    [DVKernel Verifier Statement Proof VSecret] (v₀ : Verifier) : Prop where
  not_blind : ¬ VerifierBlind Verifier Statement Proof
  outsider : ∃ w : Verifier, ∀ s : Statement,
    ¬ DischargedFor w s (simOf (Proof := Proof) (VSecret := VSecret) v₀ s)

/-- In DV receipt mode, every simulated transcript sits at the designated pole. -/
theorem DVReceiptMode.simulated_is_designated [DVKernel Verifier Statement Proof VSecret]
    {v₀ : Verifier} (mode : DVReceiptMode Verifier Statement Proof VSecret v₀) (s : Statement) :
    DesignatedFor v₀ s (simOf (Proof := Proof) (VSecret := VSecret) v₀ s) := by
  refine ⟨simOf_verifies v₀ s, fun hall => ?_⟩
  obtain ⟨w, hw⟩ := mode.outsider
  exact hw s (hall w)

/-! ## A reference DV kernel (the interface is inhabited and the poles are separated) -/

namespace Reference

/-- Two verifiers: the designated `v0` and an outsider. -/
inductive V where
  | v0
  | vOther
  deriving DecidableEq

/-- Verifier secrets. -/
def secretOf : V → Nat
  | .v0 => 1
  | .vOther => 0

/-- The trapdoor simulation. -/
def sim (sec stmt : Nat) : Nat := stmt + sec + 1

/-- `v0` accepts only its own simulation; the outsider accepts the public tag or its own. -/
def vrfy : V → Nat → Nat → Bool
  | .v0, stmt, proof => decide (proof = sim (secretOf .v0) stmt)
  | .vOther, stmt, proof => decide (proof = stmt) || decide (proof = sim (secretOf .vOther) stmt)

instance referenceKernel : DVKernel V Nat Nat Nat where
  verifyFor := vrfy
  vsecret := secretOf
  simulate := sim
  simulate_verifies := by
    intro v s
    cases v <;> simp [vrfy, sim, secretOf]

/-- `v0`'s simulated transcript for statement `7`. -/
def designatedProof : Nat := sim (secretOf .v0) 7

/-- The designated verifier is convinced (was `#guard check V.v0 7 designatedProof`). -/
theorem v0_convinced : DischargedFor V.v0 (7 : Nat) designatedProof := by
  simp [DischargedFor, designatedProof, VerifierIndexed.verifyFor,
    vrfy, sim, secretOf]

/-- The outsider is not (was `#guard check V.vOther 7 designatedProof == false`). -/
theorem vOther_unconvinced : ¬ DischargedFor V.vOther (7 : Nat) designatedProof := by
  simp [DischargedFor, designatedProof, VerifierIndexed.verifyFor,
    vrfy, sim, secretOf]

/-- The endpoints are inhabited and separated. -/
theorem dial_endpoints_distinct :
    DesignatedFor V.v0 (7 : Nat) designatedProof ∧ ¬ Transferable V (7 : Nat) designatedProof :=
  ⟨⟨v0_convinced, fun h => vOther_unconvinced (h V.vOther)⟩,
    fun h => vOther_unconvinced (h V.vOther)⟩

/-- The reference kernel satisfies DV receipt mode for `v0`: the premises of
`DVReceiptMode.simulated_is_designated` are inhabited. -/
theorem referenceReceiptMode : DVReceiptMode V Nat Nat Nat V.v0 where
  not_blind := designated_requires_dependence dial_endpoints_distinct.1
  outsider := ⟨V.vOther, fun s h => by
    simp [DischargedFor, simOf, VerifierIndexed.verifyFor,
      DVKernel.simulate, DVKernel.vsecret, vrfy, sim, secretOf] at h
    omega⟩

end Reference

end Minidregg.Theory.Transferability
