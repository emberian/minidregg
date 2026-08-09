/-
# Assurance.ExtensibleProofCompositionGame -- open-ended common security ledgers

`ProofCompositionGame.FailureClass` is intentionally exhaustive for the proof
stack that existed when it was introduced.  Reusing one of those constructors
for a new protocol would, however, identify two different failure events.
This module removes that pressure without weakening or changing the original
ledger: a finite extension is joined by the disjoint sum

    FailureClass ⊕ ExtraFailureClass.

Both injections are type-level domain separators.  The old and new priced
events are preserved definitionally, their good/bad predicates transport in
both directions, and the generic finite union theorem is proved on the one
shared `Omega`.  No independence, cryptographic reduction, or concrete price
is introduced here.

The final section instantiates the mechanism for the Ext6 gate controller.
In particular, Ext6 PCS, proximity, and oracle-transport failures inhabit the
right summand; they do not borrow the existing LogUp/additive constructors.
-/

import Assurance.Ext6GateProofControllerAdmission

namespace Minidregg.Assurance.ExtensibleProofCompositionGame

open scoped BigOperators
open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.Ext6GateProofControllerAdmission
open Minidregg.Compiler
open Minidregg.Compiler.Ext6GateProofController
open Minidregg.Compiler.GateFactoredExt6
open Minidregg.Loom

set_option autoImplicit false

noncomputable section

universe uClass

/-! ## A finite, extensible priced ledger -/

/-- A ledger indexed by an arbitrary finite failure-class type.  Finiteness is
required only when taking the exhaustive union and total price. -/
abbrev IndexedFailureLedger (Class : Type uClass) (Omega : Type)
    [Fintype Omega] :=
  Class -> PricedFailure Omega

namespace IndexedFailureLedger

variable {Class : Type uClass} {Omega : Type}
variable [Fintype Omega]

/-- At least one registered failure occurs on this exact game coin. -/
def Bad (ledger : IndexedFailureLedger Class Omega) (omega : Omega) : Prop :=
  ∃ failure : Class, (ledger failure).event omega

/-- The complement of one named registered failure. -/
def Good (ledger : IndexedFailureLedger Class Omega)
    (failure : Class) (omega : Omega) : Prop :=
  ¬(ledger failure).event omega

/-- The exact sum of every registered price. -/
def total [Fintype Class]
    (ledger : IndexedFailureLedger Class Omega) : Real :=
  ∑ failure : Class, (ledger failure).price

theorem good_of_not_bad (ledger : IndexedFailureLedger Class Omega)
    {omega : Omega} (good : ¬ledger.Bad omega) (failure : Class) :
    ledger.Good failure omega := by
  intro failed
  exact good ⟨failure, failed⟩

theorem not_bad_of_all_good (ledger : IndexedFailureLedger Class Omega)
    {omega : Omega} (good : ∀ failure, ledger.Good failure omega) :
    ¬ledger.Bad omega := by
  rintro ⟨failure, failed⟩
  exact good failure failed

/-- Finite union bound for an arbitrary registered class type.  The proof
enumerates that type; every event remains a predicate on the same `Omega`. -/
theorem bad_le_total [Fintype Class]
    (ledger : IndexedFailureLedger Class Omega) :
    uniformProb Omega ledger.Bad ≤ ledger.total := by
  classical
  let e : Fin (Fintype.card Class) ≃ Class := (Fintype.equivFin Class).symm
  have union := uniformProb_exists_le (C := Omega)
    (fun i omega => (ledger (e i)).event omega)
  calc
    uniformProb Omega ledger.Bad =
        uniformProb Omega (fun omega =>
          ∃ i : Fin (Fintype.card Class), (ledger (e i)).event omega) := by
      apply uniformProb_congr
      intro omega
      constructor
      · rintro ⟨failure, failed⟩
        exact ⟨e.symm failure, by simpa using failed⟩
      · rintro ⟨i, failed⟩
        exact ⟨e i, failed⟩
    _ ≤ ∑ i : Fin (Fintype.card Class),
          uniformProb Omega (ledger (e i)).event := union
    _ ≤ ∑ i : Fin (Fintype.card Class), (ledger (e i)).price := by
      exact Finset.sum_le_sum fun i _ => (ledger (e i)).bound
    _ = ∑ failure : Class, (ledger failure).price :=
      e.sum_comp (fun failure => (ledger failure).price)
    _ = ledger.total := rfl

end IndexedFailureLedger

/-! ## Disjoint extension of the original exhaustive ledger -/

/-- The old constructors and an extension occupy disjoint summands. -/
abbrev ExtendedFailureClass (Extra : Type uClass) := FailureClass ⊕ Extra

def baseTag {Extra : Type uClass} :
    FailureClass -> ExtendedFailureClass Extra :=
  Sum.inl

def extensionTag {Extra : Type uClass} :
    Extra -> ExtendedFailureClass Extra :=
  Sum.inr

theorem baseTag_injective {Extra : Type uClass} :
    Function.Injective (baseTag (Extra := Extra)) :=
  Sum.inl_injective

theorem extensionTag_injective {Extra : Type uClass} :
    Function.Injective (extensionTag (Extra := Extra)) :=
  Sum.inr_injective

theorem baseTag_ne_extensionTag {Extra : Type uClass}
    (base : FailureClass) (extra : Extra) :
    baseTag base ≠ extensionTag extra :=
  Sum.inl_ne_inr

/-- Join two total ledgers without renaming either component. -/
def extendLedger {Extra : Type uClass} {Omega : Type} [Fintype Omega]
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) :
    IndexedFailureLedger (ExtendedFailureClass Extra) Omega :=
  Sum.elim base extra

@[simp] theorem extendLedger_base_exact {Extra : Type uClass}
    {Omega : Type} [Fintype Omega]
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) (failure : FailureClass) :
    extendLedger base extra (baseTag failure) = base failure :=
  rfl

@[simp] theorem extendLedger_extension_exact {Extra : Type uClass}
    {Omega : Type} [Fintype Omega]
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) (failure : Extra) :
    extendLedger base extra (extensionTag failure) = extra failure :=
  rfl

namespace ExtendedLedger

variable {Extra : Type uClass} {Omega : Type}
variable [Fintype Omega]

/-- The existential rendering is extension-friendly but still exactly the old
closed ledger's manually exhaustive disjunction. -/
theorem base_bad_iff_exists (base : FailureLedger Omega) (omega : Omega) :
    base.Bad omega ↔ ∃ failure : FailureClass, (base failure).event omega := by
  constructor
  · rintro (failed | failed | failed | failed | failed | failed | failed | failed)
    · exact ⟨.logupAlgebra, failed⟩
    · exact ⟨.logupPcs, failed⟩
    · exact ⟨.historyPcs, failed⟩
    · exact ⟨.additiveProximity, failed⟩
    · exact ⟨.commitmentBinding, failed⟩
    · exact ⟨.oracleTransport, failed⟩
    · exact ⟨.oracleLog, failed⟩
    · exact ⟨.zeroKnowledge, failed⟩
  · rintro ⟨failure, failed⟩
    cases failure with
    | logupAlgebra => exact Or.inl failed
    | logupPcs => exact Or.inr (Or.inl failed)
    | historyPcs => exact Or.inr (Or.inr (Or.inl failed))
    | additiveProximity =>
        exact Or.inr (Or.inr (Or.inr (Or.inl failed)))
    | commitmentBinding =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl failed))))
    | oracleTransport =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl failed)))))
    | oracleLog =>
        exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl failed))))))
    | zeroKnowledge =>
        exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr failed))))))

theorem bad_iff_component_bad
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) (omega : Omega) :
    (extendLedger base extra).Bad omega ↔
      base.Bad omega ∨ extra.Bad omega := by
  rw [base_bad_iff_exists]
  constructor
  · rintro ⟨failure, failed⟩
    cases failure with
    | inl baseFailure => exact Or.inl ⟨baseFailure, failed⟩
    | inr extraFailure => exact Or.inr ⟨extraFailure, failed⟩
  · rintro (⟨failure, failed⟩ | ⟨failure, failed⟩)
    · exact ⟨baseTag failure, failed⟩
    · exact ⟨extensionTag failure, failed⟩

theorem base_bad_implies_bad
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) {omega : Omega}
    (failed : base.Bad omega) :
    (extendLedger base extra).Bad omega :=
  (bad_iff_component_bad base extra omega).2 (Or.inl failed)

theorem extension_bad_implies_bad
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) {omega : Omega}
    (failed : extra.Bad omega) :
    (extendLedger base extra).Bad omega :=
  (bad_iff_component_bad base extra omega).2 (Or.inr failed)

theorem base_good_exact
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega)
    (failure : FailureClass) (omega : Omega) :
    (extendLedger base extra).Good (baseTag failure) omega ↔
      base.Good failure omega :=
  Iff.rfl

theorem extension_good_exact
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega)
    (failure : Extra) (omega : Omega) :
    (extendLedger base extra).Good (extensionTag failure) omega ↔
      extra.Good failure omega :=
  Iff.rfl

theorem base_not_bad_of_extended_not_bad
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) {omega : Omega}
    (good : ¬(extendLedger base extra).Bad omega) :
    ¬base.Bad omega := by
  intro failed
  exact good (base_bad_implies_bad base extra failed)

theorem extension_not_bad_of_extended_not_bad
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) {omega : Omega}
    (good : ¬(extendLedger base extra).Bad omega) :
    ¬extra.Bad omega := by
  intro failed
  exact good (extension_bad_implies_bad base extra failed)

theorem not_bad_iff_component_not_bad
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) (omega : Omega) :
    ¬(extendLedger base extra).Bad omega ↔
      ¬base.Bad omega ∧ ¬extra.Bad omega := by
  rw [bad_iff_component_bad]
  tauto

theorem total_exact
    [Fintype Extra]
    (base : FailureLedger Omega)
    (extra : IndexedFailureLedger Extra Omega) :
    (extendLedger base extra).total =
      (∑ failure : FailureClass, (base failure).price) + extra.total := by
  rw [IndexedFailureLedger.total, Fintype.sum_sum_type]
  rfl

end ExtendedLedger

/-! ## Ext6 inhabits the new, disjoint summand -/

abbrev Ext6GlobalFailureClass :=
  ExtendedFailureClass Ext6FailureClass

abbrev Ext6GlobalFailureLedger (Omega : Type) [Fintype Omega] :=
  IndexedFailureLedger Ext6GlobalFailureClass Omega

def ext6GlobalLedger {Omega : Type} [Fintype Omega]
    (base : FailureLedger Omega) (ext6 : Ext6FailureLedger Omega) :
    Ext6GlobalFailureLedger Omega :=
  extendLedger base ext6

namespace Ext6GlobalLedger

variable {Omega : Type} [Fintype Omega]

/-- Ext6's local disjunction is exactly its existential registered view. -/
theorem ext6_bad_iff_exists (ext6 : Ext6FailureLedger Omega) (omega : Omega) :
    ext6.Bad omega ↔ ∃ failure : Ext6FailureClass, (ext6 failure).event omega := by
  constructor
  · rintro
      (failed | failed | failed | failed | failed | failed | failed | failed)
    · exact ⟨.gateAlgebra, failed⟩
    · exact ⟨.gatePcs, failed⟩
    · exact ⟨.subfield, failed⟩
    · exact ⟨.proximity, failed⟩
    · exact ⟨.binding, failed⟩
    · exact ⟨.oracleTransport, failed⟩
    · exact ⟨.challengeSampling, failed⟩
    · exact ⟨.finalLdt, failed⟩
  · rintro ⟨failure, failed⟩
    cases failure with
    | gateAlgebra => exact Or.inl failed
    | gatePcs => exact Or.inr (Or.inl failed)
    | subfield => exact Or.inr (Or.inr (Or.inl failed))
    | proximity => exact Or.inr (Or.inr (Or.inr (Or.inl failed)))
    | binding => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl failed))))
    | oracleTransport =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl failed)))))
    | challengeSampling =>
        exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl failed))))))
    | finalLdt =>
        exact Or.inr
          (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr failed))))))

theorem bad_iff_base_or_ext6
    (base : FailureLedger Omega) (ext6 : Ext6FailureLedger Omega)
    (omega : Omega) :
    (ext6GlobalLedger base ext6).Bad omega ↔
      base.Bad omega ∨ ext6.Bad omega := by
  change (extendLedger base ext6).Bad omega ↔
    base.Bad omega ∨ ext6.Bad omega
  rw [ExtendedLedger.bad_iff_component_bad]
  change (base.Bad omega ∨
      ∃ failure : Ext6FailureClass, (ext6 failure).event omega) ↔
    base.Bad omega ∨ ext6.Bad omega
  rw [← ext6_bad_iff_exists]

theorem ext6_bad_implies_global_bad
    (base : FailureLedger Omega) (ext6 : Ext6FailureLedger Omega)
    {omega : Omega} (failed : ext6.Bad omega) :
    (ext6GlobalLedger base ext6).Bad omega :=
  (bad_iff_base_or_ext6 base ext6 omega).2 (Or.inr failed)

theorem ext6_not_bad_of_global_not_bad
    (base : FailureLedger Omega) (ext6 : Ext6FailureLedger Omega)
    {omega : Omega} (good : ¬(ext6GlobalLedger base ext6).Bad omega) :
    ¬ext6.Bad omega := by
  intro failed
  exact good (ext6_bad_implies_global_bad base ext6 failed)

@[simp] theorem ext6_event_exact
    (base : FailureLedger Omega) (ext6 : Ext6FailureLedger Omega)
    (failure : Ext6FailureClass) :
    ((ext6GlobalLedger base ext6) (extensionTag failure)).event =
      (ext6 failure).event :=
  rfl

@[simp] theorem ext6_price_exact
    (base : FailureLedger Omega) (ext6 : Ext6FailureLedger Omega)
    (failure : Ext6FailureClass) :
    ((ext6GlobalLedger base ext6) (extensionTag failure)).price =
      (ext6 failure).price :=
  rfl

theorem total_exact
    (base : FailureLedger Omega) (ext6 : Ext6FailureLedger Omega) :
    (ext6GlobalLedger base ext6).total =
      (∑ failure : FailureClass, (base failure).price) +
      (∑ failure : Ext6FailureClass, (ext6 failure).price) := by
  change (extendLedger base ext6).total =
    (∑ failure : FailureClass, (base failure).price) +
    (∑ failure : Ext6FailureClass, (ext6 failure).price)
  rw [ExtendedLedger.total_exact, IndexedFailureLedger.total]

/-- The global union bound includes every old and Ext6 failure exactly once.
All events may be correlated; no independence premise is present. -/
theorem bad_le_total
    (base : FailureLedger Omega) (ext6 : Ext6FailureLedger Omega) :
    uniformProb Omega (ext6GlobalLedger base ext6).Bad ≤
      (ext6GlobalLedger base ext6).total :=
  IndexedFailureLedger.bad_le_total _

end Ext6GlobalLedger

/-! ## Admission-family transport into the global ledger -/

namespace Ext6Instantiation

variable {m nPadding : Nat}
variable {suite : Suite}
variable {statement : Statement m nPadding}
variable {verifier : Verifier suite statement}
variable {Omega : Type} [Fintype Omega]
variable {Error : Type} {request : List UInt8}

/-- The exact existing local Ext6 family, priced in the global disjoint ledger
on the same `Omega`.  The unrelated base ledger is not used by the reduction. -/
def globalLedger
    (family : GameFamily (suite := suite) (statement := statement)
      (verifier := verifier) Omega Error request)
    (base : FailureLedger Omega) : Ext6GlobalFailureLedger Omega :=
  ext6GlobalLedger base family.ledger

theorem falseAccept_globalBad
    (family : GameFamily (suite := suite) (statement := statement)
    (verifier := verifier) Omega Error request)
    (base : FailureLedger Omega) (omega : Omega)
    (accepted : family.FalseAccept omega) :
    (globalLedger family base).Bad omega := by
  exact Ext6GlobalLedger.ext6_bad_implies_global_bad base family.ledger
    (family.falseAccept_bad omega accepted)

/-- Global soundness charges the complete extended registry.  This is a plain
union bound on one coin type, not an independence claim. -/
theorem falseAccept_le_globalTotal
    (family : GameFamily (suite := suite) (statement := statement)
      (verifier := verifier) Omega Error request)
    (base : FailureLedger Omega) :
    uniformProb Omega family.FalseAccept ≤ (globalLedger family base).total :=
  le_trans (uniformProb_mono (falseAccept_globalBad family base))
    (Ext6GlobalLedger.bad_le_total base family.ledger)

/-- A globally good coin gives the original Ext6 reduction exactly the local
goodness premise it requires; no new semantic theorem is postulated. -/
theorem semantic_of_global_not_bad
    (family : GameFamily (suite := suite) (statement := statement)
      (verifier := verifier) Omega Error request)
    (base : FailureLedger Omega) {omega : Omega}
    (good : ¬(globalLedger family base).Bad omega)
    (receipt : Receipt m) (accepted : Accepts suite statement receipt) :
    ∃ trace : Nat -> BabyBear,
      AuthenticatedTraceRelation statement receipt trace ∧
      descriptorHolds statement.descriptor trace := by
  exact family.laws.semantic_of_not_bad
    (Ext6GlobalLedger.ext6_not_bad_of_global_not_bad
      base family.ledger good) receipt accepted

end Ext6Instantiation

#print axioms IndexedFailureLedger.bad_le_total
#print axioms Ext6GlobalLedger.bad_le_total
#print axioms Ext6Instantiation.falseAccept_globalBad
#print axioms Ext6Instantiation.falseAccept_le_globalTotal
#print axioms Ext6Instantiation.semantic_of_global_not_bad

end

end Minidregg.Assurance.ExtensibleProofCompositionGame
