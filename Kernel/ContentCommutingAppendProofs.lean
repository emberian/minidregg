/-
# `Kernel.ContentCommutingAppendProofs` — the proofs of `Kernel.ContentCommutingAppend`

The statements and their ATLAS fields are in `Kernel.ContentCommutingAppend`; this file
proves all of them.  `CommutingPrepare`'s accepting pole over the Effects declaration,
`HostMovedRootAccepted`, is proved in `Kernel.EffectsRevival.CommutingProofs`.
-/
module

public import Kernel.ContentCommutingAppend
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.ContentCommutingAppend

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController

set_option autoImplicit false

theorem commutingAppend : CommutingAppend := by
  intro snapshot semantics ambient command kind id capability version root root' content observe
    epoch roster pre commutes
  -- the two sides differ only in the target's root, which the arm reads only in the stale
  -- check, and a commuting command skips it
  simp only [computeTarget, contentTarget, commutes, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]
  repeat' split
  all_goals rfl

theorem keptPin : KeptPin := by
  intro snapshot semantics ambient command id capability root content observe epoch roster pre
    notCommuting moved
  have stale : (root != pre.root && !content.commutes) = true := by
    rw [Bool.and_eq_true]
    exact ⟨bne_iff_ne.mpr moved, by rw [notCommuting]; rfl⟩
  simp only [computeTarget, contentTarget, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  split
  · rfl
  · rename_i fresh
    exact absurd stale fresh

theorem commutesExactly : CommutesExactly := by
  intro content
  obtain ⟨actions⟩ := content
  simp only [ContentResource.Command.commutes, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true, ne_eq]
  constructor
  · rintro ⟨nonempty, appendOnly⟩
    refine ⟨nonempty, fun action member => ?_⟩
    have only := appendOnly action member
    cases action <;> simp_all [ContentResource.Action.appendOnly]
  · rintro ⟨nonempty, created⟩
    refine ⟨nonempty, fun action member => ?_⟩
    obtain ⟨atom, kind, payload, rfl⟩ := created action member
    rfl

theorem admittedConsumesMarker : AdmittedConsumesMarker := by
  intro F _ _ deployment profile ambient ground command prepared signed accepted shape
  rw [accepted.dataIntent_original_exact shape]
  simp

theorem replayRefused : ReplayRefused := by
  intro F _ deployment profile ambient ground command spent
  refine ⟨fun prepared => ?_⟩
  have unspent := prepared.markerSpent_false
  rw [spent] at unspent
  cases unspent

/-- The content arm under a passing header, at a run the source lowering accepts: the run's
store, then the kernel's ratchet computed from the cell met. -/
theorem computeTarget_content_ok (snapshot : AuthoritySnapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) (id : Nat) (capability : CapabilityId) (root : Digest)
    (content : ContentResource.Command) (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) (pre : ContentResource.ContentCell)
    (progress : ContentResource.Progress)
    (fresh : root = pre.root ∨ content.commutes = true) (nonempty : content.actions ≠ [])
    (ran : ContentResource.run ⟨command.subject, .object, capability⟩
      (contentOperation snapshot semantics command) (ContentResource.documentOf id)
      (contentContext snapshot ambient command) pre.logical content = .ok progress) :
    computeTarget snapshot semantics ambient command
        (contentTarget .object id capability ContentResource.commandVersion root content observe
          epoch roster) pre =
      .ok (Store.Patch.run progress.1 (HyperdocumentCell.contentBlinding.patch pre.logical ambient.height)) := by
  have pass : (root != pre.root && !content.commutes) = false := by
    rcases fresh with same | commutes
    · subst same; simp
    · simp [commutes]
  obtain ⟨prepared, preparedOk⟩ := ContentResource.prepareCell_ok_of_run _ _ _ _ pre content
    progress nonempty ran
  have sameProgress : prepared.progress = progress := by
    have computed := prepared.computed
    rw [ran] at computed
    injection computed with same
    exact same.symm
  simp only [computeTarget, contentTarget, bind, Except.bind, pure, Except.pure,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
  split
  · rename_i stale
    cases stale.symm.trans pass
  · rw [preparedOk]
    simp only [prepared.post_exact, sameProgress]

/-! ## Evaluating the witness document

Store lookups the content run and the kernel's ratchet make on the witness document: a write
to one address frames every other (`Store.set_ne`), stated at the addresses the witness lines
touch, and the ratchet writes only the blinding (`StoreCodec.Blinding.run_patch_frame`). -/

theorem set_elements_ne (S : ContentResource.ContentStore) {a b : Nat} (different : a ≠ b) v :
    (S.set ⟨Namespace.elements, (⟨⟨b⟩⟩ : ElementId)⟩ v) ⟨Namespace.elements, (⟨⟨a⟩⟩ : ElementId)⟩ =
      S ⟨Namespace.elements, (⟨⟨a⟩⟩ : ElementId)⟩ :=
  Store.Store.set_ne _ _ _ _ (fun same => different (by cases same; rfl))

theorem set_atoms_ne (S : ContentResource.ContentStore) {a b : Nat} (different : a ≠ b) v :
    (S.set ⟨Namespace.atoms, (⟨⟨b⟩⟩ : AtomId)⟩ v) ⟨Namespace.atoms, (⟨⟨a⟩⟩ : AtomId)⟩ =
      S ⟨Namespace.atoms, (⟨⟨a⟩⟩ : AtomId)⟩ :=
  Store.Store.set_ne _ _ _ _ (fun same => different (by cases same; rfl))

theorem ratchet_frame (S pre : ContentResource.ContentStore) (height : Nat) {n : Namespace}
    (other : n ≠ .blinding) (k : Hyperdocument.layout.Key n) :
    Store.Patch.run S (HyperdocumentCell.contentBlinding.patch pre height) ⟨n, k⟩ = S ⟨n, k⟩ :=
  HyperdocumentCell.contentBlinding.run_patch_frame S pre height ⟨n, k⟩
    (fun same => other (Sigma.mk.inj same).1)

set_option backward.isDefEq.respectTransparency false in
theorem childrenOf_ratchet (S pre : ContentResource.ContentStore) (height : Nat) (element : ElementId) :
    ContentResource.childrenOf (Store.Patch.run S (HyperdocumentCell.contentBlinding.patch pre height)) element =
      ContentResource.childrenOf S element := by
  have frame := HyperdocumentCell.contentBlinding.run_patch_frame S pre height ⟨.elements, element⟩
    (by simp [StoreCodec.Blinding.address, HyperdocumentCell.contentBlinding])
  unfold ContentResource.childrenOf ContentResource.elementAt Hyperdocument.lookup
  rw [frame]

/-! ## The receiver's preparation, the witness and two appenders -/

/-- **`CommutingPrepare`.**  `prepareTarget` reads the planned root only through `computeTarget`;
for a commuting command that is the same at every planned root (`commutingAppend`), and every
other step (the slot, `selectTarget`, validation at the cell's own root, the final-post law, the
policy source, the audience) does not read it.  Both sides are split in step, and each mixed
branch is refuted by the agreement of the step's inputs. -/
theorem commutingPrepare : CommutingPrepare := by
  intro deployment directory snapshot semantics ambient command kind id capability version root root'
    content observe epoch roster commutes
  have same := commutingAppend snapshot semantics ambient command kind id capability version root root'
    content observe epoch roster
  simp only [contentTarget] at same
  unfold prepareTarget
  simp only [contentTarget]
  split
  · rfl
  · simp only [selectTarget]
    split
    next sel₁ =>
      symm; split
      next sel₂ => rfl
      next pre' sel₂ => cases sel₁.symm.trans sel₂
    next pre sel₁ =>
      symm; split
      next sel₂ => cases sel₁.symm.trans sel₂
      next pre' sel₂ =>
        cases sel₁.symm.trans sel₂
        have sameAt := same pre commutes
        split
        next reason₁ c₁ =>
          symm; split
          next reason₂ c₂ => cases c₂.symm.trans (sameAt.trans c₁); rfl
          next post₂ c₂ => cases c₂.symm.trans (sameAt.trans c₁)
        next post₁ c₁ =>
          symm; split
          next reason₂ c₂ => cases c₂.symm.trans (sameAt.trans c₁)
          next post₂ c₂ =>
            cases c₂.symm.trans (sameAt.trans c₁)
            split
            next r₁ v₁ =>
              symm; split
              next r₂ v₂ => rfl
              next w₂ v₂ => cases v₁.symm.trans v₂
            next w₁ v₁ =>
              symm; split
              next r₂ v₂ => cases v₁.symm.trans v₂
              next w₂ v₂ =>
                cases v₁.symm.trans v₂
                split
                next e₁ =>
                  symm; split
                  next e₂ =>
                    split
                    next l₁ =>
                      symm; split
                      next l₂ =>
                        simp only [requireSome, bind, Except.bind]
                        split
                        · rfl
                        · split
                          · rfl
                          · rfl
                      next l₂ => exact absurd l₁ l₂
                    next l₁ =>
                      symm; split
                      next l₂ => exact absurd l₂ l₁
                      next l₂ => rfl
                  next e₂ => exact absurd e₁ e₂
                next e₁ =>
                  symm; split
                  next e₂ => exact absurd e₂ e₁
                  next e₂ => rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`MovedRootAccepted`** on the witness document: a line planned over a root the cell does not
have lands, it is the document's one line, and the post blinding is one ratchet step of the
blinding of the cell the line met. -/
theorem movedRootAccepted : MovedRootAccepted := by
  intro snapshot semantics ambient command₀ command id capability observe epoch roster
  have commutes : (witnessLine 1).commutes = true := rfl
  cases ran : ContentResource.run ⟨command.subject, .object, capability⟩
      (contentOperation snapshot semantics command) (ContentResource.documentOf id)
      (contentContext snapshot ambient command) (witnessCell snapshot semantics command₀ id capability).logical
      (witnessLine 1) with
  | error e =>
    simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
      ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
      ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
      Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
      ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, set_elements_ne _ (show (1 : Nat) ≠ 0 by decide)] at ran
  | ok progress =>
    have shape := ran
    simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
      ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
      ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
      Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
      ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, set_elements_ne _ (show (1 : Nat) ≠ 0 by decide)] at shape
    refine ⟨if (witnessCell snapshot semantics command₀ id capability).root = ⟨0⟩ then ⟨1⟩ else ⟨0⟩, _,
      ?_, computeTarget_content_ok snapshot semantics ambient command id capability _ (witnessLine 1)
        observe epoch roster _ progress (Or.inr commutes) (by simp [witnessLine]) ran, ?_, ?_⟩
    · split
      · rename_i zero; rw [zero]; decide
      · rename_i nonzero; exact fun same => nonzero same.symm
    · subst shape
      erw [childrenOf_ratchet]
      simp [ContentResource.childrenOf, ContentResource.elementAt, Hyperdocument.lookup,
        ContentResource.bodyChildren, witnessRoot, ContentResource.atomElement,
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide)]
    · apply HyperdocumentCell.contentBlinding.run_patch_blinding
      rw [HyperdocumentCell.contentBlinding.blindingKey_eq]
      simp [witnessCell, witnessStore, Store.Store.set_ne, StoreCodec.Blinding.address,
        HyperdocumentCell.contentBlinding]

set_option backward.isDefEq.respectTransparency false in
/-- **`TwoAppendersOneObservation`**: two members plan from one observation of the witness
document; either may land first and the other lands over the moved cell, each line once, in
landing order. -/
theorem twoAppendersOneObservation : TwoAppendersOneObservation := by
  intro snapshot semantics ambient command₀ command₁ command₂ id capability observe epoch roster
  have line₁ : (witnessLine 1).commutes = true := rfl
  have line₂ : (witnessLine 2).commutes = true := rfl
  have nonempty₁ : (witnessLine 1).actions ≠ [] := by simp [witnessLine]
  have nonempty₂ : (witnessLine 2).actions ≠ [] := by simp [witnessLine]
  -- member 1 first, then member 2 over the moved cell
  cases ran₁ : ContentResource.run ⟨command₁.subject, .object, capability⟩
      (contentOperation snapshot semantics command₁) (ContentResource.documentOf id)
      (contentContext snapshot ambient command₁) (witnessCell snapshot semantics command₀ id capability).logical
      (witnessLine 1) with
  | error e => simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
        ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
        ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
        Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
        ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, CellState.materialize_logical,
        set_elements_ne _ (show (1 : Nat) ≠ 0 by decide), set_elements_ne _ (show (2 : Nat) ≠ 0 by decide),
        set_elements_ne _ (show (2 : Nat) ≠ 1 by decide), set_elements_ne _ (show (1 : Nat) ≠ 2 by decide),
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide),
        set_atoms_ne _ (show (2 : Nat) ≠ 1 by decide), set_atoms_ne _ (show (1 : Nat) ≠ 2 by decide),
        ratchet_frame _ _ _ (show Namespace.atoms ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.documents ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.elements ≠ .blinding by decide)] at ran₁
  | ok P₁ =>
  have shape₁ := ran₁
  simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
        ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
        ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
        Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
        ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, CellState.materialize_logical,
        set_elements_ne _ (show (1 : Nat) ≠ 0 by decide), set_elements_ne _ (show (2 : Nat) ≠ 0 by decide),
        set_elements_ne _ (show (2 : Nat) ≠ 1 by decide), set_elements_ne _ (show (1 : Nat) ≠ 2 by decide),
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide),
        set_atoms_ne _ (show (2 : Nat) ≠ 1 by decide), set_atoms_ne _ (show (1 : Nat) ≠ 2 by decide),
        ratchet_frame _ _ _ (show Namespace.atoms ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.documents ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.elements ≠ .blinding by decide)] at shape₁
  cases ran₁₂ : ContentResource.run ⟨command₂.subject, .object, capability⟩
      (contentOperation snapshot semantics command₂) (ContentResource.documentOf id)
      (contentContext snapshot ambient command₂)
      (CellState.materialize HyperdocumentCell.contentMaterializer
        (Store.Patch.run P₁.1 (HyperdocumentCell.contentBlinding.patch
          (witnessCell snapshot semantics command₀ id capability).logical ambient.height))).logical
      (witnessLine 2) with
  | error e => subst shape₁; simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
        ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
        ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
        Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
        ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, CellState.materialize_logical,
        set_elements_ne _ (show (1 : Nat) ≠ 0 by decide), set_elements_ne _ (show (2 : Nat) ≠ 0 by decide),
        set_elements_ne _ (show (2 : Nat) ≠ 1 by decide), set_elements_ne _ (show (1 : Nat) ≠ 2 by decide),
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide),
        set_atoms_ne _ (show (2 : Nat) ≠ 1 by decide), set_atoms_ne _ (show (1 : Nat) ≠ 2 by decide),
        ratchet_frame _ _ _ (show Namespace.atoms ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.documents ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.elements ≠ .blinding by decide)] at ran₁₂
  | ok P₁₂ =>
  have shape₁₂ := ran₁₂
  subst shape₁
  simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
        ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
        ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
        Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
        ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, CellState.materialize_logical,
        set_elements_ne _ (show (1 : Nat) ≠ 0 by decide), set_elements_ne _ (show (2 : Nat) ≠ 0 by decide),
        set_elements_ne _ (show (2 : Nat) ≠ 1 by decide), set_elements_ne _ (show (1 : Nat) ≠ 2 by decide),
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide),
        set_atoms_ne _ (show (2 : Nat) ≠ 1 by decide), set_atoms_ne _ (show (1 : Nat) ≠ 2 by decide),
        ratchet_frame _ _ _ (show Namespace.atoms ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.documents ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.elements ≠ .blinding by decide)] at shape₁₂
  subst shape₁₂
  cases ran₂ : ContentResource.run ⟨command₂.subject, .object, capability⟩
      (contentOperation snapshot semantics command₂) (ContentResource.documentOf id)
      (contentContext snapshot ambient command₂) (witnessCell snapshot semantics command₀ id capability).logical
      (witnessLine 2) with
  | error e => simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
        ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
        ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
        Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
        ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, CellState.materialize_logical,
        set_elements_ne _ (show (1 : Nat) ≠ 0 by decide), set_elements_ne _ (show (2 : Nat) ≠ 0 by decide),
        set_elements_ne _ (show (2 : Nat) ≠ 1 by decide), set_elements_ne _ (show (1 : Nat) ≠ 2 by decide),
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide),
        set_atoms_ne _ (show (2 : Nat) ≠ 1 by decide), set_atoms_ne _ (show (1 : Nat) ≠ 2 by decide),
        ratchet_frame _ _ _ (show Namespace.atoms ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.documents ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.elements ≠ .blinding by decide)] at ran₂
  | ok P₂ =>
  have shape₂ := ran₂
  simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
        ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
        ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
        Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
        ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, CellState.materialize_logical,
        set_elements_ne _ (show (1 : Nat) ≠ 0 by decide), set_elements_ne _ (show (2 : Nat) ≠ 0 by decide),
        set_elements_ne _ (show (2 : Nat) ≠ 1 by decide), set_elements_ne _ (show (1 : Nat) ≠ 2 by decide),
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide),
        set_atoms_ne _ (show (2 : Nat) ≠ 1 by decide), set_atoms_ne _ (show (1 : Nat) ≠ 2 by decide),
        ratchet_frame _ _ _ (show Namespace.atoms ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.documents ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.elements ≠ .blinding by decide)] at shape₂
  cases ran₂₁ : ContentResource.run ⟨command₁.subject, .object, capability⟩
      (contentOperation snapshot semantics command₁) (ContentResource.documentOf id)
      (contentContext snapshot ambient command₁)
      (CellState.materialize HyperdocumentCell.contentMaterializer
        (Store.Patch.run P₂.1 (HyperdocumentCell.contentBlinding.patch
          (witnessCell snapshot semantics command₀ id capability).logical ambient.height))).logical
      (witnessLine 1) with
  | error e => subst shape₂; simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
        ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
        ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
        Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
        ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, CellState.materialize_logical,
        set_elements_ne _ (show (1 : Nat) ≠ 0 by decide), set_elements_ne _ (show (2 : Nat) ≠ 0 by decide),
        set_elements_ne _ (show (2 : Nat) ≠ 1 by decide), set_elements_ne _ (show (1 : Nat) ≠ 2 by decide),
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide),
        set_atoms_ne _ (show (2 : Nat) ≠ 1 by decide), set_atoms_ne _ (show (1 : Nat) ≠ 2 by decide),
        ratchet_frame _ _ _ (show Namespace.atoms ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.documents ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.elements ≠ .blinding by decide)] at ran₂₁
  | ok P₂₁ =>
  have shape₂₁ := ran₂₁
  subst shape₂
  simp [witnessCell, ContentResource.run, witnessLine, ContentResource.step, ContentResource.allocate,
        ContentResource.appendLeaf, ContentResource.rootOf, ContentResource.elementAt,
        ContentResource.rewriteElement, Hyperdocument.lookup, witnessStore, bind, Except.bind, pure,
        Except.pure, Store.Store.set_ne, Option.map, AtomKind.validPayload, witnessRoot,
        ContentResource.atomElement, Identifier.mk.injEq, Digest.mk.injEq, CellState.materialize_logical,
        set_elements_ne _ (show (1 : Nat) ≠ 0 by decide), set_elements_ne _ (show (2 : Nat) ≠ 0 by decide),
        set_elements_ne _ (show (2 : Nat) ≠ 1 by decide), set_elements_ne _ (show (1 : Nat) ≠ 2 by decide),
        set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide),
        set_atoms_ne _ (show (2 : Nat) ≠ 1 by decide), set_atoms_ne _ (show (1 : Nat) ≠ 2 by decide),
        ratchet_frame _ _ _ (show Namespace.atoms ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.documents ≠ .blinding by decide),
        ratchet_frame _ _ _ (show Namespace.elements ≠ .blinding by decide)] at shape₂₁
  subst shape₂₁
  refine ⟨_, _, _, _,
    computeTarget_content_ok snapshot semantics ambient command₁ id capability _ (witnessLine 1) observe epoch
      roster _ _ (Or.inr line₁) nonempty₁ ran₁,
    computeTarget_content_ok snapshot semantics ambient command₂ id capability _ (witnessLine 2) observe epoch
      roster _ _ (Or.inr line₂) nonempty₂ ran₁₂,
    computeTarget_content_ok snapshot semantics ambient command₂ id capability _ (witnessLine 2) observe epoch
      roster _ _ (Or.inr line₂) nonempty₂ ran₂,
    computeTarget_content_ok snapshot semantics ambient command₁ id capability _ (witnessLine 1) observe epoch
      roster _ _ (Or.inr line₁) nonempty₁ ran₂₁, ?_, ?_⟩
  · erw [childrenOf_ratchet]
    simp [ContentResource.childrenOf, ContentResource.elementAt, Hyperdocument.lookup,
      ContentResource.bodyChildren, witnessRoot, ContentResource.atomElement,
      set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide)]
  · erw [childrenOf_ratchet]
    simp [ContentResource.childrenOf, ContentResource.elementAt, Hyperdocument.lookup,
      ContentResource.bodyChildren, witnessRoot, ContentResource.atomElement,
      set_elements_ne _ (show (0 : Nat) ≠ 1 by decide), set_elements_ne _ (show (0 : Nat) ≠ 2 by decide)]

#assert_axioms commutingAppend
#assert_axioms keptPin
#assert_axioms commutesExactly
#assert_axioms admittedConsumesMarker
#assert_axioms replayRefused
#assert_axioms commutingPrepare
#assert_axioms movedRootAccepted
#assert_axioms twoAppendersOneObservation

end Minidregg.Kernel.ContentCommutingAppend
