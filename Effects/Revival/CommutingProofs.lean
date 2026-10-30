/-
# `Effects/Revival/CommutingProofs.lean` — commuting appends through the declaration

Proves `HostMovedRootAccepted` and `ContentCommuteTeeth` (`Effects.Revival.Statements`) over
the blinded sample cell of `ContentProofs`, and `Kernel.ContentCommutingAppend.CommutingPrepare`
(the receiver-level statement), whose accepting pole `HostMovedRootAccepted` is.
-/
module

public import Effects.Revival.ContentProofs
public import Effects.Revival.PrepareProofs
public import Kernel.ContentCommutingAppendProofs
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

namespace Minidregg.Effects.Revival

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel

set_option autoImplicit false

/-- One line: a text atom (id 7) and nothing else; it commutes. -/
def sampleAtomCommand : ContentResource.Command := ⟨[.createAtom ⟨⟨7⟩⟩ .text [0x78]]⟩

theorem sampleAtom_commutes : sampleAtomCommand.commutes = true := rfl

theorem sampleLink_not_commutes : sampleLinkCommand.commutes = false := rfl

/-- The line's descriptor at the blinded store: its one atom allocation (the store holds no
document, so the line is not threaded under a root). -/
def sampleAtomOps : Patch Hyperdocument.layout :=
  let author : Hyperdocument.PrincipalRef :=
    ⟨sampleCtx.command.subject, sampleCtx.kind, sampleCtx.capability⟩
  let operation := DeclaredResourceController.contentOperation sampleCtx.snapshot sampleCtx.semantics
    sampleCtx.command
  [.allocate .atoms ⟨⟨7⟩⟩ ⟨ContentResource.documentOf sampleCtx.target,
    .authored author operation .text, [0x78], author, operation, operation, none⟩]

theorem sampleAtom_emits_blinded_eq :
    contentSpec.sem sampleCtx sampleAtomCommand blindedStore = .ok sampleAtomOps := by
  simp [contentSpec, contentSem, sampleAtomCommand, ContentResource.run,
    ContentResource.step, ContentResource.allocate, ContentResource.appendLeaf,
    ContentResource.rootOf, Hyperdocument.lookup, Except.map, bind, Except.bind, pure,
    Except.pure, blindedStore, Store.set, sampleAtomOps]
  rfl

theorem sampleAtom_emits_blinded :
    ∃ ps, contentSpec.sem sampleCtx sampleAtomCommand blindedStore = .ok ps :=
  ⟨_, sampleAtom_emits_blinded_eq⟩

/-- A root the blinded cell does not have. -/
def movedRoot : Digest :=
  if (cellOf blindedStore).root = ⟨0⟩ then ⟨1⟩ else ⟨0⟩

theorem movedRoot_moved : movedRoot ≠ (cellOf blindedStore).root := by
  unfold movedRoot
  split
  · rename_i zero
    rw [zero]
    decide
  · rename_i nonzero
    exact fun same => nonzero same.symm

/-- The host dispatch at the blinded cell for any operation the derived executor admits,
under a plan that names the cell's root or whose operation commutes. -/
theorem hostDispatch_blinded_of (op : ContentResource.Command) (root : Digest)
    (fresh : root = (cellOf blindedStore).root ∨ op.commutes = true)
    (post : Store Hyperdocument.layout)
    (executed : EffectSpec.exec contentSpec 1 sampleCtx op blindedStore = .ok post) :
    hostTargetDispatch 1 (ContentResource.commandStream.encode op)
        (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none)
        (⟨.content, cellOf blindedStore⟩ : HostCell) =
      .ok (DeclaredResourceController.packTarget
        (hostTarget (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none)
          (.content op))
        (CellState.materialize (hostTarget (hostCtxOf sampleCtx sampleDeployment
          contentSpec.version root none none none) (.content op)).materializer post)) := by
  obtain ⟨-, -, -, live, -⟩ := contentAgreement sampleCtx op (cellOf blindedStore) none none none
  obtain ⟨computed, valid⟩ := ((live root rfl fresh).1 post).1 executed
  have decoded : DeclaredResourceController.payloadStream.toLawful.decode
      (UInt8.ofNat 1 :: ContentResource.commandStream.encode op) = some (.content op) :=
    DeclaredResourceController.payloadStream.toLawful.decode_encode (.content op)
  have selected : DeclaredResourceController.selectTarget sampleDeployment
      (hostTarget (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none)
        (.content op)) (⟨.content, cellOf blindedStore⟩ : HostCell) = some (cellOf blindedStore) := by
    simp only [DeclaredResourceController.selectTarget, hostTarget, hostCtxOf]
    have object : sampleCtx.kind = .object := rfl
    rw [if_pos object, if_pos blindedCell_law]
    rfl
  unfold hostTargetDispatch
  rw [if_neg (by decide), decoded]
  simp only
  rw [show (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).deployment =
    sampleDeployment from rfl, selected]
  simp only
  rw [show DeclaredResourceController.computeTarget (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).snapshot
      (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).semantics (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).ambient (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).command
      (hostTarget (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none)
        (.content op)) (cellOf blindedStore) = .ok post from computed]
  simp only
  have valid' : Patch.ValidFrom (cellOf blindedStore).logical
      (DeclaredResourceController.targetPatch (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).snapshot (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).semantics
        (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).ambient (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none).command
        (hostTarget (hostCtxOf sampleCtx sampleDeployment contentSpec.version root none none none)
          (.content op)) (cellOf blindedStore)) := valid
  exact if_pos valid'

/-- **A line over a moved root lands** (kernel proof): the host dispatch admits the commuting
line at the blinded cell under a plan naming a root the cell does not have. -/
theorem hostMovedRootAccepted : HostMovedRootAccepted := by
  obtain ⟨ps, emitted⟩ := sampleAtom_emits_blinded
  obtain ⟨post, executed⟩ := exec_ok_of_complete (code := 1) contentComplete emitted
  refine ⟨sampleAtomCommand, hostCtxOf sampleCtx sampleDeployment contentSpec.version movedRoot
    none none none, ⟨.content, cellOf blindedStore⟩, _, sampleAtom_commutes, ?_,
    hostDispatch_blinded_of sampleAtomCommand movedRoot (Or.inr sampleAtom_commutes) post executed⟩
  simp only [contentFresh, hostCtxOf, decide_eq_false_iff_not]
  exact movedRoot_moved

/-- The live arm admits the line at the blinded cell over the moved root. -/
theorem sampleAtom_moved_computed : ∃ post,
    DeclaredResourceController.computeTarget sampleCtx.snapshot sampleCtx.semantics sampleCtx.ambient
      sampleCtx.command (contentTarget sampleCtx contentSpec.version movedRoot sampleAtomCommand
        none none none) (cellOf blindedStore) = .ok post := by
  obtain ⟨ps, emitted⟩ := sampleAtom_emits_blinded
  obtain ⟨post, executed⟩ := exec_ok_of_complete (code := 1) contentComplete emitted
  obtain ⟨-, -, -, live, -⟩ := contentAgreement sampleCtx sampleAtomCommand (cellOf blindedStore)
    none none none
  exact ⟨post, (((live movedRoot rfl (Or.inr sampleAtom_commutes)).1 post).1 executed).1⟩

/-- **Teeth of `commutes`** (kernel proof).  The pinned declaration claims the line over the
moved root is refused, which the live arm does not do; the permissive one claims the link
over the moved root is admitted, which the live arm refuses. -/
theorem contentCommuteTeeth : ContentCommuteTeeth := by
  refine ⟨fun pinned => ?_, fun permissive => ?_⟩
  · obtain ⟨-, -, stale, -, -⟩ := pinned sampleCtx sampleAtomCommand (cellOf blindedStore)
      none none none
    obtain ⟨post, computed⟩ := sampleAtom_moved_computed
    have refused := stale movedRoot rfl rfl movedRoot_moved
    rw [show contentPinned.version = contentSpec.version from rfl, computed] at refused
    cases refused
  · obtain ⟨ps, emitted⟩ := sampleLink_emits_blinded
    obtain ⟨post, executed⟩ := exec_ok_of_complete (code := 1) contentComplete emitted
    obtain ⟨-, -, -, livePermissive, -⟩ := permissive sampleCtx sampleLinkCommand
      (cellOf blindedStore) none none none
    have executed' : EffectSpec.exec contentPermissive 1 sampleCtx sampleLinkCommand blindedStore =
        .ok post := executed
    obtain ⟨computed, -⟩ := ((livePermissive movedRoot rfl (Or.inr rfl)).1 post).1 executed'
    obtain ⟨-, -, stale, -, -⟩ := contentAgreement sampleCtx sampleLinkCommand (cellOf blindedStore)
      none none none
    have refused := stale movedRoot rfl sampleLink_not_commutes movedRoot_moved
    rw [show contentPermissive.version = contentSpec.version from rfl, refused] at computed
    cases computed

#assert_axioms hostMovedRootAccepted
#assert_axioms contentCommuteTeeth

end Minidregg.Effects.Revival
