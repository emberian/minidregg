/-
# Kernel.Contracts.Snapshot — six snapshot classes, no untyped promise

SHARED-CONTRACTS-20261003 §"Snapshot classes must be explicit":

1. Source/view cursor: exact revisions/selection + current or separately
   allowed historical reads.
2. Workspace checkpoint: layout, drafts, open references, activity ids.
3. Application archive: exact packaged body plus retained /var and generation.
4. Resident continuation: provider/session/result and acknowledged history.
5. Private successor: share generation, custody, correlation journal and
   current release authorization.
6. Rehearsal branch: speculative effects and suggested patch, not live
   settlement.

"They cannot share one untyped snapshot=backup=migrate=undo promise", as
type-level facts:
* `Snapshot c` is a family indexed by the class; a cross-class conversion is a
  `Conversion c d` value carrying its explicit witness.
* `*_needs_witness`: for each legal edge, no witness-free function agrees with
  the conversion (the result depends on the witness).
* `*_has_no_edge`: the illegal edges have no conversion at all (rehearsal never
  becomes an archive or a private successor; a private successor never becomes
  a view). These are by construction of `Conversion`; they record the decision.
* `lossless_store_recovers_class` / `untagged_store_is_lossy`: any single
  carrier that stores every class losslessly already determines the class, and
  a carrier that forgets it cannot be restored from.
* `rehearsal_apply_is_fresh_install`: applying a rehearsal is an ordinary
  `install?` under the current law, not a restore.
-/
import Kernel.Contracts.Cuts

namespace Minidregg.Kernel.Contracts

open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

inductive SnapshotClass where
  | sourceView
  | workspace
  | applicationArchive
  | residentContinuation
  | privateSuccessor
  | rehearsal
  deriving DecidableEq, Repr

structure SourceViewCursor where
  revisions : List RevisionRef
  selection : List ObjectRef
  /-- Each historical read with the law that separately allows it. -/
  historicalReads : List (RevisionRef × LawRef)
  deriving DecidableEq, Repr

structure WorkspaceCheckpoint where
  layout : ArtifactRef
  drafts : List ArtifactRef
  openReferences : List ObjectRef
  activities : List InvocationId
  deriving DecidableEq, Repr

structure ApplicationArchive where
  body : ArtifactRef
  varState : ArtifactRef
  generation : Nat
  deriving DecidableEq, Repr

structure ResidentContinuation where
  provider : Digest
  session : Digest
  result : Option ArtifactRef
  acknowledged : RevisionRef
  deriving DecidableEq, Repr

structure PrivateSuccessor where
  shares : GenerationId
  custody : List Custody
  correlationJournal : ArtifactRef
  releaseLaw : LawRef
  deriving DecidableEq, Repr

structure RehearsalBranch where
  base : RevisionRef
  speculativeEffects : List Effect
  suggestedPatch : ArtifactRef
  deriving DecidableEq, Repr

def SnapshotClass.Carrier : SnapshotClass → Type
  | .sourceView => SourceViewCursor
  | .workspace => WorkspaceCheckpoint
  | .applicationArchive => ApplicationArchive
  | .residentContinuation => ResidentContinuation
  | .privateSuccessor => PrivateSuccessor
  | .rehearsal => RehearsalBranch

abbrev Snapshot (c : SnapshotClass) : Type := c.Carrier

structure AnySnapshot where
  cls : SnapshotClass
  body : Snapshot cls

/-- The legal cross-class conversions, each with the witness it needs. -/
inductive Conversion : SnapshotClass → SnapshotClass → Type where
  /-- A workspace names open references, not the exact revisions to read them at. -/
  | workspaceView (revisions : List RevisionRef) : Conversion .workspace .sourceView
  /-- An archive's body becomes private custody only under a share generation,
  a correlation journal and the current release law. -/
  | archiveSuccessor (shares : GenerationId) (journal : ArtifactRef) (releaseLaw : LawRef) :
      Conversion .applicationArchive .privateSuccessor
  /-- Reading a rehearsal's base is a historical read, separately allowed. -/
  | rehearsalView (allowedBy : LawRef) : Conversion .rehearsal .sourceView

def Conversion.apply : {c d : SnapshotClass} → Conversion c d → Snapshot c → Snapshot d
  | _, _, .workspaceView revisions, (w : WorkspaceCheckpoint) =>
      (⟨revisions, w.openReferences, []⟩ : SourceViewCursor)
  | _, _, .archiveSuccessor shares journal law, (a : ApplicationArchive) =>
      (⟨shares, [.retainThrough a.generation], journal, law⟩ : PrivateSuccessor)
  | _, _, .rehearsalView law, (r : RehearsalBranch) =>
      (⟨[], [], [(r.base, law)]⟩ : SourceViewCursor)

/-! ## Witnesses are load-bearing -/

def exampleArtifact (n : Nat) : ArtifactRef := ⟨⟨n⟩, n, ⟨0⟩, exampleRevision, []⟩

def exampleWorkspace : WorkspaceCheckpoint := ⟨exampleArtifact 1, [], [exampleObject], []⟩
def exampleArchive : ApplicationArchive := ⟨exampleArtifact 2, exampleArtifact 3, 4⟩
def exampleRehearsal : RehearsalBranch := ⟨exampleRevision, [], exampleArtifact 5⟩

theorem workspace_view_needs_witness :
    ¬ ∃ F : Snapshot .workspace → Snapshot .sourceView,
      ∀ s (w : Conversion .workspace .sourceView), F s = w.apply s := by
  rintro ⟨F, agrees⟩
  have h1 := agrees exampleWorkspace (.workspaceView [])
  have h2 := agrees exampleWorkspace (.workspaceView [exampleRevision])
  have e : ((Conversion.workspaceView []).apply exampleWorkspace : SourceViewCursor) =
      (Conversion.workspaceView [exampleRevision]).apply exampleWorkspace := h1.symm.trans h2
  exact absurd (congrArg SourceViewCursor.revisions e) (by decide)

theorem archive_successor_needs_witness :
    ¬ ∃ F : Snapshot .applicationArchive → Snapshot .privateSuccessor,
      ∀ s (w : Conversion .applicationArchive .privateSuccessor), F s = w.apply s := by
  rintro ⟨F, agrees⟩
  have h1 := agrees exampleArchive (.archiveSuccessor ⟨exampleInvocation, 0⟩ (exampleArtifact 6) yesterday)
  have h2 := agrees exampleArchive (.archiveSuccessor ⟨exampleInvocation, 1⟩ (exampleArtifact 6) yesterday)
  have e : ((Conversion.archiveSuccessor ⟨exampleInvocation, 0⟩ (exampleArtifact 6) yesterday).apply
      exampleArchive : PrivateSuccessor) =
      (Conversion.archiveSuccessor ⟨exampleInvocation, 1⟩ (exampleArtifact 6) yesterday).apply
        exampleArchive := h1.symm.trans h2
  exact absurd (congrArg PrivateSuccessor.shares e) (by decide)

theorem rehearsal_view_needs_witness :
    ¬ ∃ F : Snapshot .rehearsal → Snapshot .sourceView,
      ∀ s (w : Conversion .rehearsal .sourceView), F s = w.apply s := by
  rintro ⟨F, agrees⟩
  have h1 := agrees exampleRehearsal (.rehearsalView yesterday)
  have h2 := agrees exampleRehearsal (.rehearsalView today)
  have e : ((Conversion.rehearsalView yesterday).apply exampleRehearsal : SourceViewCursor) =
      (Conversion.rehearsalView today).apply exampleRehearsal := h1.symm.trans h2
  exact absurd (congrArg SourceViewCursor.historicalReads e) (by decide)

/-! ## Illegal edges -/

theorem rehearsal_to_archive_has_no_edge : IsEmpty (Conversion .rehearsal .applicationArchive) :=
  ⟨fun w => nomatch w⟩

theorem rehearsal_to_successor_has_no_edge : IsEmpty (Conversion .rehearsal .privateSuccessor) :=
  ⟨fun w => nomatch w⟩

theorem successor_to_view_has_no_edge : IsEmpty (Conversion .privateSuccessor .sourceView) :=
  ⟨fun w => nomatch w⟩

/-! ## No untyped promise -/

/-- Any single carrier that stores every class losslessly already determines
the class: the "untyped" store is typed or it is lossy. -/
theorem lossless_store_recovers_class {U : Type} (erase : AnySnapshot → U)
    (restore : U → AnySnapshot) (lossless : ∀ s, restore (erase s) = s) :
    ∃ classOf : U → SnapshotClass, ∀ s, classOf (erase s) = s.cls :=
  ⟨fun u => (restore u).cls, fun s => by show (restore (erase s)).cls = s.cls; rw [lossless]⟩

/-- A carrier that identifies two snapshots of different classes has no
lossless restore. -/
theorem untagged_store_is_lossy {U : Type} (erase : AnySnapshot → U) (s t : AnySnapshot)
    (differ : s.cls ≠ t.cls) (collide : erase s = erase t) :
    ¬ ∃ restore : U → AnySnapshot, ∀ x, restore (erase x) = x := by
  rintro ⟨restore, lossless⟩
  apply differ
  have hs := lossless s
  rw [collide, lossless t] at hs
  rw [hs]

/-- Premise inhabitant for `untagged_store_is_lossy`: erasing to the class-free
"it is a snapshot" carrier collides a workspace with an archive. -/
theorem untagged_store_collision_exists :
    ∃ s t : AnySnapshot, s.cls ≠ t.cls ∧ (fun _ : AnySnapshot => ()) s = (fun _ => ()) t :=
  ⟨⟨.workspace, exampleWorkspace⟩, ⟨.applicationArchive, exampleArchive⟩, by decide, rfl⟩

/-! ## Applying a rehearsal is a fresh install -/

def applyRehearsal (gov : Governance) (current : LawRef) (held : List Reserve)
    (branch : RehearsalBranch) (i : Invoke) (obligation : Obligation) (preimage : List Guard) :
    Option Install :=
  install? gov current held i
    ⟨i.command, preimage, branch.speculativeEffects, obligation⟩

theorem rehearsal_apply_is_fresh_install {gov : Governance} {current : LawRef}
    {held : List Reserve} {branch : RehearsalBranch} {i : Invoke} {obligation : Obligation}
    {preimage : List Guard} {out : Install}
    (applied : applyRehearsal gov current held branch i obligation preimage = some out) :
    i.authorizedAt gov current = true ∧ out.effects = branch.speculativeEffects ∧
      ∃ r ∈ held, r.candidate = i.command ∧ r.obligation = obligation := by
  obtain ⟨authorized, rfl⟩ := install_rechecks_today applied
  exact ⟨authorized, rfl, install_requires_reservation applied⟩

#assert_axioms workspace_view_needs_witness
#assert_axioms archive_successor_needs_witness
#assert_axioms rehearsal_view_needs_witness
#assert_axioms rehearsal_to_archive_has_no_edge
#assert_axioms rehearsal_to_successor_has_no_edge
#assert_axioms successor_to_view_has_no_edge
#assert_axioms lossless_store_recovers_class
#assert_axioms untagged_store_is_lossy
#assert_axioms untagged_store_collision_exists
#assert_axioms rehearsal_apply_is_fresh_install

end Minidregg.Kernel.Contracts
