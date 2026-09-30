/-
# Theory.CellState -- canonical cells over the one store, validated patches

A cell's logical state is a `Store L` for its layout `L` (`Theory.Store`).
Canonical bytes and the root are never independent fields: both are
projections of one `Materialized` logical store through its materializer, so
the root is a function of the logical store and nothing else.

A patch is `Store.Patch L`, a list of guarded operations.  Only a
`ValidatedPatch` can be applied, and validation checks exactly two things: the
caller's expected pre-root is the cell's root, and every guard of the patch
holds at the store its prefix produced (`Patch.ValidFrom`).  Footprints are not
declared; they are derived from the patch's syntax, so the frame law that the
application satisfies is `Store.Patch.run_frame` itself.
-/
import Theory.Store
import Theory.ReactiveController

namespace Minidregg.Theory.CellState

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store

set_option autoImplicit false

universe u v w y z

/-! ## Canonical materialization -/

/-- The one canonical reading of a layout's stores: a lawful codec and a root
computed from the encoded bytes.  The root is therefore a function of the
logical store (`rootOf`); the stage-F root is a hash of the canonical bytes, and
a later authenticated-map root replaces `rootBytes ∘ codec.encode` without
changing `rootOf`'s type. -/
structure Materializer (L : Layout.{u, v, w}) (Root : Type y) where
  codec : LawfulCodec (Store L)
  rootBytes : List UInt8 → Root

/-- The root of a logical store. -/
def Materializer.rootOf {L : Layout.{u, v, w}} {Root : Type y}
    (M : Materializer L Root) (store : Store L) : Root :=
  M.rootBytes (M.codec.encode store)

/-- A dependent package indexed by its sole materializer.  The private
constructor prevents alternate root/encoding fields from being introduced. -/
structure Materialized {L : Layout.{u, v, w}} {Root : Type y}
    (M : Materializer L Root) where
  private mk ::
  logical : Store L

/-- The one constructor for canonical cells. -/
def materialize {L : Layout.{u, v, w}} {Root : Type y} (M : Materializer L Root)
    (logical : Store L) : Materialized M :=
  ⟨logical⟩

/-- Canonical bytes are projected from the packaged logical store. -/
def Materialized.bytes {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} (cell : Materialized M) : List UInt8 :=
  M.codec.encode cell.logical

/-- The root is the materializer's root of the logical store. -/
def Materialized.root {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} (cell : Materialized M) : Root :=
  M.rootOf cell.logical

@[simp] theorem materialize_logical {L : Layout.{u, v, w}} {Root : Type y}
    (M : Materializer L Root) (logical : Store L) :
    (materialize M logical).logical = logical :=
  rfl

@[simp] theorem materialize_bytes {L : Layout.{u, v, w}} {Root : Type y}
    (M : Materializer L Root) (logical : Store L) :
    (materialize M logical).bytes = M.codec.encode logical :=
  rfl

@[simp] theorem materialize_root {L : Layout.{u, v, w}} {Root : Type y}
    (M : Materializer L Root) (logical : Store L) :
    (materialize M logical).root = M.rootBytes (M.codec.encode logical) :=
  rfl

/-- Root/encoding coherence is definitional, not a separately supplied proof. -/
theorem Materialized.root_encoding_coherent {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} (cell : Materialized M) :
    cell.root = M.rootBytes cell.bytes :=
  rfl

/-- Canonical materializations are determined entirely by the logical store. -/
@[ext] theorem Materialized.ext {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {left right : Materialized M}
    (h : left.logical = right.logical) : left = right := by
  cases left
  cases right
  cases h
  rfl

/-! ## Pair-scoped root binding

A root is a digest of the canonical bytes; no global injectivity of the root
function is claimed.  A root equality between two specific stores is turned
into store equality only under the premise that this pair is not a collision.
This is the one definition: every cell family (authority, Book, content, event
log) states its root binding with it. -/

/-- A root collision between two specific stores under one materializer. -/
structure Collision {L : Layout.{u, v, w}} {Root : Type y} (M : Materializer L Root)
    (left right : Store L) : Prop where
  statesDifferent : left ≠ right
  rootsEqual : M.rootOf left = M.rootOf right

/-- A collision's canonical bytes differ: the codec is lawful, so only the root
function can identify two different stores. -/
theorem Collision.bytes_ne {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {left right : Store L} (collision : Collision M left right) :
    M.codec.encode left ≠ M.codec.encode right := by
  intro same
  apply collision.statesDifferent
  have decoded := congrArg M.codec.decode same
  rw [M.codec.decode_encode, M.codec.decode_encode] at decoded
  exact Option.some.inj decoded

/-- The pair-scoped collision-resistance premise. -/
def PairBindingPremise {L : Layout.{u, v, w}} {Root : Type y} (M : Materializer L Root)
    (left right : Store L) : Prop :=
  ¬ Collision M left right

/-- Under the pair premise, equal roots mean equal stores. -/
theorem PairBindingPremise.logical_eq {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {left right : Store L}
    (binding : PairBindingPremise M left right)
    (same : M.rootOf left = M.rootOf right) : left = right := by
  by_contra different
  exact binding ⟨different, same⟩

/-- Under the pair premise, different stores have different roots: a change a
durable read guard observes. -/
theorem PairBindingPremise.root_ne {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {left right : Store L}
    (binding : PairBindingPremise M left right)
    (different : left ≠ right) : M.rootOf left ≠ M.rootOf right :=
  fun same => different (binding.logical_eq same)

/-! ## Validated patches -/

/-- Verifier-minted validation of one patch against one exact pre-cell and the
pre-root the caller quoted.  The constructor is private: `validate` is the only
route to a value. -/
structure ValidatedPatch {L : Layout.{u, v, w}} {Root : Type y}
    (M : Materializer L Root) (pre : Materialized M) (expectedPreRoot : Root)
    (patch : Patch L) : Prop where
  private mk ::
  preRoot_bound : expectedPreRoot = pre.root
  valid : Patch.ValidFrom pre.logical patch

/-- Exhaustive validation failures.  `disabledOperation i` names the first
operation whose guard fails at the store its prefix produced. -/
inductive RejectReason
  | stalePreRoot
  | disabledOperation (index : Nat)
  deriving DecidableEq, Repr

/-- Validation is total and only acceptance exposes a `ValidatedPatch`. -/
inductive ValidationOutcome {L : Layout.{u, v, w}} {Root : Type y}
    (M : Materializer L Root) (pre : Materialized M) (expectedPreRoot : Root)
    (patch : Patch L) where
  | accepted (validated : ValidatedPatch M pre expectedPreRoot patch)
  | rejected (reason : RejectReason)

/-- Validate the quoted pre-root, then every guard in sequence. -/
def validate {L : Layout.{u, v, w}} {Root : Type y} [DecidableEq Root]
    (M : Materializer L Root) (pre : Materialized M) (expectedPreRoot : Root)
    (patch : Patch L) : ValidationOutcome M pre expectedPreRoot patch :=
  if hroot : expectedPreRoot = pre.root then
    match hcheck : Patch.firstDisabled? pre.logical patch with
    | none =>
        .accepted ⟨hroot, (Patch.firstDisabled?_eq_none_iff pre.logical patch).1 hcheck⟩
    | some index => .rejected (.disabledOperation index)
  else
    .rejected .stalePreRoot

/-- Application exists only on the validated type: run the patch on the
logical pre-store and rematerialize. -/
def ValidatedPatch.apply {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {pre : Materialized M} {expectedPreRoot : Root}
    {patch : Patch L} (_validated : ValidatedPatch M pre expectedPreRoot patch) :
    Materialized M :=
  materialize M (Patch.run pre.logical patch)

@[simp] theorem ValidatedPatch.apply_logical {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {pre : Materialized M} {expectedPreRoot : Root}
    {patch : Patch L} (validated : ValidatedPatch M pre expectedPreRoot patch) :
    validated.apply.logical = Patch.run pre.logical patch :=
  rfl

/-- The accepted patch executes exactly from the pre-store to the applied
store: the post is derived, never supplied. -/
theorem ValidatedPatch.executes {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {pre : Materialized M} {expectedPreRoot : Root}
    {patch : Patch L} (validated : ValidatedPatch M pre expectedPreRoot patch) :
    Patch.Executes pre.logical patch validated.apply.logical :=
  ⟨validated.valid, rfl⟩

/-- A rejected validation reports the exact failing guard. -/
theorem validate_disabledOperation {L : Layout.{u, v, w}} {Root : Type y}
    [DecidableEq Root] (M : Materializer L Root) (pre : Materialized M)
    (expectedPreRoot : Root) (patch : Patch L) (index : Nat)
    (rejected : validate M pre expectedPreRoot patch = .rejected (.disabledOperation index)) :
    Patch.ValidFrom pre.logical (patch.take index) ∧
      ∃ op, patch[index]? = some op ∧
        ¬ op.Enabled (Patch.run pre.logical (patch.take index)) := by
  unfold validate at rejected
  split at rejected
  · split at rejected
    · exact absurd rejected (by simp)
    · rename_i reported
      simp only [ValidationOutcome.rejected.injEq, RejectReason.disabledOperation.injEq] at rejected
      subst rejected
      exact Patch.firstDisabled?_eq_some pre.logical patch _ reported
  · exact absurd rejected (by simp)

/-- Validation is complete: a quoted root that is the cell's root and a
prefix-valid patch are accepted. -/
theorem validate_accepts {L : Layout.{u, v, w}} {Root : Type y} [DecidableEq Root]
    (M : Materializer L Root) (pre : Materialized M) (expectedPreRoot : Root)
    (patch : Patch L) (rootBound : expectedPreRoot = pre.root)
    (valid : Patch.ValidFrom pre.logical patch) :
    ∃ validated : ValidatedPatch M pre expectedPreRoot patch,
      validate M pre expectedPreRoot patch = .accepted validated := by
  have unreported := (Patch.firstDisabled?_eq_none_iff pre.logical patch).2 valid
  unfold validate
  rw [dif_pos rootBound]
  split
  · exact ⟨⟨rootBound, valid⟩, rfl⟩
  · rename_i index reported
    rw [unreported] at reported
    exact absurd reported (by simp)

/-- Validation is exactly the two checks: acceptance holds iff the quoted root
is the cell's root and the patch is prefix-valid. -/
theorem validate_accepted_iff {L : Layout.{u, v, w}} {Root : Type y} [DecidableEq Root]
    (M : Materializer L Root) (pre : Materialized M) (expectedPreRoot : Root)
    (patch : Patch L) :
    (∃ validated : ValidatedPatch M pre expectedPreRoot patch,
        validate M pre expectedPreRoot patch = .accepted validated) ↔
      expectedPreRoot = pre.root ∧ Patch.ValidFrom pre.logical patch := by
  constructor
  · rintro ⟨validated, _⟩
    exact ⟨validated.preRoot_bound, validated.valid⟩
  · rintro ⟨rootBound, valid⟩
    exact validate_accepts M pre expectedPreRoot patch rootBound valid

/-- A quoted root that is not the cell's root is refused before any guard. -/
theorem validate_stalePreRoot {L : Layout.{u, v, w}} {Root : Type y} [DecidableEq Root]
    (M : Materializer L Root) (pre : Materialized M) (expectedPreRoot : Root)
    (patch : Patch L) (stale : expectedPreRoot ≠ pre.root) :
    validate M pre expectedPreRoot patch = .rejected .stalePreRoot := by
  unfold validate
  rw [dif_neg stale]

/-- The cell visible after an attempt.  Rejection is definitionally the
original cell. -/
def ValidationOutcome.post {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {pre : Materialized M} {expectedPreRoot : Root}
    {patch : Patch L} : ValidationOutcome M pre expectedPreRoot patch → Materialized M
  | .rejected _ => pre
  | .accepted validated => validated.apply

@[simp] theorem ValidationOutcome.rejection_atomic {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {pre : Materialized M} {expectedPreRoot : Root}
    {patch : Patch L} (reason : RejectReason) :
    (ValidationOutcome.rejected (M := M) (pre := pre)
      (expectedPreRoot := expectedPreRoot) (patch := patch) reason).post = pre :=
  rfl

/-! ## Conceptual bridge to a reactive commit intent -/

/-- Static mapping from a layout's addresses into a controller's unified
footprint. -/
structure ControllerLayout (L : Layout.{u, v, w}) (T : ReactiveController.Types.{z}) where
  addressKey : Address L → T.Key

/-- The controller footprint of a patch: the image of its derived write
footprint. -/
def controllerFootprint {L : Layout.{u, v, w}} {T : ReactiveController.Types.{z}}
    [DecidableEq T.Key] (layout : ControllerLayout L T) (patch : Patch L) :
    Finset T.Key :=
  (Patch.writeFootprint patch).image layout.addressKey

/-- A proof-only bridge: a guarded `CommitIntent` may authorize a validated cell
patch exactly when both canonical roots and the unified footprint agree.  This
does not perform, or claim to perform, the external durable CAS. -/
structure IntentBinding
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    (M : Materializer L T.Root)
    (layout : ControllerLayout L T)
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    (intent : ReactiveController.CommitIntent decl obs advice proof controllerPre)
    (pre : Materialized M) {patch : Patch L}
    (validated : ValidatedPatch M pre intent.request.preRoot patch) : Prop where
  postRoot_bound : intent.verified.postRoot = validated.apply.root
  footprint_bound : controllerFootprint layout patch = decl.hole.footprint

/-- info: 'Minidregg.Theory.CellState.validate_disabledOperation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validate_disabledOperation
/-- info: 'Minidregg.Theory.CellState.validate_accepted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validate_accepted_iff

/-- info: 'Minidregg.Theory.CellState.PairBindingPremise.root_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PairBindingPremise.root_ne
/-- info: 'Minidregg.Theory.CellState.Collision.bytes_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Collision.bytes_ne
end Minidregg.Theory.CellState
