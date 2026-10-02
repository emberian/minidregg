/-
# Theory.CheckedCarry -- obligations at a change of world interpretation

Independent construction prototype. This is not a native carry endpoint and
does not authenticate a caller-supplied source snapshot. A receiving adapter
must derive the source inventory and authority from its verified old history,
construct the target, check its new laws, and retain the carry/receipt lineage.

The useful claims here are exact inventory disposition, concrete capability
admission preservation despite changed commitment roots, a semantic field
counterexample to numeric narrowing, and shared origin consumption. No theorem
below claims that copying cells into fresh genesis preserves the native journal.
-/
import Theory.TypedAuthorization

namespace Minidregg.Theory.CheckedCarry

open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Complete dispositions, without pretending Lean has linear types -/

structure Cell where
  id : Nat
  bytes : List UInt8
  deriving DecidableEq, Repr

/-- A drop is explicit source data. Its authorization is a separate receiving
obligation; the existence of a reason string grants no authority. -/
structure DropReason where
  code : Nat
  explanation : String
  nonempty : explanation ≠ ""

inductive Disposition where
  | keep (target : Cell)
  | drop (reason : DropReason)

/-- The index is in the actual verified source inventory. Consequently there
is one decision for every source occurrence, even for a tombstone. A source
inventory with duplicate IDs must be rejected before constructing this value. -/
structure Plan (source : List Cell) (keepRelation : Cell → Cell → Prop) where
  sourceUnique : (source.map Cell.id).Nodup
  decideCell : (i : Fin source.length) → Disposition
  kept : ∀ i target, decideCell i = .keep target →
    keepRelation source[i] target
  outputsUnique : ∀ i j target other,
    decideCell i = .keep target → decideCell j = .keep other →
    target.id = other.id → i = j

theorem disposition_total {source : List Cell} {relation : Cell → Cell → Prop} (plan : Plan source relation)
    (i : Fin source.length) :
    (∃ target, plan.decideCell i = .keep target) ∨
    (∃ reason, plan.decideCell i = .drop reason) := by
  cases choice : plan.decideCell i with
  | keep target => exact .inl ⟨target, choice⟩
  | drop reason => exact .inr ⟨reason, choice⟩

theorem duplicate_output_refused {source : List Cell} {relation : Cell → Cell → Prop} (plan : Plan source relation)
    (i j : Fin source.length) (different : i ≠ j) (left right : Cell)
    (hi : plan.decideCell i = .keep left)
    (hj : plan.decideCell j = .keep right) : left.id ≠ right.id := by
  intro same
  exact different (plan.outputsUnique i j left right hi hj same)

/-- Stronger requirement for the first law-component cut: no drop exists. -/
def NoDrops {source : List Cell} {relation : Cell → Cell → Prop} (plan : Plan source relation) : Prop :=
  ∀ i, ∃ target, plan.decideCell i = .keep target

theorem no_drop_at {source : List Cell} {relation : Cell → Cell → Prop} {plan : Plan source relation}
    (noDrops : NoDrops plan) (i : Fin source.length) (reason : DropReason) :
    plan.decideCell i ≠ .drop reason := by
  obtain ⟨target, kept⟩ := noDrops i
  rw [kept]
  intro impossible
  cases impossible

/-! ## The neutral authority lift uses the actual capability rules -/

/-- Hash roots, source addresses and their new membership proofs can change.
The logical authority interpretation may not. The receiver must establish this
relation from the authenticated bytes, not accept it as a host assertion. -/
structure AuthorityMeaning (old next : AuthState) : Prop where
  revoked : old.revoked = next.revoked
  issuerEpoch : old.issuerEpoch = next.issuerEpoch
  policyEpoch : old.policyEpoch = next.policyEpoch
  policyRevision : old.policyRevision = next.policyRevision
  subjectKeyEpoch : old.subjectKeyEpoch = next.subjectKeyEpoch
  parent : old.parent = next.parent

def AuthorityMeaning.symm {old next : AuthState} (same : AuthorityMeaning old next) :
    AuthorityMeaning next old :=
  ⟨same.revoked.symm, same.issuerEpoch.symm, same.policyEpoch.symm,
    same.policyRevision.symm, same.subjectKeyEpoch.symm, same.parent.symm⟩

theorem neutral_capability_forward {old next : AuthState}
    (same : AuthorityMeaning old next) {kind : ResourceKind}
    (cap : Capability kind) (request : Request kind)
    (accepted : cap.Admissible old request) : cap.Admissible next request := by
  refine
    { holder := accepted.holder
      scope := ?_
      validFrom := accepted.validFrom
      validUntil := accepted.validUntil
      requestLaw := accepted.requestLaw
      policyCurrent := ?_
      issuerCurrent := ?_
      selfNotRevoked := ?_
      ancestorNotRevoked := ?_
      channelNotRevoked := ?_ }
  · simpa only [← same.parent] using accepted.scope
  · simpa only [← same.policyEpoch] using accepted.policyCurrent
  · simpa only [← same.issuerEpoch] using accepted.issuerCurrent
  · simpa only [← same.revoked] using accepted.selfNotRevoked
  · simpa only [← same.revoked] using accepted.ancestorNotRevoked
  · simpa only [← same.revoked] using accepted.channelNotRevoked

theorem neutral_capability_iff {old next : AuthState}
    (same : AuthorityMeaning old next) {kind : ResourceKind}
    (cap : Capability kind) (request : Request kind) :
    cap.Admissible old request ↔ cap.Admissible next request :=
  ⟨neutral_capability_forward same cap request,
    neutral_capability_forward same.symm cap request⟩

/-- The unchanged request uses the unchanged logical height. Starting segment
height zero is not permission to restart grant validity windows. -/
theorem neutral_write_scope_iff {old next : AuthState}
    (same : AuthorityMeaning old next) {kind : ResourceKind}
    (scope : Scope kind) (request : Request kind) (footprint : Footprint) :
    scope.CoversWrite old.parent request footprint ↔
      scope.CoversWrite next.parent request footprint := by
  rw [same.parent]

/-! ## Meaning, not field-number inclusion -/

namespace TitleMigration

inductive Meaning where
  | title
  | membership
  deriving DecidableEq, Repr

def oldField : Meaning → CellField
  | .title => .slot 3
  | .membership => .slot 8

def nextField : Meaning → CellField
  | .title => .slot 7
  | .membership => .slot 3

def oldGrant : Option (Finset CellField) := some {CellField.slot 3}
def correctGrant : Option (Finset CellField) := some {CellField.slot 7}
def copiedGrant : Option (Finset CellField) := oldGrant

def NoNewMeaning (oldFields newFields : Option (Finset CellField)) : Prop :=
  ∀ meaning, CellField.NamedBy newFields (nextField meaning) →
    CellField.NamedBy oldFields (oldField meaning)

theorem numeric_subset_is_insufficient :
    CellField.SetNarrows copiedGrant oldGrant :=
  CellField.SetNarrows.refl oldGrant

theorem copied_title_grant_gives_membership :
    CellField.NamedBy copiedGrant (nextField .membership) := by decide

theorem copied_title_grant_not_semantic_narrowing :
    ¬ NoNewMeaning oldGrant copiedGrant := by
  intro supposed
  have forbidden := supposed .membership copied_title_grant_gives_membership
  have absent : ¬ CellField.NamedBy oldGrant (oldField .membership) := by decide
  exact absent forbidden

theorem translated_title_grant_preserves_meaning :
    NoNewMeaning oldGrant correctGrant := by
  intro meaning allowed
  cases meaning with
  | title => decide
  | membership =>
      have forbidden : ¬ CellField.NamedBy correctGrant (nextField .membership) := by decide
      exact False.elim (forbidden allowed)

structure Document where
  title : Nat
  membership : Nat
  deriving DecidableEq, Repr

structure Edit where
  field : Nat
  value : Nat
  deriving DecidableEq, Repr

def oldStep (document : Document) (edit : Edit) : Option Document :=
  if edit.field = 3 then some { document with title := edit.value }
  else if edit.field = 8 then some { document with membership := edit.value }
  else none

def nextStep (document : Document) (edit : Edit) : Option Document :=
  if edit.field = 7 then some { document with title := edit.value }
  else if edit.field = 3 then some { document with membership := edit.value }
  else none

def translate (edit : Edit) : Option Edit :=
  if edit.field = 3 then some { edit with field := 7 }
  else if edit.field = 8 then some { edit with field := 3 }
  else none

theorem translated_effect_exact (document : Document) (edit : Edit) :
    (translate edit).bind (nextStep document) = oldStep document edit := by
  rcases edit with ⟨field, value⟩
  by_cases title : field = 3
  · simp [translate, nextStep, oldStep, title]
  · by_cases member : field = 8
    · simp [translate, nextStep, oldStep, title, member]
    · simp [translate, nextStep, oldStep, title, member]

theorem byte_copy_changes_the_wrong_field :
    nextStep ⟨10, 0⟩ ⟨3, 17⟩ = some ⟨10, 17⟩ ∧
    oldStep ⟨10, 0⟩ ⟨3, 17⟩ = some ⟨17, 0⟩ := by decide

end TitleMigration

/-! ## Originals and translations consume one origin -/

structure Origin where
  domain : Digest
  genesis : Digest
  transaction : Digest
  effectIndex : Nat
  deriving DecidableEq, Repr

/-- This simplified journal row specifies the invariant required of the actual
native inherited receipt index. `meaning` is the semantic request commitment,
not a claim that old signatures cover a translated wire representation. -/
structure Receipt where
  origin : Origin
  meaning : Digest
  outcome : Digest
  deriving DecidableEq, Repr

inductive Recovery where
  | fresh
  | historical (outcome : Digest)
  | conflict
  deriving DecidableEq, Repr

def recover (journal : List Receipt) (origin : Origin) (meaning : Digest) : Recovery :=
  match journal.find? (fun receipt => receipt.origin == origin) with
  | none => .fresh
  | some receipt =>
      if receipt.meaning = meaning then .historical receipt.outcome else .conflict

theorem exact_origin_recovers (receipt : Receipt) (rest : List Receipt) :
    recover (receipt :: rest) receipt.origin receipt.meaning =
      .historical receipt.outcome := by
  simp [recover]

theorem changed_meaning_conflicts (receipt : Receipt) (rest : List Receipt)
    (different : Digest) (changed : receipt.meaning ≠ different) :
    recover (receipt :: rest) receipt.origin different = .conflict := by
  simp [recover, changed]

theorem retained_journal_does_not_refresh (receipt : Receipt) (rest : List Receipt) :
    recover (receipt :: rest) receipt.origin receipt.meaning ≠ .fresh := by
  rw [exact_origin_recovers]
  intro impossible
  cases impossible

/-- The two versions deliberately share origin and semantic commitment. New
target authority is checked separately before an unconsumed effect is admitted. -/
structure TranslatedRequest where
  origin : Origin
  meaning : Digest
  oldSignedBytes : List UInt8
  newCanonicalBytes : List UInt8
  carryArtifact : Digest

def TranslatedRequest.recovery (request : TranslatedRequest) (journal : List Receipt) : Recovery :=
  recover journal request.origin request.meaning

theorem translated_original_same_recovery (request : TranslatedRequest)
    (journal : List Receipt) :
    request.recovery journal = recover journal request.origin request.meaning := rfl


inductive Admission where
  | accepted (journal : List Receipt) (outcome : Digest)
  | replayed (outcome : Digest)
  | refused
  deriving DecidableEq, Repr

/-- Current authority gates only a fresh effect; recovering a historical result
is separate. The native adapter must use its authenticated atomic journal and
actual current authority, not a requester-provided Boolean. -/
def admit (journal : List Receipt) (request : TranslatedRequest)
    (currentAllowed : Bool) (outcome : Digest) : Admission :=
  match request.recovery journal with
  | .historical recorded => .replayed recorded
  | .conflict => .refused
  | .fresh =>
      if currentAllowed then
        .accepted (⟨request.origin, request.meaning, outcome⟩ :: journal) outcome
      else .refused

theorem original_acceptance_makes_translation_replay
    (journal : List Receipt) (request : TranslatedRequest)
    (recorded candidate : Digest) (allowed : Bool) :
    admit (⟨request.origin, request.meaning, recorded⟩ :: journal)
      request allowed candidate = .replayed recorded := by
  simp [admit, TranslatedRequest.recovery, recover]

theorem fresh_revoked_translation_refuses (journal : List Receipt)
    (request : TranslatedRequest) (outcome : Digest)
    (unconsumed : request.recovery journal = .fresh) :
    admit journal request false outcome = .refused := by
  simp [admit, unconsumed]

theorem changed_origin_meaning_refuses (journal : List Receipt)
    (request : TranslatedRequest) (oldMeaning recorded candidate : Digest)
    (allowed : Bool) (changed : oldMeaning ≠ request.meaning) :
    admit (⟨request.origin, oldMeaning, recorded⟩ :: journal)
      request allowed candidate = .refused := by
  simp [admit, TranslatedRequest.recovery, recover, changed]

end Minidregg.Theory.CheckedCarry
