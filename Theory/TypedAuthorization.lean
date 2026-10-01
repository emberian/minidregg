/-
# Theory.TypedAuthorization — request-indexed authority for a typed effect machine

This is a clean-sheet authorization kernel.  It deliberately does not inherit
an account-system permission lattice, positional capability slots, or a family
of credential-shaped bypass modes.  Every authorization witness is indexed by
the COMPLETE semantic request that it authorizes.  A witness for one target,
verb, argument/effect commitment, nonce, epoch, or pre-state therefore does not
have the type required for another request.

Cryptography stays on the executable side of the verify/find seam.  `Portal`
contains concrete Boolean verifier predicates and witness types; it contains no
`soundness : Prop` escape hatch.  The pure `Capability.Admissible` relation is
the semantic statement those verifiers must accompany.

The capability commitment verifier receives the whole `Capability`, including
its exact issuer/policy epochs, ancestry, and revocation channels.  Membership
is checked against the current capability root, and non-revocation witnesses
are checked against the current revocation root for the capability itself,
EVERY committed ancestor, and EVERY committed channel.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Minidregg.Theory.TypedAuthorization

/-! ## §1. Typed names and the complete semantic request. -/

structure SubjectId where
  value : Nat
  deriving DecidableEq, Repr

structure IssuerId where
  value : Nat
  deriving DecidableEq, Repr

structure PolicyId where
  value : Nat
  deriving DecidableEq, Repr

structure FederationId where
  value : Nat
  deriving DecidableEq, Repr

structure CapabilityId where
  value : Nat
  deriving DecidableEq, Repr

structure ChannelId where
  value : Nat
  deriving DecidableEq, Repr

structure Digest where
  value : Nat
  deriving DecidableEq, Repr

abbrev Epoch := Nat
/-- Source revision is independent of the revocable grant generation. -/
abbrev PolicyRevision := Nat
abbrev Height := Nat

/-- Resource kinds index both resource identifiers and their legal verbs. -/
inductive ResourceKind where
  | object
  | account
  | program
  deriving DecidableEq, Repr

/-- An identifier whose resource kind is present in its type. -/
structure ResourceId (_kind : ResourceKind) where
  value : Nat
  deriving DecidableEq, Repr

/-- Verbs are indexed by the kind on which they are meaningful.  A program
installation cannot accidentally be presented as an account transfer. -/
inductive Verb : ResourceKind → Type
  | observeObject : Verb .object
  | mutateObject : Verb .object
  | observeAccount : Verb .account
  | transfer : Verb .account
  | observeProgram : Verb .program
  | installProgram : Verb .program
  | delegateObject : Verb .object
  | delegateAccount : Verb .account
  | delegateProgram : Verb .program
  /-- Replacing a program resource's acceptance policy is distinct from
  editing its code. Ordinary installProgram authority cannot change its law. -/
  | installPolicy : Verb .program
  /-- Revoking a resource grant is independently scoped management authority. -/
  | revokeCapability : Verb .program
  /-- Appending one entry to a stream object: "may speak, may not edit".
  `mutateObject` covers it too (`Verb.AllowedBy`). -/
  | appendObject : Verb .object
  deriving DecidableEq, Repr

/-- The granted verbs that cover a requested verb: the verb itself, and for an
append also `mutateObject` (whoever may edit an object may append to it). -/
def Verb.grantors : {kind : ResourceKind} → Verb kind → List (Verb kind)
  | _, .appendObject => [.appendObject, .mutateObject]
  | _, verb => [verb]

/-- `verb` is allowed by a granted verb set. -/
def Verb.AllowedBy {kind : ResourceKind} (verb : Verb kind) (verbs : Finset (Verb kind)) : Prop :=
  ∃ granted ∈ verb.grantors, granted ∈ verbs

instance Verb.allowedByDecidable {kind : ResourceKind} (verb : Verb kind)
    (verbs : Finset (Verb kind)) : Decidable (verb.AllowedBy verbs) := by
  unfold Verb.AllowedBy; infer_instance

theorem Verb.mem_grantors_self {kind : ResourceKind} (verb : Verb kind) : verb ∈ verb.grantors := by
  cases verb <;> simp [Verb.grantors]

theorem Verb.AllowedBy.of_mem {kind : ResourceKind} {verb : Verb kind} {verbs : Finset (Verb kind)}
    (member : verb ∈ verbs) : verb.AllowedBy verbs :=
  ⟨verb, verb.mem_grantors_self, member⟩

theorem Verb.AllowedBy.mono {kind : ResourceKind} {verb : Verb kind} {small large : Finset (Verb kind)}
    (sub : small ⊆ large) (allowed : verb.AllowedBy small) : verb.AllowedBy large :=
  let ⟨granted, grantor, member⟩ := allowed
  ⟨granted, grantor, sub member⟩

@[simp] theorem Verb.allowedBy_singleton_self {kind : ResourceKind} (verb : Verb kind) :
    verb.AllowedBy {verb} := Verb.AllowedBy.of_mem (Finset.mem_singleton_self verb)

@[simp] theorem Verb.allowedBy_insert_self {kind : ResourceKind} (verb : Verb kind)
    (verbs : Finset (Verb kind)) : verb.AllowedBy (insert verb verbs) :=
  Verb.AllowedBy.of_mem (Finset.mem_insert_self verb verbs)

/-- Every verb but `appendObject` is allowed exactly by itself. -/
theorem Verb.allowedBy_iff_mem {kind : ResourceKind} {verb : Verb kind} {verbs : Finset (Verb kind)}
    (notAppend : verb.grantors = [verb]) : verb.AllowedBy verbs ↔ verb ∈ verbs := by
  unfold Verb.AllowedBy
  rw [notAppend]
  simp only [List.mem_singleton, exists_eq_left]

/-- **Mutate covers append**, and nothing else covers it. -/
theorem Verb.append_allowedBy_iff (verbs : Finset (Verb .object)) :
    Verb.appendObject.AllowedBy verbs ↔ Verb.appendObject ∈ verbs ∨ Verb.mutateObject ∈ verbs := by
  simp [Verb.AllowedBy, Verb.grantors]

/-- A publish-only grant may not edit. -/
theorem Verb.append_grant_cannot_mutate : ¬ Verb.mutateObject.AllowedBy {Verb.appendObject} := by
  simp [Verb.AllowedBy, Verb.grantors]

/-- info: 'Minidregg.Theory.TypedAuthorization.Verb.append_allowedBy_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Verb.append_allowedBy_iff
/-- info: 'Minidregg.Theory.TypedAuthorization.Verb.append_grant_cannot_mutate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Verb.append_grant_cannot_mutate

/-- The complete semantic authorization request.  Verifiers receive this value
directly; there are no prover-carried "bound target" strings to trust. -/
structure Request (kind : ResourceKind) where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  target : ResourceId kind
  verb : Verb kind
  argsDigest : Digest
  effectsDigest : Digest
  nonce : Nat
  height : Height
  preStateRoot : Digest
  policyId : PolicyId
  policyEpoch : Epoch
  policyRevision : PolicyRevision
  cost : Nat
  deriving DecidableEq, Repr

/-- Change only the target of a request.  This produces a DIFFERENT request
index; existing `Evidence portal state request` cannot be reused at this type. -/
def Request.retarget {kind : ResourceKind} (request : Request kind)
    (target : ResourceId kind) : Request kind :=
  { request with target := target }

theorem Request.retarget_ne {kind : ResourceKind} (request : Request kind)
    (target : ResourceId kind) (hne : target ≠ request.target) :
    request.retarget target ≠ request := by
  intro heq
  have htarget := congrArg (fun r : Request kind => r.target) heq
  exact hne (by simpa [Request.retarget] using htarget)

/-! ## §2. Holders, scopes, and monotone attenuation. -/

/-- Bearer authority and subject-bound authority are different constructors.
A bearer capability intentionally authenticates possession, not identity. -/
inductive Holder where
  | bearer
  | subject (id : SubjectId)
  deriving DecidableEq, Repr

def Holder.Covers (holder : Holder) (subject : SubjectId) : Prop :=
  match holder with
  | .bearer => True
  | .subject bound => bound = subject

/-- The system cell's parent projection. `parentage c = some room` records that
cell `c` was created under the room cell `room`. Resource and room identifiers
are compared by their raw cell values. The projection is append-only in the
world: a recorded parent is never rewritten or removed. `support` is a finite
set holding every cell with a recorded parent; it bounds every parent chain
that matters, which is what makes chain coverage decidable. -/
structure Parentage where
  parentOf : Nat → Option Nat
  support : Finset Nat
  supported : ∀ c, parentOf c ≠ none → c ∈ support

namespace Parentage

instance : CoeFun Parentage (fun _ => Nat → Option Nat) := ⟨Parentage.parentOf⟩

/-- No recorded parents. -/
def empty : Parentage := ⟨fun _ => none, ∅, fun _ h => absurd rfl h⟩

/-- The parentage that records exactly the listed `(cell, parent)` rows; a
later row for the same cell is shadowed by the first. -/
def ofList (rows : List (Nat × Nat)) : Parentage where
  parentOf c := (rows.find? (fun row => row.1 = c)).map Prod.snd
  support := (rows.map Prod.fst).toFinset
  supported c h := by
    cases found : rows.find? (fun row => row.1 = c) with
    | none => simp [found] at h
    | some row =>
        have member := List.mem_of_find?_eq_some found
        have same : row.1 = c := by simpa using List.find?_some found
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, member, same⟩)

/-- Appending rows never changes a recorded parent. -/
theorem ofList_append_extends (rows extra : List (Nat × Nat)) :
    ∀ c r, ofList rows c = some r → ofList (rows ++ extra) c = some r := by
  intro c r recorded
  change ((rows ++ extra).find? (fun row => row.1 = c)).map Prod.snd = some r
  change (rows.find? (fun row => row.1 = c)).map Prod.snd = some r at recorded
  rw [List.find?_append]
  cases found : rows.find? (fun row => row.1 = c) with
  | none => simp [found] at recorded
  | some row => simpa [found] using recorded

/-- `p.Descends c r`: `r` is `c` itself or an ancestor of `c` along recorded
parents. -/
inductive Descends (p : Parentage) : Nat → Nat → Prop
  | refl (c : Nat) : Descends p c c
  | step {c q r : Nat} : p c = some q → Descends p q r → Descends p c r

/-- The `n`-th ancestor of `c`, if the chain is that long. -/
def ancestor (p : Parentage) : Nat → Nat → Option Nat
  | 0, c => some c
  | n + 1, c => (p c).bind (ancestor p n)

theorem ancestor_add (p : Parentage) (m n c : Nat) :
    p.ancestor (m + n) c = (p.ancestor m c).bind (p.ancestor n) := by
  induction m generalizing c with
  | zero => simp [ancestor]
  | succ m ih =>
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp only [ancestor]
      cases p c with
      | none => rfl
      | some q => simp [ih]

theorem ancestor_one (p : Parentage) (c : Nat) : p.ancestor 1 c = p c := by
  cases h : p c <;> simp [ancestor, h]

theorem descends_iff_ancestor (p : Parentage) (c r : Nat) :
    p.Descends c r ↔ ∃ n, p.ancestor n c = some r := by
  constructor
  · intro d
    induction d with
    | refl c => exact ⟨0, rfl⟩
    | step link _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, by simp [ancestor, link, hn]⟩
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero =>
        simp only [ancestor, Option.some.injEq] at hn
        subst hn; exact .refl c
    | succ n ih =>
        simp only [ancestor] at hn
        cases link : p c with
        | none => simp [link] at hn
        | some q =>
            rw [link] at hn
            exact .step link (ih q hn)

theorem ancestor_isSome_of_le (p : Parentage) {i n c r : Nat} (le : i ≤ n)
    (reach : p.ancestor n c = some r) : ∃ a, p.ancestor i c = some a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [ancestor_add] at reach
  cases found : p.ancestor i c with
  | none => simp [found] at reach
  | some a => exact ⟨a, rfl⟩

/-- A chain that reaches `r` reaches it within `support.card` steps: a longer
chain repeats a cell (pigeonhole over the support), and cutting the loop gives
a shorter chain to the same `r`. -/
theorem ancestor_bounded (p : Parentage) {n c r : Nat}
    (reach : p.ancestor n c = some r) :
    ∃ m, m ≤ p.support.card ∧ p.ancestor m c = some r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases small : n ≤ p.support.card
    · exact ⟨n, small, reach⟩
    · have mapsTo : ∀ i ∈ Finset.range n, (p.ancestor i c).getD 0 ∈ p.support := by
        intro i member
        have lt := Finset.mem_range.mp member
        obtain ⟨a, ha⟩ := p.ancestor_isSome_of_le (Nat.le_of_lt lt) reach
        obtain ⟨b, hb⟩ := p.ancestor_isSome_of_le (show i + 1 ≤ n by omega) reach
        rw [ancestor_add, ha, Option.bind_some, ancestor_one] at hb
        rw [ha]
        exact p.supported a (by simp [hb])
      obtain ⟨i, hi, j, hj, ne, same⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (by simpa using (show p.support.card < n by omega)) mapsTo
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      obtain ⟨a, ha⟩ := p.ancestor_isSome_of_le (Nat.le_of_lt hi') reach
      obtain ⟨b, hb⟩ := p.ancestor_isSome_of_le (Nat.le_of_lt hj') reach
      rw [ha, hb] at same
      simp only [Option.getD_some] at same
      subst same
      -- cut the loop between the two visits
      rcases Nat.lt_or_gt_of_ne ne with lt | lt
      · have split : p.ancestor n c = (p.ancestor j c).bind (p.ancestor (n - j)) := by
          rw [← ancestor_add]; congr 1; omega
        have short : p.ancestor (i + (n - j)) c = some r := by
          rw [ancestor_add, ha, ← hb, ← split, reach]
        exact ih _ (by omega) short
      · have split : p.ancestor n c = (p.ancestor i c).bind (p.ancestor (n - i)) := by
          rw [← ancestor_add]; congr 1; omega
        have short : p.ancestor (j + (n - i)) c = some r := by
          rw [ancestor_add, hb, ← ha, ← split, reach]
        exact ih _ (by omega) short

theorem descends_iff_bounded (p : Parentage) (c r : Nat) :
    p.Descends c r ↔ ∃ n, n < p.support.card + 1 ∧ p.ancestor n c = some r := by
  rw [descends_iff_ancestor]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, le, hm⟩ := p.ancestor_bounded hn
    exact ⟨m, by omega, hm⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

instance descendsDecidable (p : Parentage) (c r : Nat) : Decidable (p.Descends c r) :=
  decidable_of_iff _ (p.descends_iff_bounded c r).symm

theorem Descends.trans {p : Parentage} {a b c : Nat}
    (first : p.Descends a b) (second : p.Descends b c) : p.Descends a c := by
  induction first with
  | refl => exact second
  | step link _ ih => exact .step link (ih second)

theorem Descends.mono {p q : Parentage}
    (grows : ∀ c r, p c = some r → q c = some r) {a b : Nat}
    (d : p.Descends a b) : q.Descends a b := by
  induction d with
  | refl => exact .refl _
  | step link _ ih => exact .step (grows _ _ link) ih

/-- A cell no recorded row names as a parent has no strict descendants:
`under c` covers exactly `c`. -/
theorem under_fresh_covers_only_self (p : Parentage) {c : Nat}
    (fresh : ∀ x, p x ≠ some c) (t : Nat) : p.Descends t c ↔ t = c := by
  constructor
  · intro d
    induction d with
    | refl => rfl
    | step link rest ih =>
        have same := ih fresh
        subst same
        exact absurd link (fresh _)
  · rintro rfl
    exact .refl _

/-- A recorded parent is an ancestor. -/
theorem Descends.ofParent {p : Parentage} {c r : Nat} (link : p c = some r) :
    p.Descends c r := .step link (.refl r)

end Parentage

/-- The targets a scope names: an explicit finite set, or `under room`: the
room cell itself and every cell whose parent chain reaches it (a room under an
area under a realm is under the realm). -/
inductive TargetSet (kind : ResourceKind) where
  | explicit (targets : Finset (ResourceId kind))
  | under (room : Nat)
  deriving DecidableEq

namespace TargetSet

variable {kind : ResourceKind}

def Covers (targets : TargetSet kind) (parentage : Parentage)
    (target : ResourceId kind) : Prop :=
  match targets with
  | .explicit ts => target ∈ ts
  | .under room => parentage.Descends target.value room

instance coversDecidable (targets : TargetSet kind) (parentage : Parentage)
    (target : ResourceId kind) : Decidable (targets.Covers parentage target) := by
  cases targets <;> unfold Covers <;> infer_instance

/-- Target narrowing. An explicit set narrows `under p` only when every named
cell is already recorded under `p`; `under c` narrows `under p` when room `c`
is itself under `p`; `under` never narrows to an explicit set. -/
def Narrows (child parent : TargetSet kind) (parentage : Parentage) : Prop :=
  match child, parent with
  | .explicit c, .explicit p => c ⊆ p
  | .under c, .under p => parentage.Descends c p
  | .explicit c, .under p => ∀ t ∈ c, parentage.Descends t.value p
  | .under _, .explicit _ => False

instance narrowsDecidable (child parent : TargetSet kind) (parentage : Parentage) :
    Decidable (child.Narrows parent parentage) := by
  cases child <;> cases parent <;> unfold Narrows <;> infer_instance

theorem Narrows.refl (targets : TargetSet kind) (parentage : Parentage) :
    targets.Narrows targets parentage := by
  cases targets with
  | explicit ts => exact Finset.Subset.refl ts
  | under room => exact Parentage.Descends.refl room

theorem Narrows.trans {young middle old : TargetSet kind} {parentage : Parentage}
    (first : young.Narrows middle parentage) (second : middle.Narrows old parentage) :
    young.Narrows old parentage := by
  match young, middle, old, first, second with
  | .explicit _, .explicit _, .explicit _, first, second =>
      exact Finset.Subset.trans first second
  | .explicit _, .explicit _, .under _, first, second =>
      exact fun t member => second t (first member)
  | .explicit _, .under _, .explicit _, _, second => exact False.elim second
  | .explicit _, .under _, .under _, first, second =>
      exact fun t member => Parentage.Descends.trans (first t member) second
  | .under _, .explicit _, _, first, _ => exact False.elim first
  | .under _, .under _, .explicit _, _, second => exact False.elim second
  | .under _, .under _, .under _, first, second => exact Parentage.Descends.trans first second

theorem covers_of_narrows {child parent : TargetSet kind} {parentage : Parentage}
    {target : ResourceId kind} (narrows : child.Narrows parent parentage)
    (covers : child.Covers parentage target) : parent.Covers parentage target := by
  match child, parent, narrows, covers with
  | .explicit _, .explicit _, narrows, covers => exact narrows covers
  | .explicit _, .under _, narrows, covers => exact narrows target covers
  | .under _, .explicit _, narrows, _ => exact False.elim narrows
  | .under _, .under _, narrows, covers =>
      exact Parentage.Descends.trans covers narrows

/-- Coverage only grows as parents are recorded. -/
theorem covers_mono {targets : TargetSet kind} {first second : Parentage}
    (grows : ∀ c p, first c = some p → second c = some p)
    {target : ResourceId kind} (covers : targets.Covers first target) :
    targets.Covers second target := by
  cases targets with
  | explicit ts => exact covers
  | under room => exact Parentage.Descends.mono grows covers

theorem narrows_mono {child parent : TargetSet kind} {first second : Parentage}
    (grows : ∀ c p, first c = some p → second c = some p)
    (narrows : child.Narrows parent first) : child.Narrows parent second := by
  match child, parent, narrows with
  | .explicit _, .explicit _, narrows => exact narrows
  | .explicit _, .under _, narrows =>
      exact fun t member => Parentage.Descends.mono grows (narrows t member)
  | .under _, .explicit _, narrows => exact narrows
  | .under _, .under _, narrows => exact Parentage.Descends.mono grows narrows

/-- The request-law binding a capability's target form requires. An explicit
capability names cells governed by the law it was issued under, so it is used
only under that law: the request carries the capability's own policy id and
epoch. An `under R` capability reaches cells born in the room, each governed by
its own law; the controller evaluates the target's committed law for the
request, and the capability stays bound to its issuing law by
`Admissible.policyCurrent` (bumping the room law's epoch revokes it). -/
def RequestLaw (targets : TargetSet kind) (policy : PolicyId) (epoch : Epoch)
    (request : Request kind) : Prop :=
  match targets with
  | .explicit _ => policy = request.policyId ∧ epoch = request.policyEpoch
  | .under _ => True

instance requestLawDecidable (targets : TargetSet kind) (policy : PolicyId) (epoch : Epoch)
    (request : Request kind) : Decidable (targets.RequestLaw policy epoch request) := by
  cases targets <;> unfold RequestLaw <;> infer_instance

end TargetSet

/-! ## §2a. Fields of a cell, as a scope names them.

A scope may name the FIELDS of the cells it covers and bound the change it may
make to each.  `fields = none` is every field; `some fs` is exactly `fs`.
`maxDelta` is a finite set of per-field bounds on the absolute net change one
admitted write makes to that field (the old Gate's `maxMove`).  Every entry
for a field applies, so two entries mean the smaller.  The empty set bounds
nothing.  Bounds are per write (one turn), not cumulative. -/

/-- A field of a cell.  `slot n` is a declared cell's object field `n`
(`resource/field/n`); `balance a` an account balance coordinate of asset `a`;
`code` a declared program's code.  A content cell has two fields: `body`
(documents, atoms, runs, elements, field records, conflicts, transclusions)
and `annotations` (links, marks, annotation records). -/
inductive CellField where
  | slot (n : Nat)
  | balance (asset : Nat)
  | code
  | body
  | annotations
  deriving DecidableEq, Repr

/-- `fields` names `field`: every field when absent, membership otherwise. -/
def CellField.NamedBy (fields : Option (Finset CellField)) (field : CellField) : Prop :=
  match fields with
  | none => True
  | some named => field ∈ named

instance CellField.namedByDecidable (fields : Option (Finset CellField)) (field : CellField) :
    Decidable (CellField.NamedBy fields field) := by
  cases fields <;> unfold CellField.NamedBy <;> infer_instance

/-- Field narrowing: anything narrows `none`; `some c` narrows `some p` when
`c ⊆ p`; `none` (every field) never narrows a named set. -/
def CellField.SetNarrows (child parent : Option (Finset CellField)) : Prop :=
  match child, parent with
  | _, none => True
  | some c, some p => c ⊆ p
  | none, some _ => False

instance CellField.setNarrowsDecidable (child parent : Option (Finset CellField)) :
    Decidable (CellField.SetNarrows child parent) := by
  cases child <;> cases parent <;> unfold CellField.SetNarrows <;> infer_instance

theorem CellField.SetNarrows.refl (fields : Option (Finset CellField)) :
    CellField.SetNarrows fields fields := by
  cases fields <;> simp [CellField.SetNarrows]

theorem CellField.SetNarrows.trans {young middle old : Option (Finset CellField)}
    (first : CellField.SetNarrows young middle) (second : CellField.SetNarrows middle old) :
    CellField.SetNarrows young old := by
  cases young <;> cases middle <;> cases old <;>
    simp_all [CellField.SetNarrows, Finset.Subset.trans]
  exact Finset.Subset.trans first second

theorem CellField.namedBy_of_setNarrows {child parent : Option (Finset CellField)}
    {field : CellField} (narrows : CellField.SetNarrows child parent)
    (named : CellField.NamedBy child field) : CellField.NamedBy parent field := by
  cases child <;> cases parent <;> simp_all [CellField.SetNarrows, CellField.NamedBy]
  exact narrows named

/-- Every parent bound is met by a child bound on the same field that is no
larger.  A child may add bounds; it may not drop or loosen one. -/
def CellField.BoundsNarrow (child parent : Finset (CellField × Nat)) : Prop :=
  ∀ bound ∈ parent, ∃ tighter ∈ child, tighter.1 = bound.1 ∧ tighter.2 ≤ bound.2

instance CellField.boundsNarrowDecidable (child parent : Finset (CellField × Nat)) :
    Decidable (CellField.BoundsNarrow child parent) := by
  unfold CellField.BoundsNarrow; infer_instance

theorem CellField.BoundsNarrow.refl (bounds : Finset (CellField × Nat)) :
    CellField.BoundsNarrow bounds bounds :=
  fun bound member => ⟨bound, member, rfl, le_rfl⟩

theorem CellField.BoundsNarrow.trans {young middle old : Finset (CellField × Nat)}
    (first : CellField.BoundsNarrow young middle) (second : CellField.BoundsNarrow middle old) :
    CellField.BoundsNarrow young old := by
  intro bound member
  obtain ⟨mid, midMember, midField, midLe⟩ := second bound member
  obtain ⟨tight, tightMember, tightField, tightLe⟩ := first mid midMember
  exact ⟨tight, tightMember, tightField.trans midField, le_trans tightLe midLe⟩

/-- What one write changes, as a scope sees it: the fields it touched and the
net signed change on each (a non-numeric field changes by `0`).  The kernel
derives it from the target's committed pre-state and its computed post-state
(`ResourceObservationAdmission.footprint`), never from a request. -/
structure Footprint where
  touched : Finset CellField
  delta : CellField → Int

/-- Under `bounds`, the net change `delta` on `field` is admitted. -/
def CellField.WithinBounds (bounds : Finset (CellField × Nat)) (field : CellField) (delta : Int) :
    Prop :=
  ∀ bound ∈ bounds, bound.1 = field → delta.natAbs ≤ bound.2

instance CellField.withinBoundsDecidable (bounds : Finset (CellField × Nat)) (field : CellField)
    (delta : Int) : Decidable (CellField.WithinBounds bounds field delta) := by
  unfold CellField.WithinBounds; infer_instance

theorem CellField.withinBounds_of_narrows {child parent : Finset (CellField × Nat)}
    {field : CellField} {delta : Int} (narrows : CellField.BoundsNarrow child parent)
    (within : CellField.WithinBounds child field delta) :
    CellField.WithinBounds parent field delta := by
  intro bound member same
  obtain ⟨tight, tightMember, tightField, tightLe⟩ := narrows bound member
  exact le_trans (within tight tightMember (tightField.trans same)) tightLe

/-- A finite, typed authority scope. -/
structure Scope (kind : ResourceKind) where
  targets : TargetSet kind
  verbs : Finset (Verb kind)
  maxCost : Nat
  /-- The fields of each covered cell this scope may write and read; `none`
  is every field. -/
  fields : Option (Finset CellField) := none
  /-- Per-field bounds on the absolute net change of one admitted write. -/
  maxDelta : Finset (CellField × Nat) := ∅
  deriving DecidableEq

structure Scope.Covers {kind : ResourceKind} (scope : Scope kind)
    (parentage : Parentage) (request : Request kind) : Prop where
  target : scope.targets.Covers parentage request.target
  verb : request.verb.AllowedBy scope.verbs
  cost : request.cost ≤ scope.maxCost

/-- `child.Narrows parent parentage` is the authority preorder at one parent
projection: fewer targets, fewer verbs, and no larger budget. -/
structure Scope.Narrows {kind : ResourceKind} (child parent : Scope kind)
    (parentage : Parentage) : Prop where
  targets : child.targets.Narrows parent.targets parentage
  verbs : child.verbs ⊆ parent.verbs
  maxCost : child.maxCost ≤ parent.maxCost
  fields : CellField.SetNarrows child.fields parent.fields
  maxDelta : CellField.BoundsNarrow child.maxDelta parent.maxDelta

theorem Scope.covers_iff_components {kind : ResourceKind} (scope : Scope kind)
    (parentage : Parentage) (request : Request kind) :
    scope.Covers parentage request ↔
      scope.targets.Covers parentage request.target ∧ request.verb.AllowedBy scope.verbs ∧
        request.cost ≤ scope.maxCost :=
  ⟨fun covers => ⟨covers.target, covers.verb, covers.cost⟩,
    fun ⟨target, verb, cost⟩ => ⟨target, verb, cost⟩⟩

instance Scope.coversDecidable {kind : ResourceKind} (scope : Scope kind)
    (parentage : Parentage) (request : Request kind) :
    Decidable (scope.Covers parentage request) :=
  decidable_of_iff _ (Scope.covers_iff_components scope parentage request).symm

theorem Scope.narrows_iff_components {kind : ResourceKind} (child parent : Scope kind)
    (parentage : Parentage) :
    child.Narrows parent parentage ↔
      child.targets.Narrows parent.targets parentage ∧ child.verbs ⊆ parent.verbs ∧
        child.maxCost ≤ parent.maxCost ∧ CellField.SetNarrows child.fields parent.fields ∧
          CellField.BoundsNarrow child.maxDelta parent.maxDelta :=
  ⟨fun narrows => ⟨narrows.targets, narrows.verbs, narrows.maxCost, narrows.fields,
      narrows.maxDelta⟩,
    fun ⟨targets, verbs, cost, fields, bounds⟩ => ⟨targets, verbs, cost, fields, bounds⟩⟩

instance Scope.narrowsDecidable {kind : ResourceKind} (child parent : Scope kind)
    (parentage : Parentage) : Decidable (child.Narrows parent parentage) :=
  decidable_of_iff _ (Scope.narrows_iff_components child parent parentage).symm

theorem Scope.Narrows.refl {kind : ResourceKind} (scope : Scope kind)
    (parentage : Parentage) : scope.Narrows scope parentage :=
  ⟨TargetSet.Narrows.refl _ _, Finset.Subset.refl _, le_rfl, CellField.SetNarrows.refl _,
    CellField.BoundsNarrow.refl _⟩

theorem Scope.Narrows.trans {kind : ResourceKind} {young middle old : Scope kind}
    {parentage : Parentage} (first : young.Narrows middle parentage)
    (second : middle.Narrows old parentage) : young.Narrows old parentage :=
  ⟨first.targets.trans second.targets, Finset.Subset.trans first.verbs second.verbs,
    le_trans first.maxCost second.maxCost, first.fields.trans second.fields,
    first.maxDelta.trans second.maxDelta⟩

theorem Scope.covers_of_narrows {kind : ResourceKind}
    {child parent : Scope kind} {parentage : Parentage} {request : Request kind}
    (hn : child.Narrows parent parentage) (hc : child.Covers parentage request) :
    parent.Covers parentage request :=
  { target := TargetSet.covers_of_narrows hn.targets hc.target
    verb := hc.verb.mono hn.verbs
    cost := le_trans hc.cost hn.maxCost }

theorem Scope.covers_mono {kind : ResourceKind} {scope : Scope kind}
    {first second : Parentage} (grows : ∀ c p, first c = some p → second c = some p)
    {request : Request kind} (covers : scope.Covers first request) :
    scope.Covers second request :=
  ⟨TargetSet.covers_mono grows covers.target, covers.verb, covers.cost⟩

/-- Every field a write touched is named by the scope, and its net change is
within every bound the scope sets on it. -/
def Scope.FieldsCover {kind : ResourceKind} (scope : Scope kind) (footprint : Footprint) : Prop :=
  ∀ field ∈ footprint.touched, CellField.NamedBy scope.fields field ∧
    CellField.WithinBounds scope.maxDelta field (footprint.delta field)

instance Scope.fieldsCoverDecidable {kind : ResourceKind} (scope : Scope kind)
    (footprint : Footprint) : Decidable (scope.FieldsCover footprint) := by
  unfold Scope.FieldsCover; infer_instance

/-- A write is covered when its request is (target, verb, cost) and every field
it changed is (names, bounds). -/
structure Scope.CoversWrite {kind : ResourceKind} (scope : Scope kind)
    (parentage : Parentage) (request : Request kind) (footprint : Footprint) : Prop where
  covers : scope.Covers parentage request
  fields : scope.FieldsCover footprint

/-- Every field a covered write touched is a field the scope names. -/
theorem fields_cover_write {kind : ResourceKind} {scope : Scope kind}
    {parentage : Parentage} {request : Request kind} {footprint : Footprint}
    (covered : scope.CoversWrite parentage request footprint)
    {field : CellField} (touched : field ∈ footprint.touched) :
    CellField.NamedBy scope.fields field :=
  (covered.fields field touched).1

/-- A covered write moves each field by at most every bound the scope sets. -/
theorem maxDelta_bounds_write {kind : ResourceKind} {scope : Scope kind}
    {parentage : Parentage} {request : Request kind} {footprint : Footprint}
    (covered : scope.CoversWrite parentage request footprint)
    {field : CellField} (touched : field ∈ footprint.touched)
    {bound : Nat} (bounded : (field, bound) ∈ scope.maxDelta) :
    (footprint.delta field).natAbs ≤ bound :=
  (covered.fields field touched).2 _ bounded rfl

/-- Narrowing is monotone on fields: what a child scope admits field by field,
its parent admits. -/
theorem narrows_fields_monotone {kind : ResourceKind} {child parent : Scope kind}
    {parentage : Parentage} {footprint : Footprint}
    (narrows : child.Narrows parent parentage) (covered : child.FieldsCover footprint) :
    parent.FieldsCover footprint := fun field touched =>
  ⟨CellField.namedBy_of_setNarrows narrows.fields (covered field touched).1,
    CellField.withinBounds_of_narrows narrows.maxDelta (covered field touched).2⟩

theorem Scope.coversWrite_of_narrows {kind : ResourceKind} {child parent : Scope kind}
    {parentage : Parentage} {request : Request kind} {footprint : Footprint}
    (narrows : child.Narrows parent parentage)
    (covered : child.CoversWrite parentage request footprint) :
    parent.CoversWrite parentage request footprint :=
  ⟨Scope.covers_of_narrows narrows covered.covers, narrows_fields_monotone narrows covered.fields⟩

/-! ## §3. Capabilities and current committed authorization state. -/

/-- A capability's entire semantic payload.  A production commitment must bind
ALL of these fields without lossy folding. -/
structure Capability (kind : ResourceKind) where
  id : CapabilityId
  root : CapabilityId
  parent : Option CapabilityId
  issuer : IssuerId
  holder : Holder
  scope : Scope kind
  notBefore : Height
  notAfter : Height
  issuerEpoch : Epoch
  policyId : PolicyId
  policyEpoch : Epoch
  ancestors : Finset CapabilityId
  channels : Finset ChannelId
  deriving DecidableEq

inductive RevocationKey where
  | capability (id : CapabilityId)
  | channel (id : ChannelId)
  /-- One signing-key version: a subject's key at one key epoch.  Its standing
  (registered, revoked) lives in the authority cell's presence planes; the key
  record itself carries no revocation flag. -/
  | signingKey (subject : SubjectId) (epoch : Epoch)
  deriving DecidableEq, Repr

/-- The authorization-relevant projection of current state.  Epoch comparisons
are exact equalities, never lower bounds and never optional. -/
structure AuthState where
  capabilityRoot : Digest
  revocationRoot : Digest
  /-- Root of the authenticated policy registry.  `policyAddress` below is the
  exact logical projection whose membership is checked against this root. -/
  policyRoot : Digest
  /-- The committed content address selected by an exact `(id,revision)` pair. -/
  policyAddress : PolicyId → PolicyRevision → Digest
  revoked : Finset RevocationKey
  issuerEpoch : IssuerId → Epoch
  policyEpoch : PolicyId → Epoch
  policyRevision : PolicyId → PolicyRevision
  subjectKeyEpoch : SubjectId → Epoch
  /-- The system cell's parent projection: which room each cell was created
  under. It decides `TargetSet.under` coverage and explicit-under-room
  narrowing. -/
  parent : Parentage

namespace Capability

/-- Pure semantic admission for one capability and one COMPLETE request. -/
structure Admissible {kind : ResourceKind} (cap : Capability kind)
    (state : AuthState) (request : Request kind) : Prop where
  holder : cap.holder.Covers request.subject
  scope : cap.scope.Covers state.parent request
  validFrom : cap.notBefore ≤ request.height
  validUntil : request.height ≤ cap.notAfter
  requestLaw : cap.scope.targets.RequestLaw cap.policyId cap.policyEpoch request
  policyCurrent : cap.policyEpoch = state.policyEpoch cap.policyId
  issuerCurrent : cap.issuerEpoch = state.issuerEpoch cap.issuer
  selfNotRevoked : RevocationKey.capability cap.id ∉ state.revoked
  ancestorNotRevoked :
    ∀ ancestor, ancestor ∈ cap.ancestors →
      RevocationKey.capability ancestor ∉ state.revoked
  channelNotRevoked :
    ∀ channel, channel ∈ cap.channels →
      RevocationKey.channel channel ∉ state.revoked

/-- A derived capability commits its exact parent/root lineage, retains the
issuer and both epochs, narrows scope/time, records the parent plus every prior
ancestor, and may only ADD revocation channels.  Scope narrowing is decided
at the parent projection `parentage` of the state the edge is checked in. -/
structure Attenuates {kind : ResourceKind} (child parent : Capability kind)
    (parentage : Parentage) : Prop where
  parentId : child.parent = some parent.id
  root : child.root = parent.root
  issuer : child.issuer = parent.issuer
  scopeNarrows : child.scope.Narrows parent.scope parentage
  notBefore : parent.notBefore ≤ child.notBefore
  notAfter : child.notAfter ≤ parent.notAfter
  issuerEpoch : child.issuerEpoch = parent.issuerEpoch
  policyId : child.policyId = parent.policyId
  policyEpoch : child.policyEpoch = parent.policyEpoch
  ancestors : child.ancestors = insert parent.id parent.ancestors
  channels : parent.channels ⊆ child.channels

/-- The central attenuation law: anything inside the child scope was already
inside the parent scope. -/
theorem attenuation_scope_monotone {kind : ResourceKind}
    {child parent : Capability kind} {parentage : Parentage} {request : Request kind}
    (ha : child.Attenuates parent parentage) (hc : child.scope.Covers parentage request) :
    parent.scope.Covers parentage request :=
  Scope.covers_of_narrows ha.scopeNarrows hc

/-- Parents are append-only, so an edge checked at one projection stays an
attenuation at every later one. -/
theorem Attenuates.mono {kind : ResourceKind} {child parent : Capability kind}
    {first second : Parentage} (grows : ∀ c p, first c = some p → second c = some p)
    (ha : child.Attenuates parent first) : child.Attenuates parent second :=
  { ha with
    scopeNarrows :=
      ⟨TargetSet.narrows_mono grows ha.scopeNarrows.targets, ha.scopeNarrows.verbs,
        ha.scopeNarrows.maxCost, ha.scopeNarrows.fields, ha.scopeNarrows.maxDelta⟩ }

/-- Full semantic monotonicity.  Holder delegation is intentionally explicit:
the caller must show that the parent holder covers the presented subject.  All
other authority facts follow from child admission and attenuation, including
the parent's revocation status because the parent id is a committed ancestor. -/
theorem attenuation_admits_subset {kind : ResourceKind}
    {child parent : Capability kind} {state : AuthState}
    {request : Request kind}
    (ha : child.Attenuates parent state.parent)
    (hc : child.Admissible state request)
    (parentHolder : parent.holder.Covers request.subject) :
    parent.Admissible state request := by
  refine
    { holder := parentHolder
      scope := attenuation_scope_monotone ha hc.scope
      validFrom := le_trans ha.notBefore hc.validFrom
      validUntil := le_trans hc.validUntil ha.notAfter
      requestLaw := ?_
      policyCurrent := ?_
      issuerCurrent := ?_
      selfNotRevoked := ?_
      ancestorNotRevoked := ?_
      channelNotRevoked := ?_ }
  · have narrows := ha.scopeNarrows.targets
    have law := hc.requestLaw
    revert narrows law
    cases parent.scope.targets with
    | under _ => intro _ _; trivial
    | explicit _ =>
        cases child.scope.targets with
        | under _ => intro narrows; exact narrows.elim
        | explicit _ =>
            intro _ law
            exact ⟨ha.policyId.symm.trans law.1, ha.policyEpoch.symm.trans law.2⟩
  · calc
      parent.policyEpoch = child.policyEpoch := ha.policyEpoch.symm
      _ = state.policyEpoch child.policyId := hc.policyCurrent
      _ = state.policyEpoch parent.policyId := congrArg state.policyEpoch ha.policyId
  · calc
      parent.issuerEpoch = child.issuerEpoch := ha.issuerEpoch.symm
      _ = state.issuerEpoch child.issuer := hc.issuerCurrent
      _ = state.issuerEpoch parent.issuer := congrArg state.issuerEpoch ha.issuer
  · apply hc.ancestorNotRevoked parent.id
    rw [ha.ancestors]
    exact Finset.mem_insert_self parent.id parent.ancestors
  · intro ancestor hmem
    apply hc.ancestorNotRevoked ancestor
    rw [ha.ancestors]
    exact Finset.mem_insert_of_mem hmem
  · intro channel hmem
    exact hc.channelNotRevoked channel (ha.channels hmem)

/-- Fields are orthogonal to request admission: re-scoping a capability's
fields or bounds changes no request it admits.  Fields constrain only what a
write changes (`AdmitsWrite`) and what a read returns. -/
theorem admissible_fields_orthogonal {kind : ResourceKind} {cap : Capability kind}
    {state : AuthState} {request : Request kind}
    (fields : Option (Finset CellField)) (bounds : Finset (CellField × Nat))
    (admitted : cap.Admissible state request) :
    ({ cap with scope := { cap.scope with fields := fields, maxDelta := bounds } } :
      Capability kind).Admissible state request :=
  ⟨admitted.holder, ⟨admitted.scope.target, admitted.scope.verb, admitted.scope.cost⟩,
    admitted.validFrom, admitted.validUntil, admitted.requestLaw, admitted.policyCurrent,
    admitted.issuerCurrent, admitted.selfNotRevoked, admitted.ancestorNotRevoked,
    admitted.channelNotRevoked⟩

/-- Admission of one write: the request is admissible and the capability's
scope covers every field the write changed. -/
structure AdmitsWrite {kind : ResourceKind} (cap : Capability kind) (state : AuthState)
    (request : Request kind) (footprint : Footprint) : Prop where
  admissible : cap.Admissible state request
  fields : cap.scope.FieldsCover footprint

/-- `attenuation_admits_subset`, field by field: a write a child admits, its
parent admits, including every named field and every per-field bound. -/
theorem attenuation_admits_write_subset {kind : ResourceKind}
    {child parent : Capability kind} {state : AuthState}
    {request : Request kind} {footprint : Footprint}
    (ha : child.Attenuates parent state.parent)
    (hc : child.AdmitsWrite state request footprint)
    (parentHolder : parent.holder.Covers request.subject) :
    parent.AdmitsWrite state request footprint :=
  ⟨attenuation_admits_subset ha hc.admissible parentHolder,
    narrows_fields_monotone ha.scopeNarrows hc.fields⟩

end Capability

/-- A narrowing checked once stays a narrowing while parents are only ever
added: every recorded `(cell, room)` pair of the earlier projection is still
recorded in the later one. An explicit target that had no recorded parent at
the check was refused then; later growth cannot reach back into that check. -/
theorem Scope.narrows_stable {kind : ResourceKind} {state₁ state₂ : AuthState}
    {child parent : Scope kind}
    (grows : ∀ c p, state₁.parent c = some p → state₂.parent c = some p)
    (narrows : child.Narrows parent state₁.parent) :
    child.Narrows parent state₂.parent :=
  ⟨TargetSet.narrows_mono grows narrows.targets, narrows.verbs, narrows.maxCost,
    narrows.fields, narrows.maxDelta⟩

/-! ## §4. Explicit verifier portals and request-indexed evidence. -/

/-- Executable cryptographic verifier boundary.  Every predicate returns a
Boolean and receives the exact statement it checks.  There is deliberately no
global proposition asserting that an arbitrary implementation is sound. -/
structure Portal where
  SignatureWitness : Type
  ProofWitness : Type
  CapabilityCommitmentWitness : Type
  /-- Request-bound invocation authority is distinct from public capability
  data. Subject holders can use an exact-request signature; bearer holders
  require a genuine possession verifier, not knowledge of a public lookup. -/
  CapabilityUseWitness : Type
  MembershipWitness : Type
  IssuerWitness : Type
  NonRevocationWitness : Type
  PolicyWitness : Type
  /-- Extract the content address named by a first-order policy witness. -/
  policyAddress : PolicyWitness → Digest
  verifySignature : {kind : ResourceKind} → Request kind → SignatureWitness → Bool
  verifyProof : {kind : ResourceKind} → Request kind → ProofWitness → Bool
  verifyCapabilityCommitment :
    {kind : ResourceKind} → Capability kind → Digest →
      CapabilityCommitmentWitness → Bool
  verifyCapabilityUse :
    {kind : ResourceKind} → Request kind → Capability kind → Digest →
      CapabilityUseWitness → Bool
  verifyMembership : Digest → Digest → MembershipWitness → Bool
  verifyIssuer : IssuerId → Epoch → Digest → IssuerWitness → Bool
  verifyNonRevocation : Digest → RevocationKey → NonRevocationWitness → Bool
  /-- Verify the policy witness only for the exact committed address supplied
  by authorization state.  Legacy address-free `verifyPolicy` no longer
  exists, so a witness cannot choose policy content outside that state. -/
  verifyCommittedPolicy :
    Digest → {kind : ResourceKind} → Request kind → PolicyWitness → Bool

/-- Evidence is indexed by the COMPLETE request.  Each constructor's verifier
therefore checks that exact value, not a separately supplied action/resource
claim.  Capability evidence additionally binds the complete cap, current root,
issuer epoch, and every exact revocation key used by semantic admission. -/
inductive Evidence (portal : Portal) (state : AuthState)
    {kind : ResourceKind} (request : Request kind) : Type where
  | signature
      (witness : portal.SignatureWitness)
      (keyEpochExact : request.subjectKeyEpoch = state.subjectKeyEpoch request.subject)
      (verified : portal.verifySignature request witness = true) :
      Evidence portal state request
  | proof
      (witness : portal.ProofWitness)
      (verified : portal.verifyProof request witness = true) :
      Evidence portal state request
  | capability
      (cap : Capability kind)
      (commitment : Digest)
      (commitmentWitness : portal.CapabilityCommitmentWitness)
      (membershipWitness : portal.MembershipWitness)
      (issuerWitness : portal.IssuerWitness)
      (selfRevocationWitness : portal.NonRevocationWitness)
      (useWitness : portal.CapabilityUseWitness)
      (semantic : cap.Admissible state request)
      (useVerified : portal.verifyCapabilityUse request cap commitment useWitness = true)
      (commitmentVerified :
        portal.verifyCapabilityCommitment cap commitment commitmentWitness = true)
      (membershipVerified :
        portal.verifyMembership state.capabilityRoot commitment membershipWitness = true)
      (issuerVerified :
        portal.verifyIssuer cap.issuer cap.issuerEpoch commitment issuerWitness = true)
      (selfRevocationVerified :
        portal.verifyNonRevocation state.revocationRoot
          (.capability cap.id) selfRevocationWitness = true)
      (ancestorVerified :
        ∀ ancestor, ancestor ∈ cap.ancestors →
          ∃ witness : portal.NonRevocationWitness,
            portal.verifyNonRevocation state.revocationRoot
              (.capability ancestor) witness = true)
      (channelVerified :
        ∀ channel, channel ∈ cap.channels →
          ∃ witness : portal.NonRevocationWitness,
            portal.verifyNonRevocation state.revocationRoot
              (.channel channel) witness = true) :
      Evidence portal state request

/-- Which public capability data a capability-mode evidence value names.
Signature and proof modes do not silently become capability invocations. -/
def Evidence.capabilityValue {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind} :
    Evidence portal state request → Option (Capability kind × Digest)
  | .capability cap commitment .. => some (cap, commitment)
  | _ => none

/-- Every capability invocation retains a verifier result bound to its whole
actual request, exact capability, and exact commitment. Membership, issuer
verification, and public stored-capability bytes cannot substitute for it. -/
theorem capability_evidence_requires_use {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence portal state request) (capability : Capability kind)
    (commitment : Digest)
    (named : evidence.capabilityValue = some (capability, commitment)) :
    ∃ witness, portal.verifyCapabilityUse request capability commitment witness = true := by
  cases evidence with
  | signature witness epoch verified => simp [Evidence.capabilityValue] at named
  | proof witness verified => simp [Evidence.capabilityValue] at named
  | capability cap address commitmentWitness membershipWitness issuerWitness
      selfRevocationWitness useWitness semantic useVerified commitmentVerified
      membershipVerified issuerVerified selfVerified ancestors channels =>
      have equal : (cap, address) = (capability, commitment) := Option.some.inj named
      rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
      exact ⟨useWitness, useVerified⟩

/-- Copying public capability data does not construct the invocation when
every request-bound use witness is refused by the selected verifier. -/
theorem no_capability_evidence_of_use_refused {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (capability : Capability kind) (commitment : Digest)
    (refused : ∀ witness,
      portal.verifyCapabilityUse request capability commitment witness ≠ true) :
    ¬∃ evidence : Evidence portal state request,
      evidence.capabilityValue = some (capability, commitment) := by
  rintro ⟨evidence, named⟩
  obtain ⟨witness, verified⟩ := capability_evidence_requires_use evidence capability commitment named
  exact refused witness verified

/-- Policy selection is one common final gate for every evidence constructor;
no evidence mode may return before it. -/
structure Authorized (portal : Portal) (state : AuthState)
    {kind : ResourceKind} (request : Request kind) : Type where
  evidence : Evidence portal state request
  policyWitness : portal.PolicyWitness
  policyMembershipWitness : portal.MembershipWitness
  policyEpochExact : request.policyEpoch = state.policyEpoch request.policyId
  policyRevisionExact : request.policyRevision = state.policyRevision request.policyId
  policyAddressExact :
    portal.policyAddress policyWitness =
      state.policyAddress request.policyId request.policyRevision
  policyMembershipVerified :
    portal.verifyMembership state.policyRoot
      (state.policyAddress request.policyId request.policyRevision)
      policyMembershipWitness = true
  policyVerified :
    portal.verifyCommittedPolicy
      (state.policyAddress request.policyId request.policyRevision)
      request policyWitness = true

/-- Retained grants follow the current mutable policy. Changing source revision
and snapshot roots does not change the immutable capability bounds. This
transports only semantic capability admission: a fresh signature, current-source
membership and acceptance by the new predicate remain separate obligations. -/
theorem Capability.Admissible.at_policy_revision {kind : ResourceKind}
    {cap : Capability kind} {before after : AuthState} {request : Request kind}
    (admitted : cap.Admissible before request)
    (sameRevocations : after.revoked = before.revoked)
    (sameIssuer : after.issuerEpoch cap.issuer = before.issuerEpoch cap.issuer)
    (sameGeneration : after.policyEpoch cap.policyId = before.policyEpoch cap.policyId)
    (parentsGrow : ∀ c p, before.parent c = some p → after.parent c = some p)
    (revision : PolicyRevision) (preRoot : Digest) :
    cap.Admissible after
      { request with policyRevision := revision, preStateRoot := preRoot } where
  holder := admitted.holder
  scope := Scope.covers_mono parentsGrow
    ⟨admitted.scope.target, admitted.scope.verb, admitted.scope.cost⟩
  validFrom := admitted.validFrom
  validUntil := admitted.validUntil
  requestLaw := admitted.requestLaw
  policyCurrent := admitted.policyCurrent.trans sameGeneration.symm
  issuerCurrent := admitted.issuerCurrent.trans sameIssuer.symm
  selfNotRevoked := by simpa only [sameRevocations] using admitted.selfNotRevoked
  ancestorNotRevoked := by simpa only [sameRevocations] using admitted.ancestorNotRevoked
  channelNotRevoked := by simpa only [sameRevocations] using admitted.channelNotRevoked

/-- No evidence mode, including signature-only and proof-only modes, can select
an obsolete or future policy source revision. -/
theorem wrong_policy_revision_rejected {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (wrong : request.policyRevision ≠ state.policyRevision request.policyId) :
    ¬ Nonempty (Authorized portal state request) := by
  rintro ⟨accepted⟩
  exact wrong accepted.policyRevisionExact

/-- Source selection uses the current revision even when the grant generation
has a different numeric value. -/
theorem Authorized.current_policy_address {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : Authorized portal state request) :
    portal.policyAddress accepted.policyWitness =
      state.policyAddress request.policyId (state.policyRevision request.policyId) := by
  rw [← accepted.policyRevisionExact]
  exact accepted.policyAddressExact

/-! ## §5. Negative teeth. -/

/-- Target substitution fails semantically, in addition to producing the wrong
`Evidence` type, whenever the substituted target is outside the committed
scope. -/
theorem target_substitution_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (target : ResourceId kind) (outside : ¬ cap.scope.targets.Covers state.parent target) :
    ¬ cap.Admissible state (request.retarget target) := by
  intro admitted
  apply outside
  simpa [Request.retarget] using admitted.scope.target

/-- Code-edit authority cannot silently become authority to replace the
acceptance policy, even at the same program target and with a valid signer. -/
theorem program_edit_capability_cannot_install_policy
    (cap : Capability .program) (state : AuthState) (request : Request .program)
    (codeOnly : cap.scope.verbs = {.installProgram})
    (policyChange : request.verb = .installPolicy) :
    ¬ cap.Admissible state request := by
  intro admitted
  have allowed := admitted.scope.verb
  simp [codeOnly, policyChange, Verb.AllowedBy, Verb.grantors] at allowed

/-- Policy replacement authority does not silently acquire revocation authority. -/
theorem policy_install_only_cannot_revoke
    (cap : Capability .program) (state : AuthState) (request : Request .program)
    (installOnly : cap.scope.verbs = {.installPolicy})
    (revocation : request.verb = .revokeCapability) :
    ¬ cap.Admissible state request := by
  intro admitted
  have allowed := admitted.scope.verb
  simp [installOnly, revocation, Verb.AllowedBy, Verb.grantors] at allowed

/-- A caller cannot pre-load a capability with a future issuer epoch.  Exact
equality to current state rejects every strictly forward epoch. -/
theorem forward_issuer_epoch_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (forward : state.issuerEpoch cap.issuer < cap.issuerEpoch) :
    ¬ cap.Admissible state request := by
  intro admitted
  exact (Nat.ne_of_lt forward) admitted.issuerCurrent.symm

/-- Revoking ANY committed ancestor kills the descendant capability. -/
theorem ancestor_revocation_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (ancestor : CapabilityId) (isAncestor : ancestor ∈ cap.ancestors)
    (isRevoked : RevocationKey.capability ancestor ∈ state.revoked) :
    ¬ cap.Admissible state request := by
  intro admitted
  exact admitted.ancestorNotRevoked ancestor isAncestor isRevoked

/-- Revocation channels have the same committed, fail-closed semantics. -/
theorem channel_revocation_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (channel : ChannelId) (isChannel : channel ∈ cap.channels)
    (isRevoked : RevocationKey.channel channel ∈ state.revoked) :
    ¬ cap.Admissible state request := by
  intro admitted
  exact admitted.channelNotRevoked channel isChannel isRevoked

/-- Stale policy epochs fail for the same exact-equality reason. -/
theorem stale_policy_epoch_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (stale : cap.policyEpoch ≠ state.policyEpoch cap.policyId) :
    ¬ cap.Admissible state request := by
  intro admitted
  exact stale admitted.policyCurrent

/-! ## §6. Concrete positive and negative poles. -/

def demoTarget : ResourceId .object := ⟨10⟩
def demoOtherTarget : ResourceId .object := ⟨11⟩

def demoRequest : Request .object where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 2
  target := demoTarget
  verb := .mutateObject
  argsDigest := ⟨5⟩
  effectsDigest := ⟨6⟩
  nonce := 7
  height := 10
  preStateRoot := ⟨8⟩
  policyId := ⟨9⟩
  policyEpoch := 5
  policyRevision := 11
  cost := 4

def demoScope : Scope .object where
  targets := .explicit {demoTarget}
  verbs := {.mutateObject}
  maxCost := 8

def demoCapability : Capability .object where
  id := ⟨20⟩
  root := ⟨20⟩
  parent := none
  issuer := ⟨7⟩
  holder := .subject ⟨4⟩
  scope := demoScope
  notBefore := 3
  notAfter := 20
  issuerEpoch := 3
  policyId := ⟨9⟩
  policyEpoch := 5
  ancestors := ∅
  channels := {⟨21⟩}

def demoState : AuthState where
  capabilityRoot := ⟨30⟩
  revocationRoot := ⟨31⟩
  policyRoot := ⟨33⟩
  policyAddress := fun _ _ => ⟨34⟩
  revoked := ∅
  issuerEpoch := fun _ => 3
  policyEpoch := fun _ => 5
  policyRevision := fun _ => 11
  subjectKeyEpoch := fun _ => 2
  parent := Parentage.empty

theorem demoCapability_admissible :
    demoCapability.Admissible demoState demoRequest := by
  refine
    { holder := ?_
      scope := ?_
      validFrom := ?_
      validUntil := ?_
      requestLaw := ?_
      policyCurrent := ?_
      issuerCurrent := ?_
      selfNotRevoked := ?_
      ancestorNotRevoked := ?_
      channelNotRevoked := ?_ }
  · simp [Holder.Covers, demoCapability, demoRequest]
  · exact
      { target := by simp [TargetSet.Covers, demoCapability, demoScope, demoRequest, demoTarget]
        verb := by simp [demoCapability, demoScope, demoRequest, Verb.AllowedBy, Verb.grantors]
        cost := by norm_num [demoCapability, demoScope, demoRequest] }
  · norm_num [demoCapability, demoRequest]
  · norm_num [demoCapability, demoRequest]
  · exact ⟨rfl, rfl⟩
  · rfl
  · rfl
  · simp [demoCapability, demoState]
  · intro ancestor hmem
    simp [demoCapability] at hmem
  · intro channel hmem
    simp [demoState]

/-- A concrete portal used only to show that the indexed API is inhabited.
Production code supplies real verifier functions; no theorem below infers
cryptographic soundness from this example. -/
def demoPortal : Portal where
  SignatureWitness := Unit
  ProofWitness := Unit
  CapabilityCommitmentWitness := Unit
  CapabilityUseWitness := Unit
  MembershipWitness := Unit
  IssuerWitness := Unit
  NonRevocationWitness := Unit
  PolicyWitness := Unit
  policyAddress := fun _ => ⟨34⟩
  verifySignature := fun _ _ => true
  verifyProof := fun _ _ => true
  verifyCapabilityCommitment := fun _ _ _ => true
  verifyCapabilityUse := fun _ _ _ _ => true
  verifyMembership := fun _ _ _ => true
  verifyIssuer := fun _ _ _ _ => true
  verifyNonRevocation := fun _ _ _ => true
  verifyCommittedPolicy := fun _ _ _ _ => true

def demoEvidence : Evidence demoPortal demoState demoRequest :=
  .capability demoCapability ⟨32⟩ () () () () () demoCapability_admissible
    rfl rfl rfl rfl rfl
    (by
      intro ancestor hmem
      simp [demoCapability] at hmem)
    (by
      intro channel _
      exact ⟨(), rfl⟩)

/-- Positive tooth: a subject-bound, current-epoch, live, unrevoked capability
with explicit commitment/membership/issuer/non-revocation checks authorizes. -/
def demo_authorized_positive : Authorized demoPortal demoState demoRequest where
  evidence := demoEvidence
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyRevisionExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

/-- Negative tooth: the same capability cannot authorize a different target. -/
theorem demo_target_substitution_rejected :
    ¬ demoCapability.Admissible demoState
      (demoRequest.retarget demoOtherTarget) := by
  apply target_substitution_rejected
  simp [TargetSet.Covers, demoCapability, demoScope, demoOtherTarget, demoTarget]

def demoForwardEpochCapability : Capability .object :=
  { demoCapability with issuerEpoch := 4 }

/-- Negative tooth: an epoch from the future is rejected, rather than surviving
future revocation bumps. -/
theorem demo_forward_epoch_rejected :
    ¬ demoForwardEpochCapability.Admissible demoState demoRequest := by
  apply forward_issuer_epoch_rejected
  norm_num [demoForwardEpochCapability, demoCapability, demoState]

def demoAncestorCapability : Capability .object :=
  { demoCapability with ancestors := {⟨99⟩} }

def demoAncestorRevokedState : AuthState :=
  { demoState with revoked := {.capability ⟨99⟩} }

/-- Negative tooth: revoking a committed ancestor rejects the descendant. -/
theorem demo_ancestor_revocation_rejected :
    ¬ demoAncestorCapability.Admissible demoAncestorRevokedState demoRequest := by
  apply ancestor_revocation_rejected
      (ancestor := (⟨99⟩ : CapabilityId))
  · simp [demoAncestorCapability]
  · simp [demoAncestorRevokedState]

/-- The positive fixture deliberately has generation five and revision eleven:
source version is not a synonym for grant generation. -/
theorem demo_generation_revision_independent :
    demoRequest.policyEpoch ≠ demoRequest.policyRevision := by decide

theorem demo_existing_grant_survives_source_update :
    demoCapability.Admissible
      { demoState with policyRevision := fun _ => 12, policyAddress := fun _ _ => ⟨35⟩ }
      { demoRequest with policyRevision := 12, preStateRoot := ⟨36⟩ } :=
  demoCapability_admissible.at_policy_revision
    (after := { demoState with policyRevision := fun _ => 12, policyAddress := fun _ _ => ⟨35⟩ }) rfl rfl rfl
    (fun _ _ recorded => recorded) 12 ⟨36⟩

theorem demo_stale_revision_rejected :
    ¬ Nonempty (Authorized demoPortal
      { demoState with policyRevision := fun _ => 12 } demoRequest) := by
  apply wrong_policy_revision_rejected
  decide

theorem demo_explicit_generation_rotation_revokes :
    ¬ demoCapability.Admissible
      { demoState with policyEpoch := fun _ => 6 } demoRequest := by
  apply stale_policy_epoch_rejected
  decide

/-- info: 'Minidregg.Theory.TypedAuthorization.Parentage.descends_iff_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Parentage.descends_iff_bounded
/-- info: 'Minidregg.Theory.TypedAuthorization.Parentage.ancestor_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Parentage.ancestor_bounded
/-- info: 'Minidregg.Theory.TypedAuthorization.Parentage.ofList_append_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Parentage.ofList_append_extends
/-- info: 'Minidregg.Theory.TypedAuthorization.TargetSet.covers_of_narrows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.TargetSet.covers_of_narrows
/-- info: 'Minidregg.Theory.TypedAuthorization.TargetSet.Narrows.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.TargetSet.Narrows.trans
/-- info: 'Minidregg.Theory.TypedAuthorization.Parentage.under_fresh_covers_only_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Parentage.under_fresh_covers_only_self
end Minidregg.Theory.TypedAuthorization
/-- info: 'Minidregg.Theory.TypedAuthorization.fields_cover_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.fields_cover_write
/-- info: 'Minidregg.Theory.TypedAuthorization.maxDelta_bounds_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.maxDelta_bounds_write
/-- info: 'Minidregg.Theory.TypedAuthorization.narrows_fields_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.narrows_fields_monotone
/-- info: 'Minidregg.Theory.TypedAuthorization.Scope.coversWrite_of_narrows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Scope.coversWrite_of_narrows
/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.attenuation_admits_write_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Capability.attenuation_admits_write_subset
/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.admissible_fields_orthogonal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Capability.admissible_fields_orthogonal
/-- info: 'Minidregg.Theory.TypedAuthorization.CellField.SetNarrows.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.CellField.SetNarrows.trans
/-- info: 'Minidregg.Theory.TypedAuthorization.CellField.BoundsNarrow.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.CellField.BoundsNarrow.trans
