/-
# Theory.CausalVersionAncestry -- admitted ancestry and conservative merge bases

This module adds proof-relevant ancestry to `CausalVersionDag` without changing
its append policy.  A direct edge is extracted from an actual `Builds.append`
certificate and one of that append's exact `resolvedParents`; it is not a host
claim that two matching digests happened to occur in a graph.

An ancestry path retains every admitted parent edge.  Strict semantic-version
increase along those edges proves soundness, transitivity, and acyclicity.  The
common-base layer distinguishes three honest outcomes: a certified lowest base,
explicitly ambiguous incomparable maximal bases, or absence of any common base.
It does not claim that an arbitrary DAG has a unique LCA.

Consensus, finality, merge semantics, and tip-selection policy remain outside
this module.
-/

import Theory.CausalVersionDag

namespace Minidregg.Theory.CausalVersionAncestry

open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uState uEvidence

section Ancestry

variable {State : Type uState}
variable {scheme : ContentAddressing}
variable {family : SemanticFamily.{uState, uEvidence} State}
variable {anchor : Anchor}

abbrev VersionNode
    (State : Type uState) (scheme : ContentAddressing)
    (family : SemanticFamily.{uState, uEvidence} State) :=
  VerifiedEvent scheme family

/-! ## Direct edges extracted from actual append certificates -/

/-- One admitted direct-parent edge in one exact `Builds` derivation.

`latest` selects a parent from the exact ordered `resolvedParents` carried by
the newest valid append.  `earlier` transports an already admitted edge through
an unrelated later append without rechecking or strengthening append policy. -/
inductive AdmittedParent :
    {events : List (VersionNode State scheme family)} ->
    Builds anchor events ->
    VersionNode State scheme family ->
    VersionNode State scheme family -> Type _ where
  | latest
      {prior : List (VersionNode State scheme family)}
      {child parent : VersionNode State scheme family}
      (built : Builds anchor prior)
      (valid : ValidAppend anchor prior child)
      (present : parent ∈ valid.resolvedParents) :
      AdmittedParent (Builds.append built valid) parent child
  | earlier
      {prior : List (VersionNode State scheme family)}
      {newest parent child : VersionNode State scheme family}
      {built : Builds anchor prior}
      {valid : ValidAppend anchor prior newest}
      (edge : AdmittedParent built parent child) :
      AdmittedParent (Builds.append built valid) parent child

namespace AdmittedParent

variable {events : List (VersionNode State scheme family)}
variable {built : Builds anchor events}
variable {parent child : VersionNode State scheme family}

/-- The parent endpoint is an actual admitted node. -/
theorem parent_mem (edge : AdmittedParent built parent child) :
    parent ∈ events := by
  induction edge with
  | latest built valid present =>
      exact List.mem_append.mpr
        (.inl (valid.resolvedParentsPresent _ present))
  | earlier edge induction =>
      exact List.mem_append.mpr (.inl induction)

/-- The child endpoint is an actual admitted node. -/
theorem child_mem (edge : AdmittedParent built parent child) :
    child ∈ events := by
  induction edge with
  | latest => simp
  | earlier edge induction =>
      exact List.mem_append.mpr (.inl induction)

/-- The edge's parent id occurs in the child's exact serialized frontier. -/
theorem parent_id_named (edge : AdmittedParent built parent child) :
    parent.entryId ∈ child.preimage.parentFrontier := by
  induction edge with
  | latest built valid present =>
      have inResolved :
          _ ∈ valid.resolvedParents.map VerifiedEvent.entryId :=
        List.mem_map_of_mem (f := VerifiedEvent.entryId) present
      rw [valid.resolvedParentsExact] at inResolved
      exact inResolved
  | earlier edge induction => exact induction

/-- Every admitted direct edge strictly increases semantic version. -/
theorem semanticVersion_lt (edge : AdmittedParent built parent child) :
    parent.preimage.semanticVersion < child.preimage.semanticVersion := by
  induction edge with
  | latest built valid present =>
      exact valid.semanticVersionIncreases _ present
  | earlier edge induction => exact induction

/-- Every admitted direct edge preserves the history anchor. -/
theorem anchor_exact (edge : AdmittedParent built parent child) :
    anchor.Contains parent.preimage /\ anchor.Contains child.preimage := by
  induction edge with
  | latest built valid present =>
      exact ⟨valid.parentAnchorExact _ present, valid.anchorExact⟩
  | earlier edge induction => exact induction

/-- Every admitted direct edge retains exact schema identity and monotone schema
version. -/
theorem schema_sound (edge : AdmittedParent built parent child) :
    parent.preimage.schema.schemaId = child.preimage.schema.schemaId /\
    parent.preimage.schema.version ≤ child.preimage.schema.version := by
  induction edge with
  | latest built valid present =>
      exact ⟨valid.parentSchemaExact _ present,
        valid.schemaVersionMonotone _ present⟩
  | earlier edge induction => exact induction

end AdmittedParent

/-- Direct-parent relation in one packaged proof-native history. -/
abbrev DirectParent (history : History (scheme := scheme) (family := family) anchor)
    (parent child : VersionNode State scheme family) : Type _ :=
  AdmittedParent history.builds parent child

/-! ## Proof-relevant strict ancestry -/

/-- A nonempty path of actual admitted direct-parent edges. -/
inductive Ancestry
    (history : History (scheme := scheme) (family := family) anchor) :
    VersionNode State scheme family -> VersionNode State scheme family -> Type _ where
  | direct {parent child : VersionNode State scheme family} :
      DirectParent history parent child -> Ancestry history parent child
  | extend {ancestor parent child : VersionNode State scheme family} :
      Ancestry history ancestor parent ->
      DirectParent history parent child ->
      Ancestry history ancestor child

namespace Ancestry

variable {history : History (scheme := scheme) (family := family) anchor}
variable {ancestor middle descendant : VersionNode State scheme family}

/-- The first endpoint of an ancestry path is admitted. -/
theorem ancestor_mem (path : Ancestry history ancestor descendant) :
    ancestor ∈ history.events := by
  induction path with
  | direct edge => exact edge.parent_mem
  | extend path edge induction => exact induction

/-- The last endpoint of an ancestry path is admitted. -/
theorem descendant_mem (path : Ancestry history ancestor descendant) :
    descendant ∈ history.events := by
  induction path with
  | direct edge => exact edge.child_mem
  | extend path edge induction => exact edge.child_mem

/-- Semantic versions strictly increase along every nonempty ancestry path. -/
theorem semanticVersion_lt (path : Ancestry history ancestor descendant) :
    ancestor.preimage.semanticVersion < descendant.preimage.semanticVersion := by
  induction path with
  | direct edge => exact edge.semanticVersion_lt
  | extend path edge induction =>
      exact Nat.lt_trans induction edge.semanticVersion_lt

/-- Concatenate two retained ancestry paths. -/
noncomputable def trans
    (left : Ancestry history ancestor middle)
    {descendant : VersionNode State scheme family}
    (right : Ancestry history middle descendant) :
    Ancestry history ancestor descendant := by
  induction right with
  | direct edge => exact .extend left edge
  | extend frontPath edge induction => exact .extend induction edge

/-- Named transitivity theorem for relation-style consumers. -/
noncomputable def transitive
    (left : Ancestry history ancestor middle)
    (right : Ancestry history middle descendant) :
    Ancestry history ancestor descendant :=
  trans left right

/-- A strict ancestry path cannot end where it began. -/
theorem ne (path : Ancestry history ancestor descendant) :
    ancestor ≠ descendant := by
  intro equal
  subst descendant
  exact (Nat.lt_irrefl ancestor.preimage.semanticVersion)
    path.semanticVersion_lt

/-- Explicit no-self tooth. -/
theorem no_self (node : VersionNode State scheme family) :
    Ancestry history node node -> False :=
  fun path => path.ne rfl

/-- Two opposed strict ancestry paths would contradict version monotonicity. -/
theorem acyclic
    (forward : Ancestry history ancestor descendant)
    (backward : Ancestry history descendant ancestor) : False :=
  (Nat.not_lt_of_ge (Nat.le_of_lt backward.semanticVersion_lt))
    forward.semanticVersion_lt

end Ancestry

/-! ## Reflexive reachability and common bases -/

/-- Reflexive reachability retains either exact admitted identity or a strict
proof-relevant ancestry path. -/
inductive Reaches
    (history : History (scheme := scheme) (family := family) anchor) :
    VersionNode State scheme family -> VersionNode State scheme family -> Type _ where
  | refl {node : VersionNode State scheme family} (admitted : node ∈ history.events) :
      Reaches history node node
  | strict {ancestor descendant : VersionNode State scheme family}
      (path : Ancestry history ancestor descendant) :
      Reaches history ancestor descendant

namespace Reaches

variable {history : History (scheme := scheme) (family := family) anchor}
variable {ancestor middle descendant : VersionNode State scheme family}

noncomputable def trans
    (left : Reaches history ancestor middle)
    (right : Reaches history middle descendant) :
    Reaches history ancestor descendant := by
  cases left with
  | refl => exact right
  | strict leftPath =>
      cases right with
      | refl => exact .strict leftPath
      | strict rightPath => exact .strict (leftPath.trans rightPath)

theorem eq_or_version_lt
    (reach : Reaches history ancestor descendant) :
    ancestor = descendant \/
      ancestor.preimage.semanticVersion < descendant.preimage.semanticVersion := by
  cases reach with
  | refl => exact .inl rfl
  | strict path => exact .inr path.semanticVersion_lt

/-- Reachability is antisymmetric because every non-reflexive path strictly
increases semantic version. -/
theorem antisymm
    (forward : Reaches history ancestor descendant)
    (backward : Reaches history descendant ancestor) :
    ancestor = descendant := by
  rcases forward.eq_or_version_lt with equal | less
  · exact equal
  rcases backward.eq_or_version_lt with equal | greater
  · exact equal.symm
  exact False.elim (Nat.lt_asymm less greater)

end Reaches

/-- One exact common ancestor of two admitted nodes.  The retained node exposes
its complete event, including the exact semantic object and post-state root. -/
structure CommonAncestor
    (history : History (scheme := scheme) (family := family) anchor)
    (left right : VersionNode State scheme family) where
  base : VersionNode State scheme family
  reachesLeft : Reaches history base left
  reachesRight : Reaches history base right

namespace CommonAncestor

variable {history : History (scheme := scheme) (family := family) anchor}
variable {left right : VersionNode State scheme family}

/-- Exact semantic state root at the selected common base. -/
def stateRoot (common : CommonAncestor history left right) : Digest :=
  common.base.preimage.postStateRoot

/-- Exact semantic object root of the selected common-base event. -/
def semanticObjectRoot (common : CommonAncestor history left right) : Digest :=
  common.base.preimage.semanticObjectRoot

end CommonAncestor

/-- A genuinely lowest common base is reachable from every common ancestor.
This certificate is intentionally stronger than merely choosing one maximal
candidate, and therefore need not exist for a general DAG. -/
structure LowestCommonBase
    (history : History (scheme := scheme) (family := family) anchor)
    (left right : VersionNode State scheme family) where
  selected : CommonAncestor history left right
  belowEvery : forall other : CommonAncestor history left right,
    Reaches history other.base selected.base

namespace LowestCommonBase

variable {history : History (scheme := scheme) (family := family) anchor}
variable {left right : VersionNode State scheme family}

/-- If two lowest-base certificates exist, they select the same admitted node.
The proof does not claim equality of proof objects. -/
theorem selected_unique
    (first second : LowestCommonBase history left right) :
    first.selected.base = second.selected.base :=
  Reaches.antisymm (second.belowEvery first.selected)
    (first.belowEvery second.selected)

end LowestCommonBase

/-- A maximal common base has no distinct common descendant.  Multiple
incomparable maximal bases are possible in a DAG. -/
structure MaximalCommonBase
    (history : History (scheme := scheme) (family := family) anchor)
    (left right : VersionNode State scheme family) where
  candidate : CommonAncestor history left right
  noLower : forall other : CommonAncestor history left right,
    Reaches history candidate.base other.base ->
      other.base = candidate.base

/-- Concrete ambiguity certificate: two distinct maximal common bases. -/
structure AmbiguousCommonBases
    (history : History (scheme := scheme) (family := family) anchor)
    (left right : VersionNode State scheme family) where
  first : MaximalCommonBase history left right
  second : MaximalCommonBase history left right
  distinct : first.candidate.base ≠ second.candidate.base

namespace AmbiguousCommonBases

variable {history : History (scheme := scheme) (family := family) anchor}
variable {left right : VersionNode State scheme family}

/-- Certified ambiguity rules out a globally lowest common base. -/
theorem excludes_lowest
    (ambiguous : AmbiguousCommonBases history left right) :
    LowestCommonBase history left right -> False := by
  intro lowest
  have firstEqual :
      lowest.selected.base = ambiguous.first.candidate.base :=
    ambiguous.first.noLower lowest.selected
      (lowest.belowEvery ambiguous.first.candidate)
  have secondEqual :
      lowest.selected.base = ambiguous.second.candidate.base :=
    ambiguous.second.noLower lowest.selected
      (lowest.belowEvery ambiguous.second.candidate)
  exact ambiguous.distinct (firstEqual.symm.trans secondEqual)

end AmbiguousCommonBases

/-- Honest output type for a conservative merge-base procedure.

No constructor is asserted to be universally obtainable.  A concrete bounded
search may return a certified lowest base, explicit maximal-base ambiguity, or
a proof that no common base exists in the admitted history. -/
inductive BaseSelection
    (history : History (scheme := scheme) (family := family) anchor)
    (left right : VersionNode State scheme family) : Type _ where
  | selected (certificate : LowestCommonBase history left right)
  | ambiguous (certificate : AmbiguousCommonBases history left right)
  | unavailable (noCommon : CommonAncestor history left right -> False)

end Ancestry

end Minidregg.Theory.CausalVersionAncestry
