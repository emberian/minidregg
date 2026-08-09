/-
# Theory.CausalVersionDag -- proof-native causal semantic versions

This module is the request-shape-neutral history substrate needed by
Hyperdreggmedia and other versioned semantic objects.  It deliberately does
not define a document schema, a merge algorithm, a consensus protocol, or a
finality predicate.

An entry identity is the abstract digest of one canonical `EventPreimage`.
The preimage binds the history domain and stream, schema identity/version,
semantic version, exact semantic-object/pre/post roots, canonical parent
frontier, and author/principal/request/effect identities.  Digest collision
resistance is *not* a theorem of this module: equality reflection is available
only to callers carrying the explicit `BindingPremise`.

`ValidAppend` is the causal admission boundary.  It resolves the ordered
parent frontier against already admitted entries, rejects duplicate parents,
missing parents, entry/request/effect replay, disconnected non-genesis events,
and semantic or schema-version rollback.  Parents need not still be current
tips: offline/concurrent siblings may arrive after one another.  A tips-only
rule is an explicit optional admission policy below, never generic DAG
validity.  The object-specific parent/pre-state law remains proof-relevant
`ParentCompatible` evidence supplied by a Lean semantic family, so a linear
edit and a multi-parent stitch cannot be silently identified.

Finally, `Replay` is relational execution over semantic states.  Its
checkpoint/suffix theorem is about the actual family `Step` relation, not just
list or digest equality.  Consensus and finality remain a separate layer over
the resulting causal DAG.
-/

import Theory.IndexedProgram
import Theory.TypedAuthorization

namespace Minidregg.Theory.CausalVersionDag

open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uState uEvidence

/-! ## Canonical event preimages and explicit content-address binding -/

/-- Schema identity and its monotone version are bound as one value. -/
structure SchemaRef where
  schemaId : Digest
  version : Nat
deriving DecidableEq, Repr

/-- Every public identity and root needed to interpret one semantic version.

`parentFrontier` contains history-entry identities, in strict increasing order
by `Digest.value`.  The ordering proof lives in `WellFormed` rather than in the
data so codecs need encode only first-order public data. -/
structure EventPreimage where
  historyDomain : Digest
  streamId : Digest
  schema : SchemaRef
  semanticVersion : Nat
  semanticObjectRoot : Digest
  preStateRoot : Digest
  postStateRoot : Digest
  parentFrontier : List Digest
  authorId : Digest
  principalId : Digest
  requestId : Digest
  effectId : Digest
deriving DecidableEq, Repr

namespace EventPreimage

/-- Canonical parent-frontier representation and elementary event hygiene.

Strict ordering is the canonical representation law; `Nodup` is retained as
an explicit no-duplicate fact consumed by append clients. -/
structure WellFormed (event : EventPreimage) : Prop where
  parentFrontierCanonical :
    event.parentFrontier.Pairwise
      (fun left right => left.value < right.value)
  parentFrontierUnique : event.parentFrontier.Nodup

end EventPreimage

/-- A deployment chooses one lawful canonical codec and one abstract digest
projection.  No cryptographic property is smuggled into the projection. -/
structure ContentAddressing where
  codec : LawfulCodec EventPreimage
  digestBytes : List UInt8 -> Digest

namespace ContentAddressing

def address (scheme : ContentAddressing) (event : EventPreimage) : Digest :=
  scheme.digestBytes (scheme.codec.encode event)

/-- Explicit ideal binding premise for a chosen deployment digest.

This is where a cryptographic instantiation must place its collision/binding
assumption or theorem.  The generic causal semantics do not manufacture it. -/
structure BindingPremise (scheme : ContentAddressing) : Prop where
  reflectsEquality : forall {left right : EventPreimage},
    scheme.address left = scheme.address right -> left = right

end ContentAddressing

/-- A history entry id is derived from the exact canonical preimage. -/
structure AddressedEvent (scheme : ContentAddressing) where
  preimage : EventPreimage
  entryId : Digest
  entryIdExact : entryId = scheme.address preimage
  wellFormed : preimage.WellFormed

namespace AddressedEvent

/-- Equal entry identities reflect equal preimages only under the explicit
deployment binding premise. -/
theorem preimage_eq_of_entryId_eq
    {scheme : ContentAddressing}
    (binding : scheme.BindingPremise)
    {left right : AddressedEvent scheme}
    (sameId : left.entryId = right.entryId) :
    left.preimage = right.preimage :=
  binding.reflectsEquality
    (left.entryIdExact.symm.trans (sameId.trans right.entryIdExact))

end AddressedEvent

/-! ## Object-specific semantic evidence -/

/-- The semantic family is deliberately neutral to request and object shape.

`ParentCompatible` is the typed seam at which a concrete family states how an
ordered parent frontier justifies the child's exact semantic pre-state.  For a
linear object it can require the sole parent's post-root to be the child
pre-root.  A stitch family can instead retain a proof of its multi-parent merge
law.  `Step` is execution over semantic states and its root laws bind execution
to the exact event preimage. -/
structure SemanticFamily (State : Type uState) where
  Evidence : EventPreimage -> Type uEvidence
  ParentCompatible : List EventPreimage -> EventPreimage -> Type uEvidence
  root : State -> Digest
  Step : EventPreimage -> State -> State -> Prop
  stepPreRoot : forall {event before after},
    Evidence event -> Step event before after -> root before = event.preStateRoot
  stepPostRoot : forall {event before after},
    Evidence event -> Step event before after -> root after = event.postStateRoot

/-- A content-addressed event carrying its actual Lean semantic evidence. -/
structure VerifiedEvent
    {State : Type uState}
    (scheme : ContentAddressing)
    (family : SemanticFamily.{uState, uEvidence} State) where
  addressed : AddressedEvent scheme
  semantics : family.Evidence addressed.preimage

namespace VerifiedEvent

variable {State : Type uState}
variable {scheme : ContentAddressing}
variable {family : SemanticFamily.{uState, uEvidence} State}

def preimage (event : VerifiedEvent scheme family) : EventPreimage :=
  event.addressed.preimage

def entryId (event : VerifiedEvent scheme family) : Digest :=
  event.addressed.entryId

def requestId (event : VerifiedEvent scheme family) : Digest :=
  event.preimage.requestId

def effectId (event : VerifiedEvent scheme family) : Digest :=
  event.preimage.effectId

end VerifiedEvent

/-! ## Causal append and frontier -/

/-- One DAG is anchored to a history domain and stream identity.  Schema
versions may advance inside the stream, but the domain/stream cannot drift. -/
structure Anchor where
  historyDomain : Digest
  streamId : Digest
deriving DecidableEq, Repr

namespace Anchor

def Contains (anchor : Anchor) (event : EventPreimage) : Prop :=
  event.historyDomain = anchor.historyDomain /\
  event.streamId = anchor.streamId

end Anchor

section History

variable {State : Type uState}
variable {scheme : ContentAddressing}
variable {family : SemanticFamily.{uState, uEvidence} State}

local notation "Node" => VerifiedEvent scheme family

/-- Update the mathematical frontier after admitting one node.  Parent tips
are consumed and the new entry becomes a tip. -/
def frontierStep (frontier : Finset Digest) (event : Node) : Finset Digest :=
  insert event.entryId (frontier \ event.preimage.parentFrontier.toFinset)

/-- The canonical semantic frontier of a chronological admitted-node list.
It is a finite set, hence independent of presentation order. -/
def frontier (events : List Node) : Finset Digest :=
  events.foldl frontierStep {}

@[simp] theorem frontier_nil : frontier ([] : List Node) = {} := rfl

theorem frontier_append_one (prior : List Node) (event : Node) :
    frontier (prior ++ [event]) = frontierStep (frontier prior) event := by
  simp [frontier, List.foldl_append]

/-- Complete proof-relevant admission of one new node after `prior`.

The exact ordered `resolvedParents` list prevents a host from validating one
set of parents and serializing another.  `parentCompatibility` is the concrete
semantic justification for the child's pre-state, not a generic merge claim. -/
structure ValidAppend
    (anchor : Anchor) (prior : List Node) (event : Node) : Type _ where
  anchorExact : anchor.Contains event.preimage
  genesisShape :
    (prior = [] /\ event.preimage.parentFrontier = [] /\
      event.preimage.semanticVersion = 0) \/
    (prior ≠ [] /\ event.preimage.parentFrontier ≠ [])
  resolvedParents : List Node
  resolvedParentsExact :
    resolvedParents.map VerifiedEvent.entryId = event.preimage.parentFrontier
  resolvedParentsPresent : forall parent,
    parent ∈ resolvedParents -> parent ∈ prior
  parentAnchorExact : forall parent,
    parent ∈ resolvedParents -> anchor.Contains parent.preimage
  parentSchemaExact : forall parent,
    parent ∈ resolvedParents ->
      parent.preimage.schema.schemaId = event.preimage.schema.schemaId
  schemaVersionMonotone : forall parent,
    parent ∈ resolvedParents ->
      parent.preimage.schema.version ≤ event.preimage.schema.version
  semanticVersionIncreases : forall parent,
    parent ∈ resolvedParents ->
      parent.preimage.semanticVersion < event.preimage.semanticVersion
  entryFresh : forall old, old ∈ prior -> old.entryId ≠ event.entryId
  requestFresh : forall old, old ∈ prior -> old.requestId ≠ event.requestId
  effectFresh : forall old, old ∈ prior -> old.effectId ≠ event.effectId
  parentCompatibility :
    family.ParentCompatible (resolvedParents.map VerifiedEvent.preimage)
      event.preimage

/-! ## Optional frontier admission policy -/

/-- Generic causal validity accepts any already admitted parent.  A deployment
may separately require every parent to remain a current tip, but that policy
must not redefine the DAG or rule out offline/concurrent sibling arrival. -/
inductive ParentAdmissionPolicy where
  | anyAdmitted
  | currentTips
  deriving DecidableEq, Repr

/-- Policy predicate over an already causally valid append. -/
def ParentAdmissionPolicy.Allows
    (policy : ParentAdmissionPolicy) (prior : List Node) (event : Node) : Prop :=
  match policy with
  | .anyAdmitted => True
  | .currentTips =>
      event.preimage.parentFrontier.toFinset ⊆ frontier prior

/-- Optional policy evidence wraps, rather than weakens or replaces, the exact
generic `ValidAppend` token. -/
structure PolicyAppend
    (policy : ParentAdmissionPolicy)
    (anchor : Anchor) (prior : List Node) (event : Node) : Type _ where
  causal : ValidAppend anchor prior event
  policyAllows : policy.Allows prior event

def ValidAppend.withAnyAdmittedPolicy
    {anchor : Anchor} {prior : List Node} {event : Node}
    (valid : ValidAppend anchor prior event) :
    PolicyAppend .anyAdmitted anchor prior event :=
  ⟨valid, trivial⟩

def ValidAppend.withCurrentTipsPolicy
    {anchor : Anchor} {prior : List Node} {event : Node}
    (valid : ValidAppend anchor prior event)
    (parentsCurrent : event.preimage.parentFrontier.toFinset ⊆ frontier prior) :
    PolicyAppend .currentTips anchor prior event :=
  ⟨valid, parentsCurrent⟩

namespace ValidAppend

variable {anchor : Anchor}
variable {prior : List (VerifiedEvent scheme family)}
variable {event : VerifiedEvent scheme family}

/-- Every serialized parent id resolves to an admitted parent node. -/
theorem parent_present
    (valid : ValidAppend anchor prior event)
    {parentId : Digest}
    (named : parentId ∈ event.preimage.parentFrontier) :
    exists parent : VerifiedEvent scheme family,
      parent ∈ prior /\ parent.entryId = parentId := by
  have inResolvedIds :
      parentId ∈ valid.resolvedParents.map VerifiedEvent.entryId := by
    rw [valid.resolvedParentsExact]
    exact named
  rcases List.mem_map.mp inResolvedIds with ⟨parent, present, exactId⟩
  exact ⟨parent, valid.resolvedParentsPresent parent present, exactId⟩

/-- A resolved parent cannot have the child's semantic version or a later one. -/
theorem no_semantic_rollback
    (valid : ValidAppend anchor prior event)
    {parent : VerifiedEvent scheme family}
    (present : parent ∈ valid.resolvedParents) :
    parent.preimage.semanticVersion < event.preimage.semanticVersion :=
  valid.semanticVersionIncreases parent present

/-- A resolved parent cannot come from a later version of the same schema. -/
theorem no_schema_rollback
    (valid : ValidAppend anchor prior event)
    {parent : VerifiedEvent scheme family}
    (present : parent ∈ valid.resolvedParents) :
    parent.preimage.schema.version ≤ event.preimage.schema.version :=
  valid.schemaVersionMonotone parent present

/-- Entry-address replay is rejected at the append boundary. -/
theorem no_entry_replay
    (valid : ValidAppend anchor prior event)
    {old : VerifiedEvent scheme family}
    (present : old ∈ prior) : old.entryId ≠ event.entryId :=
  valid.entryFresh old present

/-- Request replay is rejected independently of the entry address. -/
theorem no_request_replay
    (valid : ValidAppend anchor prior event)
    {old : VerifiedEvent scheme family}
    (present : old ∈ prior) : old.requestId ≠ event.requestId :=
  valid.requestFresh old present

/-- Effect replay is rejected independently of request and entry identities. -/
theorem no_effect_replay
    (valid : ValidAppend anchor prior event)
    {old : VerifiedEvent scheme family}
    (present : old ∈ prior) : old.effectId ≠ event.effectId :=
  valid.effectFresh old present

/-- Adding an unrelated concurrent node to the chronological log does not
invalidate an append whose parents were already present.  This is the generic
offline-sibling admission theorem that the former tips-only field made
impossible.  All three replay identities for the newly preceding node remain
explicit premises. -/
def survives_unrelated_append
    (valid : ValidAppend anchor prior event)
    (other : VerifiedEvent scheme family)
    (priorNonempty : prior ≠ [])
    (entryFresh : other.entryId ≠ event.entryId)
    (requestFresh : other.requestId ≠ event.requestId)
    (effectFresh : other.effectId ≠ event.effectId) :
    ValidAppend anchor (prior ++ [other]) event where
  anchorExact := valid.anchorExact
  genesisShape := by
    rcases valid.genesisShape with genesis | connected
    · exact False.elim (priorNonempty genesis.1)
    · exact Or.inr ⟨by simp [priorNonempty], connected.2⟩
  resolvedParents := valid.resolvedParents
  resolvedParentsExact := valid.resolvedParentsExact
  resolvedParentsPresent := by
    intro parent present
    exact List.mem_append_left [other]
      (valid.resolvedParentsPresent parent present)
  parentAnchorExact := valid.parentAnchorExact
  parentSchemaExact := valid.parentSchemaExact
  schemaVersionMonotone := valid.schemaVersionMonotone
  semanticVersionIncreases := valid.semanticVersionIncreases
  entryFresh := by
    intro old present
    simp only [List.mem_append, List.mem_singleton] at present
    rcases present with present | rfl
    · exact valid.entryFresh old present
    · exact entryFresh
  requestFresh := by
    intro old present
    simp only [List.mem_append, List.mem_singleton] at present
    rcases present with present | rfl
    · exact valid.requestFresh old present
    · exact requestFresh
  effectFresh := by
    intro old present
    simp only [List.mem_append, List.mem_singleton] at present
    rcases present with present | rfl
    · exact valid.effectFresh old present
    · exact effectFresh
  parentCompatibility := valid.parentCompatibility

theorem concurrent_sibling_append_inhabited
    (valid : ValidAppend anchor prior event)
    (other : VerifiedEvent scheme family)
    (priorNonempty : prior ≠ [])
    (entryFresh : other.entryId ≠ event.entryId)
    (requestFresh : other.requestId ≠ event.requestId)
    (effectFresh : other.effectId ≠ event.effectId) :
    Nonempty (ValidAppend anchor (prior ++ [other]) event) :=
  ⟨valid.survives_unrelated_append other priorNonempty entryFresh
    requestFresh effectFresh⟩

end ValidAppend

/-- A history is constructible only by empty initialization and valid append.
It is a causal DAG log, not a consensus or finality certificate. -/
inductive Builds (anchor : Anchor) : List Node -> Type _ where
  | empty : Builds anchor []
  | append {prior : List Node} {event : Node} :
      Builds anchor prior -> ValidAppend anchor prior event ->
      Builds anchor (prior ++ [event])

/-- Packaged proof-native causal history. -/
structure History (anchor : Anchor) where
  events : List Node
  builds : Builds anchor events

namespace History

def empty (anchor : Anchor) : History (scheme := scheme) (family := family) anchor :=
  ⟨[], Builds.empty⟩

def append
    {anchor : Anchor}
    (history : History (scheme := scheme) (family := family) anchor)
    (event : Node)
    (valid : ValidAppend anchor history.events event) :
    History (scheme := scheme) (family := family) anchor :=
  ⟨history.events ++ [event], Builds.append history.builds valid⟩

@[simp] theorem events_append
    {anchor : Anchor}
    (history : History (scheme := scheme) (family := family) anchor)
    (event : Node)
    (valid : ValidAppend anchor history.events event) :
    (history.append event valid).events = history.events ++ [event] :=
  rfl

@[simp] theorem frontier_append
    {anchor : Anchor}
    (history : History (scheme := scheme) (family := family) anchor)
    (event : Node)
    (valid : ValidAppend anchor history.events event) :
    frontier (history.append event valid).events =
      frontierStep (frontier history.events) event :=
  frontier_append_one history.events event

end History

/-! ## Semantic replay and checkpoint/suffix equivalence -/

/-- Relational replay of exact verified events over the family's semantic
state.  Each step is the family's actual Lean relation. -/
inductive Replay : State -> List Node -> State -> Prop where
  | nil (state : State) : Replay state [] state
  | cons {before after final : State} {event : Node} {rest : List Node} :
      family.Step event.preimage before after ->
      Replay after rest final ->
      Replay before (event :: rest) final

namespace Replay

theorem append
    {before checkpoint after : State}
    {front suffix : List Node}
    (frontReplay : Replay (family := family) before front checkpoint)
    (suffixReplay : Replay (family := family) checkpoint suffix after) :
    Replay (family := family) before (front ++ suffix) after := by
  induction frontReplay with
  | nil => exact suffixReplay
  | cons step restReplay induction =>
      exact .cons step (induction suffixReplay)

theorem split
    {before after : State}
    (front suffix : List Node)
    (whole : Replay (family := family) before (front ++ suffix) after) :
    exists checkpoint,
      Replay (family := family) before front checkpoint /\
      Replay (family := family) checkpoint suffix after := by
  induction front generalizing before with
  | nil =>
      exact ⟨before, .nil before, whole⟩
  | cons event rest induction =>
      cases whole with
      | cons step tail =>
          rcases induction tail with ⟨checkpoint, prefixReplay, suffixReplay⟩
          exact ⟨checkpoint, .cons step prefixReplay, suffixReplay⟩

/-- Replaying a whole path is equivalent to restoring the exact semantic
checkpoint after a prefix and replaying only the suffix. -/
theorem checkpoint_suffix_equivalence
    {before after : State} (front suffix : List Node) :
    Replay (family := family) before (front ++ suffix) after <->
      exists checkpoint,
        Replay (family := family) before front checkpoint /\
        Replay (family := family) checkpoint suffix after := by
  constructor
  · exact split front suffix
  · rintro ⟨checkpoint, frontReplay, suffixReplay⟩
    exact append frontReplay suffixReplay

/-- The first semantic step consumes the exact pre-state root in its event. -/
theorem cons_pre_root
    {before after : State} {event : Node} {rest : List Node}
    (replay : Replay (family := family) before (event :: rest) after) :
    family.root before = event.preimage.preStateRoot := by
  cases replay with
  | cons step _ => exact family.stepPreRoot event.semantics step

end Replay

end History

#print axioms ValidAppend.parent_present
#print axioms ValidAppend.concurrent_sibling_append_inhabited

end Minidregg.Theory.CausalVersionDag
