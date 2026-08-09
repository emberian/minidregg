/-
# Theory.StableRanges -- persistent document anchors and honest overlays

This module is deliberately independent of a particular hyperdocument schema.
Run and atom identities, principals, object identities, bodies, references, and
event references are parameters.  A future schema can therefore place these
objects in typed sparse namespaces without changing their transport semantics.

The load-bearing choices are:

* endpoints name a persistent atom identity together with its current run;
* split, join, insert, delete, and move have separate, exact transports;
* endpoint death is never inferred by a renderer: the endpoint carries a policy
  and the delete event carries the exact predecessor/successor candidates;
* every relocation or death-retarget is visible in an audit trace;
* marks and annotations are first-class data with authorship, lifecycle, and
  visibility metadata; indexed policies are references, not verified authority;
* projection is a deterministic, half-open slice of the current atom order.

There are intentionally no ID derivation, codec, hash, authorization, storage,
or cryptographic-validity claims here.  Those belong to the schema, accepted
effect, sparse-state, and history layers which instantiate this theory.
-/
import Theory.Hyperdocument

namespace Minidregg.Theory.StableRanges

set_option autoImplicit false

universe uRun uAtom uPrincipal uObject uKind uBody uRef uEvent uPolicy

/-! ## Persistent locations and endpoints -/

/-- The current run containing one persistent atom.  Moving or regrouping an
atom changes `run`; it never changes `atom`. -/
structure Location (RunId : Type uRun) (AtomId : Type uAtom) where
  run : RunId
  atom : AtomId
deriving DecidableEq

/-- An endpoint denotes a cut immediately before or immediately after an atom.
Ranges are therefore half-open cut intervals and need no ambiguous inclusive
endpoint convention. -/
inductive Side
  | before
  | after
deriving DecidableEq

/-- The policy to apply if the endpoint atom dies.

`keepTombstone` preserves provenance but makes the range unprojectable.
Preference policies may retarget only to a candidate carried by the exact
delete event.  If no requested candidate exists the endpoint becomes explicitly
unresolved; it never searches the current order for a convenient replacement. -/
inductive DeathPolicy
  | invalidate
  | keepTombstone
  | preferPrevious
  | preferNext
  | preferPreviousThenNext
  | preferNextThenPrevious
deriving DecidableEq

/-- One stable endpoint.  Its death behavior is data, not a UI convention. -/
structure Endpoint (RunId : Type uRun) (AtomId : Type uAtom) where
  location : Location RunId AtomId
  side : Side
  onDeath : DeathPolicy
deriving DecidableEq

/-- Change only the current location while retaining cut side and death policy. -/
def Endpoint.at
    {RunId : Type uRun} {AtomId : Type uAtom}
    (endpoint : Endpoint RunId AtomId) (location : Location RunId AtomId) :
    Endpoint RunId AtomId :=
  { endpoint with location := location }

/-- A stable half-open range `[start, stop)`.  Projection rejects reversed cuts
rather than silently normalizing user intent. -/
structure StableRange (RunId : Type uRun) (AtomId : Type uAtom) where
  start : Endpoint RunId AtomId
  stop : Endpoint RunId AtomId
deriving DecidableEq

/-! ## Exact edit vocabulary -/

/-- Exact neighbor candidates recorded when a persistent atom is deleted.
These are semantic event data.  A later accepted-effect layer must validate
that they really were the adjacent live locations in the pre-state. -/
structure DeathContext (RunId : Type uRun) (AtomId : Type uAtom) where
  previous : Option (Location RunId AtomId)
  next : Option (Location RunId AtomId)
deriving DecidableEq

/-- The bounded structural edits which can transport an endpoint.

`split` states exactly which atom IDs move to the right run; all remaining
atoms of `source` move to `left`.  `move` states exactly which atom IDs change
run.  An accepted hyperdocument operation will additionally prove the relevant
freshness, membership, ordering, and footprint conditions. -/
inductive Edit (RunId : Type uRun) (AtomId : Type uAtom)
  | split (source left right : RunId) (rightAtoms : Finset AtomId)
  | join (left right joined : RunId)
  | insert (run : RunId) (atoms : List AtomId)
      (anchor : Option (Endpoint RunId AtomId))
  | delete (location : Location RunId AtomId)
      (context : DeathContext RunId AtomId)
  | move (source destination : RunId) (atoms : Finset AtomId)

/-- Why a still-live atom acquired a different run location. -/
inductive Relocation
  | splitLeft
  | splitRight
  | joinedLeft
  | joinedRight
  | moved
deriving DecidableEq

/-- Which explicit candidate justified an endpoint-death retarget. -/
inductive DeathBias
  | previous
  | next
deriving DecidableEq

/-- The complete outcome of transporting one endpoint through one edit.

`relocated` is structural re-homing of the same persistent atom.  `retargeted`
is different: it records both the dead original and the replacement atom, plus
the selected bias.  Terminal outcomes expose why no live cut remains. -/
inductive EndpointTransport (RunId : Type uRun) (AtomId : Type uAtom)
  | unchanged (endpoint : Endpoint RunId AtomId)
  | relocated (original current : Endpoint RunId AtomId) (reason : Relocation)
  | retargeted (original current : Endpoint RunId AtomId) (bias : DeathBias)
  | tombstoned (original : Endpoint RunId AtomId)
  | invalidated (original : Endpoint RunId AtomId)
  | unresolved (original : Endpoint RunId AtomId) (policy : DeathPolicy)
deriving DecidableEq

/-- The currently projectable endpoint, if transport left one.  Tombstoned,
invalidated, and unresolved endpoints cannot accidentally render a span. -/
@[simp] def EndpointTransport.current?
    {RunId : Type uRun} {AtomId : Type uAtom} :
    EndpointTransport RunId AtomId -> Option (Endpoint RunId AtomId)
  | .unchanged endpoint => some endpoint
  | .relocated _ current _ => some current
  | .retargeted _ current _ => some current
  | .tombstoned _ => none
  | .invalidated _ => none
  | .unresolved _ _ => none

/-- Select only among the two candidates committed by the deletion event. -/
def chooseDeathReplacement
    {RunId : Type uRun} {AtomId : Type uAtom}
    (policy : DeathPolicy) (context : DeathContext RunId AtomId) :
    Option (Location RunId AtomId × DeathBias) :=
  match policy with
  | .invalidate => none
  | .keepTombstone => none
  | .preferPrevious => context.previous.map fun location => (location, .previous)
  | .preferNext => context.next.map fun location => (location, .next)
  | .preferPreviousThenNext =>
      match context.previous with
      | some location => some (location, .previous)
      | none => context.next.map fun location => (location, .next)
  | .preferNextThenPrevious =>
      match context.next with
      | some location => some (location, .next)
      | none => context.previous.map fun location => (location, .previous)

/-- Exact one-edit endpoint transport. -/
def transportEndpoint
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (edit : Edit RunId AtomId) (endpoint : Endpoint RunId AtomId) :
    EndpointTransport RunId AtomId :=
  match edit with
  | .split source left right rightAtoms =>
      if endpoint.location.run = source then
        if endpoint.location.atom ∈ rightAtoms then
          .relocated endpoint
            (endpoint.at ⟨right, endpoint.location.atom⟩) .splitRight
        else
          .relocated endpoint
            (endpoint.at ⟨left, endpoint.location.atom⟩) .splitLeft
      else
        .unchanged endpoint
  | .join left right joined =>
      if endpoint.location.run = left then
        .relocated endpoint
          (endpoint.at ⟨joined, endpoint.location.atom⟩) .joinedLeft
      else if endpoint.location.run = right then
        .relocated endpoint
          (endpoint.at ⟨joined, endpoint.location.atom⟩) .joinedRight
      else
        .unchanged endpoint
  | .insert _ _ _ => .unchanged endpoint
  | .delete location context =>
      if endpoint.location = location then
        match endpoint.onDeath with
        | .invalidate => .invalidated endpoint
        | .keepTombstone => .tombstoned endpoint
        | policy =>
            match chooseDeathReplacement policy context with
            | some (replacement, bias) =>
                .retargeted endpoint (endpoint.at replacement) bias
            | none => .unresolved endpoint policy
      else
        .unchanged endpoint
  | .move source destination atoms =>
      if endpoint.location.run = source ∧ endpoint.location.atom ∈ atoms then
        .relocated endpoint
          (endpoint.at ⟨destination, endpoint.location.atom⟩) .moved
      else
        .unchanged endpoint

/-! ## Auditable multi-edit transport -/

/-- A trace retains every nonterminal transport result.  In particular, a
death retarget remains visible after later split/join/move relocations. -/
structure EndpointTrace (RunId : Type uRun) (AtomId : Type uAtom) where
  initial : Endpoint RunId AtomId
  current : EndpointTransport RunId AtomId
  audit : List (EndpointTransport RunId AtomId)
deriving DecidableEq

/-- The empty trace starts at the named endpoint. -/
def EndpointTrace.init
    {RunId : Type uRun} {AtomId : Type uAtom}
    (endpoint : Endpoint RunId AtomId) : EndpointTrace RunId AtomId :=
  { initial := endpoint
    current := .unchanged endpoint
    audit := [] }

/-- Apply one edit only when the endpoint remains projectable.  Death is
terminal; subsequent edits cannot resurrect or silently rebind it. -/
def EndpointTrace.step
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (trace : EndpointTrace RunId AtomId) (edit : Edit RunId AtomId) :
    EndpointTrace RunId AtomId :=
  match trace.current.current? with
  | none => trace
  | some endpoint =>
      let result := transportEndpoint edit endpoint
      { trace with current := result, audit := trace.audit ++ [result] }

/-- Transport through edits in semantic order. -/
def EndpointTrace.run
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId] :
    EndpointTrace RunId AtomId -> List (Edit RunId AtomId) ->
      EndpointTrace RunId AtomId
  | trace, [] => trace
  | trace, edit :: rest => run (trace.step edit) rest

/-- A range trace transports both endpoints through the same edit sequence. -/
structure RangeTrace (RunId : Type uRun) (AtomId : Type uAtom) where
  original : StableRange RunId AtomId
  start : EndpointTrace RunId AtomId
  stop : EndpointTrace RunId AtomId
deriving DecidableEq

def RangeTrace.init
    {RunId : Type uRun} {AtomId : Type uAtom}
  (range : StableRange RunId AtomId) : RangeTrace RunId AtomId :=
  { original := range
    start := EndpointTrace.init range.start
    stop := EndpointTrace.init range.stop }

def RangeTrace.step
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (trace : RangeTrace RunId AtomId) (edit : Edit RunId AtomId) :
    RangeTrace RunId AtomId :=
  { trace with start := trace.start.step edit, stop := trace.stop.step edit }

def RangeTrace.run
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
  (range : StableRange RunId AtomId) (edits : List (Edit RunId AtomId)) :
    RangeTrace RunId AtomId :=
  { original := range
    start := (EndpointTrace.init range.start).run edits
    stop := (EndpointTrace.init range.stop).run edits }

/-! ## Deterministic range projection -/

/-- Position of a live location in the exact current document order. -/
def position?
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (target : Location RunId AtomId) :
    List (Location RunId AtomId) -> Option Nat
  | [] => none
  | location :: rest =>
      if location = target then some 0 else (position? target rest).map Nat.succ

/-- Convert an endpoint to its half-open cut coordinate. -/
def cut?
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (order : List (Location RunId AtomId))
    (endpoint : Endpoint RunId AtomId) : Option Nat :=
  (position? endpoint.location order).map fun position =>
    match endpoint.side with
    | .before => position
    | .after => position + 1

/-- A successful range projection retains the full transport audit and exact
cut coordinates alongside the selected atoms. -/
structure ProjectedRange (RunId : Type uRun) (AtomId : Type uAtom) where
  trace : RangeTrace RunId AtomId
  startCut : Nat
  stopCut : Nat
  atoms : List (Location RunId AtomId)
deriving DecidableEq

/-- Deterministically project a transported range against an exact current
order.  Missing/dead endpoints and reversed cuts yield `none`. -/
def projectRange
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (order : List (Location RunId AtomId))
    (trace : RangeTrace RunId AtomId) : Option (ProjectedRange RunId AtomId) :=
  match trace.start.current.current?, trace.stop.current.current? with
  | some startEndpoint, some stopEndpoint =>
      match cut? order startEndpoint, cut? order stopEndpoint with
      | some startCut, some stopCut =>
          if startCut ≤ stopCut then
            some
              { trace := trace
                startCut := startCut
                stopCut := stopCut
                atoms := (order.drop startCut).take (stopCut - startCut) }
          else
            none
      | _, _ => none
  | _, _ => none

/-! ## First-class marks and annotations -/

/-- Lifecycle is semantic data.  Projection retains active and resolved
objects, while retracted objects remain in history but are not displayed. -/
inductive Lifecycle (Principal : Type uPrincipal) (EventRef : Type uEvent)
  | active
  | resolved (actor : Principal) (event : EventRef)
  | retracted (actor : Principal) (event : EventRef)
deriving DecidableEq

def Lifecycle.displayable
    {Principal : Type uPrincipal} {EventRef : Type uEvent} :
    Lifecycle Principal EventRef -> Bool
  | .active => true
  | .resolved _ _ => true
  | .retracted _ _ => false

/-- Visibility is data.  `indexed` names an external policy; it does not assert
that the policy exists, is current, or authorized the viewer. -/
inductive Visibility (Principal : Type uPrincipal) (PolicyRef : Type uPolicy)
  | worldReadable
  | authorOnly
  | listed (principals : Finset Principal)
  | indexed (policy : PolicyRef)

/-- A deterministic visibility reading parameterized by an explicit indexed
policy decision function.  This function is a projection input, not authority
evidence. -/
def Visibility.visibleTo
    {Principal : Type uPrincipal} {PolicyRef : Type uPolicy}
    [DecidableEq Principal]
    (visibility : Visibility Principal PolicyRef)
    (author observer : Principal)
    (indexedDecision : PolicyRef -> Principal -> Bool) : Bool :=
  match visibility with
  | .worldReadable => true
  | .authorOnly => decide (observer = author)
  | .listed principals => decide (observer ∈ principals)
  | .indexed policy => indexedDecision policy observer

/-- Annotation content is either owned inline data or an indexed reference. -/
inductive AnnotationContent (Body : Type uBody) (Reference : Type uRef)
  | inline (body : Body)
  | reference (target : Reference)
deriving DecidableEq

/-- A mark is an independently identified range overlay.  Its author is part of
the object, avoiding the old range+kind identity which conflated two authors. -/
structure Mark
    (RunId : Type uRun) (AtomId : Type uAtom)
    (ObjectId : Type uObject) (Principal : Type uPrincipal)
    (Kind : Type uKind) (EventRef : Type uEvent) (PolicyRef : Type uPolicy) where
  id : ObjectId
  author : Principal
  target : StableRange RunId AtomId
  kind : Kind
  created : EventRef
  lifecycle : Lifecycle Principal EventRef
  visibility : Visibility Principal PolicyRef

/-- A sovereign annotation/comment object.  Body/reference, lifecycle, and
visibility are not encoded as an overloaded formatting mark. -/
structure Annotation
    (RunId : Type uRun) (AtomId : Type uAtom)
    (ObjectId : Type uObject) (Principal : Type uPrincipal)
    (Body : Type uBody) (Reference : Type uRef)
    (EventRef : Type uEvent) (PolicyRef : Type uPolicy) where
  id : ObjectId
  author : Principal
  target : StableRange RunId AtomId
  content : AnnotationContent Body Reference
  created : EventRef
  lifecycle : Lifecycle Principal EventRef
  visibility : Visibility Principal PolicyRef

/-- Marks and annotations occupy separate overlay collections. -/
structure Overlay
    (RunId : Type uRun) (AtomId : Type uAtom)
    (ObjectId : Type uObject) (Principal : Type uPrincipal)
    (Kind : Type uKind) (Body : Type uBody) (Reference : Type uRef)
    (EventRef : Type uEvent) (PolicyRef : Type uPolicy) where
  marks : List (Mark RunId AtomId ObjectId Principal Kind EventRef PolicyRef)
  annotations : List
    (Annotation RunId AtomId ObjectId Principal Body Reference EventRef PolicyRef)

structure ProjectedMark
    (RunId : Type uRun) (AtomId : Type uAtom)
    (ObjectId : Type uObject) (Principal : Type uPrincipal)
    (Kind : Type uKind) (EventRef : Type uEvent) (PolicyRef : Type uPolicy) where
  source : Mark RunId AtomId ObjectId Principal Kind EventRef PolicyRef
  range : ProjectedRange RunId AtomId

structure ProjectedAnnotation
    (RunId : Type uRun) (AtomId : Type uAtom)
    (ObjectId : Type uObject) (Principal : Type uPrincipal)
    (Body : Type uBody) (Reference : Type uRef)
    (EventRef : Type uEvent) (PolicyRef : Type uPolicy) where
  source : Annotation RunId AtomId ObjectId Principal Body Reference EventRef PolicyRef
  range : ProjectedRange RunId AtomId

structure OverlayProjection
    (RunId : Type uRun) (AtomId : Type uAtom)
    (ObjectId : Type uObject) (Principal : Type uPrincipal)
    (Kind : Type uKind) (Body : Type uBody) (Reference : Type uRef)
    (EventRef : Type uEvent) (PolicyRef : Type uPolicy) where
  marks : List
    (ProjectedMark RunId AtomId ObjectId Principal Kind EventRef PolicyRef)
  annotations : List
    (ProjectedAnnotation RunId AtomId ObjectId Principal Body Reference EventRef PolicyRef)

def projectMark
    {RunId : Type uRun} {AtomId : Type uAtom}
    {ObjectId : Type uObject} {Principal : Type uPrincipal}
    {Kind : Type uKind} {EventRef : Type uEvent} {PolicyRef : Type uPolicy}
    [DecidableEq RunId] [DecidableEq AtomId] [DecidableEq Principal]
    (order : List (Location RunId AtomId)) (edits : List (Edit RunId AtomId))
    (observer : Principal) (indexedDecision : PolicyRef -> Principal -> Bool)
    (mark : Mark RunId AtomId ObjectId Principal Kind EventRef PolicyRef) :
    Option (ProjectedMark RunId AtomId ObjectId Principal Kind EventRef PolicyRef) :=
  if !mark.lifecycle.displayable then none
  else if !mark.visibility.visibleTo mark.author observer indexedDecision then none
  else
    match projectRange order (RangeTrace.run mark.target edits) with
    | some range => some { source := mark, range := range }
    | none => none

def projectAnnotation
    {RunId : Type uRun} {AtomId : Type uAtom}
    {ObjectId : Type uObject} {Principal : Type uPrincipal}
    {Body : Type uBody} {Reference : Type uRef}
    {EventRef : Type uEvent} {PolicyRef : Type uPolicy}
    [DecidableEq RunId] [DecidableEq AtomId] [DecidableEq Principal]
    (order : List (Location RunId AtomId)) (edits : List (Edit RunId AtomId))
    (observer : Principal) (indexedDecision : PolicyRef -> Principal -> Bool)
    (annotation :
      Annotation RunId AtomId ObjectId Principal Body Reference EventRef PolicyRef) :
    Option
      (ProjectedAnnotation RunId AtomId ObjectId Principal Body Reference EventRef PolicyRef) :=
  if !annotation.lifecycle.displayable then none
  else if !annotation.visibility.visibleTo annotation.author observer indexedDecision then none
  else
    match projectRange order (RangeTrace.run annotation.target edits) with
    | some range => some { source := annotation, range := range }
    | none => none

/-- Deterministic projection preserves source order and keeps the two object
families separate. -/
def Overlay.project
    {RunId : Type uRun} {AtomId : Type uAtom}
    {ObjectId : Type uObject} {Principal : Type uPrincipal}
    {Kind : Type uKind} {Body : Type uBody} {Reference : Type uRef}
    {EventRef : Type uEvent} {PolicyRef : Type uPolicy}
    [DecidableEq RunId] [DecidableEq AtomId] [DecidableEq Principal]
    (overlay :
      Overlay RunId AtomId ObjectId Principal Kind Body Reference EventRef PolicyRef)
    (order : List (Location RunId AtomId)) (edits : List (Edit RunId AtomId))
    (observer : Principal) (indexedDecision : PolicyRef -> Principal -> Bool) :
    OverlayProjection RunId AtomId ObjectId Principal Kind Body Reference EventRef PolicyRef :=
  { marks := overlay.marks.filterMap
      (projectMark order edits observer indexedDecision)
    annotations := overlay.annotations.filterMap
      (projectAnnotation order edits observer indexedDecision) }

/-! ## Transport and projection laws -/

@[simp] theorem transport_insert
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (run : RunId) (atoms : List AtomId)
    (anchor : Option (Endpoint RunId AtomId)) :
    transportEndpoint (.insert run atoms anchor) endpoint = .unchanged endpoint :=
  rfl

@[simp] theorem transport_split_outside
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (source left right : RunId)
    (rightAtoms : Finset AtomId) (outside : endpoint.location.run ≠ source) :
    transportEndpoint (.split source left right rightAtoms) endpoint =
      .unchanged endpoint := by
  simp [transportEndpoint, outside]

@[simp] theorem transport_split_right
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (source left right : RunId)
    (rightAtoms : Finset AtomId) (inSource : endpoint.location.run = source)
    (inRight : endpoint.location.atom ∈ rightAtoms) :
    transportEndpoint (.split source left right rightAtoms) endpoint =
      .relocated endpoint (endpoint.at ⟨right, endpoint.location.atom⟩)
        .splitRight := by
  simp [transportEndpoint, inSource, inRight]

@[simp] theorem transport_split_left
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (source left right : RunId)
    (rightAtoms : Finset AtomId) (inSource : endpoint.location.run = source)
    (notRight : endpoint.location.atom ∉ rightAtoms) :
    transportEndpoint (.split source left right rightAtoms) endpoint =
      .relocated endpoint (endpoint.at ⟨left, endpoint.location.atom⟩)
        .splitLeft := by
  simp [transportEndpoint, inSource, notRight]

@[simp] theorem transport_join_left
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (left right joined : RunId)
    (inLeft : endpoint.location.run = left) :
    transportEndpoint (.join left right joined) endpoint =
      .relocated endpoint (endpoint.at ⟨joined, endpoint.location.atom⟩)
        .joinedLeft := by
  simp [transportEndpoint, inLeft]

@[simp] theorem transport_join_right
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (left right joined : RunId)
    (notLeft : endpoint.location.run ≠ left)
    (inRight : endpoint.location.run = right) :
    transportEndpoint (.join left right joined) endpoint =
      .relocated endpoint (endpoint.at ⟨joined, endpoint.location.atom⟩)
        .joinedRight := by
  have rightNeLeft : right ≠ left := by
    intro rightEqLeft
    exact notLeft (inRight.trans rightEqLeft)
  simp [transportEndpoint, inRight, rightNeLeft]

@[simp] theorem transport_join_outside
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (left right joined : RunId)
    (notLeft : endpoint.location.run ≠ left)
    (notRight : endpoint.location.run ≠ right) :
    transportEndpoint (.join left right joined) endpoint =
      .unchanged endpoint := by
  simp [transportEndpoint, notLeft, notRight]

@[simp] theorem transport_delete_other
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (location : Location RunId AtomId)
    (context : DeathContext RunId AtomId) (other : endpoint.location ≠ location) :
    transportEndpoint (.delete location context) endpoint = .unchanged endpoint := by
  simp [transportEndpoint, other]

@[simp] theorem transport_delete_invalidates
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (context : DeathContext RunId AtomId)
    (policy : endpoint.onDeath = .invalidate) :
    transportEndpoint (.delete endpoint.location context) endpoint =
      .invalidated endpoint := by
  simp [transportEndpoint, policy]

@[simp] theorem transport_delete_tombstones
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (context : DeathContext RunId AtomId)
    (policy : endpoint.onDeath = .keepTombstone) :
    transportEndpoint (.delete endpoint.location context) endpoint =
      .tombstoned endpoint := by
  simp [transportEndpoint, policy]

@[simp] theorem transport_delete_prefers_previous
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (previous : Location RunId AtomId)
    (next : Option (Location RunId AtomId))
    (policy : endpoint.onDeath = .preferPrevious) :
    transportEndpoint
        (.delete endpoint.location { previous := some previous, next := next }) endpoint =
      .retargeted endpoint (endpoint.at previous) .previous := by
  simp [transportEndpoint, policy, chooseDeathReplacement]

theorem transport_deleted_is_explicit
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (context : DeathContext RunId AtomId) :
    transportEndpoint (.delete endpoint.location context) endpoint ≠
      .unchanged endpoint := by
  cases endpoint with
  | mk location side policy =>
      cases policy <;> simp [transportEndpoint, chooseDeathReplacement]
      all_goals split <;> simp_all

@[simp] theorem transport_move_outside
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (source destination : RunId)
    (atoms : Finset AtomId)
    (outside : endpoint.location.run ≠ source ∨ endpoint.location.atom ∉ atoms) :
    transportEndpoint (.move source destination atoms) endpoint =
      .unchanged endpoint := by
  simp [transportEndpoint, not_and_or.mpr outside]

@[simp] theorem transport_move_inside
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (endpoint : Endpoint RunId AtomId) (source destination : RunId)
    (atoms : Finset AtomId) (inSource : endpoint.location.run = source)
    (moved : endpoint.location.atom ∈ atoms) :
    transportEndpoint (.move source destination atoms) endpoint =
      .relocated endpoint (endpoint.at ⟨destination, endpoint.location.atom⟩)
        .moved := by
  simp [transportEndpoint, inSource, moved]

/-- A relocation result exposes its exact current persistent atom identity. -/
theorem relocated_exposes_current_atom
    {RunId : Type uRun} {AtomId : Type uAtom}
    {original current : Endpoint RunId AtomId} {reason : Relocation}
    (result : EndpointTransport RunId AtomId)
    (isRelocation : result = .relocated original current reason) :
    (result.current?.map fun endpoint => endpoint.location.atom) =
      some current.location.atom := by
  subst result
  rfl

/-- A terminal death outcome is a frame for all later edits. -/
theorem EndpointTrace.step_terminal
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (trace : EndpointTrace RunId AtomId) (edit : Edit RunId AtomId)
    (terminal : trace.current.current? = none) :
    trace.step edit = trace := by
  cases current : trace.current <;> simp_all [EndpointTrace.step]

/-- An insertion records an audit step but leaves the current endpoint exact. -/
theorem EndpointTrace.step_insert_current
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (trace : EndpointTrace RunId AtomId) (run : RunId) (atoms : List AtomId)
    (anchor : Option (Endpoint RunId AtomId)) :
    (trace.step (.insert run atoms anchor)).current.current? =
      trace.current.current? := by
  cases current : trace.current <;>
    simp [EndpointTrace.step, current, transportEndpoint]

/-- Insertion cannot change either currently projectable endpoint.  It may
change the selected atoms only because the explicit current order changed. -/
theorem RangeTrace.step_insert_current
    {RunId : Type uRun} {AtomId : Type uAtom}
    [DecidableEq RunId] [DecidableEq AtomId]
    (trace : RangeTrace RunId AtomId) (run : RunId) (atoms : List AtomId)
    (anchor : Option (Endpoint RunId AtomId)) :
    (trace.step (.insert run atoms anchor)).start.current.current? =
        trace.start.current.current? /\
      (trace.step (.insert run atoms anchor)).stop.current.current? =
        trace.stop.current.current? := by
  constructor
  · exact EndpointTrace.step_insert_current trace.start run atoms anchor
  · exact EndpointTrace.step_insert_current trace.stop run atoms anchor

@[simp] theorem projectMark_retracted
    {RunId : Type uRun} {AtomId : Type uAtom}
    {ObjectId : Type uObject} {Principal : Type uPrincipal}
    {Kind : Type uKind} {EventRef : Type uEvent} {PolicyRef : Type uPolicy}
    [DecidableEq RunId] [DecidableEq AtomId] [DecidableEq Principal]
    (order : List (Location RunId AtomId)) (edits : List (Edit RunId AtomId))
    (observer actor : Principal) (event : EventRef)
    (indexedDecision : PolicyRef -> Principal -> Bool)
    (mark : Mark RunId AtomId ObjectId Principal Kind EventRef PolicyRef) :
    projectMark order edits observer indexedDecision
      { mark with lifecycle := .retracted actor event } = none := by
  simp [projectMark, Lifecycle.displayable]

@[simp] theorem projectAnnotation_retracted
    {RunId : Type uRun} {AtomId : Type uAtom}
    {ObjectId : Type uObject} {Principal : Type uPrincipal}
    {Body : Type uBody} {Reference : Type uRef}
    {EventRef : Type uEvent} {PolicyRef : Type uPolicy}
    [DecidableEq RunId] [DecidableEq AtomId] [DecidableEq Principal]
    (order : List (Location RunId AtomId)) (edits : List (Edit RunId AtomId))
    (observer actor : Principal) (event : EventRef)
    (indexedDecision : PolicyRef -> Principal -> Bool)
    (annotation :
      Annotation RunId AtomId ObjectId Principal Body Reference EventRef PolicyRef) :
    projectAnnotation order edits observer indexedDecision
      { annotation with lifecycle := .retracted actor event } = none := by
  simp [projectAnnotation, Lifecycle.displayable]

/-- Annotation changes cannot perturb mark projection: they occupy a separate
component and `Overlay.project.marks` depends only on `overlay.marks`. -/
theorem Overlay.project_marks_frame_annotations
    {RunId : Type uRun} {AtomId : Type uAtom}
    {ObjectId : Type uObject} {Principal : Type uPrincipal}
    {Kind : Type uKind} {Body : Type uBody} {Reference : Type uRef}
    {EventRef : Type uEvent} {PolicyRef : Type uPolicy}
    [DecidableEq RunId] [DecidableEq AtomId] [DecidableEq Principal]
    (overlay :
      Overlay RunId AtomId ObjectId Principal Kind Body Reference EventRef PolicyRef)
    (annotations : List
      (Annotation RunId AtomId ObjectId Principal Body Reference EventRef PolicyRef))
    (order : List (Location RunId AtomId)) (edits : List (Edit RunId AtomId))
    (observer : Principal) (indexedDecision : PolicyRef -> Principal -> Bool) :
    ({ overlay with annotations := annotations }.project
      order edits observer indexedDecision).marks =
      (overlay.project order edits observer indexedDecision).marks :=
  rfl

/-- Mark changes cannot perturb annotation projection. -/
theorem Overlay.project_annotations_frame_marks
    {RunId : Type uRun} {AtomId : Type uAtom}
    {ObjectId : Type uObject} {Principal : Type uPrincipal}
    {Kind : Type uKind} {Body : Type uBody} {Reference : Type uRef}
    {EventRef : Type uEvent} {PolicyRef : Type uPolicy}
    [DecidableEq RunId] [DecidableEq AtomId] [DecidableEq Principal]
    (overlay :
      Overlay RunId AtomId ObjectId Principal Kind Body Reference EventRef PolicyRef)
    (marks : List
      (Mark RunId AtomId ObjectId Principal Kind EventRef PolicyRef))
    (order : List (Location RunId AtomId)) (edits : List (Edit RunId AtomId))
    (observer : Principal) (indexedDecision : PolicyRef -> Principal -> Bool) :
    ({ overlay with marks := marks }.project
      order edits observer indexedDecision).annotations =
      (overlay.project order edits observer indexedDecision).annotations :=
  rfl

/-! ## Exact adapter from canonical Hyperdocument storage

`Theory.Hyperdocument` stores compact wire points as `(run, neighbor?, bias)`.
That representation deliberately omits endpoint-death policy, which belongs to
an operation context, and permits an empty-run anchor with no neighboring atom.
The adapter below supplies the missing policy explicitly and represents empty
anchors separately.  Consequently `decodePoint?` and `decodeRange?` cannot
invent an atom identity for an empty run.
-/

namespace HyperdocumentAdapter

abbrev StoredPoint := Hyperdocument.StablePoint
abbrev StoredRange := Hyperdocument.StableRange
abbrev SemanticEndpoint := Endpoint Hyperdocument.RunId Hyperdocument.AtomId
abbrev SemanticRange := StableRange Hyperdocument.RunId Hyperdocument.AtomId

/-- Exact conversion of the shared before/after vocabulary. -/
def sideOfBias : Hyperdocument.AnchorBias -> Side
  | .before => .before
  | .after => .after

@[simp] theorem sideOfBias_injective : Function.Injective sideOfBias := by
  intro left right equal
  cases left <;> cases right <;> simp [sideOfBias] at equal ⊢

/-- A stored point either realizes an atom-backed semantic endpoint or remains
an explicit empty-run cut.  The latter is not assigned a synthetic atom. -/
inductive PointRealization
  | anchored (endpoint : SemanticEndpoint)
  | emptyRun (run : Hyperdocument.RunId) (side : Side)
deriving DecidableEq

/-- Realize one stored point under an explicit endpoint-death policy. -/
def realizePoint (death : DeathPolicy) (point : StoredPoint) : PointRealization :=
  match point.neighbor with
  | some atom =>
      .anchored
        { location := ⟨point.run, atom⟩
          side := sideOfBias point.bias
          onDeath := death }
  | none => .emptyRun point.run (sideOfBias point.bias)

/-- The exact graph relation for stored-point realization. -/
def PointRealizes
    (death : DeathPolicy) (stored : StoredPoint) (meaning : PointRealization) : Prop :=
  meaning = realizePoint death stored

theorem point_realization_unique
    (death : DeathPolicy) (stored : StoredPoint)
    {left right : PointRealization}
    (leftRealizes : PointRealizes death stored left)
    (rightRealizes : PointRealizes death stored right) :
    left = right := by
  exact leftRealizes.trans rightRealizes.symm

/-- Decode only the atom-backed portion of the realization. -/
def PointRealization.endpoint? : PointRealization -> Option SemanticEndpoint
  | .anchored endpoint => some endpoint
  | .emptyRun _ _ => none

def decodePoint? (death : DeathPolicy) (point : StoredPoint) :
    Option SemanticEndpoint :=
  (realizePoint death point).endpoint?

@[simp] theorem decodePoint_some
    (death : DeathPolicy) (run : Hyperdocument.RunId)
    (atom : Hyperdocument.AtomId) (bias : Hyperdocument.AnchorBias) :
    decodePoint? death { run := run, neighbor := some atom, bias := bias } =
      some
        { location := ⟨run, atom⟩
          side := sideOfBias bias
          onDeath := death } :=
  rfl

@[simp] theorem decodePoint_empty
    (death : DeathPolicy) (run : Hyperdocument.RunId)
    (bias : Hyperdocument.AnchorBias) :
    decodePoint? death { run := run, neighbor := none, bias := bias } = none :=
  rfl

theorem decodePoint_eq_none_iff
    (death : DeathPolicy) (point : StoredPoint) :
    decodePoint? death point = none <-> point.neighbor = none := by
  cases point with
  | mk run neighbor bias =>
      cases neighbor <;> simp [decodePoint?, realizePoint, PointRealization.endpoint?]

/-- Start and finish endpoint-death policies remain distinct inputs. -/
structure RangeDeathPolicies where
  start : DeathPolicy
  finish : DeathPolicy
deriving DecidableEq

/-- Total stored-range realization, including empty anchors. -/
structure RangeRealization where
  stored : StoredRange
  start : PointRealization
  finish : PointRealization
deriving DecidableEq

def realizeRange (policies : RangeDeathPolicies) (stored : StoredRange) :
    RangeRealization :=
  { stored := stored
    start := realizePoint policies.start stored.start
    finish := realizePoint policies.finish stored.finish }

/-- Decode to the atom-backed semantic range only when both stored endpoints
name atoms.  Empty start or finish anchors remain visible in `realizeRange` and
produce `none` here. -/
def RangeRealization.range? (realization : RangeRealization) :
    Option SemanticRange :=
  match realization.start.endpoint?, realization.finish.endpoint? with
  | some start, some stop => some { start := start, stop := stop }
  | _, _ => none

def decodeRange? (policies : RangeDeathPolicies) (stored : StoredRange) :
    Option SemanticRange :=
  (realizeRange policies stored).range?

theorem range_realization_unique
    (policies : RangeDeathPolicies) (stored : StoredRange)
    {left right : RangeRealization}
    (leftExact : left = realizeRange policies stored)
    (rightExact : right = realizeRange policies stored) :
    left = right := by
  exact leftExact.trans rightExact.symm

@[simp] theorem decodeRange_empty_start
    (policies : RangeDeathPolicies) (startRun : Hyperdocument.RunId)
    (startBias : Hyperdocument.AnchorBias) (finish : StoredPoint) :
    decodeRange? policies
      { start := { run := startRun, neighbor := none, bias := startBias }
        finish := finish } = none :=
  rfl

@[simp] theorem decodeRange_empty_finish
    (policies : RangeDeathPolicies) (start : StoredPoint)
    (finishRun : Hyperdocument.RunId) (finishBias : Hyperdocument.AnchorBias) :
    decodeRange? policies
      { start := start
        finish := { run := finishRun, neighbor := none, bias := finishBias } } = none := by
  cases start with
  | mk startRun neighbor startBias =>
      cases neighbor <;>
        simp [decodeRange?, realizeRange, RangeRealization.range?, realizePoint,
          PointRealization.endpoint?]

/-! ### Stored mark and annotation records -/

/-- Preserve both the mark-kind digest and its canonical payload as the
semantic mark kind. -/
structure MarkPayload where
  kind : TypedAuthorization.Digest
  payload : List UInt8
deriving DecidableEq

abbrev DecodedMark :=
  Mark Hyperdocument.RunId Hyperdocument.AtomId Hyperdocument.MarkId
    Hyperdocument.PrincipalRef MarkPayload Hyperdocument.VersionEventId
    TypedAuthorization.Digest

abbrev DecodedAnnotation :=
  Annotation Hyperdocument.RunId Hyperdocument.AtomId Hyperdocument.AnnotationId
    Hyperdocument.PrincipalRef Empty Hyperdocument.DocumentId
    Hyperdocument.VersionEventId TypedAuthorization.Digest

def markLifecycle (record : Hyperdocument.MarkRecord) :
    Lifecycle Hyperdocument.PrincipalRef Hyperdocument.VersionEventId :=
  match record.tombstonedAt with
  | none => .active
  | some event => .retracted record.author event

def annotationLifecycle (record : Hyperdocument.AnnotationRecord) :
    Lifecycle Hyperdocument.PrincipalRef Hyperdocument.VersionEventId :=
  match record.tombstonedAt with
  | none => .active
  | some event => .retracted record.author event

/-- Decode a stored mark only after supplying the operational death policies
and visibility metadata absent from the P0 record.  Empty-anchor ranges remain
non-decoded rather than receiving a synthetic target. -/
def decodeMarkRecord?
    (id : Hyperdocument.MarkId) (policies : RangeDeathPolicies)
    (visibility : Visibility Hyperdocument.PrincipalRef TypedAuthorization.Digest)
    (record : Hyperdocument.MarkRecord) : Option DecodedMark :=
  match decodeRange? policies record.range with
  | none => none
  | some target =>
      some
        { id := id
          author := record.author
          target := target
          kind := { kind := record.kind, payload := record.payload }
          created := record.event
          lifecycle := markLifecycle record
          visibility := visibility }

/-- Decode a range-targeted stored annotation.  A `none` stored range denotes a
document-wide annotation and is intentionally outside this range-only semantic
object; it returns `none` instead of manufacturing a document span. -/
def decodeAnnotationRecord?
    (id : Hyperdocument.AnnotationId) (policies : RangeDeathPolicies)
    (visibility : Visibility Hyperdocument.PrincipalRef TypedAuthorization.Digest)
    (record : Hyperdocument.AnnotationRecord) : Option DecodedAnnotation :=
  match record.range with
  | none => none
  | some storedRange =>
      match decodeRange? policies storedRange with
      | none => none
      | some target =>
          some
            { id := id
              author := record.author
              target := target
              content := .reference record.body
              created := record.event
              lifecycle := annotationLifecycle record
              visibility := visibility }

@[simp] theorem decodeAnnotation_documentWide
    (id : Hyperdocument.AnnotationId) (policies : RangeDeathPolicies)
    (visibility : Visibility Hyperdocument.PrincipalRef TypedAuthorization.Digest)
    (record : Hyperdocument.AnnotationRecord) (documentWide : record.range = none) :
    decodeAnnotationRecord? id policies visibility record = none := by
  simp [decodeAnnotationRecord?, documentWide]

end HyperdocumentAdapter

end Minidregg.Theory.StableRanges
