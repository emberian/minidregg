/-
# Assurance.ReactiveLifecycleHistory -- proof-native reactive lifecycles

Promises are not an unauthenticated scheduler state machine.  A promise fixes
the complete request, canonical pre-cell, effect declaration, patch footprints,
deadline, continuation, cancellation request, and replay nullifier before any
late value exists.  The late value is only an inhabitant of the first-order
code selected by that promise.

Notification and expiration consume an existing
`SemanticHistoryFamily.VerifiedEntry`.  There is deliberately no
`ObservedReceipt` constructor and no root-only observation shim: the exact
history context, bounded claim, semantic evidence, manifest closure, dialect
evidence, and honest-code membership remain recoverable from the entry.

Reaction checks the encoded late value against the same authenticated claim.
Finalization can carry only an existing `AcceptedCellEffect` at the promise's
exact dependent indices, and therefore projects directly to a generic typed
hyperedge incidence and the common accepted-effect history claim.

This module is logical semantics only.  Scheduling, durable compare-and-swap,
receipt persistence, and nullifier insertion remain an explicit external
`PhysicalBoundary`; no Boolean named `atomic` is treated as evidence of them.
-/

import Assurance.AcceptedCellEffectHistory
import Kernel.TypedCellHyperedge

namespace Minidregg.Assurance.ReactiveLifecycleHistory

open Minidregg.Assurance.AcceptedCellEffectHistory
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y z q r h c
  uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome
  uClauseEvidence uBoundary

noncomputable section

/-! ## Eager promise shape and genuinely weak late advice -/

/--
The entire semantic shape fixed when a promise is opened.

`interpretAdvice` is Lean-authored meaning for the one eagerly selected
first-order code.  Its universal laws make the patch footprint and nullifier
independent of the late value.  The request index itself fixes authority:
finalization must retain `Authorized portal authState spec.request` inside the
accepted effect and cannot replace any request field.
-/
structure PromiseSpec
    (U : FirstOrderUniverse.{q, r})
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier)
    (Height Condition Continuation : Type h) where
  promiseId : Digest
  kind : ResourceKind
  request : Request kind
  pre : CellState.Materialized M
  declaration : family.Declaration
  adviceCode : U.Code
  interpretAdvice : U.El adviceCode -> family.Outcome declaration
  condition : Condition
  deadline : Height
  continuation : Continuation
  nullifier : Nullifier
  cancelKind : ResourceKind
  cancelRequest : Request cancelKind
  fieldFootprint : Finset S.Field
  resourceFootprint : Finset S.Resource
  requestPreRootExact : request.preStateRoot = pre.root
  requestEffectExact : request.effectsDigest = family.effectDigest declaration
  fieldFootprintExact : forall advice,
    (family.patch declaration (interpretAdvice advice)).fieldFootprint =
      fieldFootprint
  resourceFootprintExact : forall advice,
    (family.patch declaration (interpretAdvice advice)).resourceFootprint =
      resourceFootprint
  nullifierExact : forall advice,
    family.nullifier declaration (interpretAdvice advice) = some nullifier

namespace PromiseSpec

variable
    {U : FirstOrderUniverse.{q, r}}
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {Height Condition Continuation : Type h}

/-- The late carrier was selected eagerly by `adviceCode`. -/
abbrev Advice
    (spec : PromiseSpec U family Height Condition Continuation) : Type r :=
  U.El spec.adviceCode

/-- Canonical bytes for late advice; the codec is fixed by the promise. -/
def encodeAdvice
    (spec : PromiseSpec U family Height Condition Continuation)
    (advice : spec.Advice) : List UInt8 :=
  (U.codec spec.adviceCode).encode advice

/-- Late advice cannot swap codecs or logical carriers. -/
@[simp] theorem decode_encode_advice
    (spec : PromiseSpec U family Height Condition Continuation)
    (advice : spec.Advice) :
    (U.codec spec.adviceCode).decode (spec.encodeAdvice advice) = some advice :=
  (U.codec spec.adviceCode).decode_encode advice

end PromiseSpec

/-! ## Lean-owned interpretation of authenticated history events -/

/--
The lifecycle interpretation of history headers and claims.

These relations are trusted Lean semantics, not host verdict callbacks.
`Matches` states that a committed entry satisfies the promise condition;
`AdviceAllowed` binds the exact canonical advice bytes to that same entry;
`Breaks` recognizes an authenticated cancellation under the exact eager
cancellation request.  `observedHeight` is a canonical header projection, so
expiry never trusts a caller-supplied clock sample.
-/
structure HistoryRules
    (n : Nat) (F : Type*) [Field F] [DecidableEq F]
    (Height Condition BreakReason : Type h) where
  observedHeight : HistoryAdmissionContext -> Height
  Matches : Condition -> HistoryAdmissionContext ->
    BoundSemanticReceiptClaim n F -> Prop
  AdviceAllowed : Condition -> HistoryAdmissionContext ->
    BoundSemanticReceiptClaim n F -> List UInt8 -> Prop
  Breaks : {kind : ResourceKind} -> Request kind -> BreakReason ->
    HistoryAdmissionContext -> BoundSemanticReceiptClaim n F -> Prop

/-! ## Authenticated Promise -> Notify -> React -/

section Lifecycle

variable
    {U : FirstOrderUniverse.{q, r}}
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {Height Condition Continuation BreakReason : Type h}
    [LinearOrder Height]
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {entryFamily : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext -> BindingIx -> F}
    {C : Submodule F (BoundReceiptIx n -> F)}

/-- Open logical promise token.  All load-bearing data lives in its exact
`spec` index, so the token has no late shape fields. -/
structure Promise
    (spec : PromiseSpec U family Height Condition Continuation) where
  private mk ::
  opened : Unit

/-- Open the unique logical promise shape.  This schedules no physical work. -/
def Promise.open
    (spec : PromiseSpec U family Height Condition Continuation) : Promise spec :=
  ⟨()⟩

/--
An authenticated notification.  The exact verified history entry is retained.
Besides satisfying the declared condition before the deadline, its canonical
post-root must be the promise's exact pre-cell root.  This closes the usual
check-at-one-state/use-at-another-state semantic gap; physical CAS must still
recheck this root durably.
-/
structure Notification
    (rules : HistoryRules n F Height Condition BreakReason)
    (spec : PromiseSpec U family Height Condition Continuation) where
  private mk ::
  entry : Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := entryFamily)
    (headerCells := headerCells) (C := C)
  committed : entry.context.outcome = .committed
  withinDeadline : rules.observedHeight entry.context <= spec.deadline
  stateReady : entry.context.postStateRoot = spec.pre.root
  conditionHolds : rules.Matches spec.condition entry.context entry.claim

/-- Construct notification only from the complete verified history entry. -/
def notify
    (rules : HistoryRules n F Height Condition BreakReason)
    {spec : PromiseSpec U family Height Condition Continuation}
    (_promise : Promise spec)
    (entry : Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := entryFamily)
      (headerCells := headerCells) (C := C))
    (committed : entry.context.outcome = .committed)
    (withinDeadline : rules.observedHeight entry.context <= spec.deadline)
    (stateReady : entry.context.postStateRoot = spec.pre.root)
    (conditionHolds : rules.Matches spec.condition entry.context entry.claim) :
    Notification (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec :=
  ⟨entry, committed, withinDeadline, stateReady, conditionHolds⟩

/-- A reaction contains exactly one late value under the eager advice code.
The proof binds its canonical bytes to the same authenticated entry which
woke the promise. -/
structure Reaction
    (rules : HistoryRules n F Height Condition BreakReason)
    (spec : PromiseSpec U family Height Condition Continuation) where
  private mk ::
  notification : Notification (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
    (headerCells := headerCells) (C := C) rules spec
  advice : spec.Advice
  adviceAllowed : rules.AdviceAllowed spec.condition
    notification.entry.context notification.entry.claim
    (spec.encodeAdvice advice)

/-- React to one authenticated notification with shape-free late advice. -/
def react
    (rules : HistoryRules n F Height Condition BreakReason)
    {spec : PromiseSpec U family Height Condition Continuation}
    (notification : Notification (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec)
    (advice : spec.Advice)
    (allowed : rules.AdviceAllowed spec.condition
      notification.entry.context notification.entry.claim
      (spec.encodeAdvice advice)) :
    Reaction (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec :=
  ⟨notification, advice, allowed⟩

/-- Notification exposes the actual accumulated claim, never a caller-authored
summary of it. -/
def authenticatedNotificationClaim
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (notification : Notification (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec) :
    BoundSemanticReceiptClaim n F :=
  notification.entry.claim

/-- The observation point and finalization pre-cell have the same canonical
state root. -/
theorem notificationObservedStateExact
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (notification : Notification (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec) :
    notification.entry.context.postStateRoot = spec.request.preStateRoot :=
  notification.stateReady.trans spec.requestPreRootExact.symm

/-- One authenticated entry cannot simultaneously wake this promise on time
and witness that its deadline has already passed. -/
theorem notificationNotAfterDeadline
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (notification : Notification (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec) :
    ¬ (spec.deadline < rules.observedHeight notification.entry.context) :=
  not_lt_of_ge notification.withinDeadline


/-! ## Finalize as an accepted cell effect and typed hyperedge incidence -/

/--
Successful logical finalization.  There is no constructor taking roots,
footprints, an authorization bit, or a native verdict: it consumes the common
positive semantic token at the exact indices frozen by the promise and late
advice.
-/
structure Finalized
    {portal : Portal} {authState : AuthState}
    (rules : HistoryRules n F Height Condition BreakReason)
    (spec : PromiseSpec U family Height Condition Continuation) where
  private mk ::
  reaction : Reaction (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
    (headerCells := headerCells) (C := C) rules spec
  accepted : AcceptedCellEffect (portal := portal) (authState := authState)
    family spec.request spec.pre spec.declaration
      (spec.interpretAdvice reaction.advice)

/-- Finalize only with an already accepted semantic cell effect.  Durable
installation remains outside this function. -/
def finalize
    {portal : Portal} {authState : AuthState}
    (rules : HistoryRules n F Height Condition BreakReason)
    {spec : PromiseSpec U family Height Condition Continuation}
    (reaction : Reaction (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family spec.request spec.pre spec.declaration
        (spec.interpretAdvice reaction.advice)) :
    Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec :=
  ⟨reaction, accepted⟩

/-- Exact request-indexed authorization remains present. -/
def finalizedAuthorization
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) :
    Authorized portal authState spec.request :=
  finalized.accepted.authorization

/-- The final effect has the eager field footprint for every possible advice. -/
@[simp] theorem finalizedFieldFootprintExact
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) :
    finalized.accepted.prepared.delta.fieldFootprint = spec.fieldFootprint := by
  simpa only [AcceptedCellEffect.prepared_fieldFootprint] using
    spec.fieldFootprintExact finalized.reaction.advice

/-- The final effect has the eager resource footprint for every possible
advice. -/
@[simp] theorem finalizedResourceFootprintExact
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) :
    finalized.accepted.prepared.delta.resourceFootprint =
      spec.resourceFootprint := by
  simpa only [AcceptedCellEffect.prepared_resourceFootprint] using
    spec.resourceFootprintExact finalized.reaction.advice

/-- The final effect retains the eager replay nullifier. -/
@[simp] theorem finalizedNullifierExact
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) :
    finalized.accepted.prepared.nullifier = some spec.nullifier := by
  simpa only [AcceptedCellEffect.prepared_nullifier] using
    spec.nullifierExact finalized.reaction.advice

/-- The final effect starts at the state root authenticated by notification. -/
theorem finalizedObservedPreRootExact
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) :
    finalized.reaction.notification.entry.context.postStateRoot =
      finalized.accepted.prepared.preRoot := by
  rw [finalized.reaction.notification.stateReady]
  exact spec.requestPreRootExact.symm.trans
    finalized.accepted.prepared_preRoot.symm

/-- Finalization is already a generic typed-hyperedge incidence.  No legacy
reactive turn wrapper or parallel store is synthesized. -/
def finalizedToLeg
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) :
    Leg.{u, v, w, x, y, z} portal authState spec.pre where
  Nullifier := Nullifier
  family := family
  kind := spec.kind
  request := spec.request
  declaration := spec.declaration
  outcome := spec.interpretAdvice finalized.reaction.advice
  accepted := finalized.accepted

/-- Receipt events are projections after acceptance, never notification input. -/
def finalizedToReceiptEvent
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) :
    Minidregg.Theory.ReceiptEvent family :=
  finalized.accepted.toReceiptEvent

/-- Direct projection to the same bounded semantic-history claim used by all
accepted cell effects. -/
def finalizedHistoryClaim
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (projection : HistoryProjection family n F)
    (finalHeaderCells : HistoryAdmissionContext -> BindingIx -> F)
    (context : HistoryAdmissionContext)
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) :
    BoundSemanticReceiptClaim n F :=
  projection.historyClaim finalHeaderCells context finalized.accepted

/--
Package finalization as the exact accepted-effect semantic evidence consumed by
the generic history.  All public header equations are explicit arguments; no
header field is copied from a host-authored receipt object.
-/
def finalizedHistoryEvidence
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (projection : HistoryProjection family n F)
    (headerProjection :
      AcceptedCellEffectHistory.HistoryProjection.HeaderProjection
        (family := family))
    (finalHeaderCells : HistoryAdmissionContext -> BindingIx -> F)
    (context : HistoryAdmissionContext)
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec)
    (semanticObjectRootExact : context.semanticObjectRoot =
      headerProjection.semanticObjectRoot spec.request spec.pre
        spec.declaration
        (spec.interpretAdvice finalized.reaction.advice))
    (semanticRelationExact :
      context.semanticRelationId = spec.request.semantics)
    (outcomeExact : context.outcome = .committed)
    (preStateExact : context.preStateRoot = spec.pre.root)
    (postStateExact :
      context.postStateRoot = finalized.accepted.prepared.postRoot)
    (effectRootExact :
      context.effectRoot = family.effectDigest spec.declaration)
    (authorizationRootExact : context.authorizationRoot =
      headerProjection.authorizationRoot spec.request)
    (disclosureRootExact : context.disclosureRoot =
      headerProjection.disclosureRoot spec.declaration
        (spec.interpretAdvice finalized.reaction.advice)
        finalized.accepted.disclosure) :
    AcceptedCellEffectHistory.HistoryProjection.Evidence
      (portal := portal) (authState := authState)
      projection headerProjection finalHeaderCells context
      (projection.historyClaim finalHeaderCells context finalized.accepted) where
  kind := spec.kind
  request := spec.request
  pre := spec.pre
  declaration := spec.declaration
  outcome := spec.interpretAdvice finalized.reaction.advice
  accepted := finalized.accepted
  claimExact := rfl
  semanticObjectRootExact := semanticObjectRootExact
  semanticRelationExact := semanticRelationExact
  outcomeExact := outcomeExact
  preStateExact := preStateExact
  postStateExact := postStateExact
  effectRootExact := effectRootExact
  authorizationRootExact := authorizationRootExact
  disclosureRootExact := disclosureRootExact

/-! ## Authenticated terminal alternatives -/

/-- Expiration is witnessed by an authenticated committed history point whose
canonically projected height is strictly after the eager deadline. -/
structure Expired
    (rules : HistoryRules n F Height Condition BreakReason)
    (spec : PromiseSpec U family Height Condition Continuation) where
  private mk ::
  entry : Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := entryFamily)
    (headerCells := headerCells) (C := C)
  committed : entry.context.outcome = .committed
  afterDeadline : spec.deadline < rules.observedHeight entry.context

/-- Expire from history, never from a caller clock sample. -/
def expire
    (rules : HistoryRules n F Height Condition BreakReason)
    {spec : PromiseSpec U family Height Condition Continuation}
    (_promise : Promise spec)
    (entry : Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := entryFamily)
      (headerCells := headerCells) (C := C))
    (committed : entry.context.outcome = .committed)
    (afterDeadline : spec.deadline < rules.observedHeight entry.context) :
    Expired (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec :=
  ⟨entry, committed, afterDeadline⟩

/-- A break is likewise an authenticated history event recognized under the
exact eager cancellation request. -/
structure Broken
    (rules : HistoryRules n F Height Condition BreakReason)
    (spec : PromiseSpec U family Height Condition Continuation) where
  private mk ::
  reason : BreakReason
  entry : Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := entryFamily)
    (headerCells := headerCells) (C := C)
  committed : entry.context.outcome = .committed
  authorizedBreak : rules.Breaks spec.cancelRequest reason
    entry.context entry.claim

/-- Break from a verified cancellation event. -/
def breakPromise
    (rules : HistoryRules n F Height Condition BreakReason)
    {spec : PromiseSpec U family Height Condition Continuation}
    (_promise : Promise spec)
    (reason : BreakReason)
    (entry : Minidregg.Assurance.SemanticHistoryFamily.VerifiedEntry
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := entryFamily)
      (headerCells := headerCells) (C := C))
    (committed : entry.context.outcome = .committed)
    (authorizedBreak : rules.Breaks spec.cancelRequest reason
      entry.context entry.claim) :
    Broken (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec :=
  ⟨reason, entry, committed, authorizedBreak⟩

/-! ## Explicit physical boundary -/

/--
External obligations deliberately absent from logical finalization.

An implementation chooses scheduler tickets and durable receipts, but must
provide relations indexed by the exact promise/finalization.  This interface
does not construct either relation, does not call I/O, and does not claim that
a receipt Boolean proves atomicity.  Its `Persisted` relation is the explicit
system assumption at which durable CAS, receipt append, and nullifier insertion
must be implemented and audited.
-/
structure PhysicalBoundary
    {portal : Portal} {authState : AuthState}
    (rules : HistoryRules n F Height Condition BreakReason)
    (spec : PromiseSpec U family Height Condition Continuation) where
  SchedulerTicket : Type uBoundary
  DurableReceipt : Type uBoundary
  Scheduled : Promise spec -> SchedulerTicket -> Prop
  Persisted : Finalized (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
    (headerCells := headerCells) (C := C)
    (portal := portal) (authState := authState) rules spec ->
    DurableReceipt -> Prop

/-- Proof-relevant external discharge for one exact finalized value. -/
structure PhysicalBoundary.CommitEvidence
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (boundary : PhysicalBoundary (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec)
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) where
  receipt : boundary.DurableReceipt
  persisted : boundary.Persisted finalized receipt

/-- Release the canonical post only after the external physical boundary has
been discharged for this exact finalization. -/
def Finalized.releaseAfterPhysicalCommit
    {portal : Portal} {authState : AuthState}
    {rules : HistoryRules n F Height Condition BreakReason}
    {spec : PromiseSpec U family Height Condition Continuation}
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec)
    (boundary : PhysicalBoundary (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec)
    (_physical : boundary.CommitEvidence finalized) :
    CellState.Materialized M :=
  finalized.accepted.prepared.post

end Lifecycle

#print axioms PromiseSpec.decode_encode_advice
#print axioms notificationObservedStateExact
#print axioms notificationNotAfterDeadline
#print axioms finalizedFieldFootprintExact
#print axioms finalizedResourceFootprintExact
#print axioms finalizedNullifierExact
#print axioms finalizedObservedPreRootExact
#print axioms finalizedHistoryEvidence

end


end Minidregg.Assurance.ReactiveLifecycleHistory
