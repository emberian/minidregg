/-
# Compiler.DialectClauseDispatch -- manifest-closed semantic clause dispatch

`SemanticManifest.WellFormed` closes the first-order carrier, codec, and named
bridge references of a dialect clause, but deliberately does not pretend that
the clause's controller digest denotes executable native semantics.  This
module supplies the missing Lean-owned join: a separate controller registry is
closed against the exact manifest declarations, and resolution packages every
dependency before any opaque computation is invoked.

The opaque boundary receives only the query selected by the resolved Lean
controller.  It cannot provide a clause identifier or continuation.  Transport
failure is an explicit `blocked` result and is never replaced by a fabricated
reply.  A successful response is still only data: the clause-specific Lean
`check` function alone produces its outcome.

This is intentionally distinct from `NativeKernelPlan`.  That module checks
generated work plans and descriptor buffers; this module binds a semantic
dialect declaration to the controller which is allowed to interpret one such
response.  It adds no verifier relation and no native-refinement assumption.
-/
import Compiler.SemanticController
import Compiler.SemanticManifest

namespace Minidregg.Compiler.DialectClauseDispatch

open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uInput uQuery uReply uOutcome

/-! ## Lean-owned clause controller registry -/

/-- A clause controller has exactly one opaque query phase.  Query selection and
response interpretation are Lean functions indexed by the controller input.
The native boundary supplies only a value of `Reply input query`. -/
structure DialectController (clause : DialectClauseDecl) where
  Input : Type uInput
  Query : Input -> Type uQuery
  Reply : (input : Input) -> Query input -> Type uReply
  Outcome : Input -> Type uOutcome
  issue : (input : Input) -> Query input
  check : (input : Input) -> Reply input (issue input) -> Outcome input

/-- The manifest key of a clause-specific controller.  Both components are
needed: sharing controller code does not let one clause borrow another clause's
registration. -/
structure ControllerKey where
  clauseId : Digest
  controllerDigest : Digest
deriving DecidableEq, Repr

def clauseControllerKey (clause : DialectClauseDecl) : ControllerKey :=
  ⟨clause.clauseId, clause.verifierControllerDigest⟩

/-- A controller entry is indexed by the complete declaration it implements.
The declaration is checked against the manifest below; this record alone makes
no implementation claim. -/
structure ControllerEntry where
  declaration : DialectClauseDecl
  controller :
    DialectController.{uInput, uQuery, uReply, uOutcome} declaration

def ControllerEntry.key
    (entry : ControllerEntry.{uInput, uQuery, uReply, uOutcome}) :
    ControllerKey :=
  clauseControllerKey entry.declaration

structure ControllerRegistry where
  entries : List
    (ControllerEntry.{uInput, uQuery, uReply, uOutcome})

def ControllerRegistry.lookup
    (registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome})
    (key : ControllerKey) : Option
      (ControllerEntry.{uInput, uQuery, uReply, uOutcome}) :=
  registry.entries.find? fun entry => decide (entry.key = key)

def ControllerRegistry.KeysUnique
    (registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}) : Prop :=
  (registry.entries.map ControllerEntry.key).Nodup

/-- Stronger than `Manifest.WellFormed`: every controller entry is the exact
manifest declaration it claims to implement, and every manifest clause has a
controller entry at its `(clauseId, controllerDigest)` key. -/
structure ControllerRegistry.WellFormed (manifest : Manifest)
    (registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}) : Prop where
  keysUnique : registry.KeysUnique
  entriesManifestClosed : forall entry,
    entry ∈ registry.entries ->
      manifest.lookupClause entry.declaration.clauseId = some entry.declaration
  manifestControllersClosed : forall clause,
    clause ∈ manifest.dialectClauses ->
      exists entry, registry.lookup (clauseControllerKey clause) = some entry

theorem ControllerRegistry.lookup_some_closed
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {key : ControllerKey}
    {entry : ControllerEntry.{uInput, uQuery, uReply, uOutcome}}
    (found : registry.lookup key = some entry) :
    entry ∈ registry.entries /\ entry.key = key := by
  have hfind := (List.find?_eq_some_iff_append).mp found
  refine ⟨?_, of_decide_eq_true hfind.1⟩
  rcases hfind.2 with ⟨before, after, hlist, _⟩
  rw [hlist]
  simp

/-! ## Closed carrier, codec, and bridge resolution -/

/-- A required bridge together with all four of its endpoint dependencies.
No field here is a cast or a proof of the named bridge relation. -/
structure ResolvedBridge (manifest : Manifest) (bridgeId : Digest) where
  declaration : NamedBridgeRequirement
  declarationFound : manifest.lookupBridge bridgeId = some declaration
  sourceCarrier : CarrierProfile
  sourceCarrierFound :
    manifest.lookupCarrier declaration.sourceCarrierId = some sourceCarrier
  targetCarrier : CarrierProfile
  targetCarrierFound :
    manifest.lookupCarrier declaration.targetCarrierId = some targetCarrier
  sourceCodec : CodecPin
  sourceCodecFound :
    manifest.lookupCodec declaration.sourceCodecId = some sourceCodec
  targetCodec : CodecPin
  targetCodecFound :
    manifest.lookupCodec declaration.targetCodecId = some targetCodec

private theorem lookupBridge_some_mem
    {manifest : Manifest} {bridgeId : Digest}
    {bridge : NamedBridgeRequirement}
    (found : manifest.lookupBridge bridgeId = some bridge) :
    bridge ∈ manifest.bridges := by
  exact List.mem_of_find?_eq_some found

noncomputable def resolveBridge
    {manifest : Manifest} (wellFormed : manifest.WellFormed)
    {bridgeId : Digest} {bridge : NamedBridgeRequirement}
    (found : manifest.lookupBridge bridgeId = some bridge) :
    ResolvedBridge manifest bridgeId := by
  classical
  have bridgeMem : bridge ∈ manifest.bridges := lookupBridge_some_mem found
  have endpoints := wellFormed.bridgeEndpointsClosed bridge bridgeMem
  let sourceCarrier := Classical.choose endpoints.1
  have sourceCarrierFound := Classical.choose_spec endpoints.1
  let targetCarrier := Classical.choose endpoints.2.1
  have targetCarrierFound := Classical.choose_spec endpoints.2.1
  let sourceCodec := Classical.choose endpoints.2.2.1
  have sourceCodecFound := Classical.choose_spec endpoints.2.2.1
  let targetCodec := Classical.choose endpoints.2.2.2
  have targetCodecFound := Classical.choose_spec endpoints.2.2.2
  exact
    { declaration := bridge
      declarationFound := found
      sourceCarrier := sourceCarrier
      sourceCarrierFound := sourceCarrierFound
      targetCarrier := targetCarrier
      targetCarrierFound := targetCarrierFound
      sourceCodec := sourceCodec
      sourceCodecFound := sourceCodecFound
      targetCodec := targetCodec
      targetCodecFound := targetCodecFound }

/-- Complete dependency closure for the caller-selected clause identifier.
`controllerExact` is the load-bearing join: the executable controller is indexed
by the same complete declaration returned by `Manifest.lookupClause`. -/
structure ResolvedClause (manifest : Manifest)
    (registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome})
    (requestedClauseId : Digest) where
  clause : DialectClauseDecl
  clauseFound : manifest.lookupClause requestedClauseId = some clause
  carrier : CarrierProfile
  carrierFound : manifest.lookupCarrier clause.carrierProfileId = some carrier
  statementCodec : CodecPin
  statementCodecFound :
    manifest.lookupCodec clause.statementCodecId = some statementCodec
  proofCodec : CodecPin
  proofCodecFound : manifest.lookupCodec clause.proofCodecId = some proofCodec
  bridges : forall bridgeId, bridgeId ∈ clause.requiredBridgeIds ->
    ResolvedBridge manifest bridgeId
  controllerEntry :
    ControllerEntry.{uInput, uQuery, uReply, uOutcome}
  controllerFound :
    registry.lookup (clauseControllerKey clause) = some controllerEntry
  controllerExact : controllerEntry.declaration = clause

noncomputable def resolveRegistered
    {manifest : Manifest} (manifestWellFormed : manifest.WellFormed)
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    (registryWellFormed : registry.WellFormed manifest)
    {clauseId : Digest} {clause : DialectClauseDecl}
    (clauseFound : manifest.lookupClause clauseId = some clause) :
    ResolvedClause manifest registry clauseId := by
  classical
  obtain ⟨clauseMem, _⟩ := Manifest.lookupClause_some_closed clauseFound
  have dependencies :=
    manifestWellFormed.dialectClausesClosed clause clauseMem
  let carrier := Classical.choose dependencies.1
  have carrierFound := Classical.choose_spec dependencies.1
  let statementCodec := Classical.choose dependencies.2.1
  have statementCodecFound := Classical.choose_spec dependencies.2.1
  let proofCodec := Classical.choose dependencies.2.2.1
  have proofCodecFound := Classical.choose_spec dependencies.2.2.1
  have bridgesClosed := dependencies.2.2.2
  have controllerClosed :=
    registryWellFormed.manifestControllersClosed clause clauseMem
  let controllerEntry := Classical.choose controllerClosed
  have controllerFound := Classical.choose_spec controllerClosed
  obtain ⟨controllerMem, controllerKeyExact⟩ :=
    ControllerRegistry.lookup_some_closed controllerFound
  have controllerManifestFound :=
    registryWellFormed.entriesManifestClosed controllerEntry controllerMem
  have controllerClauseIdExact :
      controllerEntry.declaration.clauseId = clause.clauseId := by
    exact congrArg ControllerKey.clauseId controllerKeyExact
  have controllerFoundAtClauseId :
      manifest.lookupClause clause.clauseId =
        some controllerEntry.declaration := by
    rw [← controllerClauseIdExact]
    exact controllerManifestFound
  have clauseFoundAtClauseId :
      manifest.lookupClause clause.clauseId = some clause := by
    obtain ⟨_, idExact⟩ := Manifest.lookupClause_some_closed clauseFound
    rw [idExact]
    exact clauseFound
  have controllerExact : controllerEntry.declaration = clause :=
    manifest.lookupClause_unique manifestWellFormed.dialectClauseIdsUnique
      controllerFoundAtClauseId clauseFoundAtClauseId
  exact
    { clause := clause
      clauseFound := clauseFound
      carrier := carrier
      carrierFound := carrierFound
      statementCodec := statementCodec
      statementCodecFound := statementCodecFound
      proofCodec := proofCodec
      proofCodecFound := proofCodecFound
      bridges := fun bridgeId bridgeMem =>
        let found := bridgesClosed bridgeId bridgeMem
        resolveBridge manifestWellFormed (Classical.choose_spec found)
      controllerEntry := controllerEntry
      controllerFound := controllerFound
      controllerExact := controllerExact }

/-- Executable clause selection followed by proof-producing dependency
resolution.  Under the two well-formedness witnesses, `none` means precisely
that the requested clause identifier was not registered. -/
noncomputable def resolve
    (manifest : Manifest) (manifestWellFormed : manifest.WellFormed)
    (registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome})
    (registryWellFormed : registry.WellFormed manifest)
    (clauseId : Digest) : Option (ResolvedClause manifest registry clauseId) := by
  classical
  match found : manifest.lookupClause clauseId with
  | none => exact none
  | some clause =>
      exact some (resolveRegistered manifestWellFormed registryWellFormed found)

theorem resolve_eq_none_iff
    (manifest : Manifest) (manifestWellFormed : manifest.WellFormed)
    (registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome})
    (registryWellFormed : registry.WellFormed manifest)
    (clauseId : Digest) :
    resolve manifest manifestWellFormed registry registryWellFormed clauseId = none <->
      manifest.lookupClause clauseId = none := by
  classical
  unfold resolve
  split <;> simp_all

/-! ## Guarded opaque invocation -/

/-- Transport/runtime failure is control data, never a substitute proof reply. -/
inductive NativeFailure
  | unavailable
  | malformedResponse
deriving DecidableEq, Repr

abbrev ResolvedClause.Input
    {manifest : Manifest}
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {clauseId : Digest} (resolved : ResolvedClause manifest registry clauseId) :=
  resolved.controllerEntry.controller.Input

abbrev ResolvedClause.Query
    {manifest : Manifest}
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {clauseId : Digest} (resolved : ResolvedClause manifest registry clauseId)
    (input : resolved.Input) :=
  resolved.controllerEntry.controller.Query input

abbrev ResolvedClause.Reply
    {manifest : Manifest}
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {clauseId : Digest} (resolved : ResolvedClause manifest registry clauseId)
    (input : resolved.Input) (query : resolved.Query input) :=
  resolved.controllerEntry.controller.Reply input query

abbrev NativeOracle
    {manifest : Manifest}
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {clauseId : Digest} (resolved : ResolvedClause manifest registry clauseId)
    (input : resolved.Input) :=
  (query : resolved.Query input) -> Except NativeFailure (resolved.Reply input query)

/-- Dispatch produces a controller outcome only after an actual reply.  Native
failure remains a distinct blocked branch. -/
inductive DispatchOutcome
    {manifest : Manifest}
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {clauseId : Digest} (resolved : ResolvedClause manifest registry clauseId)
    (input : resolved.Input)
  | blocked (reason : NativeFailure)
  | completed (outcome : resolved.controllerEntry.controller.Outcome input)

/-- The clause and controller have already been fixed by `resolved`.  The oracle
is called only on the controller-issued query, and its response is passed only
to that controller's Lean check. -/
def run
    {manifest : Manifest}
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {clauseId : Digest} (resolved : ResolvedClause manifest registry clauseId)
    (input : resolved.Input) (oracle : NativeOracle resolved input) :
    DispatchOutcome resolved input :=
  let controller := resolved.controllerEntry.controller
  let query := controller.issue input
  match oracle query with
  | .error failure => .blocked failure
  | .ok reply => .completed (controller.check input reply)

@[simp] theorem run_nativeFailure
    {manifest : Manifest}
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {clauseId : Digest} (resolved : ResolvedClause manifest registry clauseId)
    (input : resolved.Input) (oracle : NativeOracle resolved input)
    (failure : NativeFailure)
    (failed : oracle (resolved.controllerEntry.controller.issue input) =
      .error failure) :
    run resolved input oracle = .blocked failure := by
  simp [run, failed]

@[simp] theorem run_reply
    {manifest : Manifest}
    {registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}}
    {clauseId : Digest} (resolved : ResolvedClause manifest registry clauseId)
    (input : resolved.Input)
    (oracle : NativeOracle resolved input)
    (reply : resolved.Reply input
      (resolved.controllerEntry.controller.issue input))
    (returned : oracle (resolved.controllerEntry.controller.issue input) =
      .ok reply) :
    run resolved input oracle =
      .completed (resolved.controllerEntry.controller.check input reply) := by
  simp [run, returned]

/-- A reusable adapter for the existing semantic receipt controller's native
phase.  Authorization remains a Lean proof in the input; a failed transport is
blocked by `run` before `SemanticController.checkReply` is reached. -/
structure AuthorizedSemanticReceiptInput
    (decl : SemanticController.ReceiptDeclaration) where
  portal : Portal
  state : AuthState
  kind : ResourceKind
  request : Request kind
  context : SemanticController.Context decl portal state request
  authorization : Nonempty (Authorized portal state request)

def authorizedSemanticReceiptController
    (clause : DialectClauseDecl)
    (decl : SemanticController.ReceiptDeclaration) :
    DialectController.{1, 0, 0, 0} clause where
  Input := AuthorizedSemanticReceiptInput decl
  Query := fun _ => SemanticController.KernelQuery decl
  Reply := fun _ _ => SemanticController.KernelReply decl
  Outcome := fun input => SemanticController.Outcome input.context
  issue := fun input => input.context.query input.context.challenge
  check := fun input reply =>
    SemanticController.checkReply input.context input.authorization
      input.context.challenge reply

end Minidregg.Compiler.DialectClauseDispatch
