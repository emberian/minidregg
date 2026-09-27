/-
Agent-origin parent selection for application dispatch. The human authoring
route explicitly refuses agent tickets. This separate source reads a reserved
AgentGrain parent from one verifier-opened image and prepares the additional
DRC witness; it is not yet an external signing route or delivery permit.
-/
import Kernel.ApplicationDispatchAuthoring

namespace Minidregg.Kernel.ApplicationDispatchAgentAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationDispatchCodec
open Minidregg.Kernel.ApplicationDispatchCommand

set_option autoImplicit false

/-- All selectors belong to the fixed agent custodian. HTTP cannot choose the
task, its capability, its observer, or the ticket issue. -/
structure Request where
  base : ApplicationDispatchAuthoring.Request
  task : Nat
  parentCapability : CapabilityId
  parentObserveCapability : CapabilityId
  deriving DecidableEq

def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchAuthoring.requestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          CredentialAuthorityEntryCodec.capabilityIdStream)))
    (fun request => (request.base, request.task,
      request.parentCapability, request.parentObserveCapability))
    (fun (base, task, parentCapability, parentObserveCapability) =>
      ⟨base, task, parentCapability, parentObserveCapability⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request :=
  NativeHostCodec.framed "DREGG/APPLICATION/AGENT-DISPATCH-AUTHOR-REQUEST/v1".toUTF8.toList
    requestStream

theorem request_decode_encode (request : Request) :
    requestCodec.decode (requestCodec.encode request) = some request :=
  requestCodec.decode_encode request

/-- The source-selected parent is an exact-state DRC witness, not a paid
reserve operation. The reserved budget remains held by the parent task. -/
structure ParentPlan where
  request : Request
  parent : ApplicationDispatchCommand.Parent
  physicalRoot : Digest
  issueIngressBytes : List UInt8

/-- Full detached signing plan with the source-selected parent retained for
the later v2 host fence. It is not a v1 human plan or delivery authority. -/
structure Plan where
  parent : ParentPlan
  signing : ApplicationDispatchAuthoring.Plan

private def stateAt (task : Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) : Option AgentGrain.State := do
  match cell with
  | ⟨.declaredObject, payload⟩ =>
      let page ← DeclaredEffectPageMaterializer.pageAt payload.logical
      AgentGrain.readState task page
  | _ => none

/-- All parent coordinates come from the exact loaded image and the issue
certificate retained by its chronological native replay. Status 3/4 and the
fixed generation are the AgentGrain witness fence. A later op34 must recheck
that old cell/root/current capability and current law; this plan is unsigned. -/
def prepareParentVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (request : Request) : Except String ParentPlan := do
  let some issue := verified.issues.find? (fun issue =>
      issue.index == request.base.issueIndex)
    | throw "agent share issue absent from verified prefix"
  let ticket := issue.evidence.ingress.spec.ticket
  if ticket.resource != request.base.ticketResource then
    throw "agent ticket differs from admitted issue"
  let generation ← match ticket.participant.origin with
    | .human => throw "agent authoring refuses human-origin ticket"
    | .agent task generation =>
        if task != request.task then throw "agent parent task differs from admitted ticket"
        pure generation
  let cell ← match verified.opened.directory.directory.slots request.task with
    | .present cell => pure cell
    | _ => throw "agent parent cell unavailable"
  let state ← NativeHost.need "agent parent state unavailable"
    (stateAt request.task cell)
  if state.generation != generation || !(state.status == 3 || state.status == 4) then
    throw "agent parent generation or reservation status changed"
  if state.reserved < 0 || state.remaining < 0 then
    throw "agent parent budget invalid"
  let parent : ApplicationDispatchCommand.Parent :=
    ⟨request.task, state, request.parentCapability,
      cell.payload.root, request.parentObserveCapability⟩
  pure ⟨request, parent, ResourceBirthCodec.physicalRoot (.live cell),
    ApplicationShareIssueSource.ingressCodec.encode issue.evidence.ingress⟩

def prepareParentRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : Except String ParentPlan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical agent dispatch authoring request"
  prepareParentVerified config verified request

/-- Reuses the one source-owned DRC/observation construction, adding the
AgentGrain second target and its exact signing/observation slots. The current
v1 receiver refuses agent origin, so no host may submit this as v1 delivery. -/
def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (request : Request) : Except String Plan := do
  let parent ← prepareParentVerified config verified request
  let signing ← ApplicationDispatchAuthoring.prepareWithParent config verified
    request.base (some parent.parent)
  pure ⟨parent, signing⟩

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical agent dispatch authoring request"
  prepareVerified config verified request

end Minidregg.Kernel.ApplicationDispatchAgentAuthoring
