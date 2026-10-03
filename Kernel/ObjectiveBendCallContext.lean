/- Stateful OO binding derives self from ACTUAL prepared participant zero and
provider/super from the loaded immutable prototype construction. Method args
are signed by a full-width hash in the existing command nonce, not detached
metadata. All observation inputs require actual current read admission. This
additive binder does not install a new native Host profile or execute opaque
argument bytes; the shared input ABI must decode/type-check them explicitly. -/
import Compiler.ObjectiveBendInstance
import Kernel.WorldMethodTrace
import Kernel.BendInvocationInput
import Theory.AssertAxioms

namespace Minidregg.Kernel.ObjectiveBendCallContext
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController
open ObjectiveBendComposition
set_option autoImplicit false

structure Request where
  self : Nat
  selfRoot : Digest
  prototype : Nat
  selector : String
  argumentCodec : String
  arguments : List UInt8
  salt : Nat
  deriving DecidableEq, Repr

def requestStream : StreamCodec Request :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product bytesStream StreamCodec.nat))))))
    (fun r => (r.self, r.selfRoot, r.prototype, r.selector, r.argumentCodec, r.arguments, r.salt))
    (fun r => ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2⟩)
    (by intro r; cases r; rfl)

def requestId (subject : SubjectId) (request : Request) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.CALL/v1".toUTF8.toList
    ((StreamCodec.product StreamCodec.nat requestStream).encode
      (subject.value, request))).digest

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {command : Command}

/-- Full-width digest Nat binds the OO request in the existing signed command.
The default transaction codec, nonce/nullifier behavior and ordinary rights are
unchanged. No injectivity of cryptographic hashing is claimed as a theorem. -/
structure Binding (prepared : PreparedInvocation deployment profile ambient durable command)
    (request : Request) where
  instance : ObjectiveBendInstance.Instance
  actions : List WorldKindInstance.Action
  world : command.targets[firstIndex prepared].payload = .world actions
  stateExact :
    WorldKindCell.instanceAt (world ▸ (prepared.targets (firstIndex prepared)).pre.logical) =
      some instance.value
  selfExact : request.self = command.targets[firstIndex prepared].target
  selfRootExact : request.selfRoot = (prepared.targets (firstIndex prepared)).pre.root
  prototypeExact : request.prototype = instance.source.construction.root.id
  nonceExact : command.nonce = (requestId command.subject request).value
  /-- This is an actual read, even for one-target methods. Write authority does
  not become read authority and cannot supply captured source state. -/
  selfEnvelope : List UInt8
  selfObserve : ReadLeg prepared (firstIndex prepared) selfEnvelope

/-- Each input is backed by its actual signed current read admission. -/
structure Observation (prepared : PreparedInvocation deployment profile ambient durable command) where
  index : TargetIndex command
  envelope : List UInt8
  admitted : ReadLeg prepared index envelope

def observationValue (prepared : PreparedInvocation deployment profile ambient durable command)
    (observation : Observation prepared) : BendInvocationInput.Observation :=
  BendInvocationInput.observe observation.admitted.selected observation.admitted.checked

/-- Every dynamic self/super demand retains one stateful self; provider cursor
comes from actual prototype resolution. Source runner arguments still need the
shared qualified bytes decoder/Values witness before Eval can be invoked. -/
structure Demand (prepared : PreparedInvocation deployment profile ambient durable command)
    (request : Request) (binding : Binding prepared request) where
  cursor : Nat
  required : Requirement
  selected : Selected
  resolved : resolve binding.instance.source.construction.layers cursor required = some selected
  observations : List (Observation prepared)

def Demand.self {prepared : PreparedInvocation deployment profile ambient durable command}
    {request : Request} {binding : Binding prepared request} (_demand : Demand prepared request binding) : Nat :=
  request.self

def Demand.coreEntry {prepared : PreparedInvocation deployment profile ambient durable command}
    {request : Request} {binding : Binding prepared request} (demand : Demand prepared request binding) : String :=
  ObjectiveBendElaboration.coreName demand.selected

def Demand.super {prepared : PreparedInvocation deployment profile ambient durable command}
    {request : Request} {binding : Binding prepared request} (demand : Demand prepared request binding)
    (interface : Interface) (selected : Selected)
    (resolved : resolve binding.instance.source.construction.layers demand.selected.provider
      ⟨.priorSuper, interface⟩ = some selected) : Demand prepared request binding :=
  ⟨demand.selected.provider, ⟨.priorSuper, interface⟩, selected, resolved, demand.observations⟩

/-- The first demand is the authored selector signed in the OO request. Its
interface is resolved by exact source type, never a numeric method index. -/
def begin (prepared : PreparedInvocation deployment profile ambient durable command)
    (request : Request) (binding : Binding prepared request) (interface : Interface)
    (selectorExact : interface.selector = request.selector)
    (observations : List (Observation prepared)) : Option (Demand prepared request binding) :=
  match selected : resolve binding.instance.source.construction.layers 0 ⟨.finalSelf, interface⟩ with
  | none => none
  | some provider => some ⟨0, ⟨.finalSelf, interface⟩, provider, selected, observations⟩

theorem same_instance_on_demand {prepared : PreparedInvocation deployment profile ambient durable command}
    {request : Request} {binding : Binding prepared request}
    (left right : Demand prepared request binding) : left.self = right.self := rfl

theorem selected_entry_exact {prepared : PreparedInvocation deployment profile ambient durable command}
    {request : Request} {binding : Binding prepared request} (demand : Demand prepared request binding) :
    ObjectiveBendElaboration.reference binding.instance.source.construction.layers
      demand.cursor demand.required = some (.Ref demand.coreEntry) :=
  ObjectiveBendElaboration.reference_exact _ _ _ _ demand.resolved

#assert_axioms same_instance_on_demand
#assert_axioms selected_entry_exact
end Minidregg.Kernel.ObjectiveBendCallContext
