/- Canonical source event63 authorizes one designated logical-party dispatch.
The dispatch is ordered and physically read back before backend work. Local
backend arrivals/outboxes are not replicated source state. This module returns
no Qualified/result/YES token and never performs a worker effect from a claim. -/
import Kernel.JointBackendPartyAdmission
import Kernel.JointReceiver
namespace Minidregg.Kernel.JointBackendPartyReceiver
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.JointBackendPartyCodec
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.JointBackendPartyAdmission
set_option autoImplicit false

/-- The semantic marker excludes credential randomness while retaining the
source-selected row, generation, slot and exact authenticated message. -/
def transactionId {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} (p : Prepared config opened pin request) : Digest :=
  ⟨marker pin request p.row p.packet⟩

def nullifier {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} (p : Prepared config opened pin request) : StableNullifier where
  codecVersion := 63
  domain := config.deployment.domain
  nullifierId := transactionId p
  canonicalBytes := "DREGG.JOINT.PRIVATE.SOURCE.NULLIFIER".toUTF8.toList ++ [1] ++
    semanticBytes pin request p.row p.packet

def event {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} (p : Prepared config opened pin request) : StableEvent where
  codecVersion := 63
  domain := config.deployment.domain
  eventId := (Sp800185Cshake256.hash "DREGG.JOINT.PRIVATE.SOURCE.EVENT".toUTF8.toList
    (requestBytes request)).digest
  canonicalBytes := requestBytes request

/-- All ten funded lanes are the deployment's fixed private packet continuation
capacity plus this concrete source-record overhead. This capacity is part of
the source-authorized semantic preimage, not a caller-provided cheap fee. The
physical worker is responsible for the corresponding bounded continuation. -/
def sourceOverhead {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} (p : Prepared config opened pin request) : Charge
  | .incidences => 1
  | .turnBytes => (requestBytes request).length
  | .memoryTouches => (readGuards p).length
  | .storageBytes => (requestBytes request).length
  | .proofWork => 1
  | .witnessBytes => (requestBytes request).length
  | .sideEffectCount => 1
  | .feeDebit | .networkBytes | .leaseByteBlocks => 0

def charge {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} (p : Prepared config opened pin request) : Charge :=
  pin.dispatchCapacity + sourceOverhead p

def intent {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} (p : Prepared config opened pin request)
    (_checked : Checked p) : DataIntent ResourceBirthCodec.rootBytes where
  transactionId := transactionId p
  writes := []
  readGuards := readGuards p
  nullifiers := [nullifier p]
  exactCharge := charge p
  event := event p
  subject := some p.row.party.subject
  postRootsBound := by intro w h; cases h
  guardsReadOnly := by intro g _; simp

structure Admitted (config : Config) (opened : Opened config) (pin : EndpointPin)
    (request : JointBackendPartyCodec.Request) where
  private mk ::
  prepared : Prepared config opened pin request
  checked : Checked prepared
  retainsFunding : Charge.fundedCheck
    (JointReservation.heldCharge config.deployment.domain prepared.control.reservations +
      prepared.control.maintenanceReserve + (intent prepared checked).exactCharge)
    opened.durable.snapshot.model.available = true
  allFacets : config.sourceGate none opened.durable.snapshot (intent prepared checked) = .ok ()

def Admitted.intent {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} (a : Admitted config opened pin request) :
    DataIntent ResourceBirthCodec.rootBytes := intent a.prepared a.checked

/-- Fresh work needs current native permission AND spare funding after ALL
application holds and protected maintenance. No held funds are borrowed. -/
def admit (config : Config) (opened : Opened config) (pin : EndpointPin)
    (request : JointBackendPartyCodec.Request) : IO (Except String (Admitted config opened pin request)) := do
  match JointBackendPartyAdmission.prepare config opened pin request with
  | .error reason => return .error reason
  | .ok prepared =>
    match ← JointBackendPartyAdmission.check prepared with
    | .error reason => return .error reason
    | .ok checked =>
      if funded : Charge.fundedCheck
          (JointReservation.heldCharge config.deployment.domain prepared.control.reservations +
            prepared.control.maintenanceReserve + (intent prepared checked).exactCharge)
          opened.durable.snapshot.model.available = true then
        match facets : config.sourceGate none opened.durable.snapshot (intent prepared checked) with
        | .error _ => return .error "private dispatch conflicts with protected source facet"
        | .ok () => return .ok ⟨prepared,checked,funded,facets⟩
      else return .error "private dispatch continuation is not funded"

/-- One physical source append. Only this private receipt can authorize the
configured designated-party worker invocation; serialized receipt bytes alone
have no such constructor. Ordinary uncertain/replayed results mint no effect. -/
structure Applied (config : Config) (opened : Opened config) (pin : EndpointPin)
    (request : JointBackendPartyCodec.Request) (admitted : Admitted config opened pin request)
    (expected : Context) where
  private mk ::
  contextPinned : config.jointConsensus = some expected
  ordered : JointReceiver.Ordered expected opened.durable admitted.intent
  appended : DurableReceiverIO.Appended ResourceBirthCodec.rootBytes opened.durable admitted.intent

inductive Result (config : Config) (opened : Opened config) (pin : EndpointPin)
    (request : JointBackendPartyCodec.Request) (admitted : Admitted config opened pin request)
    (expected : Context) where
  | applied (receipt : Applied config opened pin request admitted expected)
  | refused (reason : String)
  | ordinary (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

/-- Domain consensus orders the exact complete common event63 record alongside
ordinary transitions. No route invokes the private worker from prepare alone. -/
def apply (config : Config) (opened : Opened config) (pin : EndpointPin)
    (request : JointBackendPartyCodec.Request) (admitted : Admitted config opened pin request)
    (expected : Context) (ordered : JointReceiver.Ordered expected opened.durable admitted.intent) :
    IO (Result config opened pin request admitted expected) := do
  if pinned : config.jointConsensus = some expected then
    if expected.scope != digestStream.encode config.deployment.domain then
      return .refused "source consensus domain mismatch"
    match ← DurableReceiverIO.receiveLoadedDetailed config.physicalTransport
        ResourceBirthCodec.rootBytes opened.durable admitted.intent with
    | .ordinary result => return .ordinary result
    | .exact _ appended => return .applied ⟨pinned,ordered,appended⟩
  else return .refused "source consensus configuration mismatch"

/-- This is the exact configured-worker effect input, kept source private. It
contains no replica-local outbox/path/anchor in the common source record. -/
def Applied.requestBytes {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} {admitted : Admitted config opened pin request}
    {expected : Context} (_applied : Applied config opened pin request admitted expected) : List UInt8 :=
  JointBackendPartyCodec.requestBytes request

def Applied.enrollmentBytes {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} {admitted : Admitted config opened pin request}
    {expected : Context} (_applied : Applied config opened pin request admitted expected) : List UInt8 :=
  enrollmentStream.encode admitted.prepared.row

def Applied.sourceRecordBytes {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} {admitted : Admitted config opened pin request}
    {expected : Context} (applied : Applied config opened pin request admitted expected) : List UInt8 :=
  applied.appended.entry.record

theorem applied_dispatch_and_debit_same_record {config : Config} {opened : Opened config} {pin : EndpointPin}
    {request : JointBackendPartyCodec.Request} {admitted : Admitted config opened pin request}
    {expected : Context} (applied : Applied config opened pin request admitted expected) :
    applied.appended.next.image = opened.durable.image.append admitted.intent := applied.appended.image
#assert_axioms applied_dispatch_and_debit_same_record
end Minidregg.Kernel.JointBackendPartyReceiver
