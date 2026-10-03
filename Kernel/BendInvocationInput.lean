/- Source invocation observations are built from actual current native read
admission, narrowed through that read capability. Internal method traces and
complete loaded stores are never used as caller-visible input. This module
establishes input provenance, not an execution/funding/effect admission token. -/
import Kernel.ResourceObservationAdmission
import Compiler.BendInvocation
import Compiler.BendSourceByteCodec

namespace Minidregg.Kernel.BendInvocationInput
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellRegistry
set_option autoImplicit false

structure Observation where
  resource : Nat
  root : Digest
  physicalKind : Nat
  /-- Canonical narrowed native store, without the blinding key. -/
  resourceBytes : List UInt8
  /-- Only account coordinates named by the same read capability. -/
  accountBytes : List UInt8
  deriving DecidableEq, Repr

def observationStream : StreamCodec Observation :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product bytesStream bytesStream))))
    (fun o => (o.resource, o.root, o.physicalKind, o.resourceBytes, o.accountBytes))
    (fun o => ⟨o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2⟩)
    (by intro o; cases o; rfl)

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : ResourceObservationAdmission.Deployment}
  {durable : ResourceObservationAdmission.Durable}
  {context : ResourceObservationAdmission.Context deployment durable}
  {profile : CanonicalRuntimeProfile.Profile F} {kind : ResourceKind}
  {wanted : Request kind} {marker : Nat} {capability : CapabilityId}
  {contextBytes : List UInt8}

/-- Even after successful read admission, export is narrowed again through the
actual current capability. The root is the original authenticated root, never
replaced by the hash of the narrowed view. -/
def observe (prepared : ResourceObservationAdmission.Prepared context profile wanted
    marker capability contextBytes) {envelope : List UInt8}
    (_checked : ResourceObservationAdmission.Checked prepared envelope) : Observation :=
  let fields := ResourceObservationAdmission.readerFields context kind capability
  let packed := ResourceObservationAdmission.narrowPacked fields prepared.observed.before
  { resource := wanted.target.value
    root := prepared.observed.before.payload.root
    physicalKind := packed.kind.tag.toNat
    resourceBytes := (CanonicalCellRegistry.materializer packed.kind).codec.encode packed.payload.logical
    accountBytes := CanonicalAccountView.balanceStream.encode
      (ResourceObservationAdmission.narrowBalances fields prepared.accountBalances) }

theorem observed_actual_root
    (prepared : ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes)
    {envelope : List UInt8} (checked : ResourceObservationAdmission.Checked prepared envelope) :
    (observe prepared checked).root = wanted.preStateRoot :=
  prepared.observed.rootExact.symm

theorem observed_actual_resource
    (prepared : ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes)
    {envelope : List UInt8} (checked : ResourceObservationAdmission.Checked prepared envelope) :
    (observe prepared checked).resource = wanted.target.value := rfl

theorem observed_account_scope
    (prepared : ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes)
    (pair : Nat × Int)
    (present : pair ∈ ResourceObservationAdmission.narrowBalances
      (ResourceObservationAdmission.readerFields context kind capability) prepared.accountBalances) :
    CellField.NamedBy (ResourceObservationAdmission.readerFields context kind capability) (.balance pair.1) :=
  ResourceObservationAdmission.narrowBalances_only_named present

/-- Native consumers retain this token, rather than accepting a wire
Observation as evidence that somebody was allowed to see it. -/
structure Admitted (selectedContext : ResourceObservationAdmission.Context deployment durable)
    (selectedProfile : CanonicalRuntimeProfile.Profile F) (subject : SubjectId) where
  private mk ::
  value : Observation
  resourceKind : ResourceKind
  request : Request resourceKind
  subjectExact : request.subject = subject
  operationMarker : Nat
  readCapability : CapabilityId
  requestBytes : List UInt8
  prepared : ResourceObservationAdmission.Prepared selectedContext selectedProfile request
    operationMarker readCapability requestBytes
  envelope : List UInt8
  checked : ResourceObservationAdmission.Checked prepared envelope
  valueExact : value = observe prepared checked

def admitObservation (subject : SubjectId)
    (prepared : ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes)
    {envelope : List UInt8} (checked : ResourceObservationAdmission.Checked prepared envelope) :
    Option (Admitted context profile subject) :=
  if exact : wanted.subject = subject then
    some ⟨observe prepared checked, kind, wanted, exact, marker, capability, contextBytes,
      prepared, envelope, checked, rfl⟩
  else none

theorem admitted_root (admitted : Admitted context profile wanted.subject) :
    admitted.value.root = admitted.request.preStateRoot := by
  rw [admitted.valueExact]
  exact observed_actual_root admitted.prepared admitted.checked

/-- This immutable wire binding is consumed jointly with the OO owner's actual
carrier/provider context. Arguments retain their exact selected codec bytes;
that codec's typed-data admission remains an explicit invocation premise. -/
structure Input where
  identity : BendInvocation.ProgramIdentity
  subject : SubjectId
  nonce : Nat
  argumentCodec : Digest
  arguments : List UInt8
  observations : List Observation
  deriving DecidableEq, Repr

def stream : StreamCodec Input :=
  StreamCodec.xmap (StreamCodec.product BendInvocation.programStream
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
    (StreamCodec.product bytesStream (StreamCodec.list observationStream))))))
    (fun i => (i.identity, i.subject, i.nonce, i.argumentCodec, i.arguments, i.observations))
    (fun i => ⟨i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2.1, i.2.2.2.2.2⟩)
    (by intro i; cases i; rfl)
def frame : List UInt8 := "DREGG/BEND/INVOCATION-INPUT/v1".toUTF8.toList
def encode (input : Input) : List UInt8 := frame ++ stream.encode input
def decode (bytes : List UInt8) : Option Input :=
  NockProgramCodec.framedDecode frame stream bytes
def sourceTerm (input : Input) : BendTT.Term := BendSourceRepresentation.bytesTerm (encode input)

/-- Exact bytes are useful only with the independently retained admission
closure. No constructor accepting only Input or decoded bytes is supplied. -/
structure Bound (selectedContext : ResourceObservationAdmission.Context deployment durable)
    (selectedProfile : CanonicalRuntimeProfile.Profile F) (input : Input) where
  observations : List (Admitted selectedContext selectedProfile input.subject)
  observationsExact : input.observations = observations.map Admitted.value

theorem bound_observations_exact {input : Input} (bound : Bound context profile input) :
    input.observations = bound.observations.map Admitted.value := bound.observationsExact

theorem roundtrip (input : Input) : decode (encode input) = some input :=
  NockProgramCodec.framedDecode_encode frame stream input

theorem canonical {bytes : List UInt8} {input : Input}
    (h : decode bytes = some input) : encode input = bytes :=
  NockProgramCodec.framedDecode_canonical h

end Minidregg.Kernel.BendInvocationInput
