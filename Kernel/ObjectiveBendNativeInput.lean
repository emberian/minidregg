/- Objective invocation input: actor/nonce are host values, observations are
constructed from actual current signed read tokens. Caller arguments are data
only and cannot replace that context. Complete input bytes are bounded before
source term construction. No authority or accepted effect is minted here. -/
import Kernel.ObjectiveBendArtifactSource
import Theory.ObjectiveBendDemandCapacity
import Kernel.RunComputeBudgetDomain
namespace Minidregg.Kernel.ObjectiveBendNativeInput
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open ObjectiveBendOpenRecursion ObjectiveBendTyping
open Lean (Json)
set_option autoImplicit false

structure Observation where
  resource : Nat
  root : Digest
  physicalKind : Nat
  resourceBytes : List UInt8
  accountBytes : List UInt8
  fields : List (Nat × Int)
  deriving DecidableEq, Repr

def observationStream : StreamCodec Observation :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
    (StreamCodec.list (StreamCodec.product StreamCodec.nat IntStream.intStream)))))))
    (fun o => (o.resource,o.root,o.physicalKind,o.resourceBytes,o.accountBytes,o.fields))
    (fun o => ⟨o.1,o.2.1,o.2.2.1,o.2.2.2.1,o.2.2.2.2.1,o.2.2.2.2.2⟩)
    (by intro o; cases o; rfl)

private def visibleFields (resource : Nat) : (kind : CanonicalCellRegistry.Kind) →
    Minidregg.Theory.Store.Store (CanonicalCellRegistry.layout kind) → List (Nat × Int)
  | .declaredObject,logical | .declaredProgram,logical | .accountMetadata,logical =>
      DeclaredResourceProjection.values resource logical
  | _,_ => []

def observe {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    {context : ResourceObservationAdmission.Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {kind : ResourceKind}
    {wanted : Request kind} {marker : Nat} {capability : CapabilityId} {contextBytes : List UInt8}
    (prepared : ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes)
    {envelope : List UInt8} (_checked : ResourceObservationAdmission.Checked prepared envelope)
    (compute : Option (RunComputeBudgetDomain.Prepared deployment context.cells wanted.subject)) : Observation :=
  let fields := ResourceObservationAdmission.readerFields context kind capability
  let packed := ResourceObservationAdmission.narrowPacked fields prepared.observed.before
  let balances := match compute with
    | some funded => if kind = .account then CanonicalAccountView.accountCut
        (CanonicalResourceKernel.logicalBook funded.budget.book.post.logical) wanted.target.value
      else prepared.accountBalances
    | none => prepared.accountBalances
  ⟨wanted.target.value,prepared.observed.before.payload.root,packed.kind.tag.toNat,
    (CanonicalCellRegistry.materializer packed.kind).codec.encode packed.payload.logical,
    CanonicalAccountView.balanceStream.encode (ResourceObservationAdmission.narrowBalances fields balances),
    visibleFields wanted.target.value packed.kind packed.payload.logical⟩

structure AdmittedRead {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    (context : ResourceObservationAdmission.Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (subject : SubjectId) where
  private mk ::
  kind : ResourceKind
  request : Request kind
  subjectExact : request.subject = subject
  marker : Nat
  capability : CapabilityId
  contextBytes : List UInt8
  prepared : ResourceObservationAdmission.Prepared context profile request marker capability contextBytes
  envelope : List UInt8
  checked : ResourceObservationAdmission.Checked prepared envelope
  compute : Option (RunComputeBudgetDomain.Prepared deployment context.cells request.subject)

def AdmittedRead.value {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    {context : ResourceObservationAdmission.Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {subject : SubjectId}
    (read : AdmittedRead context profile subject) : Observation := observe read.prepared read.checked read.compute

def admitRead {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    {context : ResourceObservationAdmission.Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {kind : ResourceKind}
    {wanted : Request kind} {marker : Nat} {capability : CapabilityId} {contextBytes : List UInt8}
    (subject : SubjectId)
    (prepared : ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes)
    {envelope : List UInt8} (checked : ResourceObservationAdmission.Checked prepared envelope)
    (subjectExact : wanted.subject = subject)
    (compute : Option (RunComputeBudgetDomain.Prepared deployment context.cells wanted.subject)) :
    AdmittedRead context profile subject :=
  ⟨kind,wanted,subjectExact,marker,capability,contextBytes,prepared,envelope,checked,compute⟩

private def exactKeys (keys : List String) (json : Json) : Except String Unit := do
  let object ← json.getObj?
  let actual := object.foldl (init := []) (fun names key _ => key::names)
  if actual.length != keys.length || !actual.all keys.contains then throw "Objective argument fields"

/-- Naturals are length/bit guarded while textual, before Nat parsing. -/
def decodeData (scalarBits : Nat) : Nat → Json → Except String Term
  | 0,_ => .error "Objective argument depth"
  | fuel+1,json => do
    match ← json.getObjValAs? String "tag" with
    | "natural" =>
      exactKeys ["tag","value"] json
      let text ← json.getObjValAs? String "value"
      let n ← (ObjectiveBendDemandCapacity.decodeNatural ⟨scalarBits⟩ text).mapError
        (fun _ => "Objective natural argument capacity/canonical spelling")
      pure (.nat n)
    | "boolean" => exactKeys ["tag","value"] json; return .boolean (← json.getObjValAs? Bool "value")
    | "label" => exactKeys ["tag","value"] json; return .label (← json.getObjValAs? String "value")
    | "record" =>
      exactKeys ["tag","fields"] json
      let fields ← (← json.getObjVal? "fields").getArr?
      let parsed ← fields.toList.mapM fun field => do
        exactKeys ["name","value"] field
        return (← field.getObjValAs? String "name",← decodeData scalarBits fuel (← field.getObjVal? "value"))
      if !decide (parsed.map Prod.fst).Nodup then throw "Objective duplicate argument field"
      pure (.record parsed)
    | _ => throw "Objective data argument required"

def parseArguments (maxBytes scalarBits : Nat) (bytes : List UInt8) : Except String (List Term) := do
  let json ← ObjectiveBendSourceArtifact.parsePacket maxBytes bytes
  exactKeys ["schema","values"] json
  if (← json.getObjValAs? String "schema") != "dregg.objective-bend.argument-values.v1" then
    throw "Objective typed argument edition"
  (← (← json.getObjVal? "values").getArr?).toList.mapM (decodeData scalarBits 256)

structure Input where
  subject : SubjectId
  nonce : Nat
  arguments : List UInt8
  observations : List Observation
  deriving DecidableEq, Repr

def stream : StreamCodec Input :=
  StreamCodec.xmap (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream (StreamCodec.list observationStream))))
    (fun i => (i.subject,i.nonce,i.arguments,i.observations))
    (fun i => ⟨i.1,i.2.1,i.2.2.1,i.2.2.2⟩) (by intro i; cases i; rfl)
def frame : List UInt8 := "DREGG/OBJECTIVE-BEND/NATIVE-INPUT".toUTF8.toList ++ [1]
def encode (i : Input) : List UInt8 := frame ++ stream.encode i

def hex (bytes : List UInt8) : String := String.ofList (bytes.flatMap fun b =>
  let digits := "0123456789abcdef".toList
  [digits[b.toNat/16]!,digits[b.toNat%16]!])
def ordinalFields (terms : List Term) : List (String × Term) :=
  (terms.zipIdx).map (fun (term,index) => (toString index,term))
def observationTerm (o : Observation) : Term := .record
  [("resource",.nat o.resource),("root",.label (hex (digestStream.encode o.root))),
   ("kind",.nat o.physicalKind),("resourceBytes",.label (hex o.resourceBytes)),
   ("accountBytes",.label (hex o.accountBytes)),
   ("fields",.record (ordinalFields (o.fields.map fun (field,value) => .record
      [("field",.nat field),("negative",.boolean (value < 0)),("magnitude",.nat value.natAbs)])))]
def codecId : Digest := (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.INPUT-CODEC/v1".toUTF8.toList
  "Input={subject:Nat,nonce:Nat,arguments:ordinalData,observations:ordinal{resource,root,kind,resourceBytes,accountBytes,fields:ordinal{field,negative,magnitude}}};strict-tagged-data;current-signed-narrowed-reads".toUTF8.toList).digest

def sourceTerm (input : Input) (maxBytes scalarBits : Nat) : Except String Term := do
  if (encode input).length > maxBytes then throw "Objective complete input byte capacity"
  if ObjectiveBendDemandCapacity.bits input.subject.value > scalarBits ||
      ObjectiveBendDemandCapacity.bits input.nonce > scalarBits then throw "Objective context scalar capacity"
  if !input.observations.all (fun o => ObjectiveBendDemandCapacity.bits o.resource ≤ scalarBits &&
      ObjectiveBendDemandCapacity.bits o.physicalKind ≤ scalarBits && o.fields.all (fun (field,value) =>
        ObjectiveBendDemandCapacity.bits field ≤ scalarBits &&
        ObjectiveBendDemandCapacity.bits value.natAbs ≤ scalarBits)) then
    throw "Objective observation scalar capacity"
  let arguments ← parseArguments maxBytes scalarBits input.arguments
  pure (.record [("subject",.nat input.subject.value),("nonce",.nat input.nonce),
    ("arguments",.record (ordinalFields arguments)),
    ("observations",.record (ordinalFields (input.observations.map observationTerm)))])

/-- Path transport instantiates the selected checked definition; the native
closed checker checks this SAME application before any demand execution. -/
def instantiate (source : AnnotatedTerm) (input : Term) : AnnotatedTerm :=
  ⟨.app source.term input,fun path => match path with | 0::rest => source.annotations rest | _ => none,
    source.assumptions⟩

structure Bound {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    (context : ResourceObservationAdmission.Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (input : Input) where
  private mk ::
  reads : List (AdmittedRead context profile input.subject)
  exact : input.observations = reads.map AdmittedRead.value

def bind {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    {context : ResourceObservationAdmission.Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} (subject : SubjectId) (nonce : Nat) (arguments : List UInt8)
    (reads : List (AdmittedRead context profile subject)) :
    Bound context profile ⟨subject,nonce,arguments,reads.map AdmittedRead.value⟩ := ⟨reads,rfl⟩

theorem input_reads_exact {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    {context : ResourceObservationAdmission.Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {input : Input} (bound : Bound context profile input) :
    input.observations = bound.reads.map AdmittedRead.value := bound.exact
#assert_axioms input_reads_exact
end Minidregg.Kernel.ObjectiveBendNativeInput
