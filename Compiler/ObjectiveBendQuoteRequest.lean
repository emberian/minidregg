/- Original locally retained Objective invocation request. This carrier includes
no proposed command, produced output or caller-chosen authenticated input hash.
Expected source bytes are independently regenerated through the pinned frontend;
this codec does not establish frontend adequacy or authorize a native effect. -/
import Compiler.ObjectiveInvocationClaim
import Compiler.NativeObservationCodec
import Kernel.RunComputeBudgetDomain
namespace Minidregg.Compiler.ObjectiveBendQuoteRequest
open Minidregg.Theory Minidregg.Theory.TypedAuthorization Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.RunComputeBudgetDomain
set_option autoImplicit false

/-- Authority and disclosure selections, independently retained before source
execution. The stream encodes a read placeholder; it cannot carry proposed effects. -/
structure Role where
  kind : ResourceKind
  resource : Nat
  capability : CapabilityId
  schemaVersion : Nat
  root : Digest
  observeCapability : Option CapabilityId := none
  audienceEpoch : Option Nat := none
  audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster := none
  deriving DecidableEq, Repr

def Role.target (r : Role) (payload : Payload) : Target :=
  ⟨r.kind,r.resource,r.capability,r.schemaVersion,r.root,payload,
    r.observeCapability,r.audienceEpoch,r.audienceRoster⟩
def roleStream : StreamCodec Role := StreamCodec.xmap targetStream
  (fun r => r.target .read)
  (fun t => ⟨t.kind,t.target,t.capability,t.schemaVersion,t.expectedTargetRoot,
    t.observeCapability,t.audienceEpoch,t.audienceRoster⟩)
  (by intro r; cases r; rfl)

structure Source where
  ref : ObjectiveInvocationClaim.InputRef
  atom : Digest
  expectedArtifact : List UInt8
  expectedPackage : List UInt8
  envelope : List UInt8
  deriving DecidableEq, Repr

def sourceStream : StreamCodec Source := StreamCodec.xmap
  (StreamCodec.product ObjectiveInvocationClaim.inputRefStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream bytesStream))))
  (fun s => (s.ref,s.atom,s.expectedArtifact,s.expectedPackage,s.envelope))
  (fun s => ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2⟩)
  (by intro s; cases s; rfl)

/-- Index is intentionally absent: it is a location in a future derived command,
not part of payer consent or fee-first computation. -/
structure Funding where
  payer : Nat
  capability : CapabilityId
  asset : Nat
  credits : Nat
  expectedPayerBalance : Int
  expectedBookRoot : Digest
  deriving DecidableEq, Repr

def Funding.input (f : Funding) (index : Nat) : FundingInput :=
  ⟨index,f.payer,f.capability,f.asset,f.credits,f.expectedPayerBalance,f.expectedBookRoot⟩
def fundingStream : StreamCodec Funding := StreamCodec.xmap
  (StreamCodec.product StreamCodec.nat
    (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product IntStream.intStream digestStream)))))
  (fun f => (f.payer,f.capability,f.asset,f.credits,f.expectedPayerBalance,f.expectedBookRoot))
  (fun f => ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,f.2.2.2.2.2⟩)
  (by intro f; cases f; rfl)

structure Request where
  subject : SubjectId
  nonce : Nat
  source : Source
  arguments : List UInt8
  inputRefs : List ObjectiveInvocationClaim.InputRef
  inputEnvelopes : List (List UInt8)
  capacity : ObjectiveInvocationClaim.Capacity
  inputCodec : Digest
  outputCodec : Digest
  roles : List Role
  resultResource : Nat
  funding : Option Funding
  deriving DecidableEq, Repr

def requestStream : StreamCodec Request := StreamCodec.xmap
  (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
  (StreamCodec.product StreamCodec.nat (StreamCodec.product sourceStream
  (StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.list ObjectiveInvocationClaim.inputRefStream)
  (StreamCodec.product (StreamCodec.list bytesStream) (StreamCodec.product ObjectiveInvocationClaim.capacityStream
  (StreamCodec.product digestStream (StreamCodec.product digestStream (StreamCodec.product (StreamCodec.list roleStream)
  (StreamCodec.product StreamCodec.nat (StreamCodec.option fundingStream))))))))))))
  (fun r => (r.subject,r.nonce,r.source,r.arguments,r.inputRefs,r.inputEnvelopes,
    r.capacity,r.inputCodec,r.outputCodec,r.roles,r.resultResource,r.funding))
  (fun r => ⟨r.1,r.2.1,r.2.2.1,r.2.2.2.1,r.2.2.2.2.1,r.2.2.2.2.2.1,
    r.2.2.2.2.2.2.1,r.2.2.2.2.2.2.2.1,r.2.2.2.2.2.2.2.2.1,
    r.2.2.2.2.2.2.2.2.2.1,r.2.2.2.2.2.2.2.2.2.2.1,r.2.2.2.2.2.2.2.2.2.2.2⟩)
  (by intro r; cases r; rfl)

-- 3: the envelope carries `replayBytes`, `coreBytes` (GPT-6 row E work account).
-- 4: the envelope carries `domainWork` (A3 domain pricing).
def frame : List UInt8 := "DREGG/OBJECTIVE-BEND/LOCAL-REQUEST".toUTF8.toList ++ [4]
def codec : LawfulCodec Request := NativeHostCodec.framed frame requestStream

def queryFor (subject : SubjectId) (nonce : Nat) (ref : ObjectiveInvocationClaim.InputRef) : NativeObservationCodec.Intent :=
  ⟨subject,nonce,.query ⟨ref.kind,ref.resource,.resourceScope⟩,[⟨ref.kind,ref.resource,ref.capability⟩]⟩

/-- Public bundle refusal precedes native signature/policy IO. Full actual
policy-work/funding bounds are imposed by the same receiving input factory. -/
def wellFormed (r : Request) : Bool :=
  decide (r.inputRefs.map ObjectiveInvocationClaim.InputRef.resource).Nodup &&
  decide (r.inputRefs.length = r.inputEnvelopes.length) &&
  decide (r.roles.map Role.resource).Nodup &&
  decide (r.inputRefs.length + 1 ≤ NativeObservationCodec.maxBatchReads) &&
  decide (r.inputRefs.length + 1 ≤ r.capacity.incidences) &&
  decide ((r.source.envelope.length + (r.inputEnvelopes.map List.length).sum) ≤ r.capacity.turnBytes) &&
  decide ((r.source.envelope.length + (r.inputEnvelopes.map List.length).sum) ≤ NativeObservationCodec.maxBatchBytes)

def decode (bytes : List UInt8) : Option Request := do
  if bytes.length > FnEvidenceCodec.maxHostFrameBytes then none else do
    let r ← codec.decode bytes
    if wellFormed r then some r else none

theorem decoded_canonical {bytes : List UInt8} {request : Request}
    (h : decode bytes = some request) : codec.encode request = bytes := by
  unfold decode at h
  split at h
  · cases h
  · match hr : codec.decode bytes with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      change (if wellFormed r = true then some r else none) = some request at h
      split at h
      · cases Option.some.inj h
        exact NativeHostCodec.framed_canonical frame requestStream hr
      · cases h

#assert_axioms decoded_canonical
end Minidregg.Compiler.ObjectiveBendQuoteRequest
