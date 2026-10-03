/- Native private endpoint boundary. Decoding returns CLAIMS only. The source
receiver must select current enrollment, signatures and funded source history.
Backend progress is deliberately not Qualified or a terminal joint decision.
-/
import Compiler.ContentControlFrame
import Compiler.PrivateSuccessorCustodyCodec
import Theory.AssertAxioms
namespace Minidregg.Compiler.JointBackendPartyCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.PrivateSuccessorCustodyCodec
open Minidregg.Kernel.PrivateSuccessorCustody
set_option autoImplicit false

structure Party where
  protocol : Nat
  generation : GenerationKey
  authorityEpoch : Nat
  session : List UInt8
  party : Nat
  recipient : Nat
  recipientRole : List UInt8
  subject : SubjectId
  keyEpoch : Nat
  keyBinding : List UInt8
  credentialPurpose : List UInt8
  deriving DecidableEq

def partySourceStream : StreamCodec Party :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product generationStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream bytesStream))))))))))
    (fun p => (p.protocol,p.generation,p.authorityEpoch,p.session,p.party,p.recipient,
      p.recipientRole,p.subject,p.keyEpoch,p.keyBinding,p.credentialPurpose))
    (fun (p,g,e,s,i,r,role,subject,k,b,purpose) => ⟨p,g,e,s,i,r,role,subject,k,b,purpose⟩)
    (by intro p; cases p; rfl)

def u16Bytes (n : Nat) : List UInt8 := [UInt8.ofNat n,UInt8.ofNat (n / 256)]
def Party.bounded (p : Party) : Bool :=
  decide (p.protocol < 4) && decide (p.party < 65536) && decide (p.recipient < 65536) &&
    !p.recipientRole.isEmpty && !p.credentialPurpose.isEmpty

/-- EXACT backend wire. Fixed IDs are u16LE; full Generation is its existing
native codec inside bytes(), with arbitrary Nat dimensions preserved. -/
def partyWire (p : Party) : List UInt8 :=
  "DREGG.PRIVATE.COMMITTEE.PARTY".toUTF8.toList ++ [1,UInt8.ofNat p.protocol] ++
  bytesStream.encode (generationStream.encode p.generation) ++
  StreamCodec.nat.encode p.authorityEpoch ++ bytesStream.encode p.session ++
  u16Bytes p.party ++ u16Bytes p.recipient ++ bytesStream.encode p.recipientRole ++
  bytesStream.encode (TypedAuthorizationRequestCodec.subjectIdStream.encode p.subject) ++
  StreamCodec.nat.encode p.keyEpoch ++ bytesStream.encode p.keyBinding ++
  bytesStream.encode p.credentialPurpose

structure Enrollment where
  party : Party
  invocationCapability : CapabilityId
  candidateBytes : List UInt8
  participant : Nat
  descriptorBytes : List UInt8
  deriving DecidableEq

def capabilityIdStream : StreamCodec CapabilityId :=
  StreamCodec.xmap StreamCodec.nat (fun c => c.value) (fun n => ⟨n⟩)
    (by intro c; cases c; rfl)

def enrollmentStream : StreamCodec Enrollment :=
  StreamCodec.xmap (StreamCodec.product partySourceStream
    (StreamCodec.product capabilityIdStream
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat bytesStream))))
    (fun e => (e.party,e.invocationCapability,e.candidateBytes,e.participant,e.descriptorBytes))
    (fun (p,c,b,i,d) => ⟨p,c,b,i,d⟩) (by intro e; cases e; rfl)
def manifestStream : StreamCodec (List Enrollment) := StreamCodec.list enrollmentStream

/-- Source-pinned endpoint contract; paths and process handles remain local,
but worker semantics, route and complete ten-lane capacity are source semantics. -/
inductive EndpointPrivacy
  | trustedControllerClear
  | recipientSealed
  deriving DecidableEq

def privacyStream : StreamCodec EndpointPrivacy :=
  StreamCodec.xmap StreamCodec.bool
    (fun p => match p with | .trustedControllerClear => false | .recipientSealed => true)
    (fun b => if b then .recipientSealed else .trustedControllerClear)
    (by intro p; cases p <;> rfl)

structure EndpointPin where
  manifest : ContentControlFrame.Pin
  protocol : Nat
  recipient : Nat
  recipientRole : List UInt8
  workerProfile : Digest
  privacy : EndpointPrivacy
  dispatchCapacity : Minidregg.Theory.ResourceCost.Charge

def endpointPinStream : StreamCodec EndpointPin :=
  StreamCodec.xmap (StreamCodec.product ContentControlFrame.pinStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product bytesStream (StreamCodec.product digestStream
      (StreamCodec.product privacyStream DurableReceiverCodec.chargeStream))))))
    (fun p => (p.manifest,p.protocol,p.recipient,p.recipientRole,p.workerProfile,p.privacy,p.dispatchCapacity))
    (fun (m,p,r,role,w,privacy,c) => ⟨m,p,r,role,w,privacy,c⟩) (by intro p; cases p; rfl)

structure PacketClaim where
  recordBytes : List UInt8
  sequenceBytes : List UInt8
  message : List UInt8
  credential : List UInt8

def ingressFrame : List UInt8 := "DREGG.PRIVATE.INGRESS".toUTF8.toList ++ [1]
def authFrame : List UInt8 := "DREGG.PRIVATE.AUTH".toUTF8.toList ++ [1]
def signingFrame : List UInt8 := "DREGG.PRIVATE.AUTH.SIGN".toUTF8.toList ++ [1]
def PacketClaim.signingBytes (p : PacketClaim) : List UInt8 :=
  signingFrame ++ bytesStream.encode p.recordBytes ++ p.sequenceBytes ++ bytesStream.encode p.message
def PacketClaim.authBytes (p : PacketClaim) : List UInt8 :=
  authFrame ++ bytesStream.encode p.recordBytes ++ p.sequenceBytes ++
    bytesStream.encode p.message ++ bytesStream.encode p.credential
def PacketClaim.carrierBytes (p : PacketClaim) : List UInt8 :=
  ingressFrame ++ bytesStream.encode p.authBytes

/-- Parsing is not authentication. It preserves exact fixed u64LE sequence
bytes and refuses trailing bytes, oversized carriers, and noncanonical frames. -/
def decodeCarrier (wire : List UInt8) : Option PacketClaim := do
  if wire.length > 131100 || wire.take ingressFrame.length != ingressFrame then none else
  let (auth,outerTail) ← bytesStream.decodePrefix (wire.drop ingressFrame.length)
  if !outerTail.isEmpty || auth.take authFrame.length != authFrame then none else
  let (record,afterRecord) ← bytesStream.decodePrefix (auth.drop authFrame.length)
  if afterRecord.length < 8 then none else
  let sequence := afterRecord.take 8
  let (message,afterMessage) ← bytesStream.decodePrefix (afterRecord.drop 8)
  let (credential,tail) ← bytesStream.decodePrefix afterMessage
  if !tail.isEmpty then none else
  let claim : PacketClaim := ⟨record,sequence,message,credential⟩
  if claim.carrierBytes != wire then none else some claim

structure Request where
  candidateBytes : List UInt8
  participant : Nat
  fullGenerationBytes : List UInt8
  manifestRoot : Digest
  rawCarrier : List UInt8
def requestStream : StreamCodec Request :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream
    (StreamCodec.product digestStream bytesStream))))
    (fun r => (r.candidateBytes,r.participant,r.fullGenerationBytes,r.manifestRoot,r.rawCarrier))
    (fun (c,i,g,m,p) => ⟨c,i,g,m,p⟩) (by intro r; cases r; rfl)
def requestFrame : List UInt8 := "DREGG.JOINT.PRIVATE.REQUEST".toUTF8.toList ++ [1]
def requestBytes (request : Request) : List UInt8 := requestFrame ++ requestStream.encode request
def decodeRequest (bytes : List UInt8) : Option Request := do
  if bytes.length > 262078 || bytes.take requestFrame.length != requestFrame then none else
  let request ← requestStream.toLawful.decode (bytes.drop requestFrame.length)
  if requestBytes request != bytes then none else some request

structure ProgressClaim where
  requestBytes : List UInt8
  descriptorBytes : List UInt8
  sourceRecordBytes : List UInt8
  sourceReceiptBytes : List UInt8
  backendProgressBytes : List UInt8
  deriving DecidableEq
def progressStream : StreamCodec ProgressClaim :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream))))
    (fun p => (p.requestBytes,p.descriptorBytes,p.sourceRecordBytes,p.sourceReceiptBytes,p.backendProgressBytes))
    (fun (r,d,s,receipt,b) => ⟨r,d,s,receipt,b⟩) (by intro p; cases p; rfl)

/-- Stable response tags:0 refusal,1 unknown exact request/prior source receipt,
2 durable progress. NO Qualified/result/YES variant exists at this boundary. -/
inductive OutcomeClaim
  | refused (reason : Nat)
  | unknown (requestBytes sourceReceiptBytes : List UInt8)
  | progress (claim : ProgressClaim)
def outcomeFrame : List UInt8 := "DREGG.JOINT.PRIVATE.OUTCOME".toUTF8.toList ++ [1]
def outcomeBytes (claim : OutcomeClaim) : List UInt8 :=
  outcomeFrame ++ match claim with
  | .refused n => [0] ++ StreamCodec.nat.encode n
  | .unknown r p => [1] ++ (StreamCodec.product bytesStream bytesStream).encode (r,p)
  | .progress p => [2] ++ progressStream.encode p
def decodeOutcome (wire : List UInt8) : Option OutcomeClaim := do
  if wire.length > 262070 || wire.take outcomeFrame.length != outcomeFrame then none else
  let body := wire.drop outcomeFrame.length
  let tag ← body.head?
  let payload := body.drop 1
  let claim ←
    if tag == 0 then OutcomeClaim.refused <$> StreamCodec.nat.toLawful.decode payload
    else if tag == 1 then do
      let (r,p) ← (StreamCodec.product bytesStream bytesStream).toLawful.decode payload
      some (.unknown r p)
    else if tag == 2 then OutcomeClaim.progress <$> progressStream.toLawful.decode payload
    else none
  if outcomeBytes claim != wire then none else some claim

theorem request_source_roundtrip (request : Request) (suffix : List UInt8) :
    requestStream.decodePrefix (requestStream.encode request ++ suffix) = some (request,suffix) :=
  requestStream.decodePrefix_encode request suffix
#assert_axioms request_source_roundtrip
end Minidregg.Compiler.JointBackendPartyCodec
