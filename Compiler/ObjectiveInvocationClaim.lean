/- Objective invocation requests bind source selection, argument/return ABIs and
all public resource envelopes. They contain neither a caller-selected term nor
a claimed result. Native admission independently loads the current source and
constructs observations from the same authorized snapshot. -/
import Theory.AssertAxioms
import Compiler.NativeInvocationStatement

namespace Minidregg.Compiler.ObjectiveInvocationClaim
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- Distinct counters are not silently converted into one another. The native
implementation checks each operational bound; proofWork and feeDebit select the
source-owned compute quote, not an unmetered or refundable branch count. -/
structure Capacity where
  typeFuel : Nat
  sourceTicks : Nat
  heap : Nat
  stack : Nat
  outputNodes : Nat
  outputBytes : Nat
  inputBytes : Nat
  scalarBits : Nat
  memoryTouches : Nat
  proofWork : Nat
  feeDebit : Nat
  turnBytes : Nat
  witnessBytes : Nat
  storageBytes : Nat
  sideEffectCount : Nat
  networkBytes : Nat
  leaseByteBlocks : Nat
  incidences : Nat
  deriving DecidableEq, Repr

/-- Exact signed observation selector, independent of generated effect targets. -/
structure InputRef where
  kind : ResourceKind
  resource : Nat
  root : Digest
  capability : CapabilityId
  deriving DecidableEq, Repr

def capabilityStream : StreamCodec CapabilityId := StreamCodec.xmap StreamCodec.nat
  CapabilityId.value CapabilityId.mk (by intro c; cases c; rfl)
def inputRefStream : StreamCodec InputRef := StreamCodec.xmap
  (StreamCodec.product ResourceBirthCodec.resourceKindStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream capabilityStream)))
  (fun r => (r.kind,r.resource,r.root,r.capability))
  (fun (k,r,h,c) => ⟨k,r,h,c⟩) (by intro r; cases r; rfl)

structure Claim where
  sourceIndex : Nat
  sourceAtom : Digest
  inputCodec : Digest
  outputCodec : Digest
  arguments : List UInt8
  inputRefs : List InputRef
  inputEnvelopes : List (List UInt8)
  expectedInput : Digest
  capacity : Capacity
  deriving DecidableEq, Repr

def capacityStream : StreamCodec Capacity :=
  StreamCodec.xmap
    (StreamCodec.product
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))))))
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))
    (fun c => ((c.typeFuel,c.sourceTicks,c.heap,c.stack,c.outputNodes,c.outputBytes,
      c.inputBytes,c.scalarBits,c.memoryTouches,c.proofWork,c.feeDebit),
      (c.turnBytes,c.witnessBytes,c.storageBytes,c.sideEffectCount,c.networkBytes,c.leaseByteBlocks,c.incidences)))
    (fun ((t,s,h,k,n,b,i,w,m,p,f),(u,v,x,e,y,l,j)) => ⟨t,s,h,k,n,b,i,w,m,p,f,u,v,x,e,y,l,j⟩)
    (by intro c; cases c; rfl)

def stream : StreamCodec Claim :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream
    (StreamCodec.product (StreamCodec.list inputRefStream)
    (StreamCodec.product (StreamCodec.list bytesStream)
    (StreamCodec.product digestStream capacityStream))))))))
    (fun c => (c.sourceIndex,c.sourceAtom,c.inputCodec,c.outputCodec,c.arguments,
      c.inputRefs,c.inputEnvelopes,c.expectedInput,c.capacity))
    (fun (i,a,c,o,b,r,q,e,p) => ⟨i,a,c,o,b,r,q,e,p⟩) (by intro c; cases c; rfl)

def frame : List UInt8 := "DREGG/OBJECTIVE/INVOCATION-CLAIM/v3".toUTF8.toList

def rawCodec : LawfulCodec Claim where
  encode claim := frame ++ stream.encode claim
  decode bytes := if bytes.take frame.length = frame then
    stream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro claim
    have exact := stream.toLawful.decode_encode claim
    change stream.toLawful.decode (stream.encode claim) = some claim at exact
    simp [exact]

def codec : LawfulCodec Claim := ResourceBirthCodec.strictCodec rawCodec
abbrev encode := codec.encode
/-- Each independently signed query is paired with its exact ordered selector.
Signature, query scope, actor, nonce and current authority are checked by native
admission; syntactic validity never grants read authority. -/
def Valid (claim : Claim) : Prop :=
  (claim.inputRefs.map InputRef.resource).Nodup ∧
    claim.inputEnvelopes.length = claim.inputRefs.length
instance (claim : Claim) : Decidable (Valid claim) := inferInstanceAs
  (Decidable ((claim.inputRefs.map InputRef.resource).Nodup ∧
    claim.inputEnvelopes.length = claim.inputRefs.length))

/-- Duplicate physical resource selections are refused rather than resolved
by first/last wins. Order remains exactly signed. -/
def decode (bytes : List UInt8) : Option Claim := do
  let claim ← codec.decode bytes
  if Valid claim then some claim else none

/-- The bytes here are the actual canonical NativeInput encoding, which does
NOT include this claim or its expectedInput field. -/
def inputCommitment (nativeInputBytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.AUTHENTICATED-INPUT/v1".toUTF8.toList nativeInputBytes).digest

def family (claim : Claim) : NativeInvocationStatement.Family :=
  ⟨.objectiveMethod,encode claim⟩

@[simp] theorem decode_encode (claim : Claim)
    (valid : Valid claim) :
    decode (encode claim) = some claim := by simp [decode,codec.decode_encode,valid]

theorem encode_injective {a b : Claim} (same : encode a = encode b) : a = b := by
  have decoded := congrArg codec.decode same
  simpa only [codec.decode_encode,Option.some.injEq] using decoded

theorem decoded_raw {bytes : List UInt8} {claim : Claim}
    (accepted : decode bytes = some claim) : codec.decode bytes = some claim := by
  simp only [decode] at accepted
  cases parsed : codec.decode bytes with
  | none => simp [parsed] at accepted
  | some actual =>
    simp only [parsed] at accepted
    change (if Valid actual then some actual else none) = some claim at accepted
    split at accepted
    · cases Option.some.inj accepted; rfl
    · contradiction

theorem decoded_valid {bytes : List UInt8} {claim : Claim}
    (accepted : decode bytes = some claim) : Valid claim := by
  simp only [decode] at accepted
  cases parsed : codec.decode bytes with
  | none => simp [parsed] at accepted
  | some actual =>
    simp only [parsed] at accepted
    change (if Valid actual then some actual else none) = some claim at accepted
    split at accepted
    · cases Option.some.inj accepted; assumption
    · contradiction

theorem decoded_unique {bytes : List UInt8} {claim : Claim}
    (accepted : decode bytes = some claim) : (claim.inputRefs.map InputRef.resource).Nodup :=
  (decoded_valid accepted).1

theorem decoded_envelopes {bytes : List UInt8} {claim : Claim}
    (accepted : decode bytes = some claim) : claim.inputEnvelopes.length = claim.inputRefs.length :=
  (decoded_valid accepted).2

theorem decoded_canonical {bytes : List UInt8} {claim : Claim}
    (accepted : decode bytes = some claim) : encode claim = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec (decoded_raw accepted)

theorem family_exact (claim : Claim) (valid : Valid claim) :
    (family claim).route = .objectiveMethod ∧
      decode (family claim).contextBytes = some claim := ⟨rfl,decode_encode claim valid⟩

theorem family_injective {a b : Claim} (same : family a = family b) : a = b :=
  encode_injective (congrArg NativeInvocationStatement.Family.contextBytes same)

#assert_axioms decode_encode
#assert_axioms encode_injective
#assert_axioms decoded_raw
#assert_axioms decoded_valid
#assert_axioms decoded_unique
#assert_axioms decoded_envelopes
#assert_axioms decoded_canonical
#assert_axioms family_exact
#assert_axioms family_injective
end Minidregg.Compiler.ObjectiveInvocationClaim
