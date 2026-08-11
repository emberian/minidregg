/-
# Compiler.FramedWalRecoveryController -- Lean-owned recovery from opaque bytes

The kernel's framed WAL model deliberately stops before a storage reader or
native runtime.  This module supplies the executable controller boundary.  An
arbitrary external reader may return only one byte string or an opaque error.
Lean then, and only then:

* checks pinned controller, semantic-domain, and codec identifiers;
* splits a fixed-width framed stream;
* checks each frame's magic, version, checksum, and payload decoder;
* replays decoded `DurableDataIntent`s from the exact supplied checkpoint;
* rechecks read guards, pre-roots, nullifiers, budget, and replay identity;
* constructs `VerifiedRecovery` only for the resulting coherent snapshot.

The fixed frame width is a deployment pin, not a limitation of the kernel
model.  A variable-length production format can instantiate another
Lean-owned outer stream codec while retaining the same checked frame/replay
boundary.

**Trust ceiling.**  No theorem here says that bytes came from a disk, that a
reader observed an atomic file, that `fsync` worked, or that a native codec is
correct.  The reader remains completely opaque and fallible.  Success says
only that the exact returned bytes passed this Lean controller against the
exact checkpoint.
-/
import Kernel.FramedWalRefinement
import Kernel.DurableDataIntent

namespace Minidregg.Compiler.FramedWalRecoveryController

open Minidregg.Theory
open Minidregg.Kernel.FramedWalRefinement
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-! ## Deployment pins and wire failures -/

/-- Three outer routing bytes and the complete inner frame shape.  These are
Lean data checked before any payload obtains semantic meaning. -/
structure Pins where
  controllerId : UInt8
  domainId : UInt8
  codecId : UInt8
  frameMagic : UInt8
  frameVersion : UInt8
  frameWidth : Nat
  deriving DecidableEq, Repr

/-- A Lean-owned controller pairs pinned wire identity with the fallible
payload/frame decoder. -/
structure Controller (rootBytes : List UInt8 -> TypedAuthorization.Digest) where
  pins : Pins
  frameCodec : FrameCodec (DataIntent rootBytes)
  frameWidthPositive : 0 < pins.frameWidth
  magicPinned : frameCodec.magic = pins.frameMagic
  versionPinned : frameCodec.version = pins.frameVersion

inductive WireFailure
  | truncatedHeader
  | wrongController
  | wrongDomain
  | wrongCodec
  | truncatedFrame
  | invalidFrame
  deriving DecidableEq, Repr

inductive RecoveryFailure
  | rejected (reason : Minidregg.Kernel.DurableDataIntent.RejectReason)
  | mismatchedPayload
  | unexpectedCrash (point : Minidregg.Kernel.DurableCommitProtocol.CrashPoint)
  deriving DecidableEq, Repr

inductive Failure (Error : Type)
  | native (error : Error)
  | wire (reason : WireFailure)
  | recovery (reason : RecoveryFailure)
  deriving Repr

/-! ## Executable outer framing and Lean frame decoding -/

namespace Controller

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}

/-- Fuel-bounded fixed-width stream decoder.  Fuel begins at the byte length,
so positive frame width suffices for all well-framed inputs; malformed zero
progress can only reach `truncatedFrame`, never nontermination. -/
def decodeFramesFuel (controller : Controller rootBytes) :
    Nat -> List UInt8 ->
      Except WireFailure (List (DataIntent rootBytes))
  | 0, [] => .ok []
  | 0, _ :: _ => .error .truncatedFrame
  | _ + 1, [] => .ok []
  | fuel + 1, bytes =>
      if bytes.length < controller.pins.frameWidth then
        .error .truncatedFrame
      else
        let frame := bytes.take controller.pins.frameWidth
        let suffix := bytes.drop controller.pins.frameWidth
        match controller.frameCodec.decodeFrame frame with
        | none => .error .invalidFrame
        | some intent =>
            match decodeFramesFuel controller fuel suffix with
            | .error reason => .error reason
            | .ok rest => .ok (intent :: rest)

/-- The outer three-byte header pins controller/domain/codec identity before
the framed stream is interpreted. -/
def decodeWire (controller : Controller rootBytes) (bytes : List UInt8) :
    Except WireFailure (List (DataIntent rootBytes)) :=
  match bytes with
  | returnedController :: returnedDomain :: returnedCodec :: frames =>
      if returnedController != controller.pins.controllerId then
        .error .wrongController
      else if returnedDomain != controller.pins.domainId then
        .error .wrongDomain
      else if returnedCodec != controller.pins.codecId then
        .error .wrongCodec
      else
        controller.decodeFramesFuel frames.length frames
  | _ => .error .truncatedHeader

end Controller

/-! ## Exact guarded replay -/

/-- Execute one recovered data intent.  Complete execution can accept or
idempotently replay.  A same-id/different-payload record receives its own
failure so the byte boundary cannot disguise it as ordinary staleness. -/
def replayOne {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Except RecoveryFailure (DataSnapshot rootBytes) :=
  match Minidregg.Kernel.DurableDataIntent.execute .complete before intent with
  | .accepted next => .ok next
  | .replayed _ => .ok before
  | .rejected (.durable .transactionConflict) =>
      .error .mismatchedPayload
  | .rejected reason => .error (.rejected reason)
  | .crashed point _ => .error (.unexpectedCrash point)

def replayAll {rootBytes : List UInt8 -> TypedAuthorization.Digest} :
    DataSnapshot rootBytes -> List (DataIntent rootBytes) ->
      Except RecoveryFailure (DataSnapshot rootBytes)
  | snapshot, [] => .ok snapshot
  | snapshot, intent :: rest =>
      match replayOne snapshot intent with
      | .error reason => .error reason
      | .ok next => replayAll next rest

/-! ## Opaque reader boundary and proof-relevant success -/

/-- External authority ends at bytes or an opaque error. -/
abbrev OpaqueRecoveryReader (Error Request : Type) :=
  Request -> Except Error (List UInt8)

/-- Successful recovery retains the exact returned bytes, every exact decoded
data intent, and the exact replay equation which produced its coherent data
snapshot. -/
structure VerifiedRecovery
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (controller : Controller rootBytes)
    (checkpoint : DataSnapshot rootBytes) where
  returnedBytes : List UInt8
  intents : List (DataIntent rootBytes)
  snapshot : DataSnapshot rootBytes
  decoded : controller.decodeWire returnedBytes = .ok intents
  replayed : replayAll checkpoint intents = .ok snapshot

/-- Run the opaque reader, then grant semantic meaning only after Lean-owned
wire decoding and complete guarded replay succeed. -/
def run {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    {Error Request : Type}
    (controller : Controller rootBytes)
    (checkpoint : DataSnapshot rootBytes)
    (reader : OpaqueRecoveryReader Error Request)
    (request : Request) :
    Except (Failure Error) (VerifiedRecovery controller checkpoint) :=
  match reader request with
  | .error error => .error (.native error)
  | .ok bytes =>
      match decoded : controller.decodeWire bytes with
      | .error reason => .error (.wire reason)
      | .ok intents =>
          match replayed : replayAll checkpoint intents with
          | .error reason => .error (.recovery reason)
          | .ok snapshot => .ok ⟨bytes, intents, snapshot, decoded, replayed⟩

/-- Success contains the exact, unnormalized bytes returned by the arbitrary
reader. -/
theorem run_success_reader_bytes
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    {Error Request : Type}
    (controller : Controller rootBytes)
    (checkpoint : DataSnapshot rootBytes)
    (reader : OpaqueRecoveryReader Error Request)
    (request : Request)
    (verified : VerifiedRecovery controller checkpoint)
    (success : run controller checkpoint reader request = .ok verified) :
    reader request = .ok verified.returnedBytes := by
  unfold run at success
  split at success
  next error failed => simp at success
  next bytes returned =>
    split at success
    next reason decodeFailed => simp at success
    next intents decoded =>
      split at success
      next reason replayFailed => simp at success
      next snapshot replayed =>
        simp only [Except.ok.injEq] at success
        subst verified
        exact returned

/-- Main control-integrity result.  No reader behavior is assumed: success
still yields exact returned bytes, exact Lean decoding, exact guarded replay,
and root/byte coherence for every recovered cell. -/
theorem run_success_integrity
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    {Error Request : Type}
    (controller : Controller rootBytes)
    (checkpoint : DataSnapshot rootBytes)
    (reader : OpaqueRecoveryReader Error Request)
    (request : Request)
    (verified : VerifiedRecovery controller checkpoint)
    (success : run controller checkpoint reader request = .ok verified) :
    reader request = .ok verified.returnedBytes ∧
      controller.decodeWire verified.returnedBytes = .ok verified.intents ∧
      replayAll checkpoint verified.intents = .ok verified.snapshot ∧
      forall cellId,
        rootBytes (verified.snapshot.canonicalBytes cellId) =
          verified.snapshot.model.roots cellId :=
  ⟨run_success_reader_bytes controller checkpoint reader request verified success,
    verified.decoded, verified.replayed, verified.snapshot.coherent⟩

/-! ## Closed executable acceptance and rejection teeth -/

namespace ClosedInstance

namespace DataWitness

def lengthRoot := Minidregg.Kernel.DurableDataIntent.Witness.lengthRoot
def intent := Minidregg.Kernel.DurableDataIntent.Witness.intent
def tamperedIntent := Minidregg.Kernel.DurableDataIntent.Witness.tamperedIntent
def before := Minidregg.Kernel.DurableDataIntent.Witness.before
def afterConcurrentReadMove :=
  Minidregg.Kernel.DurableDataIntent.Witness.afterConcurrentReadMove

end DataWitness

def pins : Pins where
  controllerId := 161
  domainId := 73
  codecId := 29
  frameMagic := 215
  frameVersion := 1
  frameWidth := 6

/-- Closed decoder accepts two exact payloads: the honest intent and the
same-id/colliding-root byte-tampered intent.  The latter is included so the
replay controller, rather than the decoder, demonstrates payload-conflict
rejection. -/
def frameCodec : FrameCodec (DataIntent DataWitness.lengthRoot) where
  magic := pins.frameMagic
  version := pins.frameVersion
  encodePayload := fun _ => [10, 20, 30]
  decodePayload := fun payload =>
    if payload = [10, 20, 30] then some DataWitness.intent
    else if payload = [40, 50, 60] then some DataWitness.tamperedIntent
    else none
  checksum := fun bytes => bytes.foldl (fun acc byte => acc + byte) 0

def controller : Controller DataWitness.lengthRoot where
  pins := pins
  frameCodec := frameCodec
  frameWidthPositive := by decide
  magicPinned := rfl
  versionPinned := rfl

@[simp] theorem controller_pin_exact :
    controller.pins.controllerId = 161 ∧
      controller.pins.domainId = 73 ∧
      controller.pins.codecId = 29 ∧
      controller.frameCodec.magic = 215 ∧
      controller.frameCodec.version = 1 := by decide

/-- Construct raw inner-frame bytes from an explicit payload.  This helper is
Lean data, not a trusted native encoder. -/
def frameFor (payload : List UInt8) : List UInt8 :=
  [pins.frameMagic, pins.frameVersion] ++ payload ++
    [frameCodec.checksum (pins.frameVersion :: payload)]

def header : List UInt8 :=
  [pins.controllerId, pins.domainId, pins.codecId]

def honestFrame : List UInt8 := frameFor [10, 20, 30]
def tamperedFrame : List UInt8 := frameFor [40, 50, 60]
def honestBytes : List UInt8 := header ++ honestFrame

def reader (_ : Unit) : Except Unit (List UInt8) := .ok honestBytes

theorem honest_decode :
    controller.decodeWire honestBytes = .ok [DataWitness.intent] := by rfl

theorem honest_replay :
    replayAll DataWitness.before [DataWitness.intent] =
      .ok (DataSnapshot.install DataWitness.before DataWitness.intent) := by rfl

/-- **Positive inhabitant:** exact opaque bytes produce a verified coherent
durable data snapshot. -/
theorem honest_run_accepts :
    exists verified : VerifiedRecovery controller DataWitness.before,
      run controller DataWitness.before reader () = .ok verified ∧
      verified.snapshot =
        DataSnapshot.install DataWitness.before DataWitness.intent := by
  refine ⟨⟨honestBytes, [DataWitness.intent],
    DataSnapshot.install DataWitness.before DataWitness.intent,
    honest_decode, honest_replay⟩, rfl, rfl⟩

def corruptChecksumBytes : List UInt8 :=
  header ++ [pins.frameMagic, pins.frameVersion, 10, 20, 30, 0]

theorem corrupt_checksum_rejected :
    controller.decodeWire corruptChecksumBytes = .error .invalidFrame := by rfl

def truncatedBytes : List UInt8 := header ++ honestFrame.dropLast

theorem truncated_frame_rejected :
    controller.decodeWire truncatedBytes = .error .truncatedFrame := by rfl

def wrongControllerBytes : List UInt8 :=
  0 :: pins.domainId :: pins.codecId :: honestFrame

def wrongDomainBytes : List UInt8 :=
  pins.controllerId :: 0 :: pins.codecId :: honestFrame

def wrongCodecBytes : List UInt8 :=
  pins.controllerId :: pins.domainId :: 0 :: honestFrame

theorem mismatched_controller_rejected :
    controller.decodeWire wrongControllerBytes = .error .wrongController := by rfl

theorem mismatched_domain_rejected :
    controller.decodeWire wrongDomainBytes = .error .wrongDomain := by rfl

theorem mismatched_codec_rejected :
    controller.decodeWire wrongCodecBytes = .error .wrongCodec := by rfl

/-- The exact same record is rejected against a checkpoint whose read-only
guard moved. -/
theorem stale_guard_rejected :
    replayAll DataWitness.afterConcurrentReadMove [DataWitness.intent] =
      .error (.rejected .staleReadGuard) := by rfl

/-- Two valid frames with one transaction id but different canonical post
bytes cannot recover as a replay. -/
def mismatchedPayloadBytes : List UInt8 :=
  header ++ honestFrame ++ tamperedFrame

theorem mismatched_payload_decodes_exactly :
    controller.decodeWire mismatchedPayloadBytes =
      .ok [DataWitness.intent, DataWitness.tamperedIntent] := by rfl

theorem mismatched_payload_rejected :
    replayAll DataWitness.before
      [DataWitness.intent, DataWitness.tamperedIntent] =
      .error .mismatchedPayload := by rfl

def failingReader (_ : Unit) : Except Nat (List UInt8) := .error 404

theorem native_error_blocks :
    run controller DataWitness.before failingReader () =
      .error (.native 404) := rfl

end ClosedInstance

/-! ## Pinned axiom audit -/

/-- info: 'Minidregg.Compiler.FramedWalRecoveryController.run_success_reader_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms run_success_reader_bytes
/-- info: 'Minidregg.Compiler.FramedWalRecoveryController.run_success_integrity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms run_success_integrity
/-- info: 'Minidregg.Compiler.FramedWalRecoveryController.ClosedInstance.honest_run_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.honest_run_accepts
/-- info: 'Minidregg.Compiler.FramedWalRecoveryController.ClosedInstance.corrupt_checksum_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.corrupt_checksum_rejected
/-- info: 'Minidregg.Compiler.FramedWalRecoveryController.ClosedInstance.truncated_frame_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.truncated_frame_rejected
/-- info: 'Minidregg.Compiler.FramedWalRecoveryController.ClosedInstance.stale_guard_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.stale_guard_rejected
/-- info: 'Minidregg.Compiler.FramedWalRecoveryController.ClosedInstance.mismatched_payload_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.mismatched_payload_rejected

end Minidregg.Compiler.FramedWalRecoveryController
