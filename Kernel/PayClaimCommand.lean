/-
Closed public paid-claim actions. Prepare and seal carry exactly these canonical
bytes; submit and lookup retain the same ingress. Neither action conveys a
capability to arbitrary programs or a generic command-execution surface.
-/
import Kernel.PayEnrolClaim
import Kernel.SubjectKeyRotation

namespace Minidregg.Kernel.PayClaimCommand
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.IndexedProgram (LawfulCodec)
set_option autoImplicit false

structure RotatePendingOwner where
  ownerIdentityKey : List UInt8
  expectedEpoch : Nat
  nonce : Nat
  successorKey : List UInt8
  successorNextKeyDigest : Digest
  deriving DecidableEq, Repr

def rotationStream : StreamCodec RotatePendingOwner :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream digestStream))))
    (fun r => (r.ownerIdentityKey, r.expectedEpoch, r.nonce, r.successorKey, r.successorNextKeyDigest))
    (fun (identity, epoch, nonce, successor, next) => ⟨identity, epoch, nonce, successor, next⟩)
    (by intro r; cases r; rfl)

abbrev Action := Sum PayEnrolClaim.AcceptRequest RotatePendingOwner

def Action.valid : Action → Prop
  | .inl request => request.valid ∧ request.nonce < 2 ^ 64
  | .inr rotation => rotation.ownerIdentityKey.length = 32 ∧
      0 < rotation.expectedEpoch ∧ rotation.expectedEpoch < 2 ^ 64 - 1 ∧
      rotation.nonce < 2 ^ 64 ∧ rotation.successorKey.length = 32 ∧
      rotation.successorNextKeyDigest.value < 2 ^ 256

instance (action : Action) : Decidable action.valid := by
  cases action <;> unfold Action.valid <;> infer_instance

def actionStream : StreamCodec Action :=
  StreamCodec.sum PayEnrolClaim.acceptRequestStream rotationStream

structure Command where
  expectedAuthorityRoot : Digest
  expectedPayRoot : Digest
  action : Action
  deriving DecidableEq, Repr

def Command.valid (command : Command) : Prop :=
  command.expectedAuthorityRoot.value < 2 ^ 256 ∧
  command.expectedPayRoot.value < 2 ^ 256 ∧ command.action.valid

instance (command : Command) : Decidable command.valid := by
  unfold Command.valid; infer_instance

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream actionStream))
    (fun c => (c.expectedAuthorityRoot, c.expectedPayRoot, c.action))
    (fun (authority, pay, action) => ⟨authority, pay, action⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/PAY/CLAIM/COMMAND/v1".toUTF8.toList

def commandCodec : LawfulCodec Command :=
  ParticipantKeyEnrollment.framed commandFrame commandStream

def Command.signingKey (command : Command) : List UInt8 :=
  match command.action with
  | .inl accept => accept.authorizingKey
  | .inr rotate => rotate.successorKey

def possessionFrame (domain semantics : Digest) (command : Command) : List UInt8 :=
  "DREGG/PAY/CLAIM/POSSESSION/v1".toUTF8.toList ++
    (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, commandCodec.encode command)

/-- Both variants use one Ed25519 signature: current owner for acceptance,
precommitted successor for rotation. The variant tag is inside the signature. -/
structure Ingress where
  commandBytes : List UInt8
  possessionSignature : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun i => (i.commandBytes, i.possessionSignature))
    (fun (command, signature) => ⟨command, signature⟩)
    (by intro i; cases i; rfl)

def ingressFrame : List UInt8 := "DREGG/PAY/CLAIM/SIGNED/v1".toUTF8.toList

def ingressCodec : LawfulCodec Ingress :=
  ParticipantKeyEnrollment.framed ingressFrame ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  signatureShape : ingress.possessionSignature.length = 64
  commandShape : command.valid

def maxIngressBytes : Nat := 4096

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  if bytes.length > maxIngressBytes then none else do
    let ingress ← ingressCodec.decode bytes
    if signatureShape : ingress.possessionSignature.length = 64 then
      match exact : commandCodec.decode ingress.commandBytes with
      | none => none
      | some command =>
        if commandShape : command.valid then
          some ⟨ingress, command,
            ResourceBirthCodec.strictCodec_canonical
              (ParticipantKeyEnrollment.framedRaw commandFrame commandStream) exact,
            signatureShape, commandShape⟩
        else none
    else none

def marker (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG/PAY/CLAIM/OPERATION/v1".toUTF8.toList
    (possessionFrame domain semantics command)).digest

structure Checked (domain semantics : Digest) (ingress : DecodedIngress) where
  private mk ::
  verifier : CredentialSignatureIO.NativeConfig
  valid : Bool

def verifyNative (config : CredentialSignatureIO.NativeConfig) (domain semantics : Digest)
    (ingress : DecodedIngress) : IO (Except CredentialSignatureIO.Error (Checked domain semantics ingress)) := do
  match ← CredentialSignatureIO.verify config ingress.command.signingKey
      (possessionFrame domain semantics ingress.command) ingress.ingress.possessionSignature with
  | .error reason => return .error reason
  | .ok valid => return .ok ⟨config, valid⟩

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command := commandCodec.decode_encode _

theorem ingress_roundtrip (ingress : Ingress) :
    ingressCodec.decode (ingressCodec.encode ingress) = some ingress := ingressCodec.decode_encode _

#assert_axioms command_roundtrip
#assert_axioms ingress_roundtrip
end Minidregg.Kernel.PayClaimCommand
