/-
# Kernel.FleetTurnCodec — the bytes of a signed fleet turn

The command (`Command`: subject, payer, spend, nonce, fee, optional transfer and
publication), its framed codec, the signed ingress around it and `decodeIngress`
(command and envelope both decode canonically). Split out of `Kernel.FleetTurn`
so that the durable index (`Compiler.DurableIndexFamilies`, families 6 and 7:
the payer of a fleet turn and the destination of its transfer) decodes exactly
what the fleet controller decodes, below the controller's closure (which imports
the durable receiver).
-/
import Compiler.NativeHostFrame
import Compiler.CredentialSignatureAdmission
import Compiler.CredentialAuthorityEntryCodec
import Compiler.TypedAuthorizationRequestCodec

namespace Minidregg.Kernel.FleetTurn

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

structure Transfer where
  destination : Nat
  asset : Nat
  amount : Nat
  deriving DecidableEq, Repr

structure Publication where
  topic : List UInt8
  sequence : Nat
  payload : List UInt8
  deriving DecidableEq, Repr

/-- `fee` is stated by the signer and must equal the pinned base tariff, so
the signature is a statement about the exact debit. -/
structure Command where
  subject : SubjectId
  payer : Nat
  spend : CapabilityId
  nonce : Nat
  fee : Nat
  transfer : Option Transfer
  publication : Option Publication
  deriving DecidableEq, Repr

def transferStream : StreamCodec Transfer :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))
    (fun t => (t.destination, t.asset, t.amount))
    (fun (destination, asset, amount) => ⟨destination, asset, amount⟩)
    (by intro t; cases t; rfl)

def publicationStream : StreamCodec Publication :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat bytesStream))
    (fun p => (p.topic, p.sequence, p.payload))
    (fun (topic, sequence, payload) => ⟨topic, sequence, payload⟩)
    (by intro p; cases p; rfl)

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product capabilityIdStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product (StreamCodec.option transferStream)
                (StreamCodec.option publicationStream)))))))
    (fun c => (c.subject, c.payer, c.spend, c.nonce, c.fee, c.transfer, c.publication))
    (fun (subject, payer, spend, nonce, fee, transfer, publication) =>
      ⟨subject, payer, spend, nonce, fee, transfer, publication⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/FLEET/TURN/v1".toUTF8.toList

def commandCodec : LawfulCodec Command :=
  NativeHostCodec.framed commandFrame commandStream

structure Ingress where
  commandBytes : List UInt8
  envelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelope))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  NativeHostCodec.framed "DREGG/FLEET/TURN/SIGNED/v1".toUTF8.toList ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelope =
    some envelope

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
    match envelopeExact :
        CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command,
        NativeHostCodec.framed_canonical commandFrame commandStream commandExact,
        envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

end Minidregg.Kernel.FleetTurn
