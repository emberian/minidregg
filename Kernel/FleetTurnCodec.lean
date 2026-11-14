/-
The wire form of one signed fleet turn (`Kernel.FleetTurn` gives it meaning): the command,
its framed codec, the signed ingress and its exact decode. It sits below the receiving loop
so the Store's journal index (`Kernel.JournalIndex`) can read which account an accepted turn
was paid by and which account it paid, from the record's own retained ingress.
-/
module

public import Compiler.CredentialSignatureAdmission

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.FleetTurn

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Topic labels are bytes chosen by the account holder. They name a stream
of that account only; the same label under another account is another stream. -/
def maxTopicBytes : Nat := 64
/-- Payloads ride in the signed ingress; the entry cell stores only their digest. -/
def maxPayloadBytes : Nat := 16384

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

/-- The frame, checked, then the command (the host's framed codec, stated here so the journal
index below the receiving loop can decode an accepted turn). -/
def commandCodec : LawfulCodec Command :=
  (StreamCodec.framed commandFrame commandStream).toLawful

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
  (StreamCodec.framed "DREGG/FLEET/TURN/SIGNED/v2".toUTF8.toList ingressStream).toLawful

structure DecodedIngress where
  mk ::
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
        (StreamCodec.framed commandFrame commandStream).toLawful_canonical _ _ commandExact,
        envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

end Minidregg.Kernel.FleetTurn
