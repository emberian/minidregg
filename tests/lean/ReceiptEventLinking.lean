/- Planted receipt-linking probe (K-RECEIPT-HIDE, `Kernel.ReceiptEventHiding`).

An observer holds a receipt from op 102 and two candidate commands that differ
only in a hidden body (a stream append of "yes" or "no"), under one subject and
one nonce, so both candidates have the same transaction id. It knows the domain,
the semantics and every byte of both commands. It does not hold the signer's
authority envelope.

Scope: this probes the event-id function on the receipt path, with an opaque
stand-in for the signature; it is not accepted-path evidence and not the
cryptographic argument (`Kernel.ReceiptEventHiding` states that).

Run: `lake env lean --load-dynlib=.lake/native/libmini_kernels_lean.so tests/lean/ReceiptEventLinking.lean`
(the hashes are compiled kernels). Every `#guard` is evaluated, so a failure is
an elaboration error. -/
import Kernel.ReceiptEventHiding

namespace ReceiptEventLinking
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.ReceiptEventHiding
open Minidregg.Theory.TypedAuthorization

def domain : Digest := ⟨7001⟩
def semantics : Digest := ⟨7002⟩

def appendOf (body : String) : Minidregg.Compiler.StreamCell.Append :=
  { topic := "inbox".toUTF8.toList, payload := body.toUTF8.toList, recipient := none, ref := none }

def targetOf (body : String) : Target :=
  { kind := .object, target := 5, capability := ⟨3⟩, schemaVersion := 1,
    expectedTargetRoot := ⟨77⟩, payload := .append (appendOf body) }

def candidate (body : String) : Command :=
  { subject := ⟨41⟩, nonce := 9, targets := [targetOf body] }

def yes := candidate "yes"
def no := candidate "no"

/-- The honest signer's ingress: the authority envelope is a signature the
observer never sees (64 opaque bytes here; the id computation does not verify it). -/
def signedWith (command : Command) (signature : List UInt8) : SignedCommand :=
  { commandBytes := commandCodec.encode command, targetEnvelopes := [signature],
    observeEnvelopes := [], authorityEnvelope := signature }

def secretSignature : List UInt8 := (List.range 64).map fun index => UInt8.ofNat (index * 37 + 11)

/-- The receipt's event id: world "yes" was submitted. -/
def receiptEventId : Digest := (invocationEvent domain semantics yes (signedWith yes secretSignature)).eventId

-- Legal challenge: one transaction id, two different hidden bodies.
#guard transactionId domain semantics yes = transactionId domain semantics no
#guard yes ≠ no

-- The retired id linked the receipt to "yes": the observer's own hash of the
-- candidate matches the old fingerprint and the other candidate does not.
def retiredEventId : Digest := effectsDigest domain semantics yes
#guard retiredEventId = effectsHash (commandBytes domain semantics yes)
#guard retiredEventId ≠ effectsHash (commandBytes domain semantics no)

-- The current id: neither candidate's public fingerprint matches it.
#guard receiptEventId ≠ effectsHash (commandBytes domain semantics yes)
#guard receiptEventId ≠ effectsHash (commandBytes domain semantics no)

-- Nor does the observer's own hash of either candidate's signed ingress under
-- any envelope it can guess (empty, all zeros, and the other world's shape).
def guesses : List (List UInt8) := [[], List.replicate 64 0, List.replicate 64 255]
#guard guesses.all fun guess =>
  [yes, no].all fun command =>
    eventIdOfSigned (signedBytes domain semantics (signedWith command guess)) != receiptEventId

-- The id is bound to the signature: same command, another signature, another id.
#guard (invocationEvent domain semantics yes (signedWith yes (List.replicate 64 1))).eventId ≠ receiptEventId

-- The submitter, who holds its own signed ingress, recomputes its receipt's id.
#guard eventIdOfSigned (signedBytes domain semantics (signedWith yes secretSignature)) = receiptEventId

end ReceiptEventLinking
