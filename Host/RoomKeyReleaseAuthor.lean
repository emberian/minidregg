/- Closed authoring/inspection for the source-owned room release body. These
operations parse data and never authorize disclosure. The current-source event
67 controller/Applied lookup is a separate producer. No shared Main hooks or
legacy profile changes are made here. -/
import Compiler.RoomKeyReleaseCodec
import Lean

namespace Minidregg.Host.RoomKeyReleaseAuthor
open Lean
open Minidregg.Compiler.RoomKeyReleaseCodec
open Minidregg.Compiler.CurrentRecipientRecord
set_option autoImplicit false

private def field (j : Json) (name : String) : Except String Json :=
  j.getObjVal? name

private def nat (j : Json) : Except String Nat := do
  match j with
  | .str s =>
      let some n := s.toNat? | throw "expected canonical nonnegative decimal"
      if toString n != s then throw "noncanonical decimal" else pure n
  | _ => j.getNat?

private def digit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def hexChars : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest => do
      let hi ← digit hi
      let lo ← digit lo
      let tail ← hexChars rest
      pure (UInt8.ofNat (hi * 16 + lo) :: tail)
  | _ => none

private def bytes (j : Json) : Except String (List UInt8) := do
  let s ← j.getStr?
  if s.length > 4096 then throw "hex field exceeds2048bytes"
  let some out := hexChars s.toList | throw "expected canonical lowercase hexadecimal"
  pure out

private def hex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[b.toNat / 16]!,digits[b.toNat % 16]!])

private def delivery (j : Json) : Except String Delivery := do
  pure ⟨← nat (← field j "member"),← bytes (← field j "recordHex"),
    ← nat (← field j "roomCapability"),← bytes (← field j "entitlementEnvelopeHex"),
    ← bytes (← field j "ciphertextCommitmentHex"),← nat (← field j "atom")⟩

/-- The input is a full explicit canonical release declaration. No recipient,
actor, epoch, authority root or capability is inferred from an operator view. -/
def author (j : Json) : Except String (List UInt8) := do
  let tag ← (← field j "type").getStr?
  if tag != "minidregg-room-release-request-v1" then throw "wrong release request type"
  let entries ← (← field j "deliveries").getArr?
  if entries.size = 0 ∨ entries.size > 64 then throw "release requires1..64deliveries"
  let deliveries ← entries.toList.mapM delivery
  let prior ← field j "priorEpoch"
  let priorEpoch ← if prior = .null then pure none else some <$> nat prior
  let r : Request := ⟨← nat (← field j "room"),← nat (← field j "keysCell"),
    ← nat (← field j "decisionCell"),⟨← nat (← field j "keysRoot")⟩,
    ⟨← nat (← field j "decisionRoot")⟩,⟨← nat (← field j "authorityRoot")⟩,
    priorEpoch,← bytes (← field j "priorIdentityHex"),← bytes (← field j "certificateHex"),
    ⟨← nat (← field j "actor")⟩,← nat (← field j "capability"),
    ← bytes (← field j "operationHex"),deliveries⟩
  let some e := decodeEpoch r.certificate | throw "noncanonical epoch certificate192"
  if r.room ≥ 2^64 ∨ r.keysCell ≥ 2^64 ∨ r.actor.value ≥ 2^64 ∨
      r.operation.length != 32 ∨ r.priorIdentity.length != 32 ∨
      e.room != r.room ∨ e.keysCell != r.keysCell ∨ r.decisionCell != r.keysCell ∨
      r.decisionRoot != r.keysRoot then throw "release scope/width/root mismatch"
  if ¬ (r.deliveries.map Delivery.member).Nodup ∨ ¬ (r.deliveries.map Delivery.atom).Nodup then
    throw "duplicate delivery recipient or atom"
  match r.priorEpoch with
  | none =>
      if e.epoch != 0 ∨ e.parent != List.replicate 32 0 ∨
          r.priorIdentity != List.replicate 32 0 ∨ e.signer != r.actor then
        throw "invalid release genesis"
  | some prior =>
      if ¬ ((e.epoch = prior ∧ e.identity = r.priorIdentity) ∨
          (e.epoch = prior + 1 ∧ e.parent = r.priorIdentity ∧ e.signer = r.actor)) then
        throw "release epoch does not retain or extend prior identity"
  for d in r.deliveries do
    let some c := Minidregg.Compiler.CurrentRecipientRecord.decode ⟨d.member⟩ d.record | throw "noncanonical signed recipient148"
    if c.room != r.room ∨ c.keysCell != r.keysCell ∨ d.ciphertextCommitment.length != 32 ∨
        d.atom != (e.epoch + 1) * 2^96 + c.epoch * 2^64 + d.member then
      throw "delivery scope/commitment/address mismatch"
    if !d.entitlementEnvelope.isEmpty then
      throw "room release v1 uses source-stored offline entitlement, envelope must be empty"
  pure (encode r)

/-- Inspection exposes exact bound data, never a current key or Applied token. -/
def inspect (wire : List UInt8) : Except String Json := do
  let some r := Minidregg.Compiler.RoomKeyReleaseCodec.decode wire | throw "noncanonical room release wire"
  pure (Json.mkObj [
    ("type",.str "minidregg-room-release-request-v1"),("room",.str (toString r.room)),
    ("keysCell",.str (toString r.keysCell)),("decisionCell",.str (toString r.decisionCell)),
    ("keysRoot",.str (toString r.keysRoot.value)),("decisionRoot",.str (toString r.decisionRoot.value)),
    ("authorityRoot",.str (toString r.authorityRoot.value)),
    ("priorEpoch",r.priorEpoch.map (fun n => Json.str (toString n)) |>.getD .null),
    ("priorIdentityHex",.str (hex r.priorIdentity)),("certificateHex",.str (hex r.certificate)),
    ("actor",.str (toString r.actor.value)),("capability",.str (toString r.capability)),
    ("operationHex",.str (hex r.operation)),("deliveries",.arr (r.deliveries.map fun d =>
      Json.mkObj [("member",.str (toString d.member)),("recordHex",.str (hex d.record)),
        ("roomCapability",.str (toString d.roomCapability)),
        ("entitlementEnvelopeHex",.str (hex d.entitlementEnvelope)),
        ("ciphertextCommitmentHex",.str (hex d.ciphertextCommitment)),
        ("atom",.str (toString d.atom))]).toArray)])
end Minidregg.Host.RoomKeyReleaseAuthor
