/-
# `Kernel/ResourcePayloadTag.lean` — a command whose payload tag nothing reads is refused BY NAME

`commandCodec.decode` answers `none` for every byte string that is not a command, and the receiver
called all of them `malformedCommand`. One of them is not malformed: a command, well-formed up to a
target's payload, whose payload tag octet no declaration binds and no hand arm reads (a client
built against a registry this Host does not have). `unboundTag` finds that octet with the command
codec's own component decoders, and `decodeRefusal` names it:
`Reject.effect (.unregistered tag)`, the dispatcher's refusal for a code outside the registry.

`UnboundTagNamed` (proved): a named octet is bound by no declaration and read by no hand arm, and
the bytes that carry it are not a command. So the name is never given to a command the Host
would have run, and never to an octet it reads. Every other undecodable byte string is still
`malformedCommand`.
-/
module

public import Kernel.ResourceTransaction
public import Theory.AssertAxioms

import all Init.Control.Except
import all Init.Data.List.Basic

@[expose] public section

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- The payload tags the hand arms read (`legacyPayloadDecode`). -/
def legacyPayloadTags : List UInt8 := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- An octet no declaration binds and no hand arm reads. -/
def payloadUnread (tag : UInt8) : Bool := !registeredOctet tag && !legacyPayloadTags.contains tag

/-- The payload decoder refuses an unread octet, whatever follows it. -/
theorem payload_unread {tag : UInt8} (unread : payloadUnread tag = true) (bytes : List UInt8) :
    payloadStream.decodePrefix (tag :: bytes) = none := by
  simp only [payloadUnread, Bool.and_eq_true, Bool.not_eq_true'] at unread
  obtain ⟨unbound, outside⟩ := unread
  show (if registeredOctet tag = true then _ else legacyPayloadDecode (tag :: bytes)) = none
  rw [if_neg (by rw [unbound]; exact Bool.false_ne_true)]
  have ne : ∀ k ∈ legacyPayloadTags, tag ≠ k := fun k member same =>
    absurd (List.contains_iff_mem.mpr (same ▸ member)) (by rw [outside]; exact Bool.false_ne_true)
  have h0 := ne 0 (by decide)
  have h1 := ne 1 (by decide)
  have h2 := ne 2 (by decide)
  have h3 := ne 3 (by decide)
  have h4 := ne 4 (by decide)
  have h5 := ne 5 (by decide)
  have h6 := ne 6 (by decide)
  have h7 := ne 7 (by decide)
  have h8 := ne 8 (by decide)
  simp [legacyPayloadDecode, h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-- A target's fields before its payload, as `targetStream` reads them. -/
def targetHeadStream :
    StreamCodec (ResourceKind × Nat × CapabilityId × Nat × Digest) :=
  StreamCodec.product ResourceBirthCodec.resourceKindStream
    (StreamCodec.product StreamCodec.nat
    (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
    (StreamCodec.product StreamCodec.nat digestStream)))

/-- The first unread payload tag among `count` targets: each target's head is read, its payload
tag inspected, and a target whose tag is read is consumed by `targetStream` itself. -/
def unboundTagIn : Nat → List UInt8 → Option UInt8
  | 0, _ => none
  | count + 1, bytes =>
    match targetHeadStream.decodePrefix bytes with
    | some (_, tag :: _) =>
      if payloadUnread tag = true then some tag
      else match targetStream.decodePrefix bytes with
        | some (_, after) => unboundTagIn count after
        | none => none
    | _ => none

/-- A command body up to its targets: subject, nonce, the target count, then the targets. -/
def unboundTagBody (body : List UInt8) : Option UInt8 :=
  match TypedAuthorizationRequestCodec.subjectIdStream.decodePrefix body with
  | some (_, afterSubject) =>
    match StreamCodec.nat.decodePrefix afterSubject with
    | some (_, afterNonce) =>
      match StreamCodec.nat.decodePrefix afterNonce with
      | some (count, targets) => unboundTagIn count targets
      | none => none
    | none => none
  | none => none

/-- **The unread payload tag of command bytes**, under either command frame. -/
def unboundTag (bytes : List UInt8) : Option UInt8 :=
  if bytes.take commandFrame.length = commandFrame then
    unboundTagBody (bytes.drop commandFrame.length)
  else if bytes.take familyCommandFrame.length = familyCommandFrame then
    unboundTagBody (bytes.drop familyCommandFrame.length)
  else none

/-- **What the receiver answers for bytes that are not a command**: the unread payload tag by
name, or `malformedCommand`. -/
def decodeRefusal (bytes : List UInt8) : Reject :=
  match unboundTag bytes with
  | some tag => .effect (.unregistered tag.toNat)
  | none => .malformedCommand

/-- **THE STATEMENT.** A named octet is bound by nothing and read by nothing, and its bytes are
not a command. -/
def UnboundTagNamed : Prop :=
  ∀ bytes tag, unboundTag bytes = some tag →
    registeredOctet tag = false ∧ tag ∉ legacyPayloadTags ∧ commandCodec.decode bytes = none

/-! ## Proof -/

theorem product_right_none {α β : Type} (l : StreamCodec α) (r : StreamCodec β)
    {bytes mid : List UInt8} {a : α} (left : l.decodePrefix bytes = some (a, mid))
    (right : r.decodePrefix mid = none) : (StreamCodec.product l r).decodePrefix bytes = none := by
  simp [StreamCodec.product, left, right]

theorem product_left_none {α β : Type} (l : StreamCodec α) (r : StreamCodec β)
    {bytes : List UInt8} (left : l.decodePrefix bytes = none) :
    (StreamCodec.product l r).decodePrefix bytes = none := by
  simp [StreamCodec.product, left]

theorem product_some {α β : Type} (l : StreamCodec α) (r : StreamCodec β)
    {bytes rest : List UInt8} {value : α × β}
    (decoded : (StreamCodec.product l r).decodePrefix bytes = some (value, rest)) :
    ∃ mid, l.decodePrefix bytes = some (value.1, mid) ∧ r.decodePrefix mid = some (value.2, rest) := by
  cases left : l.decodePrefix bytes with
  | none => simp [StreamCodec.product, left] at decoded
  | some first =>
    obtain ⟨a, mid⟩ := first
    cases right : r.decodePrefix mid with
    | none => simp [StreamCodec.product, left, right] at decoded
    | some second =>
      obtain ⟨b, after⟩ := second
      simp [StreamCodec.product, left, right] at decoded
      obtain ⟨same, rfl⟩ := decoded
      subst same
      exact ⟨mid, rfl, right⟩

/-- A target whose head reads and whose payload tag is unread is not a target. -/
theorem target_unread {bytes rest : List UInt8} {tag : UInt8}
    {head : ResourceKind × Nat × CapabilityId × Nat × Digest}
    (headed : targetHeadStream.decodePrefix bytes = some (head, tag :: rest))
    (unread : payloadUnread tag = true) : targetStream.decodePrefix bytes = none := by
  obtain ⟨m1, d1, headed⟩ := product_some _ _ headed
  obtain ⟨m2, d2, headed⟩ := product_some _ _ headed
  obtain ⟨m3, d3, headed⟩ := product_some _ _ headed
  obtain ⟨m4, d4, d5⟩ := product_some _ _ headed
  have inner := product_right_none _ _ d1 (product_right_none _ _ d2 (product_right_none _ _ d3
    (product_right_none _ _ d4 (product_right_none _ _ d5
      (product_left_none payloadStream
        (StreamCodec.product (StreamCodec.option CredentialAuthorityEntryCodec.capabilityIdStream)
          (StreamCodec.product (StreamCodec.option StreamCodec.nat)
            (StreamCodec.option Minidregg.Compiler.ObjectAudienceRoster.rosterStream)))
        (payload_unread unread rest))))))
  simp only [targetStream, StreamCodec.xmap]
  rw [inner]
  rfl

theorem unboundTagIn_sound : ∀ (count : Nat) (bytes : List UInt8) (tag : UInt8),
    unboundTagIn count bytes = some tag →
      payloadUnread tag = true ∧ StreamCodec.decodeMany targetStream count bytes = none
  | 0, _, _, found => by cases found
  | count + 1, bytes, tag, found => by
    unfold unboundTagIn at found
    split at found
    · rename_i head octet rest headed
      split at found
      · rename_i unread
        cases found
        exact ⟨unread, by simp [StreamCodec.decodeMany, target_unread headed unread]⟩
      · split at found
        · rename_i target after decoded
          obtain ⟨unread, many⟩ := unboundTagIn_sound count after tag found
          exact ⟨unread, by simp [StreamCodec.decodeMany, decoded, many]⟩
        · cases found
    · cases found

theorem unboundTagBody_sound {body : List UInt8} {tag : UInt8}
    (found : unboundTagBody body = some tag) :
    payloadUnread tag = true ∧ legacyCommandStream.decodePrefix body = none := by
  unfold unboundTagBody at found
  split at found
  · rename_i subject afterSubject subjected
    split at found
    · rename_i nonce afterNonce nonced
      split at found
      · rename_i count targets counted
        obtain ⟨unread, many⟩ := unboundTagIn_sound count targets tag found
        refine ⟨unread, ?_⟩
        have listed : (StreamCodec.list targetStream).decodePrefix afterNonce = none := by
          simp [StreamCodec.list, counted, many]
        exact product_right_none _ _ subjected (product_right_none _ _ nonced
          (product_left_none _ _ listed))
      · cases found
    · cases found
  · cases found

theorem unboundTagNamed : UnboundTagNamed := by
  intro bytes tag found
  have named : ∀ t, payloadUnread t = true → registeredOctet t = false ∧ t ∉ legacyPayloadTags := by
    intro t unread
    simp only [payloadUnread, Bool.and_eq_true, Bool.not_eq_true'] at unread
    exact ⟨unread.1, fun member => absurd (List.contains_iff_mem.mpr member)
      (by rw [unread.2]; exact Bool.false_ne_true)⟩
  have raw : payloadUnread tag = true ∧ rawCommandCodec.decode bytes = none := by
    unfold unboundTag at found
    split at found
    · rename_i framed
      obtain ⟨unread, body⟩ := unboundTagBody_sound found
      exact ⟨unread, by simp [rawCommandCodec, framed, StreamCodec.toLawful, body]⟩
    · rename_i unframed
      split at found
      · rename_i framed
        obtain ⟨unread, body⟩ := unboundTagBody_sound found
        have whole : commandStream.decodePrefix (bytes.drop familyCommandFrame.length) = none := by
          simp only [commandStream, StreamCodec.xmap]
          rw [product_left_none _ _ body]
          rfl
        exact ⟨unread, by simp [rawCommandCodec, unframed, framed, StreamCodec.toLawful, whole]⟩
      · cases found
  obtain ⟨unread, undecoded⟩ := raw
  refine ⟨(named tag unread).1, (named tag unread).2, ?_⟩
  simp [commandCodec, ResourceBirthCodec.strictCodec, undecoded]

#assert_axioms unboundTagNamed

/-! ## The probe the executed poles use (`Assurance/RegistryRefusalPoles.lean`) -/

/-- A command body of one target, its payload tag `tag` and nothing after the tag's own bytes. -/
def tagProbe (payload : List UInt8) : List UInt8 :=
  commandFrame ++ TypedAuthorizationRequestCodec.subjectIdStream.encode ⟨0⟩ ++ StreamCodec.nat.encode 0 ++
    StreamCodec.nat.encode 1 ++ targetHeadStream.encode (.object, 0, ⟨0⟩, 1, ⟨0⟩) ++ payload

end Minidregg.Kernel.DeclaredResourceController
