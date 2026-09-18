/-
# Compiler.CredentialAuthorityStateCodec -- the full canonical authority cell

This is an exact executable codec for the existing sparse authority schema,
not a codec focused on one supplied page or a second authority model. Every
present dependent field is encoded in canonical key order. Absent fields,
explicit zero epochs and explicit false membership values remain distinct.
The complete domain receiver derives this cell from every anchored shard.
Its semantic root is distinct from all physical catalogue and shard roots.
-/
import Compiler.CredentialAuthorityEntryCodec
import Compiler.FiniteDependentMapCodec
import Compiler.Sp800185Cshake256

namespace Minidregg.Compiler.CredentialAuthorityStateCodec

open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.FiniteDependentMapCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def fieldCode : AuthorityField → Nat
  | .capability .object identifier => Nat.pair 0 identifier.value
  | .capability .account identifier => Nat.pair 1 identifier.value
  | .capability .program identifier => Nat.pair 2 identifier.value
  | .issuerEpoch issuer => Nat.pair 3 issuer.value
  | .policyEpoch policy => Nat.pair 4 policy.value
  | .policyAddress policy epoch => Nat.pair 5 (Nat.pair policy.value epoch)
  | .subjectKeyEpoch subject => Nat.pair 6 subject.value
  | .revoked (.capability identifier) => Nat.pair 7 identifier.value
  | .revoked (.channel channel) => Nat.pair 8 channel.value
  | .nullifier identifier => Nat.pair 9 identifier

def fieldOfCode (code : Nat) : AuthorityField :=
  match Nat.unpair code with
  | (0, value) => .capability .object ⟨value⟩
  | (1, value) => .capability .account ⟨value⟩
  | (2, value) => .capability .program ⟨value⟩
  | (3, value) => .issuerEpoch ⟨value⟩
  | (4, value) => .policyEpoch ⟨value⟩
  | (5, value) => .policyAddress ⟨(Nat.unpair value).1⟩ (Nat.unpair value).2
  | (6, value) => .subjectKeyEpoch ⟨value⟩
  | (7, value) => .revoked (.capability ⟨value⟩)
  | (8, value) => .revoked (.channel ⟨value⟩)
  | (9, value) => .nullifier value
  | _ => .nullifier 0

theorem fieldOfCode_code (field : AuthorityField) :
    fieldOfCode (fieldCode field) = field := by
  cases field with
  | capability kind identifier =>
      cases kind <;> cases identifier <;> simp [fieldCode, fieldOfCode]
  | issuerEpoch issuer => cases issuer; simp [fieldCode, fieldOfCode]
  | policyEpoch policy => cases policy; simp [fieldCode, fieldOfCode]
  | policyAddress policy epoch => cases policy; simp [fieldCode, fieldOfCode]
  | subjectKeyEpoch subject => cases subject; simp [fieldCode, fieldOfCode]
  | revoked key =>
      cases key with
      | capability identifier => cases identifier; simp [fieldCode, fieldOfCode]
      | channel channel => cases channel; simp [fieldCode, fieldOfCode]
  | nullifier identifier => simp [fieldCode, fieldOfCode]

theorem fieldCode_injective : Function.Injective fieldCode := by
  intro left right equal
  have decoded := congrArg fieldOfCode equal
  simpa [fieldOfCode_code] using decoded

local instance fieldOrder : LinearOrder AuthorityField :=
  LinearOrder.lift' fieldCode fieldCode_injective

local instance schemaFieldOrder : LinearOrder CredentialAuthorityState.schema.Field :=
  inferInstanceAs (LinearOrder AuthorityField)

instance valueDecidableEq (field : AuthorityField) : DecidableEq (AuthorityField.Value field) := by
  cases field <;> simp only [AuthorityField.Value] <;> infer_instance

local instance schemaOptionalValueDecidableEq :
    (field : CredentialAuthorityState.schema.Field) →
      DecidableEq (Option (CredentialAuthorityState.schema.FieldType field)) := by
  intro field
  change DecidableEq (Option (AuthorityField.Value field))
  infer_instance

def fieldStream : StreamCodec AuthorityField :=
  StreamCodec.xmap StreamCodec.nat fieldCode fieldOfCode fieldOfCode_code

def valueStream : (field : AuthorityField) → StreamCodec (AuthorityField.Value field)
  | .capability kind _ => storedCapabilityStream kind
  | .issuerEpoch _ => StreamCodec.nat
  | .policyEpoch _ => StreamCodec.nat
  | .policyAddress _ _ => digestStream
  | .subjectKeyEpoch _ => StreamCodec.nat
  | .revoked _ => StreamCodec.bool
  | .nullifier _ => StreamCodec.bool

def fieldsStream : StreamCodec (FieldStore CredentialAuthorityState.schema.{0, 0}) :=
  FiniteDependentMapCodec.stream fieldStream
    (fun field => StreamCodec.option (valueStream field))

def stateOfFields (fields : FieldStore CredentialAuthorityState.schema.{0, 0}) :
    LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields := fields
  resources := fun resource => nomatch resource

theorem stateOfFields_fields (state : LogicalState CredentialAuthorityState.schema.{0, 0}) :
    stateOfFields state.fields = state := by
  cases state with
  | mk fields resources =>
      have resourcesExact : resources = fun resource => nomatch resource := by
        funext resource
        exact Empty.elim resource
      rw [resourcesExact]
      rfl

def stateStream : StreamCodec (LogicalState CredentialAuthorityState.schema.{0, 0}) :=
  StreamCodec.xmap fieldsStream LogicalState.fields stateOfFields stateOfFields_fields

def wireFrame : List UInt8 := "LOOM/AUTH/STATE".toUTF8.toList ++ [1]

def encode (state : LogicalState CredentialAuthorityState.schema.{0, 0}) : List UInt8 :=
  wireFrame ++ stateStream.encode state

def decodeRaw (bytes : List UInt8) :
    Option (LogicalState CredentialAuthorityState.schema.{0, 0}) :=
  if bytes.take wireFrame.length = wireFrame then
    stateStream.toLawful.decode (bytes.drop wireFrame.length)
  else none

@[simp] theorem decodeRaw_encode (state : LogicalState CredentialAuthorityState.schema.{0, 0}) :
    decodeRaw (encode state) = some state := by
  have payload := stateStream.toLawful.decode_encode state
  change stateStream.toLawful.decode (stateStream.encode state) = some state at payload
  simp [decodeRaw, encode, payload]

def decode (bytes : List UInt8) : Option (LogicalState CredentialAuthorityState.schema.{0, 0}) := do
  let state ← decodeRaw bytes
  if encode state = bytes then some state else none

@[simp] theorem decode_encode (state : LogicalState CredentialAuthorityState.schema.{0, 0}) :
    decode (encode state) = some state := by simp [decode]

theorem decode_canonical {bytes : List UInt8}
    {state : LogicalState CredentialAuthorityState.schema.{0, 0}}
    (accepted : decode bytes = some state) : encode state = bytes := by
  unfold decode at accepted
  cases raw : decodeRaw bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical => cases Option.some.inj accepted; exact canonical
      next => contradiction

def stateCodec : LawfulCodec (LogicalState CredentialAuthorityState.schema.{0, 0}) where
  encode := encode
  decode := decode
  decode_encode := decode_encode

def rootCustomization : List UInt8 := "LOOM.AUTH.STATE.ROOT/v1".toUTF8.toList

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest where
  codec := stateCodec
  rootBytes := rootBytes

theorem encode_injective : Function.Injective encode := by
  intro left right equal
  have decoded := congrArg decode equal
  simpa using decoded

theorem decoded_root_exact {bytes : List UInt8}
    {state : LogicalState CredentialAuthorityState.schema.{0, 0}}
    (accepted : decode bytes = some state) :
    (materialize materializer state).root = rootBytes bytes :=
  congrArg rootBytes (decode_canonical accepted)

theorem decode_some_iff (bytes : List UInt8)
    (state : LogicalState CredentialAuthorityState.schema.{0, 0}) :
    decode bytes = some state ↔ encode state = bytes := by
  constructor
  · exact decode_canonical
  · intro canonical
    rw [← canonical]
    exact decode_encode state

/-- Explicit false is committed data, distinct from an absent address even
though the higher semantic Boolean reader chooses the same default. -/
theorem absent_ne_explicit_false (key : RevocationKey) :
    encode (stateOfFields 0) ≠
      encode (stateOfFields ((0 : FieldStore CredentialAuthorityState.schema.{0, 0}).write
        (.revoked key) false)) := by
  intro same
  have fieldsSame := congrArg
    (fun state : LogicalState CredentialAuthorityState.schema.{0, 0} => state.fields (.revoked key))
    (encode_injective same)
  simp [stateOfFields] at fieldsSame

/-- info: 'Minidregg.Compiler.CredentialAuthorityStateCodec.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_encode
/-- info: 'Minidregg.Compiler.CredentialAuthorityStateCodec.decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_canonical
/-- info: 'Minidregg.Compiler.CredentialAuthorityStateCodec.absent_ne_explicit_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_ne_explicit_false

end Minidregg.Compiler.CredentialAuthorityStateCodec
