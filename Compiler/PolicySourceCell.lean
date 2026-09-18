/-
# Compiler.PolicySourceCell — immutable canonical policy source payloads

This representation stores the existing complete `PolicyRecord`, using its
existing canonical codec. A source cell's physical identifier is derived from
the deployment domain and the record's actual content address. No theorem
asserts that either hash is injective: occupied, retired and colliding physical
identifiers must be refused by the existing lifecycle allocator.

Initial-policy admission retains exact source bytes, content address, policy
identity, version zero, absent predecessor, deployment domain and the actual
receiving compiler profile. It cannot obtain its profile from the submitted
record. There is no policy interpreter or mutation operation in this module.
-/
import Compiler.PolicyRecordCodec
import Theory.ResourceBirth

namespace Minidregg.Compiler.PolicySourceCell

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def wireVersion : Nat := 1
def registryTag : UInt8 := 10
def schemaId : Nat := 91009

def recordStream : StreamCodec PolicyRecord where
  encode record := bytesStream.encode (PolicyRecordCodec.encode record)
  decodePrefix bytes := do
    let (source, suffix) ← bytesStream.decodePrefix bytes
    let record ← PolicyRecordCodec.decode source
    some (record, suffix)
  decodePrefix_encode := by
    intro record suffix
    simp [bytesStream.decodePrefix_encode, PolicyRecordCodec.decode_encode]

def schema : CellState.Schema.{0, 0, 0, 0} where
  Field := Unit
  FieldType := fun _ => PolicyRecord
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun resource => resource.elim

def stateOfOption : Option PolicyRecord → LogicalState schema
  | none => { fields := 0, resources := fun resource => nomatch resource }
  | some record =>
      { fields := (0 : FieldStore schema).write () record
        resources := fun resource => nomatch resource }

def recordAt (state : LogicalState schema) : Option PolicyRecord := state.fields ()

@[simp] theorem recordAt_stateOfOption (record : Option PolicyRecord) :
    recordAt (stateOfOption record) = record := by
  cases record <;> rfl

theorem state_ext (state : LogicalState schema) :
    state = stateOfOption (recordAt state) := by
  cases state with
  | mk fields resources =>
      have resourcesExact : resources = fun resource => nomatch resource := by
        funext resource
        exact Empty.elim resource
      cases present : fields () with
      | none =>
          have fieldsExact : fields = (0 : FieldStore schema) := by
            apply DFinsupp.ext
            intro field
            cases field
            simpa using present
          rw [fieldsExact, resourcesExact]
          rfl
      | some record =>
          have fieldsExact : fields = (0 : FieldStore schema).write () record := by
            apply DFinsupp.ext
            intro field
            cases field
            simp [present]
          rw [fieldsExact, resourcesExact]
          rfl

def payloadStream := StreamCodec.product StreamCodec.nat (StreamCodec.option recordStream)

def wireFrame : List UInt8 := "DREGG/POLICY/SOURCE".toUTF8.toList

def encode (state : LogicalState schema) : List UInt8 :=
  wireFrame ++ payloadStream.encode (wireVersion, recordAt state)

def decodeRaw (bytes : List UInt8) : Option (LogicalState schema) :=
  if bytes.take wireFrame.length = wireFrame then do
    let (version, record) ← payloadStream.toLawful.decode (bytes.drop wireFrame.length)
    if version = wireVersion then some (stateOfOption record) else none
  else none

@[simp] theorem decodeRaw_encode (state : LogicalState schema) :
    decodeRaw (encode state) = some state := by
  have decoded := payloadStream.toLawful.decode_encode (wireVersion, recordAt state)
  change payloadStream.toLawful.decode
    (payloadStream.encode (wireVersion, recordAt state)) =
      some (wireVersion, recordAt state) at decoded
  simp [decodeRaw, encode, decoded, ← state_ext state]

def decode (bytes : List UInt8) : Option (LogicalState schema) := do
  let state ← decodeRaw bytes
  if encode state = bytes then some state else none

@[simp] theorem decode_encode (state : LogicalState schema) :
    decode (encode state) = some state := by
  simp [decode]

theorem decode_canonical {bytes : List UInt8} {state : LogicalState schema}
    (accepted : decode bytes = some state) : encode state = bytes := by
  unfold decode at accepted
  cases raw : decodeRaw bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical =>
        cases Option.some.inj accepted
        exact canonical
      next => contradiction

theorem encode_injective : Function.Injective encode := by
  intro left right same
  have decoded := congrArg decode same
  simpa using decoded

theorem wrong_version_refused (version : Nat) (record : Option PolicyRecord)
    (different : version ≠ wireVersion) :
    decode (wireFrame ++ payloadStream.encode (version, record)) = none := by
  have decoded := payloadStream.toLawful.decode_encode (version, record)
  change payloadStream.toLawful.decode (payloadStream.encode (version, record)) =
    some (version, record) at decoded
  simp [decode, decodeRaw, decoded, different]

def stateCodec : LawfulCodec (LogicalState schema) where
  encode := encode
  decode := decode
  decode_encode := decode_encode

def rootCustomization : List UInt8 := [68, 82, 69, 71, 71, 46, 80, 79, 76, 73, 67, 89, 46, 83, 79, 85, 82, 67, 69, 46, 83, 84, 65, 84, 69, 47, 118, 49]
def idCustomization : List UInt8 := [68, 82, 69, 71, 71, 46, 80, 79, 76, 73, 67, 89, 46, 83, 79, 85, 82, 67, 69, 46, 73, 68, 47, 118, 49]

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : Materializer schema Digest where
  codec := stateCodec
  rootBytes := rootBytes

def physicalId (domain address : Digest) : Nat :=
  (Sp800185Cshake256.hash idCustomization
    ((StreamCodec.product digestStream digestStream).encode (domain, address))).digest.value

theorem state_and_identifier_domains_distinct : rootCustomization ≠ idCustomization := by
  decide

def SourceValid (domain : Digest) (cellId : Nat) (record : PolicyRecord) : Prop :=
  record.domain = domain ∧ cellId = physicalId domain (PolicyRecordCodec.digest record)

instance sourceValidDecidable (domain : Digest) (cellId : Nat) (record : PolicyRecord) :
    Decidable (SourceValid domain cellId record) := by
  unfold SourceValid
  infer_instance

def initialIds (domain : Digest) (initials : List ResourceBirth.InitialPolicy) : List Nat :=
  initials.map fun initial => physicalId domain initial.address

def InitialFacts {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) (initial : ResourceBirth.InitialPolicy)
    (record : PolicyRecord) : Prop :=
  profile.descriptor?.isSome = true ∧
  record.policyId = initial.policyId ∧
  PolicyRecordCodec.digest record = initial.address ∧
  record.domain = domain ∧ record.semantics = profile.semantics ∧
  record.version = 0 ∧ record.previous = none ∧
  Minidregg.Compiler.supported profile.compiler record.predicate = true

instance initialFactsDecidable {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) (initial : ResourceBirth.InitialPolicy)
    (record : PolicyRecord) : Decidable (InitialFacts domain profile initial record) := by
  unfold InitialFacts
  infer_instance

structure CheckedInitial {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) (initial : ResourceBirth.InitialPolicy) where
  record : PolicyRecord
  decoded : PolicyRecordCodec.decode initial.canonicalBytes = some record
  facts : InitialFacts domain profile initial record

def checkInitial {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) (initial : ResourceBirth.InitialPolicy) :
    Option (CheckedInitial domain profile initial) :=
  match decoded : PolicyRecordCodec.decode initial.canonicalBytes with
  | none => none
  | some record =>
      if facts : InitialFacts domain profile initial record then
        some ⟨record, decoded, facts⟩
      else none

theorem CheckedInitial.bytes_exact {F : Type} [Field F] {domain : Digest}
    {profile : PolicyCompilerProfile F} {initial : ResourceBirth.InitialPolicy}
    (checked : CheckedInitial domain profile initial) :
    PolicyRecordCodec.encode checked.record = initial.canonicalBytes :=
  PolicyRecordCodec.decode_canonical checked.decoded

theorem CheckedInitial.source_valid {F : Type} [Field F] {domain : Digest}
    {profile : PolicyCompilerProfile F} {initial : ResourceBirth.InitialPolicy}
    (checked : CheckedInitial domain profile initial) :
    SourceValid domain (physicalId domain initial.address) checked.record := by
  exact ⟨checked.facts.2.2.2.1, by rw [checked.facts.2.2.1]⟩

theorem checkInitial_of_valid {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) (initial : ResourceBirth.InitialPolicy)
    (record : PolicyRecord)
    (decoded : PolicyRecordCodec.decode initial.canonicalBytes = some record)
    (facts : InitialFacts domain profile initial record) :
    ∃ checked, checkInitial domain profile initial = some checked := by
  unfold checkInitial
  split
  next absent => simp [decoded] at absent
  next selected found =>
    have same : selected = record := Option.some.inj (found.symm.trans decoded)
    subst selected
    rw [dif_pos facts]
    exact ⟨_, rfl⟩

theorem wrong_domain_refused {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) (initial : ResourceBirth.InitialPolicy)
    (record : PolicyRecord)
    (decoded : PolicyRecordCodec.decode initial.canonicalBytes = some record)
    (different : record.domain ≠ domain) :
    checkInitial domain profile initial = none := by
  cases result : checkInitial domain profile initial with
  | none => rfl
  | some checked =>
      have same : checked.record = record := Option.some.inj (checked.decoded.symm.trans decoded)
      have exactDomain := checked.facts.2.2.2.1
      rw [same] at exactDomain
      exact False.elim (different exactDomain)

theorem wrong_digest_refused {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) (initial : ResourceBirth.InitialPolicy)
    (record : PolicyRecord)
    (decoded : PolicyRecordCodec.decode initial.canonicalBytes = some record)
    (different : PolicyRecordCodec.digest record ≠ initial.address) :
    checkInitial domain profile initial = none := by
  cases result : checkInitial domain profile initial with
  | none => rfl
  | some checked =>
      have same : checked.record = record := Option.some.inj (checked.decoded.symm.trans decoded)
      have exactDigest := checked.facts.2.2.1
      rw [same] at exactDigest
      exact False.elim (different exactDigest)

theorem research_profile_refused {F : Type} [Field F] (domain semantics : Digest)
    (initial : ResourceBirth.InitialPolicy) :
    checkInitial domain (PolicyCompilerProfile.researchDisabled (F := F) semantics) initial =
      none := by
  cases result : checkInitial domain (PolicyCompilerProfile.researchDisabled (F := F) semantics) initial with
  | none => rfl
  | some checked =>
      have source := checked.facts.1
      simp [PolicyCompilerProfile.descriptor?] at source

structure CheckedInitials {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) (initials : List ResourceBirth.InitialPolicy) where
  records : List PolicyRecord
  checked : List.Forall₂
    (fun initial record => PolicyRecordCodec.decode initial.canonicalBytes = some record ∧
      InitialFacts domain profile initial record) initials records

def checkInitials {F : Type} [Field F] (domain : Digest)
    (profile : PolicyCompilerProfile F) :
    (initials : List ResourceBirth.InitialPolicy) →
      Option (CheckedInitials domain profile initials)
  | [] => some ⟨[], .nil⟩
  | initial :: initials => do
      let head ← checkInitial domain profile initial
      let tail ← checkInitials domain profile initials
      some ⟨head.record :: tail.records, .cons ⟨head.decoded, head.facts⟩ tail.checked⟩

theorem CheckedInitials.ids_exact {F : Type} [Field F] {domain : Digest}
    {profile : PolicyCompilerProfile F} {initials : List ResourceBirth.InitialPolicy}
    (checked : CheckedInitials domain profile initials) :
    checked.records.map (fun record => physicalId domain (PolicyRecordCodec.digest record)) =
      initialIds domain initials := by
  rcases checked with ⟨records, valid⟩
  induction valid with
  | nil => rfl
  | @cons initial record initials records head tail induction =>
      simp only [List.map_cons, initialIds] at induction ⊢
      rw [head.2.2.2.1, induction]

theorem CheckedInitials.record_of_member {F : Type} [Field F] {domain : Digest}
    {profile : PolicyCompilerProfile F} {initials : List ResourceBirth.InitialPolicy}
    (checked : CheckedInitials domain profile initials)
    (initial : ResourceBirth.InitialPolicy) (member : initial ∈ initials) :
    ∃ record ∈ checked.records,
      PolicyRecordCodec.decode initial.canonicalBytes = some record ∧
        InitialFacts domain profile initial record := by
  rcases checked with ⟨records, valid⟩
  induction valid generalizing initial with
  | nil => simp at member
  | @cons first record initials records head tail induction =>
      rcases List.mem_cons.mp member with same | member
      · subst initial
        exact ⟨record, by simp, head⟩
      · obtain ⟨selected, selectedMember, decoded, facts⟩ := induction initial member
        exact ⟨selected, List.mem_cons_of_mem _ selectedMember, decoded, facts⟩

end Minidregg.Compiler.PolicySourceCell
