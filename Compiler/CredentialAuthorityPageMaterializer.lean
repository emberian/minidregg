/-
# Compiler.CredentialAuthorityPageMaterializer -- bounded committed authority

`CredentialAuthorityState` is the canonical, unbounded sparse authority
semantics. This module supplies one concrete bounded
representation shard: four typed authority entries with a stable wire frame,
prefix-decodable payload, and a Lean cSHAKE256 root over the exact bytes.

Each entry projects to the actual dependent `AuthorityField` addresses:
complete capability lineage, issuer/subject epochs, policy epoch/address,
revocation flags, and operation nullifiers. The page's root is the
`capabilityRoot`/`policyRoot`/`revocationRoot` used by its `AuthState`
projection. No parallel host-authored authority lookup exists.

Capacity is explicit.  `insert?` fills the first empty slot, never overwrites,
and returns `none` exactly for a full page. A page number identifies a shard;
composing shards requires unique address routing and a combined projection.
This page does not pretend the global authority universe is finite.
As with the event-page representation, collision resistance is only
a pair-scoped premise, never an impossible global injection into 256 bits.
-/
import Compiler.Sp800185Cshake256
import Compiler.CredentialAuthorityEntryCodec
import Theory.CredentialAuthorityState

namespace Minidregg.Compiler.CredentialAuthorityPageMaterializer

open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Canonical bounded authority entries -/

theorem lawfulCodec_encode_injective {alpha : Type}
    (codec : LawfulCodec alpha) : Function.Injective codec.encode := by
  intro left right equal
  have decoded := congrArg codec.decode equal
  rw [codec.decode_encode, codec.decode_encode] at decoded
  exact Option.some.inj decoded

def revocationKeyStream : StreamCodec RevocationKey where
  encode
    | .capability capability => 0 :: capabilityIdStream.encode capability
    | .channel channel => 1 :: channelIdStream.encode channel
  decodePrefix
    | 0 :: bytes => do
        let (capability, suffix) <- capabilityIdStream.decodePrefix bytes
        some (.capability capability, suffix)
    | 1 :: bytes => do
        let (channel, suffix) <- channelIdStream.decodePrefix bytes
        some (.channel channel, suffix)
    | _ => none
  decodePrefix_encode := by
    intro key suffix
    cases key with
    | capability capability => simp [capabilityIdStream.decodePrefix_encode]
    | channel channel => simp [channelIdStream.decodePrefix_encode]

/-- One exact authority record. Capability identity is taken from the stored
head, so a separate caller-supplied slot cannot retarget a grant. -/
inductive Entry where
  | policy (policy : PolicyId) (epoch : Epoch) (address : Digest)
  | revocation (key : RevocationKey) (revoked : Bool)
  | capability (kind : ResourceKind) (stored : StoredCapability kind)
  | issuerEpoch (issuer : IssuerId) (epoch : Epoch)
  | subjectKeyEpoch (subject : SubjectId) (epoch : Epoch)
  | subjectKey (key : CredentialSigningKey.KeyRecord)
  | nullifier (id : Nat) (consumed : Bool)
  deriving DecidableEq, Repr

def entryStream : StreamCodec Entry where
  encode
    | .policy policy epoch address =>
        0 :: policyIdStream.encode policy ++ StreamCodec.nat.encode epoch ++
          digestStream.encode address
    | .revocation key revoked =>
        1 :: revocationKeyStream.encode key ++ StreamCodec.bool.encode revoked
    | .capability .object stored => 2 :: (storedCapabilityStream .object).encode stored
    | .capability .account stored => 3 :: (storedCapabilityStream .account).encode stored
    | .capability .program stored => 4 :: (storedCapabilityStream .program).encode stored
    | .issuerEpoch issuer epoch =>
        5 :: issuerIdStream.encode issuer ++ StreamCodec.nat.encode epoch
    | .subjectKeyEpoch subject epoch =>
        6 :: subjectIdStream.encode subject ++ StreamCodec.nat.encode epoch
    | .nullifier nullifierId consumed =>
        7 :: StreamCodec.nat.encode nullifierId ++ StreamCodec.bool.encode consumed
    | .subjectKey key => 8 :: CredentialSigningKeyCodec.keyRecordStream.encode key
  decodePrefix
    | 0 :: bytes => do
        let (policy, afterPolicy) <- policyIdStream.decodePrefix bytes
        let (epoch, afterEpoch) <- StreamCodec.nat.decodePrefix afterPolicy
        let (address, suffix) <- digestStream.decodePrefix afterEpoch
        some (.policy policy epoch address, suffix)
    | 1 :: bytes => do
        let (key, afterKey) <- revocationKeyStream.decodePrefix bytes
        let (revoked, suffix) <- StreamCodec.bool.decodePrefix afterKey
        some (.revocation key revoked, suffix)
    | 2 :: bytes => do
        let (stored, suffix) ← (storedCapabilityStream .object).decodePrefix bytes
        some (.capability .object stored, suffix)
    | 3 :: bytes => do
        let (stored, suffix) ← (storedCapabilityStream .account).decodePrefix bytes
        some (.capability .account stored, suffix)
    | 4 :: bytes => do
        let (stored, suffix) ← (storedCapabilityStream .program).decodePrefix bytes
        some (.capability .program stored, suffix)
    | 5 :: bytes => do
        let (issuer, afterIssuer) ← issuerIdStream.decodePrefix bytes
        let (epoch, suffix) ← StreamCodec.nat.decodePrefix afterIssuer
        some (.issuerEpoch issuer epoch, suffix)
    | 6 :: bytes => do
        let (subject, afterSubject) ← subjectIdStream.decodePrefix bytes
        let (epoch, suffix) ← StreamCodec.nat.decodePrefix afterSubject
        some (.subjectKeyEpoch subject epoch, suffix)
    | 7 :: bytes => do
        let (nullifierId, afterId) ← StreamCodec.nat.decodePrefix bytes
        let (consumed, suffix) ← StreamCodec.bool.decodePrefix afterId
        some (.nullifier nullifierId consumed, suffix)
    | 8 :: bytes => do
        let (key, suffix) ← CredentialSigningKeyCodec.keyRecordStream.decodePrefix bytes
        some (.subjectKey key, suffix)
    | _ => none
  decodePrefix_encode := by
    intro entry suffix
    cases entry with
    | policy policy epoch address =>
        simp [List.append_assoc, policyIdStream.decodePrefix_encode,
          StreamCodec.nat.decodePrefix_encode, digestStream.decodePrefix_encode]
    | revocation key revoked =>
        simp [List.append_assoc, revocationKeyStream.decodePrefix_encode,
          StreamCodec.bool.decodePrefix_encode]
    | capability kind stored =>
        cases kind <;> simp [StreamCodec.decodePrefix_encode]
    | issuerEpoch issuer epoch =>
        simp [List.append_assoc, StreamCodec.decodePrefix_encode]
    | subjectKeyEpoch subject epoch =>
        simp [List.append_assoc, StreamCodec.decodePrefix_encode]
    | nullifier id consumed =>
        simp [List.append_assoc, StreamCodec.decodePrefix_encode]
    | subjectKey key => simp [StreamCodec.decodePrefix_encode]

/-- Exact canonical authority addresses written by one entry. -/
def Entry.fields : Entry -> List AuthorityField
  | .policy policyId epoch _address =>
      [.policyEpoch policyId, .policyAddress policyId epoch]
  | .revocation key _ => [.revoked key]
  | .capability kind stored => [.capability kind stored.head.id]
  | .issuerEpoch issuer _ => [.issuerEpoch issuer]
  | .subjectKeyEpoch subject _ => [.subjectKeyEpoch subject]
  | .subjectKey key => [.subjectKeyEpoch ⟨key.subject⟩, .subjectKey ⟨key.subject⟩ key.keyEpoch]
  | .nullifier nullifierId _ => [.nullifier nullifierId]

/-- Install one entry into the canonical sparse authority field carrier. -/
def Entry.install
    (fields : FieldStore CredentialAuthorityState.schema.{0, 0}) :
    Entry -> FieldStore CredentialAuthorityState.schema.{0, 0}
  | .policy policyId epoch address =>
      (fields.write (.policyEpoch policyId) epoch).write
        (.policyAddress policyId epoch) address
  | .revocation key revoked => fields.write (.revoked key) revoked
  | .capability kind stored => fields.write (.capability kind stored.head.id) stored
  | .issuerEpoch issuer epoch => fields.write (.issuerEpoch issuer) epoch
  | .subjectKeyEpoch subject epoch => fields.write (.subjectKeyEpoch subject) epoch
  | .subjectKey key =>
      (fields.write (.subjectKeyEpoch ⟨key.subject⟩) key.keyEpoch).write
        (.subjectKey ⟨key.subject⟩ key.keyEpoch) key
  | .nullifier nullifierId consumed => fields.write (.nullifier nullifierId) consumed

/-- An entry leaves every unrelated canonical coordinate unchanged. -/
theorem Entry.install_frame (entry : Entry)
    (fields : FieldStore CredentialAuthorityState.schema.{0, 0})
    (field : AuthorityField) (outside : field ∉ entry.fields) :
    Entry.install fields entry field = fields field := by
  cases entry with
  | policy policy epoch address =>
      simp only [Entry.fields, List.mem_cons, List.not_mem_nil,
        or_false, not_or] at outside
      exact (CellState.FieldStore.write_other _ (Ne.symm outside.2) address).trans
        (CellState.FieldStore.write_other fields (Ne.symm outside.1) epoch)
  | revocation key revoked =>
      simp only [Entry.fields, List.mem_singleton] at outside
      exact CellState.FieldStore.write_other fields (Ne.symm outside) revoked
  | capability kind stored =>
      simp only [Entry.fields, List.mem_singleton] at outside
      exact CellState.FieldStore.write_other fields (Ne.symm outside) stored
  | issuerEpoch issuer epoch =>
      simp only [Entry.fields, List.mem_singleton] at outside
      exact CellState.FieldStore.write_other fields (Ne.symm outside) epoch
  | subjectKeyEpoch subject epoch =>
      simp only [Entry.fields, List.mem_singleton] at outside
      exact CellState.FieldStore.write_other fields (Ne.symm outside) epoch
  | subjectKey key =>
      simp only [Entry.fields, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      exact (CellState.FieldStore.write_other _ (Ne.symm outside.2) key).trans
        (CellState.FieldStore.write_other fields (Ne.symm outside.1) key.keyEpoch)
  | nullifier nullifierId consumed =>
      simp only [Entry.fields, List.mem_singleton] at outside
      exact CellState.FieldStore.write_other fields (Ne.symm outside) consumed

/-- On its named coordinates an entry determines the complete typed value,
independently of the previous contents. -/
theorem Entry.install_exact (entry : Entry)
    (fields : FieldStore CredentialAuthorityState.schema.{0, 0})
    (field : AuthorityField) (inside : field ∈ entry.fields) :
    Entry.install fields entry field = Entry.install 0 entry field := by
  cases entry with
  | policy policy epoch address =>
      simp only [Entry.fields, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> simp [Entry.install]
  | revocation key revoked =>
      simp only [Entry.fields, List.mem_singleton] at inside
      subst field
      simp [Entry.install]
  | capability kind stored =>
      simp only [Entry.fields, List.mem_singleton] at inside
      subst field
      simp [Entry.install]
  | issuerEpoch issuer epoch =>
      simp only [Entry.fields, List.mem_singleton] at inside
      subst field
      simp [Entry.install]
  | subjectKeyEpoch subject epoch =>
      simp only [Entry.fields, List.mem_singleton] at inside
      subst field
      simp [Entry.install]
  | subjectKey key =>
      simp only [Entry.fields, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> simp [Entry.install]
  | nullifier id consumed =>
      simp only [Entry.fields, List.mem_singleton] at inside
      subst field
      simp [Entry.install]

/-! ## Four-slot pages, membership, and overflow -/

structure Page where
  authorityDomain : Digest
  pageNumber : Nat
  slot0 : Option Entry
  slot1 : Option Entry
  slot2 : Option Entry
  slot3 : Option Entry
  deriving DecidableEq, Repr

abbrev PageTuple :=
  Digest × Nat × Option Entry × Option Entry × Option Entry × Option Entry

def pageTupleStream : StreamCodec PageTuple :=
  StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.option entryStream)
        (StreamCodec.product (StreamCodec.option entryStream)
          (StreamCodec.product (StreamCodec.option entryStream)
            (StreamCodec.option entryStream)))))

def pageTuple (page : Page) : PageTuple :=
  ⟨page.authorityDomain, page.pageNumber, page.slot0, page.slot1, page.slot2,
    page.slot3⟩

def pageOfTuple (tuple : PageTuple) : Page where
  authorityDomain := tuple.1
  pageNumber := tuple.2.1
  slot0 := tuple.2.2.1
  slot1 := tuple.2.2.2.1
  slot2 := tuple.2.2.2.2.1
  slot3 := tuple.2.2.2.2.2

@[simp] theorem pageOfTuple_tuple (page : Page) :
    pageOfTuple (pageTuple page) = page :=
  rfl

def pageStream : StreamCodec Page :=
  StreamCodec.xmap pageTupleStream pageTuple pageOfTuple pageOfTuple_tuple

def Page.entries (page : Page) : List Entry :=
  [page.slot0, page.slot1, page.slot2, page.slot3].filterMap _root_.id

def Page.Contains (page : Page) (entry : Entry) : Prop :=
  entry ∈ page.entries

@[simp] theorem Page.entries_length_le_four (page : Page) :
    page.entries.length ≤ 4 := by
  rcases page with
    ⟨authorityDomain, pageNumber, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.entries]

def Page.fields (page : Page) : List AuthorityField :=
  page.entries.flatMap Entry.fields

/-- A valid page cannot name one canonical authority address twice.  In
particular two current epochs for one policy cannot coexist in a page. -/
def Page.Valid (page : Page) : Prop :=
  page.fields.Nodup

instance pageValidDecidable (page : Page) : Decidable page.Valid := by
  unfold Page.Valid
  infer_instance

def Page.Full (page : Page) : Prop :=
  page.slot0.isSome = true /\ page.slot1.isSome = true /\
    page.slot2.isSome = true /\ page.slot3.isSome = true

instance pageFullDecidable (page : Page) : Decidable page.Full := by
  unfold Page.Full
  infer_instance

instance pageContainsDecidable (page : Page) (entry : Entry) :
    Decidable (page.Contains entry) := by
  unfold Page.Contains
  infer_instance

/-- Fill the first empty slot.  Existing occupied slots are never replaced. -/
def Page.insert? (page : Page) (entry : Entry) : Option Page :=
  match page.slot0 with
  | none => some { page with slot0 := some entry }
  | some _ =>
      match page.slot1 with
      | none => some { page with slot1 := some entry }
      | some _ =>
          match page.slot2 with
          | none => some { page with slot2 := some entry }
          | some _ =>
              match page.slot3 with
              | none => some { page with slot3 := some entry }
              | some _ => none

theorem Page.insert_none_iff_full (page : Page) (entry : Entry) :
    page.insert? entry = none <-> page.Full := by
  rcases page with
    ⟨authorityDomain, pageNumber, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.insert?, Page.Full]

theorem Page.insert_contains {page post : Page} {entry : Entry}
    (inserted : page.insert? entry = some post) :
    post.Contains entry := by
  rcases page with
    ⟨authorityDomain, pageNumber, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.insert?, Page.Contains, Page.entries] at inserted ⊢ <;>
    subst post <;> simp

theorem Page.insert_member_iff {page post : Page} {entry : Entry}
    (inserted : page.insert? entry = some post) (candidate : Entry) :
    post.Contains candidate ↔ candidate = entry ∨ page.Contains candidate := by
  rcases page with ⟨domain, number, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.insert?] at inserted <;> subst post <;>
    simp [Page.Contains, Page.entries, or_left_comm, or_comm]

/-- Address conflict and capacity exhaustion are distinct admission failures. -/
inductive InsertError where
  | invalidPage
  | addressConflict
  | full
  deriving DecidableEq, Repr

def Entry.Conflicts (entry : Entry) (page : Page) : Prop :=
  ∃ field ∈ entry.fields, field ∈ page.fields

instance entryConflictsDecidable (entry : Entry) (page : Page) :
    Decidable (entry.Conflicts page) := by
  unfold Entry.Conflicts
  infer_instance

/-- Validated insertion rejects an already-invalid page, then field reuse,
then physical exhaustion.  Success returns the new page together with its
canonical-address uniqueness proof; no caller may forget that boundary. -/
def Page.admitInsert (page : Page) (entry : Entry) :
    Except InsertError { post : Page // post.Valid } :=
  if _pageValid : page.Valid then
    if entry.Conflicts page then
      .error .addressConflict
    else
      match page.insert? entry with
      | none => .error .full
      | some post =>
          if postValid : post.Valid then .ok ⟨post, postValid⟩
          else .error .addressConflict
  else
    .error .invalidPage

theorem Page.admitInsert_exact {page : Page} {entry : Entry}
    {post : { post : Page // post.Valid }}
    (admitted : page.admitInsert entry = .ok post) :
    page.Valid ∧ ¬ entry.Conflicts page ∧ page.insert? entry = some post.val := by
  unfold Page.admitInsert at admitted
  split at admitted
  next valid =>
    split at admitted
    next => contradiction
    next fresh =>
      cases inserted : page.insert? entry with
      | none => simp [inserted] at admitted
      | some candidate =>
          simp only [inserted] at admitted
          split at admitted
          next =>
            have equal := congrArg Subtype.val (Except.ok.inj admitted)
            exact ⟨valid, fresh, congrArg some equal⟩
          next => contradiction
  next => contradiction

/-- One physical page update for a whole fresh batch. A later failure exposes
no partially updated page. Every step checks canonical-coordinate freshness. -/
def Page.admitInsertMany (page : Page) : List Entry →
    Except InsertError { post : Page // post.Valid }
  | [] =>
      if valid : page.Valid then .ok ⟨page, valid⟩ else .error .invalidPage
  | entry :: rest =>
      match page.admitInsert entry with
      | .error reason => .error reason
      | .ok post => post.val.admitInsertMany rest

/-- Every original entry survives an accepted insertion batch unchanged. -/
theorem Page.admitInsertMany_retains {page : Page} {entries : List Entry}
    {post : { post : Page // post.Valid }}
    (admitted : page.admitInsertMany entries = .ok post)
    (entry : Entry) (member : page.Contains entry) : post.val.Contains entry := by
  induction entries generalizing page with
  | nil =>
      simp only [Page.admitInsertMany] at admitted
      split at admitted
      next =>
        have equal := congrArg Subtype.val (Except.ok.inj admitted)
        exact equal ▸ member
      next => contradiction
  | cons first rest induction =>
      simp only [Page.admitInsertMany] at admitted
      cases head : page.admitInsert first with
      | error reason => simp [head] at admitted
      | ok next =>
          apply induction (by simpa [head] using admitted)
          exact (Page.insert_member_iff (Page.admitInsert_exact head).2.2 entry).mpr
            (Or.inr member)

/-- All requested records are present together in the returned valid page.
A conflicting later grant cannot overwrite an earlier grant in the batch. -/
theorem Page.admitInsertMany_contains {page : Page} {entries : List Entry}
    {post : { post : Page // post.Valid }}
    (admitted : page.admitInsertMany entries = .ok post)
    (entry : Entry) (member : entry ∈ entries) : post.val.Contains entry := by
  induction entries generalizing page with
  | nil => simp at member
  | cons first rest induction =>
      simp only [Page.admitInsertMany] at admitted
      cases head : page.admitInsert first with
      | error reason => simp [head] at admitted
      | ok next =>
          have tail : next.val.admitInsertMany rest = .ok post := by
            simpa [head] using admitted
          rcases List.mem_cons.mp member with rfl | inTail
          · apply Page.admitInsertMany_retains tail
            exact Page.insert_contains (Page.admitInsert_exact head).2.2
          · exact induction tail inTail

def Page.mapEntries (page : Page) (transform : Entry → Entry) : Page :=
  { page with
      slot0 := page.slot0.map transform
      slot1 := page.slot1.map transform
      slot2 := page.slot2.map transform
      slot3 := page.slot3.map transform }

theorem Page.entries_mapEntries (page : Page) (transform : Entry → Entry) :
    (page.mapEntries transform).entries = page.entries.map transform := by
  rcases page with ⟨domain, number, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.entries, Page.mapEntries]

def Entry.replace (old replacement entry : Entry) : Entry :=
  if entry = old then replacement else entry

/-- Exact expected-entry replacement, never an implicit upsert. On a valid
page the expected entry has only one occurrence because its fields are unique. -/
def Page.replaceEntry? (page : Page) (old replacement : Entry) : Option Page :=
  if page.Contains old then some (page.mapEntries (Entry.replace old replacement))
  else none

inductive ReplaceError where
  | invalidPage
  | missingEntry
  | addressConflict
  deriving DecidableEq, Repr

def Page.admitReplace (page : Page) (old replacement : Entry) :
    Except ReplaceError { post : Page // post.Valid } :=
  if _valid : page.Valid then
    match page.replaceEntry? old replacement with
    | none => .error .missingEntry
    | some post =>
        if valid : post.Valid then .ok ⟨post, valid⟩
        else .error .addressConflict
  else .error .invalidPage

theorem Page.replaceEntry_exact {page post : Page} {old replacement : Entry}
    (replaced : page.replaceEntry? old replacement = some post) :
    page.Contains old ∧
      post = page.mapEntries (Entry.replace old replacement) := by
  unfold Page.replaceEntry? at replaced
  split at replaced
  next member => exact ⟨member, (Option.some.inj replaced).symm⟩
  next => contradiction

theorem Page.replaceEntry_address {page post : Page} {old replacement : Entry}
    (replaced : page.replaceEntry? old replacement = some post) :
    post.authorityDomain = page.authorityDomain ∧
      post.pageNumber = page.pageNumber := by
  rw [(Page.replaceEntry_exact replaced).2]
  exact ⟨rfl, rfl⟩

theorem Page.replaceEntry_contains {page post : Page} {old replacement : Entry}
    (replaced : page.replaceEntry? old replacement = some post) :
    post.Contains replacement := by
  obtain ⟨member, exactPost⟩ := Page.replaceEntry_exact replaced
  rw [exactPost]
  change replacement ∈ (page.mapEntries (Entry.replace old replacement)).entries
  rw [Page.entries_mapEntries]
  exact List.mem_map.mpr ⟨old, member, by simp [Entry.replace]⟩

theorem Page.replaceEntry_retains {page post : Page} {old replacement : Entry}
    (replaced : page.replaceEntry? old replacement = some post)
    (entry : Entry) (member : page.Contains entry) (different : entry ≠ old) :
    post.Contains entry := by
  rw [(Page.replaceEntry_exact replaced).2]
  change entry ∈ (page.mapEntries (Entry.replace old replacement)).entries
  rw [Page.entries_mapEntries]
  exact List.mem_map.mpr ⟨entry, member, by simp [Entry.replace, different]⟩

theorem Page.admitReplace_exact {page : Page} {old replacement : Entry}
    {post : { post : Page // post.Valid }}
    (admitted : page.admitReplace old replacement = .ok post) :
    page.Valid ∧ page.Contains old ∧
      post.val = page.mapEntries (Entry.replace old replacement) := by
  unfold Page.admitReplace at admitted
  split at admitted
  next valid =>
    cases replaced : page.replaceEntry? old replacement with
    | none => simp [replaced] at admitted
    | some candidate =>
        simp only [replaced] at admitted
        split at admitted
        next =>
          have equal := congrArg Subtype.val (Except.ok.inj admitted)
          exact ⟨valid, (Page.replaceEntry_exact replaced).1,
            equal.symm.trans (Page.replaceEntry_exact replaced).2⟩
        next => contradiction
  next => contradiction

/-! ## Projection into `CredentialAuthorityState` -/

def Page.toCanonicalState (page : Page) :
    LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields := page.entries.foldl Entry.install 0
  resources := fun resource => nomatch resource

theorem installEntries_frame (entries : List Entry)
    (fields : FieldStore CredentialAuthorityState.schema.{0, 0})
    (field : AuthorityField) (outside : field ∉ entries.flatMap Entry.fields) :
    (entries.foldl Entry.install fields) field = fields field := by
  induction entries generalizing fields with
  | nil => rfl
  | cons entry entries induction =>
      have outsideHead : field ∉ entry.fields := by
        intro member
        exact outside (by simp [member])
      have outsideTail : field ∉ entries.flatMap Entry.fields := by
        intro member
        exact outside (by simp [member])
      change (entries.foldl Entry.install (Entry.install fields entry)) field = _
      rw [induction _ outsideTail, Entry.install_frame entry fields field outsideHead]

theorem installEntries_coordinate_congr (entries : List Entry)
    (left right : FieldStore CredentialAuthorityState.schema.{0, 0})
    (field : AuthorityField) (equal : left field = right field) :
    (entries.foldl Entry.install left) field =
      (entries.foldl Entry.install right) field := by
  induction entries generalizing left right with
  | nil => exact equal
  | cons entry rest induction =>
      apply induction
      by_cases inside : field ∈ entry.fields
      · rw [Entry.install_exact entry left field inside,
          Entry.install_exact entry right field inside]
      · rw [Entry.install_frame entry left field inside,
          Entry.install_frame entry right field inside]
        exact equal

theorem installEntries_replace_frame (entries : List Entry)
    (fields : FieldStore CredentialAuthorityState.schema.{0, 0})
    (old replacement : Entry) (field : AuthorityField)
    (outsideOld : field ∉ old.fields) (outsideNew : field ∉ replacement.fields) :
    ((entries.map (Entry.replace old replacement)).foldl Entry.install fields) field =
      (entries.foldl Entry.install fields) field := by
  induction entries generalizing fields with
  | nil => rfl
  | cons entry rest induction =>
      change
        ((rest.map (Entry.replace old replacement)).foldl Entry.install
          (Entry.install fields (Entry.replace old replacement entry))) field =
        (rest.foldl Entry.install (Entry.install fields entry)) field
      rw [induction]
      apply installEntries_coordinate_congr
      by_cases same : entry = old
      · subst entry
        simp only [Entry.replace, ↓reduceIte]
        rw [Entry.install_frame replacement fields field outsideNew,
          Entry.install_frame old fields field outsideOld]
      · simp [Entry.replace, same]

theorem installEntries_exact (entries : List Entry)
    (valid : (entries.flatMap Entry.fields).Nodup)
    (entry : Entry) (member : entry ∈ entries) (field : AuthorityField)
    (inside : field ∈ entry.fields)
    (fields : FieldStore CredentialAuthorityState.schema.{0, 0}) :
    (entries.foldl Entry.install fields) field = Entry.install 0 entry field := by
  induction entries generalizing fields with
  | nil => simp at member
  | cons head tail induction =>
      have validAppend : (head.fields ++ tail.flatMap Entry.fields).Nodup := valid
      have tailValid := (List.nodup_append.mp validAppend).2.1
      rcases List.mem_cons.mp member with equal | inTail
      · subst head
        have outsideTail : field ∉ tail.flatMap Entry.fields := by
          intro inTail
          exact List.disjoint_of_nodup_append validAppend inside inTail
        change (tail.foldl Entry.install (Entry.install fields entry)) field = _
        rw [installEntries_frame tail _ field outsideTail]
        exact Entry.install_exact entry fields field inside
      · exact induction tailValid inTail (Entry.install fields head)

/-- Every valid committed entry projects to its exact dependent authority
value; no later page entry can replace a capability or epoch behind it. -/
theorem Page.entry_projection_exact (page : Page) (valid : page.Valid)
    (entry : Entry) (member : page.Contains entry) (field : AuthorityField)
    (inside : field ∈ entry.fields) :
    page.toCanonicalState.fields field = Entry.install 0 entry field :=
  installEntries_exact page.entries valid entry member field inside 0

/-- Absence is retained as absence, before an AuthState reader chooses a
zero/false default. This theorem covers every authority coordinate. -/
theorem Page.absent_projection (page : Page) (field : AuthorityField)
    (outside : field ∉ page.fields) :
    page.toCanonicalState.fields field = none :=
  installEntries_frame page.entries 0 field outside

/-- Exact replacement changes no authority coordinate outside the declared
old/new field footprint, including fields that remain absent. -/
theorem Page.replaceEntry_projection_frame {page post : Page} {old replacement : Entry}
    (replaced : page.replaceEntry? old replacement = some post)
    (field : AuthorityField) (outsideOld : field ∉ old.fields)
    (outsideNew : field ∉ replacement.fields) :
    post.toCanonicalState.fields field = page.toCanonicalState.fields field := by
  rw [(Page.replaceEntry_exact replaced).2]
  simp only [Page.toCanonicalState, Page.entries_mapEntries]
  exact installEntries_replace_frame page.entries 0 old replacement field
    outsideOld outsideNew

def Page.policyEpochAt (page : Page) (policy : PolicyId) : Epoch :=
  (show Option Epoch from
    page.toCanonicalState.fields (.policyEpoch policy)).getD (show Epoch from 0)

def Page.policyAddressAt (page : Page) (policy : PolicyId)
    (epoch : Epoch) : Digest :=
  (show Option Digest from
    page.toCanonicalState.fields (.policyAddress policy epoch)).getD ⟨0⟩

def Page.readCapability (page : Page) (kind : ResourceKind)
    (id : CapabilityId) : Option (StoredCapability kind) :=
  page.toCanonicalState.fields (.capability kind id)

def Page.issuerEpochAt (page : Page) (issuer : IssuerId) : Epoch :=
  (page.toCanonicalState.fields (.issuerEpoch issuer)).getD (show Epoch from 0)

def Page.subjectKeyEpochAt (page : Page) (subject : SubjectId) : Epoch :=
  (page.toCanonicalState.fields (.subjectKeyEpoch subject)).getD (show Epoch from 0)

def Page.isNullified (page : Page) (id : Nat) : Bool :=
  (page.toCanonicalState.fields (.nullifier id)).getD false

theorem Page.capability_exact (page : Page) (valid : page.Valid)
    (kind : ResourceKind) (stored : StoredCapability kind)
    (member : page.Contains (.capability kind stored)) :
    page.readCapability kind stored.head.id = some stored := by
  have exactField := page.entry_projection_exact valid (.capability kind stored)
    member (.capability kind stored.head.id) (by simp [Entry.fields])
  simpa [Page.readCapability, Entry.install] using exactField

theorem Page.issuerEpoch_exact (page : Page) (valid : page.Valid)
    (issuer : IssuerId) (epoch : Epoch)
    (member : page.Contains (.issuerEpoch issuer epoch)) :
    page.issuerEpochAt issuer = epoch := by
  have exactField := page.entry_projection_exact valid (.issuerEpoch issuer epoch)
    member (.issuerEpoch issuer) (by simp [Entry.fields])
  unfold Page.issuerEpochAt
  rw [exactField]
  simp [Entry.install]

theorem Page.subjectKeyEpoch_exact (page : Page) (valid : page.Valid)
    (subject : SubjectId) (epoch : Epoch)
    (member : page.Contains (.subjectKeyEpoch subject epoch)) :
    page.subjectKeyEpochAt subject = epoch := by
  have exactField := page.entry_projection_exact valid (.subjectKeyEpoch subject epoch)
    member (.subjectKeyEpoch subject) (by simp [Entry.fields])
  unfold Page.subjectKeyEpochAt
  rw [exactField]
  simp [Entry.install]

theorem Page.nullifier_exact (page : Page) (valid : page.Valid)
    (nullifierId : Nat) (consumed : Bool)
    (member : page.Contains (.nullifier nullifierId consumed)) :
    page.isNullified nullifierId = consumed := by
  have exactField := page.entry_projection_exact valid (.nullifier nullifierId consumed)
    member (.nullifier nullifierId) (by simp [Entry.fields])
  unfold Page.isNullified
  rw [exactField]
  simp [Entry.install]

def Entry.revokedKey? : Entry -> Option RevocationKey
  | .revocation key true => some key
  | _ => none

def Page.revoked (page : Page) : Finset RevocationKey :=
  (page.entries.filterMap Entry.revokedKey?).toFinset.filter fun key =>
    (show Option Bool from page.toCanonicalState.fields (.revoked key)).getD false

/-- The page root is the committed policy and revocation root.  Every policy
address and epoch is read back from the exact canonical sparse projection. -/
def Page.authState (page : Page) (root : Digest) : AuthState where
  capabilityRoot := root
  revocationRoot := root
  policyRoot := root
  policyAddress := page.policyAddressAt
  revoked := page.revoked
  issuerEpoch := page.issuerEpochAt
  policyEpoch := page.policyEpochAt
  subjectKeyEpoch := page.subjectKeyEpochAt

@[simp] theorem Page.authState_policyRoot (page : Page) (root : Digest) :
    (page.authState root).policyRoot = root :=
  rfl

@[simp] theorem Page.authState_policyAddress (page : Page) (root : Digest)
    (policy : PolicyId) (epoch : Epoch) :
    (page.authState root).policyAddress policy epoch =
      page.policyAddressAt policy epoch :=
  rfl

/-! ## Stable framed materialization -/

def schema : CellState.Schema where
  Field := Unit
  FieldType := fun _ => Page
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun resource => resource.elim

def stateOfOption : Option Page -> LogicalState schema
  | none =>
      { fields := 0
        resources := fun resource => nomatch resource }
  | some page =>
      { fields := (0 : FieldStore schema).write () page
        resources := fun resource => nomatch resource }

def pageAt (state : LogicalState schema) : Option Page :=
  state.fields ()

/-- The physical schema owns this projection. Request callers select neither
the authority field interpretation nor an independently supplied root. -/
def projection : CredentialAuthorityState.StateProjection schema where
  toCanonicalState logical :=
    match pageAt logical with
    | some page => page.toCanonicalState
    | none =>
        { fields := 0
          resources := fun resource => nomatch resource }
  revocationKeys logical :=
    match pageAt logical with
    | some page => page.revoked
    | none => ∅

@[simp] theorem projection_present (page : Page) :
    projection.toCanonicalState (stateOfOption (some page)) =
      page.toCanonicalState := rfl

@[simp] theorem projection_absent :
    projection.toCanonicalState (stateOfOption none) =
      { fields := 0, resources := fun resource => nomatch resource } := rfl

theorem state_ext (state : LogicalState schema) :
    state = stateOfOption (pageAt state) := by
  cases state with
  | mk fields resources =>
      have resourcesExact :
          resources = fun resource => nomatch resource := by
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
      | some page =>
          have fieldsExact :
              fields = (0 : FieldStore schema).write () page := by
            apply DFinsupp.ext
            intro field
            cases field
            simp [present]
          rw [fieldsExact, resourcesExact]
          rfl

def stateStream : StreamCodec (LogicalState schema) :=
  StreamCodec.xmap (StreamCodec.option pageStream) pageAt stateOfOption
    (by intro state; exact (state_ext state).symm)

/-- Stable marker: `LOOM/AUTH/POLICYPAGE`, wire version 3, capacity 4.
Version 3 adds committed signing keys, atomically paired with their current
subject epoch. Prior wire versions are not silently reinterpreted. -/
def wireFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73, 67, 89, 80, 65,
    71, 69, 3, 4]

def decodeStateRaw : List UInt8 -> Option (LogicalState schema)
  | 76 :: 79 :: 79 :: 77 :: 47 :: 65 :: 85 :: 84 :: 72 :: 47 :: 80 :: 79 ::
      76 :: 73 :: 67 :: 89 :: 80 :: 65 :: 71 :: 69 :: 3 :: 4 :: payload =>
      stateStream.toLawful.decode payload
  | _ => none

def encodeState (state : LogicalState schema) : List UInt8 :=
  wireFrame ++ stateStream.encode state

@[simp] theorem decodeStateRaw_encode (state : LogicalState schema) :
    decodeStateRaw (encodeState state) = some state := by
  change stateStream.toLawful.decode (stateStream.encode state) = some state
  exact stateStream.toLawful.decode_encode state

/-- Only one exact spelling of every materialized authority state is admitted.
This rejects unsorted/duplicate finite-set elements, natural/tag aliases, and
trailing bytes; the raw parser alone is deliberately not an admission gate. -/
def decodeState (bytes : List UInt8) : Option (LogicalState schema) := do
  let state ← decodeStateRaw bytes
  if encodeState state = bytes then some state else none

/-- Earlier frames never reinterpret the expanded current entry vocabulary. -/
theorem decodeState_rejects_v2 (payload : List UInt8) :
    decodeState ([76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73,
      67, 89, 80, 65, 71, 69, 2, 4] ++ payload) = none := rfl

theorem decodeState_rejects_v1 (payload : List UInt8) :
    decodeState ([76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73,
      67, 89, 80, 65, 71, 69, 1, 4] ++ payload) = none := rfl

@[simp] theorem decodeState_encode (state : LogicalState schema) :
    decodeState (encodeState state) = some state := by
  simp [decodeState]

theorem decodeState_canonical {bytes : List UInt8}
    {state : LogicalState schema} (accepted : decodeState bytes = some state) :
    encodeState state = bytes := by
  unfold decodeState at accepted
  cases raw : decodeStateRaw bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical =>
        cases Option.some.inj accepted
        exact canonical
      next => contradiction

theorem decodeState_some_iff (bytes : List UInt8) (state : LogicalState schema) :
    decodeState bytes = some state ↔ bytes = encodeState state := by
  constructor
  · intro accepted
    exact (decodeState_canonical accepted).symm
  · intro exactBytes
    rw [exactBytes, decodeState_encode]

theorem reject_noncanonical {bytes : List UInt8} {state : LogicalState schema}
    (parsed : decodeStateRaw bytes = some state)
    (different : encodeState state ≠ bytes) : decodeState bytes = none := by
  simp [decodeState, parsed, different]

def stateCodec : LawfulCodec (LogicalState schema) where
  encode := encodeState
  decode := decodeState
  decode_encode := decodeState_encode

def rootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 65, 85, 84, 72, 46, 80, 79, 76, 73, 67, 89, 80, 65,
    71, 69, 46, 82, 79, 79, 84, 47, 118, 51]

theorem wire_and_root_domains_distinct : wireFrame ≠ rootCustomization := by
  decide

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : CellState.Materializer schema Digest where
  codec := stateCodec
  rootBytes := rootBytes

/-- The durable receiver hashes the exact canonical authority payload it
received, under this materializer's own domain. No equality with another
schema's root function is assumed. -/
theorem decoded_root_exact {bytes : List UInt8} {state : LogicalState schema}
    (accepted : stateCodec.decode bytes = some state) :
    (CellState.materialize materializer state).root = rootBytes bytes := by
  change rootBytes (encodeState state) = rootBytes bytes
  exact congrArg rootBytes (decodeState_canonical accepted)

@[simp] theorem encode_absent :
    stateCodec.encode (stateOfOption none) = wireFrame ++ [0] :=
  rfl

@[simp] theorem encode_present (page : Page) :
    stateCodec.encode (stateOfOption (some page)) =
      wireFrame ++ 1 :: pageStream.encode page :=
  rfl

@[simp] theorem reject_wrong_version (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73, 67, 89,
        80, 65, 71, 69, 1, 4] ++ payload) = none := by
  simp [decodeState, decodeStateRaw]

@[simp] theorem reject_wrong_capacity (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73, 67, 89,
        80, 65, 71, 69, 2, 5] ++ payload) = none := by
  simp [decodeState, decodeStateRaw]

/-! ## Pair-scoped collision-resistance boundary -/

structure Collision (left right : LogicalState schema) : Prop where
  statesDifferent : left ≠ right
  bytesDifferent : stateCodec.encode left ≠ stateCodec.encode right
  rootsEqual : rootBytes (stateCodec.encode left) =
    rootBytes (stateCodec.encode right)

theorem collision_of_root_eq_of_ne
    {left right : LogicalState schema} (different : left ≠ right)
    (sameRoot : rootBytes (stateCodec.encode left) =
      rootBytes (stateCodec.encode right)) :
    Collision left right where
  statesDifferent := different
  bytesDifferent := by
    intro sameBytes
    apply different
    exact lawfulCodec_encode_injective stateCodec sameBytes
  rootsEqual := sameRoot

structure PairBindingPremise (left right : LogicalState schema) : Prop where
  noCollision : ¬ Collision left right

theorem state_eq_of_root_eq
    {left right : LogicalState schema}
    (binding : PairBindingPremise left right)
    (sameRoot : rootBytes (stateCodec.encode left) =
      rootBytes (stateCodec.encode right)) :
    left = right := by
  by_contra different
  exact binding.noCollision (collision_of_root_eq_of_ne different sameRoot)

/-! ## Closed policy-update and revocation witness -/

def examplePolicy : PolicyId := ⟨17⟩
def exampleRevocation : RevocationKey := .channel ⟨9⟩

def oldPolicy : Entry := .policy examplePolicy 2 ⟨2200⟩
def newPolicy : Entry := .policy examplePolicy 3 ⟨3300⟩
def activeRevocation : Entry := .revocation exampleRevocation true

def prePage : Page where
  authorityDomain := ⟨8100⟩
  pageNumber := 0
  slot0 := some oldPolicy
  slot1 := none
  slot2 := none
  slot3 := none

def postPage : Page where
  authorityDomain := prePage.authorityDomain
  pageNumber := prePage.pageNumber
  slot0 := some newPolicy
  slot1 := some activeRevocation
  slot2 := none
  slot3 := none

theorem prePage_valid : prePage.Valid := by
  decide

theorem postPage_valid : postPage.Valid := by
  decide

def preCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some prePage))

def postCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some postPage))

@[simp] theorem postCell_bytes :
    postCell.bytes = wireFrame ++ 1 :: pageStream.encode postPage :=
  rfl

@[simp] theorem postCell_root :
    postCell.root =
      (Sp800185Cshake256.hash rootCustomization
        (wireFrame ++ 1 :: pageStream.encode postPage)).digest :=
  rfl

@[simp] theorem post_policy_epoch_exact :
    postPage.policyEpochAt examplePolicy = 3 := by
  simp [Page.policyEpochAt, Page.toCanonicalState, Page.entries, postPage,
    Entry.install, newPolicy, activeRevocation, examplePolicy]
  rfl

@[simp] theorem post_policy_address_exact :
    postPage.policyAddressAt examplePolicy 3 = ⟨3300⟩ := by
  simp [Page.policyAddressAt, Page.toCanonicalState, Page.entries, postPage,
    Entry.install, newPolicy, activeRevocation, examplePolicy]
  rfl

@[simp] theorem old_policy_address_absent :
    postPage.policyAddressAt examplePolicy 2 = ⟨0⟩ := by
  change
    (((0 : FieldStore CredentialAuthorityState.schema.{0, 0}).write
        (.policyEpoch examplePolicy)
          (show CredentialAuthorityState.schema.{0, 0}.FieldType
              (.policyEpoch examplePolicy) from (3 : Epoch))).write
      (.policyAddress examplePolicy 3) ⟨3300⟩
      (.policyAddress examplePolicy 2)).getD ⟨0⟩ = ⟨0⟩
  rw [CellState.FieldStore.write_other
    (fields := (0 : FieldStore CredentialAuthorityState.schema.{0, 0}).write
      (.policyEpoch examplePolicy)
        (show CredentialAuthorityState.schema.{0, 0}.FieldType
            (.policyEpoch examplePolicy) from (3 : Epoch)))
    (field := .policyAddress examplePolicy 2)
    (other := .policyAddress examplePolicy 3)
    (different := by decide) (value := ⟨3300⟩)]
  rw [CellState.FieldStore.write_other
    (fields := (0 : FieldStore CredentialAuthorityState.schema.{0, 0}))
    (field := .policyAddress examplePolicy 2)
    (other := .policyEpoch examplePolicy)
    (different := by decide)
    (value := show CredentialAuthorityState.schema.{0, 0}.FieldType
        (.policyEpoch examplePolicy) from (3 : Epoch))]
  rfl

@[simp] theorem post_revocation_member :
    exampleRevocation ∈ postPage.revoked := by
  simp [Page.revoked, Page.entries, postPage, Entry.revokedKey?,
    activeRevocation, newPolicy, Page.toCanonicalState, Entry.install]
  rfl

@[simp] theorem committed_policy_root_exact :
    (postPage.authState postCell.root).policyRoot = postCell.root :=
  rfl

@[simp] theorem committed_policy_address_exact :
    (postPage.authState postCell.root).policyAddress examplePolicy 3 = ⟨3300⟩ :=
  post_policy_address_exact

def updatePatch : CellState.Patch schema Digest where
  expectedPreRoot := preCell.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some postPage }]
  resourceWrites := []

theorem updatePatch_accepted :
    ∃ validated : CellState.ValidatedPatch materializer preCell updatePatch,
      CellState.validate materializer preCell updatePatch =
        CellState.ValidationOutcome.accepted validated := by
  unfold CellState.validate
  rw [dif_pos (show updatePatch.expectedPreRoot = preCell.root from rfl)]
  rw [dif_pos
    (show updatePatch.fieldFootprint = updatePatch.namedFields by decide)]
  rw [dif_pos
    (show updatePatch.resourceFootprint = updatePatch.namedResources by decide)]
  exact ⟨_, rfl⟩

theorem accepted_post_exact
    (validated : CellState.ValidatedPatch materializer preCell updatePatch) :
    validated.apply = postCell := by
  apply CellState.Materialized.ext
  change
    { fields := CellState.applyFieldWrites updatePatch.fieldWrites
        preCell.logical.fields
      resources := CellState.applyResourceWrites updatePatch.resourceWrites
        preCell.logical.resources } =
      stateOfOption (some postPage)
  congr 1
  apply DFinsupp.ext
  intro field
  cases field
  simp [CellState.applyFieldWrites, updatePatch, preCell, stateOfOption,
    CellState.FieldStore.assign]

/-! ## Closed overflow and retained-membership witness -/

def fullPage : Page where
  authorityDomain := ⟨8200⟩
  pageNumber := 4
  slot0 := some (.revocation (.channel ⟨1⟩) true)
  slot1 := some (.revocation (.channel ⟨2⟩) true)
  slot2 := some (.revocation (.channel ⟨3⟩) true)
  slot3 := some (.revocation (.channel ⟨4⟩) true)

theorem fullPage_valid : fullPage.Valid := by
  decide

theorem fullPage_full : fullPage.Full := by
  decide

@[simp] theorem fullPage_overflow_rejected :
    fullPage.insert? (.policy ⟨99⟩ 1 ⟨9999⟩) = none :=
  rfl

@[simp] theorem fullPage_admission_reports_full :
    fullPage.admitInsert (.policy ⟨99⟩ 1 ⟨9999⟩) = .error .full := by
  decide

@[simp] theorem policy_address_conflict_rejected :
    postPage.admitInsert (.policy examplePolicy 4 ⟨4400⟩) =
      .error .addressConflict := by
  decide

@[simp] theorem fullPage_retains_membership :
    fullPage.Contains (.revocation (.channel ⟨1⟩) true) := by
  decide

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page.entry_projection_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Page.entry_projection_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page.admitInsertMany_contains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Page.admitInsertMany_contains
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page.replaceEntry_projection_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Page.replaceEntry_projection_frame
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.decodeState_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeState_canonical
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.decoded_root_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_root_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.pageOfTuple_tuple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pageOfTuple_tuple
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stateCodec
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.collision_of_root_eq_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collision_of_root_eq_of_ne
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.updatePatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms updatePatch_accepted
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.fullPage_overflow_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fullPage_overflow_rejected

end Minidregg.Compiler.CredentialAuthorityPageMaterializer
