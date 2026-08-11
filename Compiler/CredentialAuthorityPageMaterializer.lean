/-
# Compiler.CredentialAuthorityPageMaterializer -- bounded committed authority

`CredentialAuthorityState` is the canonical, unbounded sparse authority
semantics.  Its countability-selected materializer is an inhabitation witness,
not a production representation.  This module supplies one concrete bounded
representation shard: four policy/revocation entries with a stable wire frame,
prefix-decodable payload, and a Lean cSHAKE256 root over the exact bytes.

Each entry projects to the actual dependent `AuthorityField` addresses.  A
policy entry writes both the current epoch and the exact `(policy, epoch)`
content address; a revocation entry writes the canonical Boolean membership
cell.  The page's root is therefore the `policyRoot`/`revocationRoot` used by
its `AuthState` projection.  No parallel host-authored policy lookup exists.

Capacity is explicit.  `insert?` fills the first empty slot, never overwrites,
and returns `none` exactly for a full page.  Another page number extends the
authority domain; this page does not pretend the global authority universe is
finite.  As with the event-page representation, collision resistance is only
a pair-scoped premise, never an impossible global injection into 256 bits.
-/
import Compiler.Sp800185Cshake256
import Compiler.TypedAuthorizationRequestCodec
import Theory.CredentialAuthorityState

namespace Minidregg.Compiler.CredentialAuthorityPageMaterializer

open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
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

def capabilityIdStream : StreamCodec CapabilityId :=
  StreamCodec.xmap StreamCodec.nat CapabilityId.value CapabilityId.mk
    (by intro value; cases value; rfl)

def channelIdStream : StreamCodec ChannelId :=
  StreamCodec.xmap StreamCodec.nat ChannelId.value ChannelId.mk
    (by intro value; cases value; rfl)

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

/-- One bounded authority record.  Policy and revocation are different wire
constructors and cannot be retagged without changing bytes. -/
inductive Entry where
  | policy (policy : PolicyId) (epoch : Epoch) (address : Digest)
  | revocation (key : RevocationKey) (revoked : Bool)
  deriving DecidableEq, Repr

def entryStream : StreamCodec Entry where
  encode
    | .policy policy epoch address =>
        0 :: policyIdStream.encode policy ++ StreamCodec.nat.encode epoch ++
          digestStream.encode address
    | .revocation key revoked =>
        1 :: revocationKeyStream.encode key ++ StreamCodec.bool.encode revoked
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

/-- Exact canonical authority addresses written by one entry. -/
def Entry.fields : Entry -> List AuthorityField
  | .policy policyId epoch _address =>
      [.policyEpoch policyId, .policyAddress policyId epoch]
  | .revocation key _ => [.revoked key]

/-- Install one entry into the canonical sparse authority field carrier. -/
def Entry.install
    (fields : FieldStore CredentialAuthorityState.schema.{0, 0}) :
    Entry -> FieldStore CredentialAuthorityState.schema.{0, 0}
  | .policy policyId epoch address =>
      (fields.write (.policyEpoch policyId) epoch).write
        (.policyAddress policyId epoch) address
  | .revocation key revoked => fields.write (.revoked key) revoked

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

/-! ## Projection into `CredentialAuthorityState` -/

def Page.toCanonicalState (page : Page) :
    LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields := page.entries.foldl Entry.install 0
  resources := fun resource => nomatch resource

def Page.policyEpochAt (page : Page) (policy : PolicyId) : Epoch :=
  (show Option Epoch from
    page.toCanonicalState.fields (.policyEpoch policy)).getD (show Epoch from 0)

def Page.policyAddressAt (page : Page) (policy : PolicyId)
    (epoch : Epoch) : Digest :=
  (show Option Digest from
    page.toCanonicalState.fields (.policyAddress policy epoch)).getD ⟨0⟩

def Entry.revokedKey? : Entry -> Option RevocationKey
  | .revocation key true => some key
  | _ => none

def Page.revoked (page : Page) : Finset RevocationKey :=
  (page.entries.filterMap Entry.revokedKey?).toFinset

/-- The page root is the committed policy and revocation root.  Every policy
address and epoch is read back from the exact canonical sparse projection. -/
def Page.authState (page : Page) (root : Digest) : AuthState where
  capabilityRoot := root
  revocationRoot := root
  policyRoot := root
  policyAddress := page.policyAddressAt
  revoked := page.revoked
  issuerEpoch := fun _ => 0
  policyEpoch := page.policyEpochAt
  subjectKeyEpoch := fun _ => 0

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

/-- Stable marker: `LOOM/AUTH/POLICYPAGE`, wire version 1, capacity 4. -/
def wireFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73, 67, 89, 80, 65,
    71, 69, 1, 4]

def decodeState : List UInt8 -> Option (LogicalState schema)
  | 76 :: 79 :: 79 :: 77 :: 47 :: 65 :: 85 :: 84 :: 72 :: 47 :: 80 :: 79 ::
      76 :: 73 :: 67 :: 89 :: 80 :: 65 :: 71 :: 69 :: 1 :: 4 :: payload =>
      stateStream.toLawful.decode payload
  | _ => none

def stateCodec : LawfulCodec (LogicalState schema) where
  encode state := wireFrame ++ stateStream.encode state
  decode := decodeState
  decode_encode := by
    intro state
    change stateStream.toLawful.decode (stateStream.encode state) = some state
    exact stateStream.toLawful.decode_encode state

def rootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 65, 85, 84, 72, 46, 80, 79, 76, 73, 67, 89, 80, 65,
    71, 69, 46, 82, 79, 79, 84, 47, 118, 49]

theorem wire_and_root_domains_distinct : wireFrame ≠ rootCustomization := by
  decide

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : CellState.Materializer schema Digest where
  codec := stateCodec
  rootBytes := rootBytes

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
        80, 65, 71, 69, 2, 4] ++ payload) = none := by
  simp [decodeState]

@[simp] theorem reject_wrong_capacity (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73, 67, 89,
        80, 65, 71, 69, 1, 5] ++ payload) = none := by
  simp [decodeState]

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
    activeRevocation, newPolicy]

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

/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.pageOfTuple_tuple' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms pageOfTuple_tuple
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stateCodec
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.collision_of_root_eq_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collision_of_root_eq_of_ne
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.updatePatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms updatePatch_accepted
/-- info: 'Minidregg.Compiler.CredentialAuthorityPageMaterializer.fullPage_overflow_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fullPage_overflow_rejected

end Minidregg.Compiler.CredentialAuthorityPageMaterializer
