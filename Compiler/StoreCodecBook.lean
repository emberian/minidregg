/-
# Compiler.StoreCodecBook -- the finite Book as a store at the Book layout

The existing Book codec (`CanonicalResourcePageMaterializer.bookStream`) is not
literally an instance of `StoreCodec`: it writes three sections (sorted
accounts, sorted nonzero balances, sorted present leases) each ordered by a
Lean `LinearOrder` (numeric order, and `Nat.pair` order for balance
coordinates), inside an outer present/absent tag.  `StoreCodec` writes one
list of namespace-tagged addresses in address-BYTE order.  The bytes differ,
so this module states the smallest adapter instead of a byte equality:

* `layout` — namespaces `account : AccountId ↦ Unit`,
  `balance : AccountId × AssetId ↦ Int`, `lease : LeaseId ↦ LeaseRecord`;
* `bookStore` / `bookOfStore` — the Book's exact pointwise meaning as a store
  (a zero balance is absence, as in the Book), with
  `bookOfStore_bookStore : bookOfStore (bookStore book) = book`;
* `decodeBook` — `StoreCodec.decode` at this layout, then canonical re-encoding
  of the Book, so a store that is not the image of a Book (an explicit zero
  balance) is refused (`explicit_zero_balance_rejected`);
* `transcode` — every cell the existing codec accepts maps to a cell this
  codec accepts denoting the same Book (`transcode_sound`, `transcode_complete`).

The outer present/absent Book tag is not a store namespace: under the world
model an absent Book is an absent cell, not a cell holding a marker.
-/
import Compiler.StoreCodec
import Compiler.CanonicalResourcePageMaterializer

namespace Minidregg.Compiler.StoreCodecBook

open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Theory.CanonicalResourceKernel

set_option autoImplicit false

inductive Space
  | account
  | balance
  | lease
  deriving DecidableEq, Repr

def Space.Key : Space → Type
  | .account => AccountId
  | .balance => AccountId × AssetId
  | .lease => LeaseId

def Space.Value : Space → Type
  | .account => Unit
  | .balance => Int
  | .lease => LeaseRecord

/-- Every Book namespace is RAM here; whether registrations and leases become
append-only is a kernel decision for the Book's own lane, not a codec fact. -/
instance Space.keyDecEq : (space : Space) → DecidableEq (Space.Key space)
  | .account => inferInstanceAs (DecidableEq Nat)
  | .balance => inferInstanceAs (DecidableEq (Nat × Nat))
  | .lease => inferInstanceAs (DecidableEq Nat)

instance Space.valueDecEq : (space : Space) → DecidableEq (Space.Value space)
  | .account => inferInstanceAs (DecidableEq Unit)
  | .balance => inferInstanceAs (DecidableEq Int)
  | .lease => inferInstanceAs (DecidableEq LeaseRecord)

def layout : Layout.{0, 0, 0} where
  Namespace := Space
  Key := Space.Key
  Value := Space.Value
  discipline _ := .ram

def spaceStream : StreamCodec Space where
  encode
    | .account => [0]
    | .balance => [1]
    | .lease => [2]
  decodePrefix
    | 0 :: suffix => some (.account, suffix)
    | 1 :: suffix => some (.balance, suffix)
    | 2 :: suffix => some (.lease, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def keyStream : (space : Space) → StreamCodec (Space.Key space)
  | .account => StreamCodec.nat
  | .balance => StreamCodec.product StreamCodec.nat StreamCodec.nat
  | .lease => StreamCodec.nat

def valueStream : (space : Space) → StreamCodec (Space.Value space)
  | .account => unitStream
  | .balance => IntStream.intStream
  | .lease => CanonicalResourcePageMaterializer.leaseStream

def wire : Wire layout where
  name := "dregg/book/v1"
  namespaces := [.account, .balance, .lease]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := spaceStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId
    | .account => "nat/base255"
    | .balance => "nat/base255 x nat/base255"
    | .lease => "nat/base255"
  valueCodecId
    | .account => "unit/empty"
    | .balance => IntStream.intCodecId
    | .lease => "lease-record/v1"

/-! ## The Book's pointwise meaning as a store -/

def bookValue (book : Book) : (address : Address layout) → Option (layout.Value address.1)
  | ⟨.account, account⟩ => if (account : AccountId) ∈ book.accounts then some () else none
  | ⟨.balance, coordinate⟩ =>
      if book.balances (coordinate : AccountId × AssetId) = 0 then none
      else some (book.balances coordinate)
  | ⟨.lease, lease⟩ => book.leaseRecords (lease : LeaseId)

def accountAddress : AccountId ↪ Address layout := ⟨fun account => ⟨.account, account⟩, by
  intro left right same; simpa using same⟩

def balanceAddress : (AccountId × AssetId) ↪ Address layout := ⟨fun coordinate => ⟨.balance, coordinate⟩, by
  intro left right same; simpa using same⟩

def leaseAddress : LeaseId ↪ Address layout := ⟨fun lease => ⟨.lease, lease⟩, by
  intro left right same; simpa using same⟩

def bookSupport (book : Book) : Finset (Address layout) :=
  book.accounts.map accountAddress ∪ book.balances.support.map balanceAddress ∪
    book.leaseRecords.support.map leaseAddress

def bookStore (book : Book) : Store layout :=
  DFinsupp.mk (bookSupport book) fun address => bookValue book address.1

theorem bookStore_apply (book : Book) (address : Address layout) :
    (bookStore book) address = bookValue book address := by
  unfold bookStore
  rw [DFinsupp.mk_apply]
  split_ifs with member
  · rfl
  · rcases address with ⟨space, key⟩
    cases space
    · have absent : key ∉ book.accounts := by
        simpa [bookSupport, accountAddress, balanceAddress, leaseAddress] using member
      change (0 : Option Unit) = if key ∈ book.accounts then some () else none
      rw [if_neg absent]
      rfl
    · have absent : book.balances key = 0 := by
        simpa [bookSupport, accountAddress, balanceAddress, leaseAddress,
          DFinsupp.mem_support_toFun] using member
      change (0 : Option Int) =
        if book.balances key = 0 then none else some (book.balances key)
      rw [if_pos absent]
      rfl
    · have absent : book.leaseRecords key = none := by
        simpa [bookSupport, accountAddress, balanceAddress, leaseAddress,
          DFinsupp.mem_support_toFun] using member
      change (0 : Option LeaseRecord) = book.leaseRecords key
      rw [absent]
      rfl

def accountOf : Address layout → AccountId
  | ⟨.account, account⟩ => account
  | _ => 0

def balanceOf : Address layout → AccountId × AssetId
  | ⟨.balance, coordinate⟩ => coordinate
  | _ => (0, 0)

def leaseOf : Address layout → LeaseId
  | ⟨.lease, lease⟩ => lease
  | _ => 0

/-- The store's `account` namespace, re-indexed by account. -/
def accountsOf (store : Store layout) : Π₀ _ : AccountId, Option Unit :=
  DFinsupp.comapDomain' (β := fun address : Address layout => Option (layout.Value address.1))
    (fun account : AccountId => (⟨Space.account, account⟩ : Address layout))
    (h' := accountOf) (fun _ => rfl) store

def balancesOf (store : Store layout) : Π₀ _ : AccountId × AssetId, Option Int :=
  DFinsupp.comapDomain' (β := fun address : Address layout => Option (layout.Value address.1))
    (fun coordinate : AccountId × AssetId => (⟨Space.balance, coordinate⟩ : Address layout))
    (h' := balanceOf) (fun _ => rfl) store

def leasesOf (store : Store layout) : Π₀ _ : LeaseId, Option LeaseRecord :=
  DFinsupp.comapDomain' (β := fun address : Address layout => Option (layout.Value address.1))
    (fun lease : LeaseId => (⟨Space.lease, lease⟩ : Address layout))
    (h' := leaseOf) (fun _ => rfl) store

/-- Read a store at the Book layout as a Book; absence of a balance is zero. -/
def bookOfStore (store : Store layout) : Book where
  accounts := (accountsOf store).support
  balances := DFinsupp.mapRange (β₁ := fun _ : AccountId × AssetId => Option Int)
    (β₂ := fun _ => Int) (fun _ value => value.getD 0) (fun _ => rfl) (balancesOf store)
  leaseRecords := leasesOf store

theorem bookOfStore_account (store : Store layout) (account : AccountId) :
    account ∈ (bookOfStore store).accounts ↔
      store ⟨Space.account, account⟩ ≠ none := by
  change account ∈ (accountsOf store).support ↔ _
  rw [DFinsupp.mem_support_toFun]
  rfl

theorem balancesOf_apply (store : Store layout) (coordinate : AccountId × AssetId) :
    balancesOf store coordinate = store ⟨Space.balance, coordinate⟩ :=
  rfl

theorem bookOfStore_balance (store : Store layout) (coordinate : AccountId × AssetId) :
    (bookOfStore store).balances coordinate = (balancesOf store coordinate).getD 0 := by
  change (DFinsupp.mapRange (β₁ := fun _ : AccountId × AssetId => Option Int)
    (β₂ := fun _ => Int) (fun _ value => value.getD 0) (fun _ => rfl) (balancesOf store))
      coordinate = _
  rw [DFinsupp.mapRange_apply]

theorem bookOfStore_lease (store : Store layout) (lease : LeaseId) :
    (bookOfStore store).leaseRecords lease = store ⟨Space.lease, lease⟩ :=
  rfl

theorem book_ext {left right : Book} (accounts : left.accounts = right.accounts)
    (balances : left.balances = right.balances)
    (leases : left.leaseRecords = right.leaseRecords) : left = right := by
  cases left
  cases right
  cases accounts
  cases balances
  cases leases
  rfl

theorem bookOfStore_bookStore (book : Book) : bookOfStore (bookStore book) = book := by
  apply book_ext
  · ext account
    rw [bookOfStore_account, bookStore_apply]
    change (if account ∈ book.accounts then some () else none) ≠ none ↔ _
    split_ifs with member <;> simp [member]
  · apply DFinsupp.ext
    intro coordinate
    rw [bookOfStore_balance, balancesOf_apply, bookStore_apply]
    change (if book.balances coordinate = 0 then none
      else some (book.balances coordinate)).getD 0 = book.balances coordinate
    split_ifs with zero
    · exact zero.symm
    · rfl
  · apply DFinsupp.ext
    intro lease
    rw [bookOfStore_lease, bookStore_apply]
    rfl

/-! ## The Book codec as an instance of the store codec -/

def encodeBook (book : Book) : List UInt8 :=
  encode wire (bookStore book)

def decodeBook (bytes : List UInt8) : Option Book := do
  let store ← decode wire bytes
  let book := bookOfStore store
  if encodeBook book = bytes then some book else none

theorem decodeBook_encodeBook (book : Book) : decodeBook (encodeBook book) = some book := by
  simp [decodeBook, encodeBook, decode_encode, bookOfStore_bookStore]

theorem decodeBook_eq_some_iff (bytes : List UInt8) (book : Book) :
    decodeBook bytes = some book ↔ encodeBook book = bytes := by
  constructor
  · intro accepted
    unfold decodeBook at accepted
    cases decoded : decode wire bytes with
    | none => simp [decoded] at accepted
    | some store =>
        simp only [decoded, Option.bind_eq_bind, Option.bind_some] at accepted
        split at accepted
        · rename_i exact
          cases Option.some.inj accepted
          exact exact
        · cases accepted
  · intro exact
    rw [← exact]
    exact decodeBook_encodeBook book

theorem encodeBook_injective : Function.Injective encodeBook := by
  intro left right same
  have decoded := congrArg decodeBook same
  rwa [decodeBook_encodeBook, decodeBook_encodeBook, Option.some.injEq] at decoded

/-- A well-formed store cell is a Book cell exactly when it is the image of
its own Book reading. -/
theorem decodeBook_store_eq_none_iff (store : Store layout) :
    decodeBook (encode wire store) = none ↔ bookStore (bookOfStore store) ≠ store := by
  simp only [decodeBook, decode_encode, Option.bind_eq_bind, Option.bind_some, encodeBook]
  constructor
  · intro refused same
    simp [same] at refused
  · intro different
    rw [if_neg]
    intro same
    exact different (encode_injective wire same)

/-- Refuted misuse: an explicit zero balance is a well-formed store but not a
Book, because a Book's zero balance is absence. -/
def explicitZeroStore : Store layout :=
  fromEntries [(⟨⟨Space.balance, ((1 : AccountId), (0 : AssetId))⟩, (0 : Int)⟩ : Entry layout)]

theorem explicitZeroStore_balance :
    explicitZeroStore ⟨Space.balance, ((1 : AccountId), (0 : AssetId))⟩ =
      some (0 : Int) :=
  fromEntries_apply_of_mem _ (by simp) (List.mem_singleton_self _)

theorem explicit_zero_balance_rejected : decodeBook (encode wire explicitZeroStore) = none := by
  rw [decodeBook_store_eq_none_iff]
  intro same
  have atCoordinate := congrArg
    (fun store : Store layout => store ⟨Space.balance, ((1 : AccountId), (0 : AssetId))⟩)
    same
  simp only [bookStore_apply, explicitZeroStore_balance] at atCoordinate
  have read : (bookOfStore explicitZeroStore).balances ((1 : AccountId), (0 : AssetId)) = 0 := by
    rw [bookOfStore_balance, balancesOf_apply, explicitZeroStore_balance]
    rfl
  have absent : bookValue (bookOfStore explicitZeroStore)
      ⟨Space.balance, ((1 : AccountId), (0 : AssetId))⟩ = none := by
    change (if (bookOfStore explicitZeroStore).balances ((1 : AccountId), (0 : AssetId)) = 0
      then (none : Option Int)
      else some ((bookOfStore explicitZeroStore).balances ((1 : AccountId), (0 : AssetId)))) = none
    rw [if_pos read]
  rw [absent] at atCoordinate
  cases atCoordinate

/-- Satisfiable pole: a Book with a hidden (unregistered) balance coordinate
and a lease round-trips. -/
theorem hidden_book_roundtrip :
    decodeBook (encodeBook witnessHiddenBook) = some witnessHiddenBook :=
  decodeBook_encodeBook witnessHiddenBook

/-! ## Transcoding from the existing Book cell codec -/

open CanonicalResourcePageMaterializer in
/-- Read an existing Book cell, write the store cell of the same Book. -/
def transcode (old : List UInt8) : Option (List UInt8) := do
  let state ← stateCodec.decode old
  let book ← bookAt state
  some (encodeBook book)

open CanonicalResourcePageMaterializer in
theorem transcode_complete (book : Book) :
    transcode (stateCodec.encode (stateOfOption (some book))) = some (encodeBook book) := by
  simp [transcode, stateCodec.decode_encode, bookAt_some]

open CanonicalResourcePageMaterializer in
/-- Every transcoded cell is accepted by the store codec and denotes the same
Book the existing codec read. -/
theorem transcode_sound {old new : List UInt8} (transcoded : transcode old = some new) :
    ∃ book, (stateCodec.decode old).bind bookAt = some book ∧ decodeBook new = some book := by
  unfold transcode at transcoded
  cases decoded : stateCodec.decode old with
  | none => simp [decoded] at transcoded
  | some state =>
      cases present : bookAt state with
      | none => simp [decoded, present] at transcoded
      | some book =>
          simp only [decoded, present, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at transcoded
          subst new
          exact ⟨book, by simp [present], decodeBook_encodeBook book⟩

/-- info: 'Minidregg.Compiler.StoreCodecBook.bookOfStore_bookStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bookOfStore_bookStore
/-- info: 'Minidregg.Compiler.StoreCodecBook.decodeBook_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeBook_eq_some_iff
/-- info: 'Minidregg.Compiler.StoreCodecBook.explicit_zero_balance_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms explicit_zero_balance_rejected
/-- info: 'Minidregg.Compiler.StoreCodecBook.transcode_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transcode_sound

end Minidregg.Compiler.StoreCodecBook
