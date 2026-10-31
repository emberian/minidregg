/-
# Theory.CanonicalResourceBookEntries -- the account book as store entries

`Theory.CanonicalResourceKernel` keeps the whole `Book` as ONE value at one
address (`bookAddress`), so every admitted operation re-encodes and re-roots the
whole account map: O(accounts + balances + leases + floors) per write, a law-17
red for a book that grows with history. This module is the statement of the
replacement layout, entered before the migration:

* four namespaces, one entry per account, per (account, asset) balance, per lease
  and per (account, asset) floor (`layout`);
* `Represents store book`: the store holds exactly the book's entries (a zero
  balance or floor and an absent lease are absent addresses), and it is
  functional (`represents_unique`), so a store denotes at most one book;
* `operationPatch store operation`: the guarded patch of one operation, which
  touches only that operation's own entries;
* the keystone `PatchStatement` (`patchStatement`): run from a store representing
  `book`, the patch is valid and its result represents `operation.apply book`;
* the teeth: the patch writes at most the operation's two balance coordinates
  and its lease or floor entry (`patch_writeFootprint_subset`, at most 3
  addresses, `patch_writeFootprint_card_le`), whatever the size of the book;
  and a representation is never of two different books.

Satisfiable: the empty store represents the empty book (`represents_empty`).
-/
module

public import Theory.CanonicalResourceKernel

@[expose] public section

namespace Minidregg.Theory.CanonicalResourceKernel.Entries

open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CanonicalResourceKernel

set_option autoImplicit false

/-! ## The layout -/

/-- One namespace per kind of book entry. -/
inductive Field
  | account
  | balance
  | lease
  | floor
  deriving DecidableEq, Repr

/-- The key of each namespace. -/
abbrev Field.Key : Field → Type
  | .account => AccountId
  | .balance => AccountId × AssetId
  | .lease => LeaseId
  | .floor => AccountId × AssetId

/-- The value of each namespace: presence for an account, a nonzero balance, a
lease record, a nonzero floor. -/
abbrev Field.Value : Field → Type
  | .account => Unit
  | .balance => Int
  | .lease => LeaseRecord
  | .floor => Nat

instance Field.keyDecEq : (field : Field) → DecidableEq field.Key
  | .account => inferInstanceAs (DecidableEq AccountId)
  | .balance => inferInstanceAs (DecidableEq (AccountId × AssetId))
  | .lease => inferInstanceAs (DecidableEq LeaseId)
  | .floor => inferInstanceAs (DecidableEq (AccountId × AssetId))

instance Field.valueDecEq : (field : Field) → DecidableEq field.Value
  | .account => inferInstanceAs (DecidableEq Unit)
  | .balance => inferInstanceAs (DecidableEq Int)
  | .lease => inferInstanceAs (DecidableEq LeaseRecord)
  | .floor => inferInstanceAs (DecidableEq Nat)

/-- The book's entries, each its own RAM address. -/
abbrev layout : Layout.{0, 0, 0} where
  Namespace := Field
  Key := Field.Key
  Value := Field.Value
  discipline := fun _ => .ram
  keyDecEq := Field.keyDecEq
  valueDecEq := Field.valueDecEq

abbrev accountAddress (account : AccountId) : Address layout := ⟨.account, account⟩
abbrev balanceAddress (coordinate : AccountId × AssetId) : Address layout := ⟨.balance, coordinate⟩
abbrev leaseAddress (leaseId : LeaseId) : Address layout := ⟨.lease, leaseId⟩
abbrev floorAddress (coordinate : AccountId × AssetId) : Address layout := ⟨.floor, coordinate⟩

/-- A sparse number as a store value: zero is absence. -/
def nonzero {α : Type} [Zero α] [DecidableEq α] (value : α) : Option α :=
  if value = 0 then none else some value

/-! ## Representation -/

/-- `store` holds exactly `book`'s entries and nothing else. -/
structure Represents (store : Store layout) (book : Book) : Prop where
  accounts : ∀ account,
    store (accountAddress account) = if account ∈ book.accounts then some () else none
  balances : ∀ coordinate, store (balanceAddress coordinate) = nonzero (book.balances coordinate)
  leases : ∀ leaseId, store (leaseAddress leaseId) = book.leaseRecords leaseId
  floors : ∀ coordinate, store (floorAddress coordinate) = nonzero (book.floors coordinate)

theorem nonzero_injective {α : Type} [Zero α] [DecidableEq α] {a b : α}
    (same : nonzero a = nonzero b) : a = b := by
  unfold nonzero at same
  by_cases za : a = 0 <;> by_cases zb : b = 0 <;> simp_all

/-- **Teeth**: a store represents at most one book. -/
theorem represents_unique {store : Store layout} {book book' : Book}
    (left : Represents store book) (right : Represents store book') : book = book' := by
  obtain ⟨accounts, balances, leaseRecords, floors⟩ := book
  obtain ⟨accounts', balances', leaseRecords', floors'⟩ := book'
  have accountsEq : accounts = accounts' := by
    ext account
    have h := (left.accounts account).symm.trans (right.accounts account)
    by_cases a : account ∈ accounts <;> by_cases b : account ∈ accounts' <;> simp_all
  have balancesEq : balances = balances' := DFinsupp.ext fun coordinate =>
    nonzero_injective ((left.balances coordinate).symm.trans (right.balances coordinate))
  have leasesEq : leaseRecords = leaseRecords' := DFinsupp.ext fun leaseId =>
    (left.leases leaseId).symm.trans (right.leases leaseId)
  have floorsEq : floors = floors' := DFinsupp.ext fun coordinate =>
    nonzero_injective ((left.floors coordinate).symm.trans (right.floors coordinate))
  subst accountsEq balancesEq leasesEq floorsEq
  rfl

/-- **Satisfiable**: the empty store represents the empty book. -/
theorem represents_empty : Represents 0 Book.empty where
  accounts _ := by simp [Book.empty] <;> rfl
  balances _ := by simp [Book.empty, nonzero] <;> rfl
  leases _ := by simp [Book.empty] <;> rfl
  floors _ := by simp [Book.empty, nonzero] <;> rfl

/-! ## The patch of one operation -/

/-- Install `value` at `address` from what `store` holds there: allocate, write, free,
or nothing when it already holds it. Guarded by the exact prior value. -/
def entryPatch (store : Store layout) (address : Address layout)
    (value : Option (layout.Value address.1)) : Patch layout :=
  match store address, value with
  | none, none => []
  | none, some after => [.allocate address.1 address.2 after]
  | some before, none => [.free address.1 address.2 before]
  | some before, some after => if before = after then [] else [.write address.1 address.2 before after]

/-- The balance an operation's posting leaves at `coordinate`, read from the store. -/
def postedBalance (store : Store layout) (posting : Posting) (coordinate : AccountId × AssetId) : Int :=
  Option.getD (α := Int) (store (balanceAddress coordinate)) 0 +
    (if coordinate = (posting.source, posting.asset) then -(Int.ofNat posting.amount) else 0) +
    (if coordinate = (posting.destination, posting.asset) then Int.ofNat posting.amount else 0)

/-- The guarded patch of `operation` over `store`: the posting's source balance, then its
destination balance (each read from the store the earlier part left), then the lease
record or the floor the operation installs. Nothing else is read or written. -/
def operationPatch (store : Store layout) (operation : Operation) : Patch layout :=
  let posting := operation.posting
  let source := (posting.source, posting.asset)
  let destination := (posting.destination, posting.asset)
  let first := entryPatch store (balanceAddress source) (nonzero (α := Int) (postedBalance store posting source))
  let afterFirst := Patch.run store first
  let second := if destination = source then [] else
    entryPatch afterFirst (balanceAddress destination) (nonzero (α := Int) (postedBalance store posting destination))
  let afterSecond := Patch.run afterFirst second
  let third := match operation.leaseRecord?, operation.floorSetting? with
    | some (leaseId, record), _ => entryPatch afterSecond (leaseAddress leaseId) (some record)
    | none, some (coordinate, floor) => entryPatch afterSecond (floorAddress coordinate) (nonzero (α := Nat) floor)
    | none, none => []
  first ++ second ++ third

/-- The addresses `operation` may write: its posting's two balance coordinates and the
lease or floor entry it installs. -/
def touched (operation : Operation) : Finset (Address layout) :=
  let posting := operation.posting
  {balanceAddress (posting.source, posting.asset), balanceAddress (posting.destination, posting.asset)} ∪
    match operation.leaseRecord?, operation.floorSetting? with
    | some (leaseId, _), _ => {leaseAddress leaseId}
    | none, some (coordinate, _) => {floorAddress coordinate}
    | none, none => ∅

theorem entryPatch_writeFootprint_subset (store : Store layout) (address : Address layout)
    (value : Option (layout.Value address.1)) :
    Patch.writeFootprint (entryPatch store address value) ⊆ {address} := by
  unfold entryPatch
  split
  · simp [Patch.writeFootprint]
  · simp [Patch.writeFootprint, Op.writeAddress?, Op.address]
  · simp [Patch.writeFootprint, Op.writeAddress?, Op.address]
  · split <;> simp [Patch.writeFootprint, Op.writeAddress?, Op.address]

theorem writeFootprint_append (left right : Patch layout) :
    Patch.writeFootprint (left ++ right) = Patch.writeFootprint left ∪ Patch.writeFootprint right := by
  simp [Patch.writeFootprint, List.filterMap_append, List.toFinset_append]

/-- **Teeth (law 17)**: an operation's patch writes only that operation's own entries,
whatever the size of the book the store holds. -/
theorem patch_writeFootprint_subset (store : Store layout) (operation : Operation) :
    Patch.writeFootprint (operationPatch store operation) ⊆ touched operation := by
  unfold operationPatch touched
  simp only [writeFootprint_append]
  refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
  · exact (entryPatch_writeFootprint_subset _ _ _).trans (by simp)
  · split
    · simp [Patch.writeFootprint]
    · exact (entryPatch_writeFootprint_subset _ _ _).trans (by simp)
  · split
    · exact (entryPatch_writeFootprint_subset _ _ _).trans (by simp_all)
    · exact (entryPatch_writeFootprint_subset _ _ _).trans (by simp_all)
    · simp [Patch.writeFootprint]

/-- At most three addresses per operation. -/
theorem touched_card_le (operation : Operation) : (touched operation).card ≤ 3 := by
  unfold touched
  refine (Finset.card_union_le _ _).trans ?_
  have pair := Finset.card_le_two (a := balanceAddress (operation.posting.source, operation.posting.asset))
    (b := balanceAddress (operation.posting.destination, operation.posting.asset))
  split <;> simp only [Finset.card_singleton, Finset.card_empty] <;> omega

theorem patch_writeFootprint_card_le (store : Store layout) (operation : Operation) :
    (Patch.writeFootprint (operationPatch store operation)).card ≤ 3 :=
  (Finset.card_le_card (patch_writeFootprint_subset store operation)).trans (touched_card_le operation)

/-! ## The keystone, stated -/

/-- **Keystone**: from a store representing `book`, an operation's patch is
valid and its result represents the operation's book. With `represents_unique`, the
entry layout computes exactly the book `Theory.CanonicalResourceKernel` defines, one
operation's entries at a time. -/
def PatchStatement : Prop :=
  ∀ (store : Store layout) (book : Book) (operation : Operation), Represents store book →
    Patch.ValidFrom store (operationPatch store operation) ∧
      Represents (Patch.run store (operationPatch store operation)) (operation.apply book)

/-! ## The keystone, proved -/

def setBalance (store : Store layout) (c : AccountId × AssetId) (v : Option Int) : Store layout :=
  store.set (balanceAddress c) v

theorem setBalance_same (store : Store layout) (c : AccountId × AssetId) (v : Option Int) :
    setBalance store c v (balanceAddress c) = v := Store.set_eq _ _ _

theorem setBalance_ne (store : Store layout) (c : AccountId × AssetId) (v : Option Int)
    (a : Address layout) (ne : a ≠ balanceAddress c) :
    setBalance store c v a = store a := Store.set_ne _ _ _ _ ne

theorem set_self (store : Store layout) (address : Address layout) :
    store.set address (store address) = store := by
  refine DFinsupp.ext fun other => ?_
  by_cases same : other = address
  · subst same; exact Store.set_eq _ _ _
  · exact Store.set_ne _ _ _ _ same

theorem entryPatch_run (store : Store layout) (address : Address layout)
    (value : Option (layout.Value address.1)) :
    Patch.run store (entryPatch store address value) = store.set address value := by
  unfold entryPatch
  cases hs : store address with
  | none => cases value with
    | none => simp only; rw [← hs]; exact (set_self store address).symm
    | some after => rfl
  | some before => cases value with
    | none => rfl
    | some after =>
      simp only
      split
      · rename_i same; subst same; rw [← hs]; exact (set_self store address).symm
      · rfl

theorem entryPatch_valid (store : Store layout) (address : Address layout)
    (value : Option (layout.Value address.1)) :
    Patch.ValidFrom store (entryPatch store address value) := by
  unfold entryPatch
  cases hs : store address with
  | none => cases value with
    | none => trivial
    | some after => exact ⟨⟨fun e => Discipline.noConfusion e, hs⟩, trivial⟩
  | some before => cases value with
    | none => exact ⟨⟨rfl, hs⟩, trivial⟩
    | some after =>
      simp only
      split
      · trivial
      · exact ⟨⟨rfl, hs⟩, trivial⟩


def setLease (store : Store layout) (leaseId : LeaseId) (v : Option LeaseRecord) : Store layout :=
  store.set (leaseAddress leaseId) v

def setFloor (store : Store layout) (c : AccountId × AssetId) (v : Option Nat) : Store layout :=
  store.set (floorAddress c) v

theorem getD_nonzero (value : Int) : Option.getD (nonzero value) 0 = value := by
  unfold nonzero; split <;> simp_all

theorem balance_injective {c c' : AccountId × AssetId} (same : balanceAddress c = balanceAddress c') : c = c' := by
  simpa [balanceAddress] using same

/-- The store after an operation's patch, as typed entry writes. -/
def posted (store : Store layout) (posting : Posting) : Store layout :=
  let source := (posting.source, posting.asset)
  let destination := (posting.destination, posting.asset)
  let first := setBalance store source (nonzero (postedBalance store posting source))
  if destination = source then first
  else setBalance first destination (nonzero (postedBalance store posting destination))

def installed (store : Store layout) (operation : Operation) : Store layout :=
  match operation.leaseRecord?, operation.floorSetting? with
  | some (leaseId, record), _ => setLease store leaseId (some record)
  | none, some (coordinate, floor) => setFloor store coordinate (nonzero floor)
  | none, none => store

theorem operationPatch_run (store : Store layout) (operation : Operation) :
    Patch.run store (operationPatch store operation) = installed (posted store operation.posting) operation := by
  unfold operationPatch posted installed
  simp only [Patch.run_append, entryPatch_run, setBalance, setLease, setFloor]
  split_ifs <;> split <;> simp only [entryPatch_run, Patch.run]

theorem setBalance_get (store : Store layout) (c : AccountId × AssetId) (v : Option Int)
    (c' : AccountId × AssetId) :
    setBalance store c v (balanceAddress c') = if c' = c then v else store (balanceAddress c') := by
  by_cases h : c' = c
  · subst h; rw [if_pos rfl]; exact Store.set_eq _ _ _
  · rw [if_neg h]; exact Store.set_ne _ _ _ _ (fun e => h (balance_injective e))

theorem setBalance_other (store : Store layout) (c : AccountId × AssetId) (v : Option Int)
    (a : Address layout) (h : a.1 ≠ .balance) : setBalance store c v a = store a :=
  Store.set_ne _ _ _ _ (fun e => h (by rw [e]))

theorem postedBalance_eq {store : Store layout} {book : Book} (held : Represents store book)
    (posting : Posting) (c : AccountId × AssetId) :
    postedBalance store posting c = (book.applyPosting posting).balances c := by
  simp only [postedBalance, held.balances c, getD_nonzero, Book.applyPosting, DFinsupp.add_apply,
    DFinsupp.single_apply]
  by_cases hs : (posting.source, posting.asset) = c <;> by_cases hd : (posting.destination, posting.asset) = c <;>
    simp_all [eq_comm]

theorem posted_balance {store : Store layout} {book : Book} (held : Represents store book)
    (posting : Posting) (c : AccountId × AssetId) :
    posted store posting (balanceAddress c) = nonzero (postedBalance store posting c) := by
  dsimp only [posted]
  have untouched : c ≠ (posting.source, posting.asset) → c ≠ (posting.destination, posting.asset) →
      store (balanceAddress c) = nonzero (postedBalance store posting c) := by
    intro hs hd
    rw [held.balances c]
    simp only [postedBalance, held.balances c, getD_nonzero, if_neg hs, if_neg hd]
    simp
  split_ifs with same
  · rw [setBalance_get]
    split_ifs with hs
    · rw [hs]
    · exact untouched hs (fun e => hs (e.trans same))
  · rw [setBalance_get, setBalance_get]
    split_ifs with hd hs
    · rw [hd]
    · rw [hs]
    · exact untouched hs hd

theorem posted_other (store : Store layout) (posting : Posting) (a : Address layout)
    (h : a.1 ≠ .balance) : posted store posting a = store a := by
  dsimp only [posted]
  split_ifs <;> simp only [setBalance_other _ _ _ _ h]

theorem posted_represents {store : Store layout} {book : Book} (held : Represents store book)
    (posting : Posting) : Represents (posted store posting) (book.applyPosting posting) where
  accounts account := by
    rw [posted_other _ _ _ (by simp), held.accounts]; rfl
  balances c := by rw [posted_balance held, postedBalance_eq held]
  leases leaseId := by rw [posted_other _ _ _ (by simp), held.leases]; rfl
  floors c := by rw [posted_other _ _ _ (by simp), held.floors]; rfl

theorem lease_represents {store : Store layout} {book : Book} (held : Represents store book)
    (leaseId : LeaseId) (record : LeaseRecord) :
    Represents (setLease store leaseId (some record))
      { book with leaseRecords := book.leaseRecords.update leaseId (some record) } where
  accounts account := by
    rw [show setLease store leaseId (some record) (accountAddress account) = store (accountAddress account)
      from Store.set_ne _ _ _ _ (by simp), held.accounts]
  balances c := by
    rw [show setLease store leaseId (some record) (balanceAddress c) = store (balanceAddress c)
      from Store.set_ne _ _ _ _ (by simp), held.balances]
  leases other := by
    by_cases same : other = leaseId
    · subst same
      rw [show setLease store other (some record) (leaseAddress other) = some record from Store.set_eq _ _ _]
      simp
    · rw [show setLease store leaseId (some record) (leaseAddress other) = store (leaseAddress other)
        from Store.set_ne _ _ _ _ (by simpa using same), held.leases]
      rw [DFinsupp.coe_update, Function.update_of_ne same]
  floors c := by
    rw [show setLease store leaseId (some record) (floorAddress c) = store (floorAddress c)
      from Store.set_ne _ _ _ _ (by simp), held.floors]

theorem floor_represents {store : Store layout} {book : Book} (held : Represents store book)
    (coordinate : AccountId × AssetId) (floor : Nat) :
    Represents (setFloor store coordinate (nonzero floor))
      { book with floors := book.floors.update coordinate floor } where
  accounts account := by
    rw [show setFloor store coordinate (nonzero floor) (accountAddress account) = store (accountAddress account)
      from Store.set_ne _ _ _ _ (by simp), held.accounts]
  balances c := by
    rw [show setFloor store coordinate (nonzero floor) (balanceAddress c) = store (balanceAddress c)
      from Store.set_ne _ _ _ _ (by simp), held.balances]
  leases leaseId := by
    rw [show setFloor store coordinate (nonzero floor) (leaseAddress leaseId) = store (leaseAddress leaseId)
      from Store.set_ne _ _ _ _ (by simp), held.leases]
  floors other := by
    by_cases same : other = coordinate
    · subst same
      rw [show setFloor store other (nonzero floor) (floorAddress other) = nonzero floor from Store.set_eq _ _ _]
      simp
    · rw [show setFloor store coordinate (nonzero floor) (floorAddress other) = store (floorAddress other)
        from Store.set_ne _ _ _ _ (by simpa using same), held.floors]
      rw [DFinsupp.coe_update, Function.update_of_ne same]

theorem operationPatch_valid (store : Store layout) (operation : Operation) :
    Patch.ValidFrom store (operationPatch store operation) := by
  unfold operationPatch
  rw [Patch.validFrom_append, Patch.validFrom_append, Patch.run_append]
  refine ⟨⟨entryPatch_valid _ _ _, ?_⟩, ?_⟩
  · split
    · trivial
    · exact entryPatch_valid _ _ _
  · split <;> split <;> first | trivial | exact entryPatch_valid _ _ _

/-- **The keystone**: the entry layout computes exactly the book
`Theory.CanonicalResourceKernel` defines, one operation's entries at a time. -/
theorem patchStatement : PatchStatement := by
  intro store book operation held
  refine ⟨operationPatch_valid store operation, ?_⟩
  rw [operationPatch_run]
  have paid := posted_represents held operation.posting
  unfold installed Operation.apply
  cases lease : operation.leaseRecord? with
  | some entry =>
    obtain ⟨leaseId, record⟩ := entry
    exact lease_represents paid leaseId record
  | none =>
    cases setting : operation.floorSetting? with
    | some entry =>
      obtain ⟨coordinate, floor⟩ := entry
      exact floor_represents paid coordinate floor
    | none => exact paid

#assert_axioms patchStatement
#assert_axioms represents_unique
#assert_axioms patch_writeFootprint_card_le

end Minidregg.Theory.CanonicalResourceKernel.Entries
