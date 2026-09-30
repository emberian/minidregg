/-
# Theory.Store -- one typed sparse store, one guarded patch

The kernel's state is a finitely-supported partial map from typed addresses to
typed values, and its only mutation primitive is a list of guarded operations.
This module is the single home of both.  It replaces two carriers that were one
type under two names (`CellState.FieldStore` and
`SparseAuthenticatedState.Store`) and the guarded-write types that lived beside
them.

* A `Layout` chooses namespaces, a key type and a value type per namespace, and
  a mutation discipline per namespace (ROM, RAM, append-only).  Addresses are
  `Σ n, Key n`.
* A `Store` is `Π₀ a : Address L, Option (Value a.1)`.  `none` is absence and
  is a value of the representation, never a default.
* An `Op` is `read a observed | write a before after | allocate a v | free a before`:
  every mutation names the exact value it expects to replace, and allocation
  requires absence.  `Patch L := List (Op L)` is the free monoid on operations.
* `Patch.run` is the monoid action on stores (`run_append`); `Patch.ValidFrom`
  checks each guard at the store its prefix produced; `Patch.writeFootprint` is
  derived from syntax.  The frame law `run_frame` is the one frame theorem the
  cell and transition layers use.

Byte codecs, key order and roots are deliberately absent: they are
representations of a store, and live with the encoders (`Compiler/`) and the
materializers (`Theory.CellState`).
-/
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Minidregg.Theory.Store

set_option autoImplicit false
/- `Store.Store` is the store type of the `Store` module; the qualified name is
only visible to readers who do not `open Minidregg.Theory.Store`. -/
set_option linter.dupNamespace false

universe u v w

/-! ## Layouts, addresses, stores -/

/-- The mutation discipline of one namespace.  ROM is initialized outside an
execution and can only be read.  Append-only storage permits fresh allocation
but never overwrite or free.  RAM permits all four operations. -/
inductive Discipline
  | rom
  | ram
  | appendOnly
  deriving DecidableEq, Repr

/-- A heterogeneous address layout.  Keys and values stay indexed by their
namespace; there is no universal payload and no unchecked cast.  Decidable
equality of namespaces, keys and values is part of the layout, so every guard
is decidable and no signature downstream repeats the instance binders. -/
structure Layout where
  Namespace : Type u
  Key : Namespace → Type v
  Value : Namespace → Type w
  discipline : Namespace → Discipline
  [namespaceDecEq : DecidableEq Namespace]
  [keyDecEq : (space : Namespace) → DecidableEq (Key space)]
  [valueDecEq : (space : Namespace) → DecidableEq (Value space)]

attribute [instance] Layout.namespaceDecEq Layout.keyDecEq Layout.valueDecEq

/-- One typed address: a namespace and a key of that namespace. -/
abbrev Address (L : Layout.{u, v, w}) := Σ space : L.Namespace, L.Key space

/-- `none` is the representation-level zero of a sparse typed map.  It means
"address absent" and does not choose a semantic default. -/
instance optionZero (α : Type w) : Zero (Option α) := ⟨none⟩

/-- The one store.  Finite support is structural and equality is extensional,
so insertion order and overwritten history are not part of a store's
identity. -/
abbrev Store (L : Layout.{u, v, w}) :=
  Π₀ address : Address L, Option (L.Value address.1)

namespace Store

variable {L : Layout.{u, v, w}}

@[simp] theorem zero_apply (address : Address L) :
    (0 : Store L) address = none :=
  rfl

/-- Update one exact address.  `none` deallocates it. -/
def set (store : Store L) (address : Address L)
    (value : Option (L.Value address.1)) : Store L :=
  DFinsupp.update store address value

@[simp] theorem set_eq (store : Store L) (address : Address L)
    (value : Option (L.Value address.1)) :
    store.set address value address = value := by
  simp [set]

/-- Updating one address frames every distinct address. -/
theorem set_ne (store : Store L) (address : Address L)
    (value : Option (L.Value address.1)) (other : Address L)
    (different : other ≠ address) :
    store.set address value other = store other := by
  change Function.update (⇑store) address value other = store other
  rw [Function.update_of_ne different]

/-- Allocation freshness is exactly absence. -/
def Fresh (store : Store L) (address : Address L) : Prop :=
  store address = none

instance (store : Store L) (address : Address L) :
    Decidable (store.Fresh address) :=
  inferInstanceAs (Decidable (store address = none))

end Store

/-! ## Guarded operations -/

/-- Typed guarded-operation syntax.  Reads retain the value observed.  Writes
and frees retain the exact prior value, so an accepted patch cannot hide a stale
read.  Allocation carries no caller-authored freshness flag. -/
inductive Op (L : Layout.{u, v, w})
  | read (space : L.Namespace) (key : L.Key space)
      (observed : Option (L.Value space))
  | write (space : L.Namespace) (key : L.Key space)
      (before after : L.Value space)
  | allocate (space : L.Namespace) (key : L.Key space)
      (value : L.Value space)
  | free (space : L.Namespace) (key : L.Key space)
      (before : L.Value space)

namespace Op

variable {L : Layout.{u, v, w}}

/-- The sole address an operation touches. -/
def address : Op L → Address L
  | .read space key _ => ⟨space, key⟩
  | .write space key _ _ => ⟨space, key⟩
  | .allocate space key _ => ⟨space, key⟩
  | .free space key _ => ⟨space, key⟩

/-- The address an operation modifies, if any. -/
def writeAddress? : Op L → Option (Address L)
  | .read _ _ _ => none
  | op@(.write _ _ _ _) => some op.address
  | op@(.allocate _ _ _) => some op.address
  | op@(.free _ _ _) => some op.address

/-- The address an operation freshly allocates, if any. -/
def allocationAddress? : Op L → Option (Address L)
  | op@(.allocate _ _ _) => some op.address
  | _ => none

/-- The address an operation deallocates, if any. -/
def freeAddress? : Op L → Option (Address L)
  | op@(.free _ _ _) => some op.address
  | _ => none

theorem writeAddress?_eq_some {op : Op L} {address : Address L}
    (h : op.writeAddress? = some address) : op.address = address := by
  cases op <;> simp_all [writeAddress?]

/-- The guard of one operation.  Discipline and stale-value checks are part of
this relation, not proof-system side conditions. -/
def Enabled (store : Store L) : Op L → Prop
  | .read space key observed => store ⟨space, key⟩ = observed
  | .write space key before _ =>
      L.discipline space = .ram ∧ store ⟨space, key⟩ = some before
  | .allocate space key _ =>
      L.discipline space ≠ .rom ∧ store.Fresh ⟨space, key⟩
  | .free space key before =>
      L.discipline space = .ram ∧ store ⟨space, key⟩ = some before

instance decidableEnabled (store : Store L) : (op : Op L) → Decidable (op.Enabled store)
  | .read space key observed =>
      inferInstanceAs (Decidable (store ⟨space, key⟩ = observed))
  | .write space key before _ =>
      inferInstanceAs
        (Decidable (L.discipline space = .ram ∧ store ⟨space, key⟩ = some before))
  | .allocate space key _ =>
      inferInstanceAs
        (Decidable (L.discipline space ≠ .rom ∧ store.Fresh ⟨space, key⟩))
  | .free space key before =>
      inferInstanceAs
        (Decidable (L.discipline space = .ram ∧ store ⟨space, key⟩ = some before))

/-- Application is total syntax interpretation.  Acceptance must also carry
`Enabled`; application alone grants no authority or validity. -/
def apply (store : Store L) : Op L → Store L
  | .read _ _ _ => store
  | .write space key _ after => store.set ⟨space, key⟩ (some after)
  | .allocate space key value => store.set ⟨space, key⟩ (some value)
  | .free space key _ => store.set ⟨space, key⟩ none

/-- A fresh allocation is enabled only at an absent address. -/
theorem allocate_enabled_fresh (store : Store L)
    (space : L.Namespace) (key : L.Key space) (value : L.Value space)
    (enabled : (Op.allocate space key value).Enabled store) :
    store.Fresh ⟨space, key⟩ :=
  enabled.2

/-- ROM admits no enabled modifying operation. -/
theorem no_enabled_rom_write (store : Store L) (op : Op L)
    (enabled : op.Enabled store) (rom : L.discipline op.address.1 = .rom) :
    op.writeAddress? = none := by
  cases op with
  | read => rfl
  | write space key before after =>
      exact False.elim (Discipline.noConfusion (enabled.1.symm.trans rom))
  | allocate space key value => exact False.elim (enabled.1 rom)
  | free space key before =>
      exact False.elim (Discipline.noConfusion (enabled.1.symm.trans rom))

/-- Append-only namespaces accept modification only through fresh allocation. -/
theorem enabled_appendOnly_modification_is_allocate (store : Store L) (op : Op L)
    (enabled : op.Enabled store)
    (appendOnly : L.discipline op.address.1 = .appendOnly)
    (modifies : op.writeAddress? ≠ none) :
    op.allocationAddress? = some op.address := by
  cases op with
  | read => exact False.elim (modifies rfl)
  | write space key before after =>
      exact False.elim (Discipline.noConfusion (enabled.1.symm.trans appendOnly))
  | allocate => rfl
  | free space key before =>
      exact False.elim (Discipline.noConfusion (enabled.1.symm.trans appendOnly))

/-- One operation changes no address except its derived write address. -/
theorem apply_frame (store : Store L) (op : Op L) (address : Address L)
    (outside : op.writeAddress? ≠ some address) :
    op.apply store address = store address := by
  cases op with
  | read => rfl
  | write space key before after =>
      exact Store.set_ne _ _ _ _ (fun h => outside (by simp [writeAddress?, Op.address, h]))
  | allocate space key value =>
      exact Store.set_ne _ _ _ _ (fun h => outside (by simp [writeAddress?, Op.address, h]))
  | free space key before =>
      exact Store.set_ne _ _ _ _ (fun h => outside (by simp [writeAddress?, Op.address, h]))

end Op

/-! ## Patches: the free monoid of guarded operations and its action -/

/-- A patch is a finite list of guarded operations.  Concatenation is the
free-monoid product; `Patch.run` is its action on stores. -/
abbrev Patch (L : Layout.{u, v, w}) := List (Op L)

namespace Patch

variable {L : Layout.{u, v, w}}

/-- Every accessed address, derived from syntax. -/
def accessFootprint (patch : Patch L) : Finset (Address L) :=
  (List.map Op.address patch).toFinset

/-- Every modified address, derived from syntax.  Reads cannot enter it. -/
def writeFootprint (patch : Patch L) : Finset (Address L) :=
  (List.filterMap Op.writeAddress? patch).toFinset

/-- Every freshly allocated address, derived from allocation syntax. -/
def allocationFootprint (patch : Patch L) : Finset (Address L) :=
  (List.filterMap Op.allocationAddress? patch).toFinset

/-- Every freed address, derived from free syntax. -/
def freeFootprint (patch : Patch L) : Finset (Address L) :=
  (List.filterMap Op.freeAddress? patch).toFinset

/-- Unconditional interpretation.  `ValidFrom` checks each operation at the
exact store produced by its prefix. -/
def run : Store L → Patch L → Store L
  | store, [] => store
  | store, op :: rest => run (op.apply store) rest

/-- Prefix validity.  In particular, allocation freshness and every `before`
guard are tested after all preceding operations, not against the initial
store. -/
def ValidFrom : Store L → Patch L → Prop
  | _, [] => True
  | store, op :: rest => op.Enabled store ∧ ValidFrom (op.apply store) rest

instance decidableValidFrom : (store : Store L) → (patch : Patch L) →
    Decidable (ValidFrom store patch)
  | _, [] => isTrue trivial
  | store, op :: rest =>
      haveI := decidableValidFrom (op.apply store) rest
      inferInstanceAs (Decidable (op.Enabled store ∧ ValidFrom (op.apply store) rest))

/-- The exact execution relation.  There is no caller-selected post-store. -/
def Executes (pre : Store L) (patch : Patch L) (post : Store L) : Prop :=
  ValidFrom pre patch ∧ run pre patch = post

/-- The index of the first operation whose guard fails at its prefix store, if
any.  This is the executable checker; `firstDisabled?_eq_none_iff` and
`firstDisabled?_eq_some` say it decides `ValidFrom` and names the exact
failing operation. -/
def firstDisabled? : Store L → Patch L → Option Nat
  | _, [] => none
  | store, op :: rest =>
      if op.Enabled store then (firstDisabled? (op.apply store) rest).map Nat.succ
      else some 0

@[simp] theorem run_nil (store : Store L) : run store [] = store :=
  rfl

@[simp] theorem run_cons (store : Store L) (op : Op L) (rest : Patch L) :
    run store (op :: rest) = run (op.apply store) rest :=
  rfl

/-- `run` is a monoid action of the free monoid of operations. -/
@[simp] theorem run_append (store : Store L) (left right : Patch L) :
    run store (left ++ right) = run (run store left) right := by
  induction left generalizing store with
  | nil => rfl
  | cons op rest ih => exact ih (op.apply store)

theorem validFrom_append (store : Store L) (left right : Patch L) :
    ValidFrom store (left ++ right) ↔
      ValidFrom store left ∧ ValidFrom (run store left) right := by
  induction left generalizing store with
  | nil => simp [ValidFrom, run]
  | cons op rest ih =>
      simp only [List.cons_append, ValidFrom, run]
      rw [ih (op.apply store)]
      tauto

/-- Accepted patches compose by list append. -/
theorem Executes.append {pre middle post : Store L} {left right : Patch L}
    (leftExecutes : Executes pre left middle)
    (rightExecutes : Executes middle right post) :
    Executes pre (left ++ right) post := by
  rcases leftExecutes with ⟨leftValid, rfl⟩
  rcases rightExecutes with ⟨rightValid, rfl⟩
  exact ⟨(validFrom_append pre left right).2 ⟨leftValid, rightValid⟩,
    run_append pre left right⟩

theorem firstDisabled?_eq_none_iff (store : Store L) (patch : Patch L) :
    firstDisabled? store patch = none ↔ ValidFrom store patch := by
  induction patch generalizing store with
  | nil => simp [firstDisabled?, ValidFrom]
  | cons op rest ih =>
      by_cases enabled : op.Enabled store
      · simp [firstDisabled?, ValidFrom, enabled, ih]
      · simp [firstDisabled?, ValidFrom, enabled]

/-- A reported index is exact: every earlier operation is enabled in sequence,
and the operation at the index is disabled at the store its prefix produced. -/
theorem firstDisabled?_eq_some (store : Store L) (patch : Patch L) (index : Nat)
    (reported : firstDisabled? store patch = some index) :
    ValidFrom store (patch.take index) ∧
      ∃ op, patch[index]? = some op ∧ ¬ op.Enabled (run store (patch.take index)) := by
  induction patch generalizing store index with
  | nil => simp [firstDisabled?] at reported
  | cons op rest ih =>
      by_cases enabled : op.Enabled store
      · simp only [firstDisabled?, enabled, if_true, Option.map_eq_some_iff] at reported
        rcases reported with ⟨tailIndex, tailReported, rfl⟩
        rcases ih (op.apply store) tailIndex tailReported with ⟨valid, failing, at_, disabled⟩
        exact ⟨⟨enabled, valid⟩, failing, at_, disabled⟩
      · simp only [firstDisabled?, enabled, if_false, Option.some.injEq] at reported
        subst reported
        exact ⟨trivial, op, rfl, enabled⟩

instance (pre : Store L) (patch : Patch L) (post : Store L) :
    Decidable (Executes pre patch post) :=
  inferInstanceAs (Decidable (ValidFrom pre patch ∧ run pre patch = post))

/-! ### Footprints -/

@[simp] theorem accessFootprint_append (left right : Patch L) :
    accessFootprint (left ++ right) = accessFootprint left ∪ accessFootprint right := by
  simp [accessFootprint]

@[simp] theorem writeFootprint_append (left right : Patch L) :
    writeFootprint (left ++ right) = writeFootprint left ∪ writeFootprint right := by
  simp [writeFootprint]

/-- No ghost keys: membership in the write footprint is exactly a literal
modifying operation in the patch. -/
theorem mem_writeFootprint_iff (patch : Patch L) (address : Address L) :
    address ∈ writeFootprint patch ↔
      ∃ op, op ∈ patch ∧ op.writeAddress? = some address := by
  simp [writeFootprint]

/-- No ghost keys, allocation subset. -/
theorem mem_allocationFootprint_iff (patch : Patch L) (address : Address L) :
    address ∈ allocationFootprint patch ↔
      ∃ op, op ∈ patch ∧ op.allocationAddress? = some address := by
  simp [allocationFootprint]

theorem writeFootprint_subset_accessFootprint (patch : Patch L) :
    writeFootprint patch ⊆ accessFootprint patch := by
  intro address member
  rcases (mem_writeFootprint_iff patch address).1 member with ⟨op, mem, written⟩
  simp only [accessFootprint, List.mem_toFinset, List.mem_map]
  exact ⟨op, mem, Op.writeAddress?_eq_some written⟩

/-! ### The frame law -/

/-- **The frame law.**  An address outside the syntactic write footprint is
unchanged by running the patch.  This is the one frame theorem: the cell layer
(`CellState.ValidatedPatch.apply`) and the transition layer
(`CanonicalTransition.CellDelta.ofValidatedPatch`) both use it directly. -/
theorem run_frame (store : Store L) (patch : Patch L) (address : Address L)
    (outside : address ∉ writeFootprint patch) :
    run store patch address = store address := by
  induction patch generalizing store with
  | nil => rfl
  | cons op rest ih =>
      have headOutside : op.writeAddress? ≠ some address := fun written =>
        outside ((mem_writeFootprint_iff _ address).2 ⟨op, List.mem_cons_self, written⟩)
      have tailOutside : address ∉ writeFootprint rest := fun member => by
        rcases (mem_writeFootprint_iff rest address).1 member with ⟨op', mem, written⟩
        exact outside ((mem_writeFootprint_iff _ address).2
          ⟨op', List.mem_cons_of_mem _ mem, written⟩)
      rw [run_cons, ih (op.apply store) tailOutside]
      exact op.apply_frame store address headOutside

/-- Contrapositive frame: every actual change is named by the write footprint. -/
theorem changed_only_declared (store : Store L) (patch : Patch L) (address : Address L)
    (changed : run store patch address ≠ store address) :
    address ∈ writeFootprint patch := by
  by_contra outside
  exact changed (run_frame store patch address outside)

/-! ### Disciplines, lifted to valid patches -/

/-- A valid patch leaves every ROM address unchanged, whatever its syntax names. -/
theorem rom_preserved (store : Store L) (patch : Patch L) (address : Address L)
    (valid : ValidFrom store patch) (rom : L.discipline address.1 = .rom) :
    run store patch address = store address := by
  induction patch generalizing store with
  | nil => rfl
  | cons op rest ih =>
      rcases valid with ⟨enabled, tailValid⟩
      rw [run_cons, ih (op.apply store) tailValid]
      apply op.apply_frame store address
      intro written
      have same := Op.writeAddress?_eq_some written
      subst same
      rw [op.no_enabled_rom_write store enabled rom] at written
      simp at written

/-- A valid patch never changes a present value of an append-only namespace. -/
theorem appendOnly_present_preserved (store : Store L) (patch : Patch L)
    (address : Address L) (value : L.Value address.1)
    (valid : ValidFrom store patch)
    (appendOnly : L.discipline address.1 = .appendOnly)
    (present : store address = some value) :
    run store patch address = some value := by
  induction patch generalizing store with
  | nil => exact present
  | cons op rest ih =>
      rcases valid with ⟨enabled, tailValid⟩
      rw [run_cons]
      apply ih (op.apply store) tailValid
      rw [← present]
      apply op.apply_frame store address
      intro written
      have same := Op.writeAddress?_eq_some written
      subst same
      have isAllocate := op.enabled_appendOnly_modification_is_allocate store enabled
        appendOnly (by simp [written])
      cases op with
      | read => simp [Op.writeAddress?] at written
      | write => simp [Op.allocationAddress?] at isAllocate
      | free => simp [Op.allocationAddress?] at isAllocate
      | allocate space key v =>
          have fresh : store (Op.allocate space key v).address = none := enabled.2
          exact absurd (fresh.symm.trans present) (by simp)

end Patch

/-! ## Poles

A three-namespace layout (ROM `code`, RAM `heap`, append-only `log`) over `Nat`.
Every theorem above whose premise carries content has, here, a built instance
that satisfies it and a built instance that shows the premise is load-bearing.
All by `decide`. -/

namespace Example

inductive Namespace
  | code
  | heap
  | log
  deriving DecidableEq, Repr

abbrev layout : Layout where
  Namespace := Namespace
  Key := fun _ => Nat
  Value := fun _ => Nat
  discipline
    | .code => .rom
    | .heap => .ram
    | .log => .appendOnly

def at_ (space : Namespace) (key : Nat) : Address layout := ⟨space, key⟩

def empty : Store layout := 0

def allocate (space : Namespace) (key value : Nat) : Op layout :=
  @Op.allocate layout space key value

def write (space : Namespace) (key before after : Nat) : Op layout :=
  @Op.write layout space key before after

def read (space : Namespace) (key : Nat) (observed : Option Nat) : Op layout :=
  @Op.read layout space key observed

/-- A store with ROM `code[0] = 1`, as if initialized outside execution. -/
def codeStore : Store layout :=
  empty.set (at_ .code 0) (some (1 : Nat))

/-- Allocate `heap[7] = 42`, then overwrite it with the exact prior value. -/
def samplePatch : Patch layout :=
  [allocate .heap 7 42, write .heap 7 42 43]

/-! ### `ValidFrom`: satisfied, and refused for each guard -/

theorem samplePatch_valid : Patch.ValidFrom empty samplePatch := by decide

theorem samplePatch_post : Patch.run empty samplePatch (at_ .heap 7) = some (43 : Nat) := by
  decide

/-- Freshness has teeth: the same allocation cannot execute twice. -/
theorem duplicate_allocation_rejected :
    ¬ Patch.ValidFrom empty [allocate .heap 7 42, allocate .heap 7 42] := by decide

/-- The checker names the exact failing operation. -/
theorem duplicate_allocation_index :
    Patch.firstDisabled? empty [allocate .heap 7 42, allocate .heap 7 42] = some 1 := by
  decide

/-- A write whose `before` is stale is refused. -/
theorem stale_write_rejected :
    ¬ Patch.ValidFrom empty [allocate .heap 7 42, write .heap 7 41 43] := by decide

/-- A write to an absent address is refused (absence is not zero). -/
theorem write_absent_rejected :
    ¬ Patch.ValidFrom empty [write .heap 7 0 1] := by decide

/-- A read guard that disagrees with the store is refused. -/
theorem stale_read_rejected :
    ¬ Patch.ValidFrom empty [read .heap 7 (some 0)] := by decide

/-- ROM overwrite is not an enabled operation. -/
theorem rom_write_rejected :
    ¬ (write .code 0 1 2).Enabled codeStore := by decide

/-- Append-only storage allocates but does not overwrite. -/
theorem appendOnly_allocate_valid :
    Patch.ValidFrom empty [allocate .log 0 5] := by decide

theorem appendOnly_overwrite_rejected :
    ¬ Patch.ValidFrom empty [allocate .log 0 5, write .log 0 5 6] := by decide

/-! ### The frame law: satisfied outside the footprint, false inside it -/

/-- Satisfied: `heap[8]` is outside the footprint and unchanged. -/
theorem frame_outside :
    at_ .heap 8 ∉ Patch.writeFootprint samplePatch ∧
      Patch.run empty samplePatch (at_ .heap 8) = empty (at_ .heap 8) := by
  decide

/-- The premise is load-bearing: `heap[7]` is inside the footprint and changed,
so the frame conclusion fails there. -/
theorem frame_inside_changes :
    at_ .heap 7 ∈ Patch.writeFootprint samplePatch ∧
      Patch.run empty samplePatch (at_ .heap 7) ≠ empty (at_ .heap 7) := by
  decide

/-- Reads never enter the write footprint. -/
theorem read_not_in_writeFootprint :
    at_ .heap 7 ∈ Patch.accessFootprint [read .heap 7 none] ∧
      at_ .heap 7 ∉ Patch.writeFootprint [read .heap 7 none] := by
  decide

/-! ### Disciplines: preserved under validity, broken without it -/

/-- Satisfied: a valid patch that reads ROM leaves it unchanged. -/
theorem rom_read_valid_preserved :
    Patch.ValidFrom codeStore [read .code 0 (some 1)] ∧
      Patch.run codeStore [read .code 0 (some 1)] (at_ .code 0) = some (1 : Nat) := by
  decide

/-- The validity premise is load-bearing: unvalidated, a ROM write does move
the ROM address. -/
theorem rom_write_unvalidated_moves :
    ¬ Patch.ValidFrom codeStore [write .code 0 1 2] ∧
      Patch.run codeStore [write .code 0 1 2] (at_ .code 0) ≠ codeStore (at_ .code 0) := by
  decide

/-- The append-only premise is load-bearing: unvalidated, an overwrite of a
present log entry moves it. -/
theorem appendOnly_overwrite_unvalidated_moves :
    ¬ Patch.ValidFrom (Patch.run empty [allocate .log 0 5]) [write .log 0 5 6] ∧
      Patch.run empty [allocate .log 0 5, write .log 0 5 6] (at_ .log 0) = some (6 : Nat) := by
  decide

end Example

/-- info: 'Minidregg.Theory.Store.Patch.run_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.run_frame
/-- info: 'Minidregg.Theory.Store.Patch.changed_only_declared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.changed_only_declared
/-- info: 'Minidregg.Theory.Store.Patch.run_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.run_append
/-- info: 'Minidregg.Theory.Store.Patch.validFrom_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.validFrom_append
/-- info: 'Minidregg.Theory.Store.Patch.firstDisabled?_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.firstDisabled?_eq_none_iff
/-- info: 'Minidregg.Theory.Store.Patch.firstDisabled?_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.firstDisabled?_eq_some
/-- info: 'Minidregg.Theory.Store.Patch.mem_writeFootprint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.mem_writeFootprint_iff
/-- info: 'Minidregg.Theory.Store.Patch.rom_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.rom_preserved
/-- info: 'Minidregg.Theory.Store.Patch.appendOnly_present_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.appendOnly_present_preserved
/-- info: 'Minidregg.Theory.Store.Example.samplePatch_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.samplePatch_valid
/-- info: 'Minidregg.Theory.Store.Example.duplicate_allocation_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.duplicate_allocation_rejected
/-- info: 'Minidregg.Theory.Store.Example.duplicate_allocation_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.duplicate_allocation_index
/-- info: 'Minidregg.Theory.Store.Example.stale_write_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.stale_write_rejected
/-- info: 'Minidregg.Theory.Store.Example.write_absent_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.write_absent_rejected
/-- info: 'Minidregg.Theory.Store.Example.stale_read_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.stale_read_rejected
/-- info: 'Minidregg.Theory.Store.Example.rom_write_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.rom_write_rejected
/-- info: 'Minidregg.Theory.Store.Example.appendOnly_overwrite_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.appendOnly_overwrite_rejected
/-- info: 'Minidregg.Theory.Store.Example.frame_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.frame_outside
/-- info: 'Minidregg.Theory.Store.Example.frame_inside_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.frame_inside_changes
/-- info: 'Minidregg.Theory.Store.Example.rom_read_valid_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.rom_read_valid_preserved
/-- info: 'Minidregg.Theory.Store.Example.rom_write_unvalidated_moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.rom_write_unvalidated_moves
/-- info: 'Minidregg.Theory.Store.Example.appendOnly_overwrite_unvalidated_moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.appendOnly_overwrite_unvalidated_moves

end Minidregg.Theory.Store
