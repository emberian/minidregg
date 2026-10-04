/-
# Kernel.FieldClosure -- a declared cell holds only the fields it declares (K-FIELD-CLOSURE)

A friend's law is a `Pred` over named slots, so it cannot say "no field other
than these".  A law that freezes a closed job's sixteen fields still admitted a
write that CREATES field 20 (lane C1's `closed_job_admits_undeclared_field`).
That gap was every law's (a sealed board, a write-once record, a treasury
sheet), and it was a covert channel: an undeclared field is a place to put
bytes on a cell someone else's law governs.

The kernel closes it, default-closed:

* A declared cell carries its **declaration** in its own store, written at
  birth: `fieldDeclared ⟨cell⟩ ⟨n⟩` for each field it may hold, optionally
  `fieldsFrom ⟨cell⟩` holding `t` for every field at or above `t` (an unbounded
  tail: a room's roster, whose rows are allocated on join), or
  `fieldsOpen ⟨cell⟩` for an open kind.  No action writes a declaration key
  (`admitted_preserves_declared`), so the declaration is fixed for the cell's
  life.  A cell that declares nothing is closed to every field.
* The registry's cell law (`CanonicalCellRegistry.DeclaredCellLaw`) requires
  every field the cell holds to be declared (`Closed`).  It is checked on every
  loaded cell and on every receiver's post (`PhysicalPostLaw`), births included.
* The scalar receiver (`DeclaredResourceScalar.prepareCell`, which is invoke's
  and grain birth's target computation) refuses a write that changes an
  undeclared field BY NAME, `undeclaredField n`, before any law is evaluated.

The rule is stated once, over the projection's field values (`firstUndeclared`),
so the kernel's check and a law-level model (`Kernel.Job`) apply the same
function.
-/
import Kernel.DeclaredResourceProjection
import Theory.AssertAxioms

namespace Minidregg.Kernel.FieldClosure

open Minidregg.Compiler
open Minidregg.Theory.EffectDeclaration (StateKey effectLayout)
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (ResourceKind ResourceId)
open Minidregg.Kernel.DeclaredResourceProjection (Values values get)

set_option autoImplicit false

/-! ## §1. The rule, over field values -/

/-- A declared cell's field set: exactly the listed fields and, with a `tail`,
every field at or above it; or open. -/
inductive FieldSet where
  | closed (fields : List Nat) (tail : Option Nat := none)
  | «open»
  deriving DecidableEq, Repr

def FieldSet.covers : FieldSet → Nat → Bool
  | .closed fields tail, n => decide (n ∈ fields) || tail.any (fun first => decide (first ≤ n))
  | .open, _ => true

/-- Every field a write could have changed: those present before or after. -/
def candidates (pre post : Values) : List Nat := pre.map Prod.fst ++ post.map Prod.fst

/-- The first field a write changed (its value or its presence) that `covers`
does not declare. -/
def firstUndeclared (covers : Nat → Bool) (pre post : Values) : Option Nat :=
  (candidates pre post).find? fun n => get pre n != get post n && !covers n

theorem find?_holds {α : Type} {pred : α → Bool} :
    ∀ {xs : List α} {a : α}, xs.find? pred = some a → pred a = true ∧ a ∈ xs
  | [], _, found => by simp at found
  | x :: xs, a, found => by
    by_cases hx : pred x = true
    · simp only [List.find?, hx, Option.some.injEq] at found
      subst found
      exact ⟨hx, List.mem_cons_self⟩
    · simp only [Bool.not_eq_true] at hx
      simp only [List.find?, hx] at found
      obtain ⟨holds, mem⟩ := find?_holds found
      exact ⟨holds, List.mem_cons_of_mem _ mem⟩

theorem get_ne_none_mem {xs : Values} {n : Nat} (present : get xs n ≠ none) :
    n ∈ xs.map Prod.fst := by
  unfold DeclaredResourceProjection.get at present
  cases found : xs.find? (fun p => p.1 == n) with
  | none => rw [found] at present; exact absurd rfl present
  | some p =>
    obtain ⟨key, mem⟩ := find?_holds found
    exact List.mem_map.mpr ⟨p, mem, by simpa using key⟩

theorem get_mem_ne_none {xs : Values} {p : Nat × Int} (member : p ∈ xs) :
    get xs p.1 ≠ none := by
  unfold DeclaredResourceProjection.get
  cases found : xs.find? (fun q => q.1 == p.1) with
  | none =>
    rw [List.find?_eq_none] at found
    exact (found p member (by simp)).elim
  | some q => simp

/-- `firstUndeclared` names nothing exactly when every changed field is declared. -/
theorem firstUndeclared_none_iff (covers : Nat → Bool) (pre post : Values) :
    firstUndeclared covers pre post = none ↔
      ∀ n, get pre n ≠ get post n → covers n = true := by
  unfold firstUndeclared
  rw [List.find?_eq_none]
  constructor
  · intro none_found n changed
    have mem : n ∈ candidates pre post := by
      unfold candidates
      rw [List.mem_append]
      by_cases absent : get pre n = none
      · right
        apply get_ne_none_mem
        intro absentPost
        exact changed (absent.trans absentPost.symm)
      · left
        exact get_ne_none_mem absent
    cases hc : covers n
    · exact (none_found n mem (by simp [hc, changed])).elim
    · rfl
  · intro covered n _ found
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at found
    rw [covered n found.1] at found
    cases found.2

/-- What `firstUndeclared` names was changed by the write and is not declared. -/
theorem firstUndeclared_some {covers : Nat → Bool} {pre post : Values} {n : Nat}
    (named : firstUndeclared covers pre post = some n) :
    get pre n ≠ get post n ∧ covers n = false := by
  unfold firstUndeclared at named
  have holds := (find?_holds named).1
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at holds
  exact holds

/-- **The open-kind pole**: an open cell's declaration covers every field, so no
write is refused for its fields. -/
theorem open_admits_every_field (pre post : Values) :
    firstUndeclared FieldSet.open.covers pre post = none :=
  (firstUndeclared_none_iff _ _ _).mpr fun _ _ => rfl

/-! ## §2. The declaration a cell carries, and the two checks -/

def declaredKey (cellId n : Nat) : StateKey := .fieldDeclared ⟨cellId⟩ ⟨n⟩
def openKey (cellId : Nat) : StateKey := .fieldsOpen ⟨cellId⟩
def fromKey (cellId : Nat) : StateKey := .fieldsFrom ⟨cellId⟩

/-- The tail a `fieldsFrom` entry holding `lowest` declares covers field `n`. -/
def tailCovers (lowest : Option Int) (n : Nat) : Bool :=
  lowest.any fun first => decide (first ≤ (n : Int))

/-- Field `n` is declared at cell `cellId`: the cell is open, declares `n`, or
declares a tail at or below `n`.  Each disjunct is one lookup: the check never
scans the declaration, however many fields a tail admits. -/
def declaredIn (cellId : Nat) (store : Store effectLayout) (n : Nat) : Bool :=
  (store (openKey cellId).address).isSome || (store (declaredKey cellId n).address).isSome ||
    tailCovers (store (fromKey cellId).address) n

/-- A present key is admissible under the cell's declaration: an object field of
this cell is declared; every other key is the key law's to judge. -/
def KeyDeclared (cellId : Nat) (store : Store effectLayout) : StateKey → Prop
  | .objectField object field => object.value = cellId → declaredIn cellId store field.value = true
  | _ => True

instance keyDeclaredDecidable (cellId : Nat) (store : Store effectLayout) (key : StateKey) :
    Decidable (KeyDeclared cellId store key) := by
  cases key <;> unfold KeyDeclared <;> infer_instance

/-- **The state law**: every field the cell holds is declared.  (Stated over the
store's support, as the key law is, so a concrete cell decides it.) -/
def Closed (cellId : Nat) (store : Store effectLayout) : Prop :=
  ∀ address ∈ store.support, KeyDeclared cellId store address.2

instance closedDecidable (cellId : Nat) (store : Store effectLayout) :
    Decidable (Closed cellId store) := by
  unfold Closed
  infer_instance

/-- The projection reads a field of the cell exactly as the store holds it. -/
theorem get_values (cellId n : Nat) (store : Store effectLayout) :
    get (values cellId store) n = store (StateKey.objectField ⟨cellId⟩ ⟨n⟩).address := by
  -- every entry holds its address's value
  have entryValue : ∀ e ∈ StoreCodec.entries DeclaredEffectCell.wire store, store e.1 = some e.2 := by
    intro e member
    unfold StoreCodec.entries at member
    obtain ⟨a, _, found⟩ := List.mem_filterMap.mp member
    cases hs : store a with
    | none => rw [hs] at found; cases found
    | some v => rw [hs] at found; cases found; exact hs
  -- a pair of the projection names its entry's object field
  have pairEntry : ∀ q ∈ values cellId store,
      store (StateKey.objectField ⟨cellId⟩ ⟨q.1⟩).address = some q.2 := by
    intro q member
    unfold values at member
    obtain ⟨e, eMember, found⟩ := List.mem_filterMap.mp member
    obtain ⟨⟨u, key⟩, value⟩ := e
    cases key with
    | objectField object field =>
      simp only at found
      split at found
      · rename_i same
        cases found
        have held := entryValue _ eMember
        obtain ⟨objectValue⟩ := object
        obtain ⟨fieldValue⟩ := field
        simp only at same
        subst same
        exact held
      · cases found
    | accountBalance _ _ => simp at found
    | programCode _ => simp at found
    | blinding => simp at found
    | fieldDeclared _ _ => simp at found
    | fieldsOpen _ => simp at found
    | fieldsFrom _ => simp at found
  cases held : store (StateKey.objectField ⟨cellId⟩ ⟨n⟩).address with
  | none =>
    unfold DeclaredResourceProjection.get
    cases found : (values cellId store).find? (fun q => q.1 == n) with
    | none => rfl
    | some q =>
      obtain ⟨key, member⟩ := find?_holds found
      have same : q.1 = n := by simpa using key
      have := pairEntry q member
      rw [same, held] at this
      cases this
  | some v =>
    have member : (n, v) ∈ values cellId store := by
      unfold values
      apply List.mem_filterMap.mpr
      refine ⟨⟨(StateKey.objectField ⟨cellId⟩ ⟨n⟩).address, v⟩, ?_, by simp [StateKey.address]⟩
      unfold StoreCodec.entries
      apply List.mem_filterMap.mpr
      refine ⟨(StateKey.objectField ⟨cellId⟩ ⟨n⟩).address, ?_, by rw [held]; rfl⟩
      exact (StoreCodec.mem_sortedSupport DeclaredEffectCell.wire store _).mpr (by rw [held]; simp)
    unfold DeclaredResourceProjection.get
    cases found : (values cellId store).find? (fun q => q.1 == n) with
    | none =>
      rw [List.find?_eq_none] at found
      exact (found _ member (by simp)).elim
    | some q =>
      obtain ⟨key, qMember⟩ := find?_holds found
      have same : q.1 = n := by simpa using key
      have qHeld := pairEntry q qMember
      rw [same, held] at qHeld
      simp only [Option.map_some, Option.some.injEq]
      exact (Option.some.inj qHeld).symm

/-- **The named check**: the first field the write changed that the cell's
declaration, read in the pre-state, does not cover. -/
def check (cellId : Nat) (pre post : Store effectLayout) : Option Nat :=
  firstUndeclared (declaredIn cellId pre) (values cellId pre) (values cellId post)

/-- **A write inside the declaration keeps the cell closed**: from a closed
pre-state, under an unchanged declaration, a write the check passes leaves a
closed post.  So for such a write, the cell law's verdict is its key law's
verdict, as before the closure (`CanonicalCellRegistry.declared_fields_admit_as_before`). -/
theorem closed_preserved {cellId : Nat} {pre post : Store effectLayout}
    (preClosed : Closed cellId pre)
    (sameDeclaration : ∀ n, declaredIn cellId post n = declaredIn cellId pre n)
    (inside : check cellId pre post = none) : Closed cellId post := by
  intro address member
  obtain ⟨u, key⟩ := address
  cases key with
  | objectField object field =>
    intro own
    obtain ⟨objectValue⟩ := object
    obtain ⟨n⟩ := field
    simp only at own
    subst own
    show declaredIn objectValue post n = true
    rw [sameDeclaration]
    by_cases changed : get (values objectValue pre) n = get (values objectValue post) n
    · have presentPost : post (StateKey.objectField ⟨objectValue⟩ ⟨n⟩).address ≠ none :=
        (DFinsupp.mem_support_toFun _ _).mp member
      rw [← get_values, ← changed, get_values] at presentPost
      exact preClosed _ ((DFinsupp.mem_support_toFun _ _).mpr presentPost) rfl
    · exact (firstUndeclared_none_iff _ _ _).mp inside n changed
  | accountBalance _ _ => trivial
  | programCode _ => trivial
  | blinding => trivial
  | fieldDeclared _ _ => trivial
  | fieldsOpen _ => trivial
  | fieldsFrom _ => trivial

/-! ## §3. Writing a declaration at birth -/

/-- The declaration entries of `set`: each listed field's key holding `0`, the
tail's key holding its first field, or the open key holding `0`. -/
def FieldSet.entries (cellId : Nat) : FieldSet → List (StateKey × Int)
  | .closed fields tail =>
      fields.map (fun n => (declaredKey cellId n, 0)) ++
        (tail.map fun first => (fromKey cellId, (first : Int))).toList
  | .open => [(openKey cellId, 0)]

/-- `store` with `set`'s declaration written into it. -/
def declare (cellId : Nat) (set : FieldSet) (store : Store effectLayout) : Store effectLayout :=
  (set.entries cellId).foldl (fun acc entry => acc.set entry.1.address (some entry.2)) store

private def setAll (entries : List (StateKey × Int)) (store : Store effectLayout) : Store effectLayout :=
  entries.foldl (fun acc entry => acc.set entry.1.address (some entry.2)) store

private theorem setAll_apply_not_mem (entries : List (StateKey × Int)) (store : Store effectLayout)
    (key : StateKey) (absent : ∀ entry ∈ entries, entry.1 ≠ key) :
    setAll entries store key.address = store key.address := by
  induction entries generalizing store with
  | nil => rfl
  | cons entry rest ih =>
    show setAll rest (store.set entry.1.address (some entry.2)) key.address = _
    rw [ih _ (fun other mem => absent other (List.mem_cons_of_mem _ mem))]
    exact Store.set_ne _ _ _ _ fun same =>
      absent entry List.mem_cons_self (StateKey.address_injective same).symm

private theorem setAll_apply_mem (entries : List (StateKey × Int)) (store : Store effectLayout)
    (key : StateKey) (present : ∃ entry ∈ entries, entry.1 = key) :
    (setAll entries store key.address).isSome := by
  induction entries generalizing store with
  | nil => simp at present
  | cons entry rest ih =>
    show (setAll rest (store.set entry.1.address (some entry.2)) key.address).isSome
    by_cases later : ∃ other ∈ rest, other.1 = key
    · exact ih _ later
    · have head : entry.1 = key := by
        obtain ⟨other, mem, same⟩ := present
        rcases List.mem_cons.mp mem with rfl | mem
        · exact same
        · exact absurd ⟨other, mem, same⟩ later
      push Not at later
      rw [setAll_apply_not_mem rest _ key later, head]
      simp

/-- **Birth writes exactly the declared set**: on a store holding none of the
cell's declaration keys, `declare` makes `declaredIn` the field set's `covers`,
for every field: the listed fields, every field at or above the tail, and no
other.  (`room_birth_declared_boundary` is five instances of this.) -/
theorem declaredIn_declare (cellId : Nat) (set : FieldSet) (store : Store effectLayout)
    (noOpen : store (openKey cellId).address = none)
    (noFrom : store (fromKey cellId).address = none)
    (noField : ∀ m, store (declaredKey cellId m).address = none) (n : Nat) :
    declaredIn cellId (declare cellId set store) n = set.covers n := by
  cases set with
  | «open» =>
    have opened : (declare cellId .open store (openKey cellId).address).isSome :=
      setAll_apply_mem _ _ _ ⟨(openKey cellId, 0), by simp [FieldSet.entries], rfl⟩
    simp [declaredIn, FieldSet.covers, opened]
  | closed fields tail =>
    have openAbsent : declare cellId (.closed fields tail) store (openKey cellId).address = none := by
      rw [show declare cellId (.closed fields tail) store = setAll _ store from rfl,
        setAll_apply_not_mem _ _ _ (by
          intro entry mem
          simp only [FieldSet.entries, List.mem_append, List.mem_map, Option.mem_toList,
            Option.map_eq_some_iff] at mem
          rcases mem with ⟨m, _, rfl⟩ | ⟨first, _, rfl⟩ <;> simp [declaredKey, fromKey, openKey]),
        noOpen]
    have fieldLookup : (declare cellId (.closed fields tail) store (declaredKey cellId n).address).isSome =
        decide (n ∈ fields) := by
      by_cases listed : n ∈ fields
      · rw [decide_eq_true listed]
        exact setAll_apply_mem _ _ _ ⟨(declaredKey cellId n, 0), by
          simp only [FieldSet.entries, List.mem_append, List.mem_map]
          exact .inl ⟨n, listed, rfl⟩, rfl⟩
      · rw [decide_eq_false listed]
        rw [show declare cellId (.closed fields tail) store = setAll _ store from rfl,
          setAll_apply_not_mem _ _ _ (by
            intro entry mem
            simp only [FieldSet.entries, List.mem_append, List.mem_map, Option.mem_toList,
              Option.map_eq_some_iff] at mem
            rcases mem with ⟨m, mem, rfl⟩ | ⟨first, _, rfl⟩
            · intro same
              simp only [declaredKey, StateKey.fieldDeclared.injEq] at same
              exact listed (by cases same.2; exact mem)
            · simp [declaredKey, fromKey]),
          noField]
        rfl
    have tailLookup : declare cellId (.closed fields tail) store (fromKey cellId).address =
        tail.map (fun first => (first : Int)) := by
      cases tail with
      | none =>
        rw [show declare cellId (.closed fields none) store = setAll _ store from rfl,
          setAll_apply_not_mem _ _ _ (by
            intro entry mem
            simp [FieldSet.entries] at mem
            obtain ⟨m, _, rfl⟩ := mem
            simp [declaredKey, fromKey]),
          noFrom]
        rfl
      | some first =>
        show setAll _ store _ = _
        simp [setAll, FieldSet.entries, List.foldl_append]
    simp only [declaredIn, openAbsent, Option.isSome_none, Bool.false_or, fieldLookup, tailLookup,
      FieldSet.covers]
    cases tail <;> simp [tailCovers]

/-- `declaredIn_declare` at a birth from the empty store (the premises hold by `rfl`). -/
theorem declaredIn_declare_empty (cellId : Nat) (set : FieldSet) (n : Nat) :
    declaredIn cellId (declare cellId set 0) n = set.covers n :=
  declaredIn_declare cellId set 0 rfl rfl (fun _ => rfl) n

/-! ## §4. No action writes a declaration -/

theorem writableKeyCheck_not_declaration {kind : ResourceKind} (target : ResourceId kind)
    (key : StateKey) (writable : writableKeyCheck target key = true) :
    (∀ object field, key ≠ .fieldDeclared object field) ∧ (∀ object, key ≠ .fieldsOpen object) ∧
      ∀ object, key ≠ .fieldsFrom object := by
  cases kind <;> cases key <;> simp_all [writableKeyCheck]

/-- An admitted declaration's patch writes no declaration key. -/
theorem admitted_writes_no_declaration {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) (admitted : declaration.Admitted) (key : StateKey)
    (isDeclaration : (∃ object field, key = .fieldDeclared object field) ∨
      (∃ object, key = .fieldsOpen object) ∨ ∃ object, key = .fieldsFrom object) :
    key.address ∉ Patch.writeFootprint declaration.patch := by
  intro written
  rw [Patch.mem_writeFootprint_iff] at written
  obtain ⟨op, member, address⟩ := written
  unfold Declaration.patch at member
  obtain ⟨action, actionMember, opMember⟩ := List.mem_flatMap.mp member
  have actionAdmitted := (declaration.admitted_iff.mp admitted) action actionMember
  cases action with
  | create written initial =>
    simp only [Action.ops, List.mem_singleton] at opMember
    subst opMember
    rw [guardedSet_address] at address
    have same := StateKey.address_injective (Option.some.inj address)
    have writable : writableKeyCheck target written = true := actionAdmitted
    obtain ⟨notDeclared, notOpen, notFrom⟩ := writableKeyCheck_not_declaration target written writable
    rcases isDeclaration with ⟨object, field, rfl⟩ | ⟨object, rfl⟩ | ⟨object, rfl⟩
    · exact notDeclared object field same
    · exact notOpen object same
    · exact notFrom object same
  | write written expected replacement =>
    simp only [Action.ops, List.mem_singleton] at opMember
    subst opMember
    rw [guardedSet_address] at address
    have same := StateKey.address_injective (Option.some.inj address)
    have writable : writableKeyCheck target written = true := actionAdmitted
    obtain ⟨notDeclared, notOpen, notFrom⟩ := writableKeyCheck_not_declaration target written writable
    rcases isDeclaration with ⟨object, field, rfl⟩ | ⟨object, rfl⟩ | ⟨object, rfl⟩
    · exact notDeclared object field same
    · exact notOpen object same
    · exact notFrom object same
  | move source destination resource sourceExpected destinationExpected amount =>
    simp only [Action.ops, List.mem_cons, List.not_mem_nil, or_false] at opMember
    rcases opMember with rfl | rfl <;>
    · rw [guardedSet_address] at address
      have same := StateKey.address_injective (Option.some.inj address)
      rcases isDeclaration with ⟨object, field, rfl⟩ | ⟨object, rfl⟩ | ⟨object, rfl⟩ <;> cases same

/-- **A cell's declaration is fixed**: running an admitted declaration leaves
every field's declared-ness as it was. -/
theorem admitted_preserves_declared {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) (admitted : declaration.Admitted)
    (cellId : Nat) (store : Store effectLayout) (n : Nat) :
    declaredIn cellId (Patch.run store declaration.patch) n = declaredIn cellId store n := by
  unfold declaredIn openKey declaredKey fromKey
  rw [Patch.run_frame _ _ _
      (admitted_writes_no_declaration declaration admitted _ (.inr (.inl ⟨_, rfl⟩))),
    Patch.run_frame _ _ _
      (admitted_writes_no_declaration declaration admitted _ (.inl ⟨_, _, rfl⟩)),
    Patch.run_frame _ _ _
      (admitted_writes_no_declaration declaration admitted _ (.inr (.inr ⟨_, rfl⟩)))]

/-! ## §5. Poles, on field values -/

/-- A closed sixteen-field set (the job's): creating field 20 is named. -/
theorem closed_names_created_field :
    firstUndeclared (FieldSet.closed (List.range 16)).covers [(0, 6), (8, 0)]
      [(0, 6), (8, 0), (20, 1)] = some 20 := by decide

/-- The same write on an open cell is not refused for its fields. -/
theorem open_admits_created_field :
    firstUndeclared FieldSet.open.covers [(0, 6), (8, 0)] [(0, 6), (8, 0), (20, 1)] = none := by
  decide

/-- A write inside the set names nothing. -/
theorem closed_admits_declared_write :
    firstUndeclared (FieldSet.closed (List.range 16)).covers [(0, 6), (8, 0)]
      [(0, 6), (8, 0), (12, 77)] = none := by decide

/-- **The tail's satisfiable pole** (a room: fixed fields 1001..1012, roster tail
from 2000): rows created at the tail's first field and far above it are
declared, however many members came before. -/
theorem tail_admits_rows_at_and_above :
    firstUndeclared (FieldSet.closed ((List.range 12).map (· + 1001)) (some 2000)).covers
      [(1001, 5)] [(1001, 5), (2000, 7), (2001, 9), (1000001, 3)] = none := by decide

/-- **The tail's refutable pole**: the field just below the tail, outside the
listed fields, is named. -/
theorem tail_names_field_below :
    firstUndeclared (FieldSet.closed ((List.range 12).map (· + 1001)) (some 2000)).covers
      [(1001, 5)] [(1001, 5), (1999, 7)] = some 1999 := by decide

/-- A declared cell's lookup (`declaredIn`, what the receiver and the cell law
evaluate) on a room's birth store: the listed fields and the tail are declared,
the gap between them is not, and the tail is one entry (`declaration_one_tail_entry`). -/
theorem room_birth_declared_boundary :
    declaredIn 7 (declare 7 (.closed [1001, 1012] (some 2000)) 0) 1012 = true ∧
    declaredIn 7 (declare 7 (.closed [1001, 1012] (some 2000)) 0) 2000 = true ∧
    declaredIn 7 (declare 7 (.closed [1001, 1012] (some 2000)) 0) 1000000 = true ∧
    declaredIn 7 (declare 7 (.closed [1001, 1012] (some 2000)) 0) 1999 = false ∧
    declaredIn 7 (declare 7 (.closed [1001, 1012] (some 2000)) 0) 1013 = false := by
  decide

/-- The width the room schema saves: a declaration with a tail writes one entry
for the whole unbounded roster, where the pre-declared roster wrote one entry
per slot. -/
theorem declaration_one_tail_entry (cellId : Nat) (fields : List Nat) (first : Nat) :
    ((FieldSet.closed fields (some first)).entries cellId).length = fields.length + 1 := by
  simp [FieldSet.entries]

end Minidregg.Kernel.FieldClosure

/-- info: 'Minidregg.Kernel.FieldClosure.firstUndeclared_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.firstUndeclared_none_iff
/-- info: 'Minidregg.Kernel.FieldClosure.firstUndeclared_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.firstUndeclared_some
/-- info: 'Minidregg.Kernel.FieldClosure.open_admits_every_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.open_admits_every_field
/-- info: 'Minidregg.Kernel.FieldClosure.get_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.get_values
/-- info: 'Minidregg.Kernel.FieldClosure.closed_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.closed_preserved
/-- info: 'Minidregg.Kernel.FieldClosure.admitted_writes_no_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.admitted_writes_no_declaration
/-- info: 'Minidregg.Kernel.FieldClosure.admitted_preserves_declared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.admitted_preserves_declared
/-- info: 'Minidregg.Kernel.FieldClosure.closed_names_created_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.closed_names_created_field
/-- info: 'Minidregg.Kernel.FieldClosure.open_admits_created_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.open_admits_created_field
/-- info: 'Minidregg.Kernel.FieldClosure.closed_admits_declared_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FieldClosure.closed_admits_declared_write
#assert_axioms Minidregg.Kernel.FieldClosure.tail_admits_rows_at_and_above
#assert_axioms Minidregg.Kernel.FieldClosure.tail_names_field_below
#assert_axioms Minidregg.Kernel.FieldClosure.room_birth_declared_boundary
#assert_axioms Minidregg.Kernel.FieldClosure.declaration_one_tail_entry
#assert_axioms Minidregg.Kernel.FieldClosure.declaredIn_declare
#assert_axioms Minidregg.Kernel.FieldClosure.declaredIn_declare_empty
