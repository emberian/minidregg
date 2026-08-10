/-
# Theory.StoreFiniteSupport -- which stores can be materialized at all

`Theory.MaterializerCardinality` proves `DeclaredTurn.effectSchema` admits no
materializer, and `Theory.SparseLogicalState` supplies the fix: a finitely
supported cell state.  Migrating that schema means `DeclaredTurn.logicalOfStore`
can no longer accept an arbitrary `EffectDeclaration.Store`, because a total
function `StateKey -> Int` is not finitely supported in general.

This states the missing invariant rather than changing 113 semantic call sites.
The store stays a total function where it is doing semantics -- semantics needs
no codec -- and finite support becomes a requirement exactly at the
materialization boundary, which is where the obstruction actually is.

The invariant is real and has always held: a turn begins at the zero store and
each mutation writes one key.  Nobody had said so, which is why nobody noticed
the boundary could not be crossed.

Nothing here changes an existing definition.  It supplies the two facts the
migration needs -- the base case and the step -- so that
`logicalOfStore`'s successor can demand a witness that its callers can actually
produce.
-/
import Theory.DeclaredTurn
import Theory.EffectDeclaration
import Theory.SparseLogicalState

namespace Minidregg.Theory.StoreFiniteSupport

open Minidregg.Theory
open Minidregg.Theory.EffectDeclaration

set_option autoImplicit false

/-! ## The invariant -/

/-- A store is finitely supported when some finite key set carries every
nonzero entry.  Stated with an explicit carrier rather than as a `Finsupp` so
that `applyPatch`'s step can name the key it just wrote. -/
def FinitelySupported (store : Store) : Prop :=
  ∃ carrier : Finset StateKey, ∀ key, key ∉ carrier → store key = 0

/-- **The base case.**  The zero store is supported by the empty set. -/
theorem finitelySupported_zero : FinitelySupported (fun _ => 0) :=
  ⟨∅, fun _ _ => rfl⟩

/-- **The step.**  One mutation writes one key, so it enlarges the carrier by
at most that key.  This is the fact that makes the invariant inductive. -/
theorem finitelySupported_applyMutation (mutation : Mutation) {store : Store}
    (supported : FinitelySupported store) :
    FinitelySupported (applyMutation mutation store) := by
  obtain ⟨carrier, outside⟩ := supported
  refine ⟨insert mutation.key carrier, fun key notMember => ?_⟩
  have notKey : key ≠ mutation.key := by
    intro same
    exact notMember (same ▸ Finset.mem_insert_self _ _)
  have notCarrier : key ∉ carrier := fun member =>
    notMember (Finset.mem_insert_of_mem member)
  rw [applyMutation_frame mutation store key notKey]
  exact outside key notCarrier

/-- **The invariant is preserved by a whole patch**, by induction on the
mutation list. -/
theorem finitelySupported_applyPatch (mutations : List Mutation) {store : Store}
    (supported : FinitelySupported store) :
    FinitelySupported (applyPatch mutations store) := by
  induction mutations generalizing store with
  | nil => exact supported
  | cons mutation rest ih =>
      exact ih (finitelySupported_applyMutation mutation supported)

/-- Every store reachable from zero by a patch is finitely supported -- the
statement the migration actually consumes at a call site. -/
theorem finitelySupported_ofZero (mutations : List Mutation) :
    FinitelySupported (applyPatch mutations (fun _ => 0)) :=
  finitelySupported_applyPatch mutations finitelySupported_zero

/-! ## The bridge to the sparse cell state

A finitely supported store becomes a sparse cell state by listing its carrier.
`sparseOfStore_readD` is the theorem that makes the replacement faithful: read
the result back with the zero default and you have the original store, on every
key, including the ones outside the carrier.  Without it the migration would be
a change of representation with no guarantee it preserved meaning. -/

open Minidregg.Theory.SparseLogicalState

instance : DecidableEq DeclaredTurn.effectSchema.Field :=
  inferInstanceAs (DecidableEq StateKey)

/-- Entries for an explicit key list. -/
def entriesOf (store : Store) (keys : List StateKey) :
    List (Sigma DeclaredTurn.effectSchema.FieldType) :=
  keys.map fun key => ⟨key, show Int from store key⟩

/-- Reading those entries is membership in the key list. -/
theorem read_entriesOf (store : Store) (keys : List StateKey) (key : StateKey) :
    (⟨entriesOf store keys⟩ : SparseState DeclaredTurn.effectSchema).read key =
      if key ∈ keys then some (show Int from store key) else none := by
  induction keys with
  | nil => rfl
  | cons head rest ih =>
      show List.findSome?
          (fun entry => if same : entry.1 = key then some (same ▸ entry.2) else none)
          (⟨head, show Int from store head⟩ :: entriesOf store rest) = _
      rw [List.findSome?_cons]
      by_cases same : head = key
      · subst same
        rw [dif_pos rfl, if_pos List.mem_cons_self]
        rfl
      · rw [dif_neg same]
        show (⟨entriesOf store rest⟩ : SparseState DeclaredTurn.effectSchema).read key = _
        rw [ih]
        simp [Ne.symm same]

/-- A finitely supported store as a sparse cell state. -/
noncomputable def sparseOfStore (store : Store) (supported : FinitelySupported store) :
    SparseState DeclaredTurn.effectSchema :=
  ⟨entriesOf store supported.choose.toList⟩

/-- **The bridge is faithful.**  Reading the sparse state with the zero default
returns the original store at every key -- inside the carrier by lookup, outside
it because the invariant says the store is zero there. -/
theorem sparseOfStore_readD (store : Store) (supported : FinitelySupported store)
    (key : StateKey) :
    (sparseOfStore store supported).readD (fun _ => show Int from 0) key =
      store key := by
  rw [sparseOfStore, SparseState.readD, read_entriesOf]
  by_cases member : key ∈ supported.choose.toList
  · rw [if_pos member]
    rfl
  · rw [if_neg member]
    exact (supported.choose_spec key (by simpa using member)).symm

/-! ## Teeth: the invariant is not free

If every store were finitely supported the requirement would be decoration.
It is not: the constant-one store is a perfectly good `Store` and is supported
by nothing, which is exactly the store that cannot be materialized. -/

/-- `StateKey` is infinite -- program identifiers are `Nat`-indexed -- which is
what the teeth below rest on. -/
instance : Infinite StateKey :=
  Infinite.of_injective (fun index => StateKey.programCode ⟨index⟩)
    (by intro left right same; cases same; rfl)

/-- The constant-one store is not finitely supported: no finite carrier can
cover an infinite key space. -/
theorem not_finitelySupported_one : ¬FinitelySupported (fun _ => 1) := by
  rintro ⟨carrier, outside⟩
  obtain ⟨key, notMember⟩ := Infinite.exists_notMem_finset carrier
  have zero : (1 : Int) = 0 := outside key notMember
  exact absurd zero (by decide)

/-- info: 'Minidregg.Theory.StoreFiniteSupport.finitelySupported_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finitelySupported_zero
/-- info: 'Minidregg.Theory.StoreFiniteSupport.finitelySupported_applyMutation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finitelySupported_applyMutation
/-- info: 'Minidregg.Theory.StoreFiniteSupport.finitelySupported_applyPatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finitelySupported_applyPatch
/-- info: 'Minidregg.Theory.StoreFiniteSupport.finitelySupported_ofZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finitelySupported_ofZero
/-- info: 'Minidregg.Theory.StoreFiniteSupport.read_entriesOf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms read_entriesOf
/-- info: 'Minidregg.Theory.StoreFiniteSupport.sparseOfStore_readD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sparseOfStore_readD
/-- info: 'Minidregg.Theory.StoreFiniteSupport.not_finitelySupported_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_finitelySupported_one

end Minidregg.Theory.StoreFiniteSupport
