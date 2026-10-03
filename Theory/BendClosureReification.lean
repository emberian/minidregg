/- Transport of actual closure-arena reification under immutable heap growth.
These lemmas preserve denotation, not source Value or termination. In particular,
a retained Q0 thunk is not made into a live value by extending its heap.
-/
import Theory.BendClosureArena

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

/-- Existing values, thunks, pairs and application spines keep their exact
source term when the heap preserves all previously readable rows. -/
theorem Denotes.extends {program : Program} {old next : Heap}
    (extension : Extends old next) {pointer : Nat} {term : Term}
    (denotation : Denotes program old pointer term) :
    Denotes program next pointer term := by
  apply @Denotes.rec program old
    (fun pointer term _ => Denotes program next pointer term)
    (fun pointer values _ => EnvironmentDenotes program next pointer values)
    ?_ ?_ ?_ ?_ ?_ pointer term denotation
  · intro pointer code environment term values found codeExact envExact envIH
    exact .closure (extension _ _ found) codeExact envIH
  · intro pointer q first second A B found firstExact secondExact firstIH secondIH
    exact .pair (extension _ _ found) firstIH secondIH
  · intro pointer q function argument F X found functionExact argumentExact functionIH argumentIH
    exact .application (extension _ _ found) functionIH argumentIH
  · intro pointer found
    exact .nil (extension _ _ found)
  · intro pointer value tail term values found valueExact tailExact valueIH tailIH
    exact .cons (extension _ _ found) valueIH tailIH

/-- An environment preserves the whole ordered substitution, including unused
binder positions. Heap growth does not erase or reorder its entries. -/
theorem EnvironmentDenotes.extends {program : Program} {old next : Heap}
    (extension : Extends old next) {pointer : Nat} {values : List Term}
    (denotation : EnvironmentDenotes program old pointer values) :
    EnvironmentDenotes program next pointer values := by
  apply @EnvironmentDenotes.rec program old
    (fun pointer term _ => Denotes program next pointer term)
    (fun pointer values _ => EnvironmentDenotes program next pointer values)
    ?_ ?_ ?_ ?_ ?_ pointer values denotation
  · intro pointer code environment term values found codeExact envExact envIH
    exact .closure (extension _ _ found) codeExact envIH
  · intro pointer q first second A B found firstExact secondExact firstIH secondIH
    exact .pair (extension _ _ found) firstIH secondIH
  · intro pointer q function argument F X found functionExact argumentExact functionIH argumentIH
    exact .application (extension _ _ found) functionIH argumentIH
  · intro pointer found
    exact .nil (extension _ _ found)
  · intro pointer value tail term values found valueExact tailExact valueIH tailIH
    exact .cons (extension _ _ found) valueIH tailIH

/-- Exact functional full-scan write semantics, including out-of-range reads. -/
theorem fill_read (rows : Array Row) (pointer index : Nat) (value : Row) :
    (fill rows pointer value)[index]? =
      rows[index]?.map (fun old => if index = pointer then value else old) := by
  simp [fill, List.getElem?_map, List.getElem?_zipIdx, Option.map_map,
    Function.comp_def]

theorem fill_size (rows : Array Row) (pointer : Nat) (value : Row) :
    (fill rows pointer value).size = rows.size := by
  simp [fill]

/-- Appending at the old frontier preserves every previously readable row,
independently of what the newly allocated row denotes. -/
theorem append_extends (heap : Heap) (value : Row) :
    Extends heap {rows := fill heap.rows heap.used value, used := heap.used + 1} := by
  intro pointer row found
  have before : pointer < heap.used := by
    by_cases inside : pointer < heap.used
    · exact inside
    · simp [Heap.get?, inside] at found
  have different : pointer ≠ heap.used := Nat.ne_of_lt before
  have after : pointer < heap.used + 1 := by omega
  simpa [Heap.get?, before, after, fill_read, different] using found

/-- If the append frontier is in the fixed buffer, the new pointer reads the
new row exactly. Together with append_extends this is the arena simulation seam. -/
theorem append_reads_new (heap : Heap) (value : Row)
    (room : heap.used < heap.rows.size) :
    Heap.get? {rows := fill heap.rows heap.used value, used := heap.used + 1}
      heap.used = some value := by
  simp [Heap.get?, fill_read, Array.getElem?_eq_getElem room]

/-- A successful allocation returns precisely the frontier and appended heap;
none of its refusal branches can be treated as a successful allocation. -/
theorem allocate_shape {shape : Shape} {codeBound : Nat} {heap next : Heap}
    {value : Row} {pointer : Nat}
    (accepted : allocate shape codeBound heap value = .ok (pointer, next)) :
    pointer = heap.used ∧
      next = {rows := fill heap.rows heap.used value, used := heap.used + 1} := by
  unfold allocate at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · split at accepted
      · contradiction
      · split at accepted
        · contradiction
        · cases accepted
          exact ⟨rfl, rfl⟩

theorem allocate_extends {shape : Shape} {codeBound : Nat} {heap next : Heap}
    {value : Row} {pointer : Nat}
    (accepted : allocate shape codeBound heap value = .ok (pointer, next)) :
    Extends heap next := by
  obtain ⟨_, rfl⟩ := allocate_shape accepted
  exact append_extends heap value

/-- The controller can retain its exact source entry through any certified
extension without reconstructing or executing a source term at runtime. -/
def Entry.extend {program : Program} {old next : Heap} {source : Term}
    (entry : Entry program old source) (extension : Extends old next) :
    Entry program next source :=
  { pointer := entry.pointer, exact := entry.exact.extends extension }

theorem Entry.extend_pointer {program : Program} {old next : Heap} {source : Term}
    (entry : Entry program old source) (extension : Extends old next) :
    (entry.extend extension).pointer = entry.pointer := rfl

#assert_axioms fill_read
#assert_axioms fill_size
#assert_axioms append_extends
#assert_axioms append_reads_new
#assert_axioms allocate_shape
#assert_axioms allocate_extends
#assert_axioms Denotes.extends
#assert_axioms EnvironmentDenotes.extends
#assert_axioms Entry.extend_pointer
end Minidregg.Theory.BendClosureArena
