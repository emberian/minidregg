/- Exact semantic installation of a newly allocated closure/environment row.
These lemmas concern the actual arena allocate function and its checked result;
they do not assume allocation succeeds or turn retained thunks into Values. -/
import Theory.BendClosureReification
import Theory.BendClosureDenotation

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

/-- Meaning of a candidate term row before its pointer exists. -/
inductive TermRowDenotes (program : Program) (heap : Heap) : Row → Term → Prop
  | closure {pc environment : Nat} {source : Term} {values : Env} :
      CodeDenotes program pc source →
      EnvironmentDenotes program heap environment values →
      TermRowDenotes program heap (.closure pc environment)
        (Term.sub (Env.sub values) source)
  | pair {q : Quan} {first second : Nat} {a b : Term} :
      Denotes program heap first a → Denotes program heap second b →
      TermRowDenotes program heap (.pair q first second) (.Tup q a b)
  | application {q : Quan} {function argument : Nat} {f x : Term} :
      Denotes program heap function f → Denotes program heap argument x →
      TermRowDenotes program heap (.application q function argument) (.App q f x)

inductive EnvironmentRowDenotes (program : Program) (heap : Heap) : Row → Env → Prop
  | nil : EnvironmentRowDenotes program heap .nil []
  | cons {value tail : Nat} {source : Term} {values : Env} :
      Denotes program heap value source → EnvironmentDenotes program heap tail values →
      EnvironmentRowDenotes program heap (.environment value tail) (source :: values)

theorem allocate_room {shape : Shape} {codeBound : Nat} {heap next : Heap}
    {value : Row} {pointer : Nat}
    (accepted : allocate shape codeBound heap value = .ok (pointer, next)) :
    heap.used < heap.rows.size := by
  by_cases valid : heap.valid shape = true
  · have size : heap.rows.size = shape.slots := by
      simp only [Heap.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
      omega
    by_cases room : heap.used < shape.slots
    · omega
    · have full : heap.used ≥ shape.slots := Nat.le_of_not_gt room
      simp [allocate, valid, full] at accepted
  · simp [allocate, valid] at accepted

theorem allocate_reads_new {shape : Shape} {codeBound : Nat} {heap next : Heap}
    {value : Row} {pointer : Nat}
    (accepted : allocate shape codeBound heap value = .ok (pointer, next)) :
    next.get? pointer = some value := by
  have room := allocate_room accepted
  obtain ⟨rfl, rfl⟩ := allocate_shape accepted
  exact append_reads_new heap value room

theorem allocate_term {program : Program} {shape : Shape} {heap next : Heap}
    {row : Row} {pointer : Nat} {source : Term}
    (meaning : TermRowDenotes program heap row source)
    (accepted : allocate shape program.code.size heap row = .ok (pointer, next)) :
    Denotes program next pointer source := by
  have extension := allocate_extends accepted
  have found := allocate_reads_new accepted
  cases meaning with
  | closure code captured => exact .closure found code (captured.extends extension)
  | pair first second => exact .pair found (first.extends extension) (second.extends extension)
  | application function argument =>
    exact .application found (function.extends extension) (argument.extends extension)

theorem allocate_environment {program : Program} {shape : Shape} {heap next : Heap}
    {row : Row} {pointer : Nat} {values : Env}
    (meaning : EnvironmentRowDenotes program heap row values)
    (accepted : allocate shape program.code.size heap row = .ok (pointer, next)) :
    EnvironmentDenotes program next pointer values := by
  have extension := allocate_extends accepted
  have found := allocate_reads_new accepted
  cases meaning with
  | nil => exact .nil found
  | cons value tail => exact .cons found (value.extends extension) (tail.extends extension)

/-- Any independently supplied decode of the fresh pointer agrees exactly
with the source row used for the actual successful allocation. -/
theorem allocated_term_unique {program : Program} {shape : Shape} {heap next : Heap}
    {row : Row} {pointer : Nat} {source decoded : Term}
    (meaning : TermRowDenotes program heap row source)
    (accepted : allocate shape program.code.size heap row = .ok (pointer, next))
    (decode : Denotes program next pointer decoded) : decoded = source :=
  decode.functional (allocate_term meaning accepted)

#assert_axioms allocate_room
#assert_axioms allocate_reads_new
#assert_axioms allocate_term
#assert_axioms allocate_environment
#assert_axioms allocated_term_unique

/-- Every true cache bit has a real source Data witness. This stronger reachable
invariant is not vacuous on a pointer with no denotation, unlike implication-only
cache soundness. The witnesses are proofs, never runtime materialized terms. -/
def CacheCertified (program : Program) (heap : Heap) (bits : Array Bool) : Prop :=
  ∀ pointer, bits[pointer]? = some true →
    ∃ source, Denotes program heap pointer source ∧ Data source

theorem CacheCertified.sound {program : Program} {heap : Heap} {bits : Array Bool}
    (certified : CacheCertified program heap bits) {pointer : Nat} {source : Term}
    (bit : bits[pointer]? = some true) (meaning : Denotes program heap pointer source) :
    Data source := by
  obtain ⟨witness, exact, data⟩ := certified pointer bit
  rw [meaning.functional exact]
  exact data

/-- This is the literal fixed-size data-cache write used by Machine.allocate. -/
theorem cache_fill_read (bits : Array Bool) (pointer index : Nat) (value : Bool) :
    ((bits.toList.zipIdx.map fun pair =>
      if pair.2 = pointer then value else pair.1).toArray)[index]? =
      bits[index]?.map (fun old => if index = pointer then value else old) := by
  simp [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Function.comp_def]

theorem CacheCertified.fill {program : Program} {old next : Heap} {bits : Array Bool}
    (certified : CacheCertified program old bits) (extension : Extends old next)
    (pointer : Nat) (value : Bool)
    (fresh : value = true → ∃ source, Denotes program next pointer source ∧ Data source) :
    CacheCertified program next
      (bits.toList.zipIdx.map fun pair =>
        if pair.2 = pointer then value else pair.1).toArray := by
  intro index trueBit
  rw [cache_fill_read] at trueBit
  by_cases same : index = pointer
  · subst index
    have valueTrue : value = true := by
      cases found : bits[pointer]? <;> simp_all
    exact fresh valueTrue
  · have oldTrue : bits[index]? = some true := by
      simpa [same] using trueBit
    obtain ⟨source, exact, data⟩ := certified index oldTrue
    exact ⟨source, exact.extends extension, data⟩

theorem CacheCertified.allocate {program : Program} {shape : Shape}
    {old next : Heap} {bits : Array Bool} {row : Row} {pointer : Nat} (value : Bool)
    (certified : CacheCertified program old bits)
    (accepted : allocate shape program.code.size old row = .ok (pointer, next))
    (qualifies : value = true →
      ∃ source, TermRowDenotes program old row source ∧ Data source) :
    CacheCertified program next
      (bits.toList.zipIdx.map fun pair =>
        if pair.2 = pointer then value else pair.1).toArray := by
  apply certified.fill (allocate_extends accepted) pointer value
  intro yes
  obtain ⟨source, meaning, data⟩ := qualifies yes
  exact ⟨source, allocate_term meaning accepted, data⟩

#assert_axioms CacheCertified.sound
#assert_axioms cache_fill_read
#assert_axioms CacheCertified.fill
#assert_axioms CacheCertified.allocate


theorem cache_bit_of_getD {bits : Array Bool} {pointer : Nat}
    (trueBit : bits[pointer]?.getD false = true) : bits[pointer]? = some true := by
  cases found : bits[pointer]? with
  | none => simp [found] at trueBit
  | some value => cases value <;> simp_all

theorem code_label_data {program : Program} {pc label : Nat} {source : Term}
    (meaning : CodeDenotes program pc source)
    (found : program.code[pc]? = some (.lab label)) (substitution : Subst) :
    Data (Term.sub substitution source) := by
  cases meaning <;> simp_all [Term.sub]
  exact .lab

theorem code_rfl_data {program : Program} {pc : Nat} {source : Term}
    (meaning : CodeDenotes program pc source)
    (found : program.code[pc]? = some .rfl) (substitution : Subst) :
    Data (Term.sub substitution source) := by
  cases meaning <;> simp_all [Term.sub]
  exact .rfl

theorem TermRowDenotes.label_data {program : Program} {heap : Heap}
    {pc environment label : Nat} {source : Term}
    (meaning : TermRowDenotes program heap (.closure pc environment) source)
    (found : program.code[pc]? = some (.lab label)) : Data source := by
  cases meaning with
  | closure exact captured => exact code_label_data exact found _

theorem TermRowDenotes.rfl_data {program : Program} {heap : Heap}
    {pc environment : Nat} {source : Term}
    (meaning : TermRowDenotes program heap (.closure pc environment) source)
    (found : program.code[pc]? = some .rfl) : Data source := by
  cases meaning with
  | closure exact captured => exact code_rfl_data exact found _

/-- The actual pair qualification expression examines only live first fields.
A dead Q0 field still has exact reification, but needs no Data/Value assumption. -/
theorem TermRowDenotes.pair_data {program : Program} {heap : Heap} {bits : Array Bool}
    {q : Quan} {first second : Nat} {source : Term}
    (certified : CacheCertified program heap bits)
    (meaning : TermRowDenotes program heap (.pair q first second) source)
    (qualifies : ((!q.live || bits[first]?.getD false) &&
      bits[second]?.getD false) = true) : Data source := by
  have parts : (!q.live || bits[first]?.getD false) = true ∧ bits[second]?.getD false = true := by
    simpa only [Bool.and_eq_true] using qualifies
  cases meaning with
  | pair head tail =>
    apply Data.tup
    · intro live
      have firstTrue : bits[first]?.getD false = true := by
        simpa [live] using parts.1
      exact certified.sound (cache_bit_of_getD firstTrue) head
    · exact certified.sound (cache_bit_of_getD parts.2) tail

#assert_axioms cache_bit_of_getD
#assert_axioms code_label_data
#assert_axioms code_rfl_data
#assert_axioms TermRowDenotes.label_data
#assert_axioms TermRowDenotes.rfl_data
#assert_axioms TermRowDenotes.pair_data


theorem allocate_checks {shape : Shape} {codeBound : Nat} {heap next : Heap}
    {value : Row} {pointer : Nat}
    (accepted : allocate shape codeBound heap value = .ok (pointer, next)) :
    heap.valid shape = true ∧ heap.used < shape.slots ∧
      value.fits (2 ^ shape.wordBits) = true ∧
      value.referencesFit codeBound heap.used = true := by
  unfold allocate at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · split at accepted
      · contradiction
      · split at accepted
        · contradiction
        · simp_all

theorem fill_all_fits (rows : Array Row) (pointer limit : Nat) (value : Row)
    (oldFits : rows.all (Row.fits limit) = true)
    (newFits : value.fits limit = true) :
    (fill rows pointer value).all (Row.fits limit) = true := by
  apply Array.all_eq_true.mpr
  intro index inside
  have oldInside : index < rows.size := by simpa [fill_size] using inside
  have read : (fill rows pointer value)[index]? =
      some (if index = pointer then value else rows[index]) := by
    rw [fill_read, Array.getElem?_eq_getElem oldInside]
    rfl
  have exact := Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans read)
  rw [exact]
  split
  · exact newFits
  · exact Array.all_eq_true.mp oldFits index oldInside

/-- Successful actual allocation preserves the checked fixed buffer shape,
word bounds and frontier. Circuit packing may consume this invariant instead
of rechecking every unchanged row on each allocation. -/
theorem allocate_valid {shape : Shape} {codeBound : Nat} {heap next : Heap}
    {value : Row} {pointer : Nat}
    (accepted : allocate shape codeBound heap value = .ok (pointer, next)) :
    next.valid shape = true := by
  obtain ⟨valid, room, fits, _⟩ := allocate_checks accepted
  obtain ⟨_, rfl⟩ := allocate_shape accepted
  simp only [Heap.valid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at valid ⊢
  obtain ⟨size, used, rowsFit⟩ := valid
  refine ⟨?_, ?_, fill_all_fits heap.rows heap.used _ value rowsFit fits⟩
  · simpa [fill_size] using size
  · omega

#assert_axioms allocate_checks
#assert_axioms fill_all_fits
#assert_axioms allocate_valid

end Minidregg.Theory.BendClosureArena

