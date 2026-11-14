/- Generic scalar projection for declared resource policy evaluation.
All values come from the declared-effect cell's store (`Compiler.DeclaredEffectCell`),
read in its canonical address order.  A resource contributes every field it
has; there is no page capacity.  Pair deltas expose linear conservation
constraints to the existing Pred algebra without opaque checks,
application-specific evaluator branches or a host-provided admission bit. -/
module

public import Compiler.DeclaredEffectCell

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.String.Defs
import all Init.Data.List.Basic
import all Init.Data.String.Bootstrap

@[expose] public section

namespace Minidregg.Kernel.DeclaredResourceProjection
open Minidregg.Compiler
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Store
set_option autoImplicit false

/-- Full field identifier, not a reduced digest or truncated address. -/
def fieldName (n : Nat) (view : String) : String := s!"resource/field/{n}/{view}"
def pairName (a b : Nat) : String := s!"resource/pair/{a}/{b}/delta"

abbrev Values := List (Nat × Int)

/-- The present fields of object `task`, in the cell's canonical entry order. -/
def values (task : Nat) (store : Store effectLayout) : Values :=
  (StoreCodec.entries DeclaredEffectCell.wire store).filterMap fun entry =>
    match entry.1.2, entry.2 with
    | .objectField object field, value =>
        if object.value = task then some (field.value, value) else none
    | _, _ => none

def get (xs : Values) (key : Nat) : Option Int :=
  (xs.find? (fun p => p.1 == key)).map (·.2)

/-- Only jointly present values have a delta. Absence is not a stored zero. -/
def scalarSlots (before after : Values) : List (String × Int) :=
  before.map (fun p => (fieldName p.1 "before", p.2)) ++
  after.map (fun p => (fieldName p.1 "after", p.2)) ++
  after.filterMap (fun p => (get before p.1).map fun old =>
    (fieldName p.1 "delta", p.2 - old)) ++
  after.flatMap (fun a => after.filterMap fun b => do
    let oldA ← get before a.1
    let oldB ← get before b.1
    return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB))

def project (task : Nat) (before after : Store effectLayout) : List (String × Int) :=
  scalarSlots (values task before) (values task after)

/-! ### Demanded projection

A law reads a declared cell by name (`Pred.reads`, `Pred.eval_restrict`). `scalarSlots` names
three views of every field and one delta for every PAIR of fields, so building it whole and
filtering costs the square of the cell's field count in formatted names. `scalarSlotsDemand`
builds the slots a demand names: each field view is tested by name before anything is looked
up, and the pair deltas led by field `a` are built only when `leads a` (some demanded name
contains `pairStem a`). For a fixed law it is linear in the cell's fields.
`scalarSlotsDemand_eq`: it is the full projection filtered, slot for slot and in order. -/

/-- The stem every pair slot led by field `a` begins with. -/
def pairStem (a : Nat) : String := s!"resource/pair/{a}/"

theorem pairName_stem (a b : Nat) :
    (pairName a b).toList = (pairStem a).toList ++ (toString b ++ "/delta").toList := by
  show ("resource/pair/" ++ toString a ++ "/" ++ toString b ++ "/delta").toList =
    ("resource/pair/" ++ toString a ++ "/").toList ++ (toString b ++ "/delta").toList
  simp only [String.toList_append, List.append_assoc]

def scalarSlotsDemand (want : String → Bool) (leads : Nat → Bool) (before after : Values) :
    List (String × Int) :=
  before.filterMap (fun p =>
    if want (fieldName p.1 "before") then some (fieldName p.1 "before", p.2) else none) ++
  after.filterMap (fun p =>
    if want (fieldName p.1 "after") then some (fieldName p.1 "after", p.2) else none) ++
  after.filterMap (fun p =>
    if want (fieldName p.1 "delta") then
      (get before p.1).map fun old => (fieldName p.1 "delta", p.2 - old)
    else none) ++
  after.flatMap (fun a =>
    if leads a.1 then
      match get before a.1 with
      | none => []
      | some oldA => after.filterMap fun b =>
          if want (pairName a.1 b.1) then
            (get before b.1).map fun oldB => (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)
          else none
    else [])

set_option linter.unusedSimpArgs false in
/-- **The demanded projection is the full projection on every demanded slot**: the same slots,
in the same order, as `scalarSlots` filtered by `want`, whenever `leads` covers every pair
`want` names. Teeth: `scalarSlotsDemand_needs_leads`. -/
theorem scalarSlotsDemand_eq (want : String → Bool) (leads : Nat → Bool)
    (sound : ∀ a b, want (pairName a b) = true → leads a = true) (before after : Values) :
    scalarSlotsDemand want leads before after =
      (scalarSlots before after).filter fun slot => want slot.1 := by
  have named : ∀ (l : Values) (name : Nat → String),
      (l.map fun p => (name p.1, p.2)).filter (fun slot => want slot.1) =
        l.filterMap fun p => if want (name p.1) then some (name p.1, p.2) else none := by
    intro l name
    induction l with
    | nil => rfl
    | cons p rest ih =>
        cases h : want (name p.1) <;> simp [List.filter_cons, List.filterMap_cons, h, ih]
  have delta : (after.filterMap fun p => (get before p.1).map fun old =>
        (fieldName p.1 "delta", p.2 - old)).filter (fun slot => want slot.1) =
      after.filterMap fun p => if want (fieldName p.1 "delta") then
        (get before p.1).map fun old => (fieldName p.1 "delta", p.2 - old) else none := by
    induction after with
    | nil => rfl
    | cons p rest ih =>
        cases g : get before p.1 <;> cases h : want (fieldName p.1 "delta") <;>
          simp [List.filter_cons, List.filterMap_cons, g, h, ih]
  have row : ∀ (a : Nat × Int) (l : Values),
      (l.filterMap fun b => do
          let oldA ← get before a.1
          let oldB ← get before b.1
          return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)).filter (fun slot => want slot.1) =
        match get before a.1 with
        | none => []
        | some oldA => l.filterMap fun b =>
            if want (pairName a.1 b.1) then
              (get before b.1).map fun oldB => (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)
            else none := by
    intro a l
    cases ga : get before a.1 with
    | none => simp
    | some oldA =>
        induction l with
        | nil => rfl
        | cons b rest ih =>
            simp only [Option.bind_some, Option.bind_eq_bind, bind, pure] at ih ⊢
            cases gb : get before b.1 <;> cases h : want (pairName a.1 b.1) <;>
              simp [List.filter_cons, List.filterMap_cons, gb, h, ih]
  have unled : ∀ (a : Nat × Int), leads a.1 = false →
      (after.filterMap fun b => do
          let oldA ← get before a.1
          let oldB ← get before b.1
          return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)).filter (fun slot => want slot.1) = [] := by
    intro a off
    refine List.filter_eq_nil_iff.mpr fun slot member wanted => ?_
    obtain ⟨b, _, made⟩ := List.mem_filterMap.mp member
    cases ga : get before a.1 with
    | none => simp [ga] at made
    | some oldA =>
      cases gb : get before b.1 with
      | none => simp [ga, gb] at made
      | some oldB =>
        simp only [ga, gb, Option.bind_some, Option.bind_eq_bind, bind, pure, Option.some.injEq] at made
        subst made
        rw [sound _ _ wanted] at off
        exact Bool.noConfusion off
  unfold scalarSlotsDemand scalarSlots
  rw [List.filter_append, List.filter_append, List.filter_append,
    named before (fun n => fieldName n "before"), named after (fun n => fieldName n "after"), delta,
    List.filter_flatMap]
  congr 1
  have rows : ∀ l : Values,
      (l.flatMap fun a => if leads a.1 then
          match get before a.1 with
          | none => []
          | some oldA => after.filterMap fun b =>
              if want (pairName a.1 b.1) then
                (get before b.1).map fun oldB => (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)
              else none
        else []) =
      l.flatMap (List.filter (fun slot => want slot.1) ∘ fun a => after.filterMap fun b => do
        let oldA ← get before a.1
        let oldB ← get before b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a rest ih =>
        rw [List.flatMap_cons, List.flatMap_cons, ih]
        congr 1
        cases led : leads a.1 with
        | true => simpa using (row a after).symm
        | false => simpa using (unled a led).symm
  exact rows after

/-- **Teeth**: a `leads` that does not cover a demanded pair drops that pair's slot, so the
premise of `scalarSlotsDemand_eq` is load-bearing. -/
theorem scalarSlotsDemand_needs_leads :
    scalarSlotsDemand (fun name => name == pairName 1 2) (fun _ => false) [(1, 5), (2, 7)]
        [(1, 6), (2, 6)] = [] ∧
      (scalarSlots [(1, 5), (2, 7)] [(1, 6), (2, 6)]).filter
        (fun slot => slot.1 == pairName 1 2) = [(pairName 1 2, 0)] := by
  decide

/-- `project` built for a demand (`scalarSlotsDemand`). -/
def projectDemand (want : String → Bool) (leads : Nat → Bool) (task : Nat)
    (before after : Store effectLayout) : List (String × Int) :=
  scalarSlotsDemand want leads (values task before) (values task after)

theorem projectDemand_eq (want : String → Bool) (leads : Nat → Bool)
    (sound : ∀ a b, want (pairName a b) = true → leads a = true) (task : Nat)
    (before after : Store effectLayout) :
    projectDemand want leads task before after =
      (project task before after).filter fun slot => want slot.1 :=
  scalarSlotsDemand_eq want leads sound _ _

/-- This arithmetic projection is exact over integers, before the existing
compiler checks its supported range and injective field cast. -/
theorem pair_delta_nonpositive_iff (oldA oldB newA newB : Int) :
    newA + newB - oldA - oldB ≤ 0 ↔ newA + newB ≤ oldA + oldB := by omega

theorem zero_delta_fences (before after generation : Int)
    (bound : after = generation) (same : after - before = 0) : before = generation := by omega
end Minidregg.Kernel.DeclaredResourceProjection
