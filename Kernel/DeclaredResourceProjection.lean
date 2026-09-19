/- Generic scalar projection for declared resource policy evaluation.
All values come from canonical resource pages. Pair deltas expose linear
conservation constraints to the existing Pred algebra without opaque checks,
application-specific evaluator branches or a host-provided admission bit. -/
import Compiler.DeclaredEffectPageMaterializer

namespace Minidregg.Kernel.DeclaredResourceProjection
open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Theory.EffectDeclaration
set_option autoImplicit false

/-- Full field identifier, not a reduced digest or truncated address. -/
def fieldName (n : Nat) (view : String) : String := s!"resource/field/{n}/{view}"
def pairName (a b : Nat) : String := s!"resource/pair/{a}/{b}/delta"

abbrev Values := List (Nat × Int)

def values (task : Nat) (page : Page) : Values :=
  page.entries.filterMap fun entry => match entry.key with
    | .objectField object field =>
        if object.value = task then some (field.value, entry.value) else none
    | _ => none

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

def project (task : Nat) (before after : Page) : List (String × Int) :=
  scalarSlots (values task before) (values task after)

/-- This arithmetic projection is exact over integers, before the existing
compiler checks its supported range and injective field cast. -/
theorem pair_delta_nonpositive_iff (oldA oldB newA newB : Int) :
    newA + newB - oldA - oldB ≤ 0 ↔ newA + newB ≤ oldA + oldB := by omega

theorem zero_delta_fences (before after generation : Int)
    (bound : after = generation) (same : after - before = 0) : before = generation := by omega
end Minidregg.Kernel.DeclaredResourceProjection
