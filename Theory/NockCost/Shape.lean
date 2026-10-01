import Theory.Noun

/-!
# Theory.NockCost.Shape — the subject shapes a step bound is read from

Split out of `Theory.NockCost` (NC-2) so the kernel can name a program's declared sample shape
(`Kernel.NockProgramCell.shapeOf`) without importing the abstract interpreter or its forge fixture.
-/

namespace Minidregg.Theory
namespace NockCost

open Noun

/-- A subject shape. `exact` is a known noun (a battery, a constant); `range lo hi` an atom in
`[lo, hi]` (DML's `int` index); `atom` any atom; `list n e` a null-terminated list of at most
`n` elements of shape `e`; `any` anything. -/
inductive Shape where
  | exact (n : Noun)
  | range (lo hi : Nat)
  | atom
  | cell (h t : Shape)
  | list (n : Nat) (e : Shape)
  | any
  /-- No noun: the product of a formula that cannot answer (`!!`, a walk into an atom). -/
  | bot
  deriving Repr, Inhabited

/-- An atom of at most `b` bits. -/
def Shape.bits (b : Nat) : Shape := .range 0 (2 ^ b - 1)

/-- Membership of a noun in a shape. -/
def fits : Noun → Shape → Bool
  | v, .exact n => decide (v = n)
  | _, .any => true
  | _, .bot => false
  | .atom k, .range lo hi => decide (lo ≤ k ∧ k ≤ hi)
  | .atom _, .atom => true
  | .atom k, .list _ _ => decide (k = 0)
  | .atom _, .cell _ _ => false
  | .cell _ _, .range _ _ => false
  | .cell _ _, .atom => false
  | .cell h t, .cell a b => fits h a && fits t b
  | .cell _ _, .list 0 _ => false
  | .cell h t, .list (n + 1) e => fits h e && fits t (.list n e)

def HasShape (v : Noun) (sh : Shape) : Prop := fits v sh = true

instance (v : Noun) (sh : Shape) : Decidable (HasShape v sh) :=
  inferInstanceAs (Decidable (fits v sh = true))

end NockCost
end Minidregg.Theory
