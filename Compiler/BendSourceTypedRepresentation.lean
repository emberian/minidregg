import Compiler.BendSourceRepresentation
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT

/-- Definition identity is compared structurally; a matching name is insufficient.
Checked whole Book supplies the actual kernel admission boundary separately. -/
structure BoolBookBinding (bk : Book) : Prop where
  arms : Book.get bk "Bool.arms" = some armsDef
  typeDef : Book.get bk "Bool" = some boolDef
  checked : Book.check bk = .ok ()

private theorem arms_closed : Minidregg.Theory.BendTT.Term.Closed armsDef.v := by
  intro σ; rfl
private theorem bool_closed : Minidregg.Theory.BendTT.Term.Closed boolDef.v := by
  intro σ; rfl

/-- Exact dependent constructor typing, retaining the emitted Bool.arms Ref. -/
theorem boolTerm_typed (bk : Book) (binding : BoolBookBinding bk) (b : Bool) :
    Typed bk [] (boolTerm b) (.Ref "Bool") := by
  apply Typed.conv (U := boolDef.v)
  · apply Typed.tup
    · cases b <;> exact Typed.lab (by simp)
    · apply Typed.conv (U := .Enu ["()"])
      · exact Typed.lab (by simp)
      · apply Or.inl
        refine ⟨.Enu ["()"], .refl, ?_⟩
        cases b with
        | false =>
          exact .step (.app (.delta binding.arms arms_closed) (.lab))
            (.step (.hit (.enu)) .refl)
        | true =>
          exact .step (.app (.delta binding.arms arms_closed) (.lab))
            (.step (.miss (by decide) (.mat (.enu) .efq))
              (.step (.hit (.enu)) .refl))
  · exact Or.inl ⟨boolDef.v, .refl, .step (.delta binding.typeDef bool_closed) .refl⟩

/-- Source-byte admission is a fail-closed domain check after structural decode.
It retains the Nat semantics and never coerces a malformed/wide value to zero. -/
def decodeByteNats (t : BTerm) : Option (List Nat) := do
  let ns ← decodeNatList t
  if ns.all (fun n => n < 256) then some ns else none

theorem decode_represented_bytes {t : BTerm} {ns : List Nat} (h : RepBytes t ns) :
    decodeByteNats t = some ns := by
  rcases h with ⟨rfl, bound⟩
  simp [decodeByteNats, decode_natListTerm, List.all_eq_true]
  exact bound

#assert_axioms boolTerm_typed
#assert_axioms decode_represented_bytes
end Minidregg.Compiler.BendSourceRepresentation
