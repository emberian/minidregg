import Compiler.ObliviousVectorSemantics

namespace Minidregg.Compiler.ObliviousCompositeSemantics
open ObliviousNetwork ObliviousWords ObliviousWordSemantics ObliviousVectorSemantics
set_option autoImplicit false

/-- Generic composition of actual vector builders, including nested words used
for the physical heap, frame stack, and both argument buffers. Stability is a
proof about emitted-wire extension, never an assumed execution result. -/
theorem ofFnM_establishes {α : Type} {width : Nat} (base : Network)
    (builders : Fin width → Builder α) (post : Fin width → Network → α → Prop)
    (stable : ∀ bit first last, Extension base first → Extension first last →
      ∀ value, post bit first value → post bit last value)
    (each : ∀ bit current, Extension base current →
      let result := (builders bit).run current
      Extension current result.2 ∧ post bit result.2 result.1)
    (current : Network) (extended : Extension base current) :
    let result := (Vector.ofFnM builders).run current
    Extension current result.2 ∧ ∀ bit : Fin width, post bit result.2 result.1[bit] := by
  induction width with
  | zero =>
      simp only [Vector.ofFnM_zero]
      exact ⟨Extension.refl current, fun bit => Fin.elim0 bit⟩
  | succ width ih =>
      let initialPart := (Vector.ofFnM (fun bit : Fin width => builders bit.castSucc)).run current
      have initialFacts := ih (fun bit => builders bit.castSucc)
        (fun bit => post bit.castSucc) (fun bit => stable bit.castSucc)
        (fun bit => each bit.castSucc)
      have allInitial : Extension base initialPart.2 := extended.trans initialFacts.1
      let final := (builders (Fin.last width)).run initialPart.2
      have finalFacts := each (Fin.last width) initialPart.2 allInitial
      rw [Vector.ofFnM_succ]
      change Extension current final.2 ∧
        ∀ bit : Fin (width + 1), post bit final.2 (initialPart.1.push final.1)[bit]
      refine ⟨initialFacts.1.trans finalFacts.1, ?_⟩
      intro bit
      refine Fin.lastCases ?_ (fun previous => ?_) bit
      · simpa using finalFacts.2
      · simpa using stable previous.castSucc initialPart.2 final.2 allInitial
          finalFacts.1 initialPart.1[previous] (initialFacts.2 previous)

/-- Exact word observation together with the bounds needed to retain its bits
when subsequent controller blocks append more gates. -/
def WordHolds {width : Nat} (input : Array Bool) (value : Fin width → Bool)
    (network : Network) (word : Word width) : Prop :=
  input.size = network.inputCount ∧ ∀ bit : Fin width,
    word[bit] < network.inputCount + network.gates.size ∧
    read network input word[bit] = value bit

theorem WordHolds.extends {width : Nat} {input : Array Bool} {value : Fin width → Bool}
    {first last : Network} {word : Word width}
    (extension : Extension first last) (held : WordHolds input value first word) :
    WordHolds input value last word := by
  refine ⟨held.1.trans extension.inputs.symm, ?_⟩
  intro bit
  exact ⟨extension.bound (held.2 bit).1,
    (extension.read input word[bit] held.1 (held.2 bit).1).trans (held.2 bit).2⟩

/-- This is the literal nested vector constructor in muxState/muxControl: heap,
stack and argument rows retain the chosen original values after ALL rows have
been emitted. It applies to arbitrary public row and word capacities. -/
theorem muxRows_produces {slots width : Nat} (network : Network) (input : Array Bool)
    (shape : input.size = network.inputCount) (selector : Nat)
    (yes no : Vector (Word width) slots)
    (selectorBound : selector < network.inputCount + network.gates.size)
    (yesBound : ∀ row : Fin slots, ∀ bit : Fin width,
      yes[row][bit] < network.inputCount + network.gates.size)
    (noBound : ∀ row : Fin slots, ∀ bit : Fin width,
      no[row][bit] < network.inputCount + network.gates.size) :
    let result := (Vector.ofFnM (fun row : Fin slots => mux selector yes[row] no[row])).run network
    Extension network result.2 ∧ ∀ row : Fin slots,
      WordHolds input (fun bit => if read network input selector then
        read network input yes[row][bit] else read network input no[row][bit]) result.2 result.1[row] := by
  apply ofFnM_establishes network _ _ _ _ network (Extension.refl network)
  · intro row first last _ extension value held
    exact WordHolds.extends extension held
  · intro row current extension
    have currentShape := shape.trans extension.inputs.symm
    have facts := mux_produces current input currentShape selector yes[row] no[row]
      (extension.bound selectorBound) (fun bit => extension.bound (yesBound row bit))
      (fun bit => extension.bound (noBound row bit))
    refine ⟨facts.1, currentShape.trans facts.1.inputs.symm, ?_⟩
    intro bit
    refine ⟨(facts.2 bit).1, ?_⟩
    have value := (facts.2 bit).2
    rw [extension.read input selector shape selectorBound,
      extension.read input yes[row][bit] shape (yesBound row bit),
      extension.read input no[row][bit] shape (noBound row bit)] at value
    exact value

#assert_axioms ofFnM_establishes
#assert_axioms WordHolds.extends
#assert_axioms muxRows_produces
end Minidregg.Compiler.ObliviousCompositeSemantics
