import Compiler.ObliviousCompositeSemantics
import Compiler.BendObliviousState

namespace Minidregg.Compiler.BendObliviousStateSemantics
open ObliviousNetwork ObliviousWords ObliviousWordSemantics ObliviousVectorSemantics
open ObliviousCompositeSemantics BendObliviousState
set_option autoImplicit false

def WordBound {width : Nat} (network : Network) (word : Word width) : Prop :=
  ∀ bit : Fin width, word[bit] < network.inputCount + network.gates.size

def RowsBound {slots width : Nat} (network : Network)
    (rows : Vector (Word width) slots) : Prop := ∀ row : Fin slots, WordBound network rows[row]

def WordRep {width : Nat} (base : Network) (input : Array Bool) (expected : Word width)
    (network : Network) (actual : Word width) : Prop :=
  WordHolds input (fun bit => read base input expected[bit]) network actual

def RowsRep {slots width : Nat} (base : Network) (input : Array Bool)
    (expected : Vector (Word width) slots) (network : Network)
    (actual : Vector (Word width) slots) : Prop :=
  ∀ row : Fin slots, WordRep base input expected[row] network actual[row]

theorem WordRep.extends {width : Nat} {base first last : Network} {input : Array Bool}
    {expected actual : Word width} (extension : Extension first last)
    (held : WordRep base input expected first actual) :
    WordRep base input expected last actual := WordHolds.extends extension held

theorem RowsRep.extends {slots width : Nat} {base first last : Network} {input : Array Bool}
    {expected actual : Vector (Word width) slots} (extension : Extension first last)
    (held : RowsRep base input expected first actual) :
    RowsRep base input expected last actual := fun row => WordRep.extends extension (held row)

theorem muxWord_at {width : Nat} (base current : Network) (input : Array Bool)
    (shape : input.size = base.inputCount) (extension : Extension base current)
    (selector : Nat) (yes no : Word width)
    (selectorBound : selector < base.inputCount + base.gates.size)
    (yesBound : WordBound base yes) (noBound : WordBound base no) :
    let result := (mux selector yes no).run current
    Extension current result.2 ∧
    WordRep base input (if read base input selector then yes else no) result.2 result.1 := by
  have facts := mux_produces current input (shape.trans extension.inputs.symm) selector yes no
    (extension.bound selectorBound) (fun bit => extension.bound (yesBound bit))
    (fun bit => extension.bound (noBound bit))
  refine ⟨facts.1, (shape.trans extension.inputs.symm).trans facts.1.inputs.symm, ?_⟩
  intro bit
  refine ⟨(facts.2 bit).1, ?_⟩
  have value := (facts.2 bit).2
  rw [extension.read input selector shape selectorBound,
    extension.read input yes[bit] shape (yesBound bit),
    extension.read input no[bit] shape (noBound bit)] at value
  cases selected : read base input selector <;> simpa [selected] using value

theorem muxRows_at {slots width : Nat} (base current : Network) (input : Array Bool)
    (shape : input.size = base.inputCount) (extension : Extension base current)
    (selector : Nat) (yes no : Vector (Word width) slots)
    (selectorBound : selector < base.inputCount + base.gates.size)
    (yesBound : RowsBound base yes) (noBound : RowsBound base no) :
    let result := (Vector.ofFnM (fun row : Fin slots => mux selector yes[row] no[row])).run current
    Extension current result.2 ∧
    RowsRep base input (if read base input selector then yes else no) result.2 result.1 := by
  have facts := muxRows_produces current input (shape.trans extension.inputs.symm) selector yes no
    (extension.bound selectorBound) (fun row bit => extension.bound (yesBound row bit))
    (fun row bit => extension.bound (noBound row bit))
  refine ⟨facts.1, ?_⟩
  intro row
  refine ⟨(facts.2 row).1, ?_⟩
  intro bit
  refine ⟨((facts.2 row).2 bit).1, ?_⟩
  have value := ((facts.2 row).2 bit).2
  dsimp only at value
  rw [extension.read input selector shape selectorBound,
    extension.read input yes[row][bit] shape (yesBound row bit),
    extension.read input no[row][bit] shape (noBound row bit)] at value
  cases selected : read base input selector <;> simpa [selected] using value

structure ControlBound {shape : BendObliviousState.Shape} (network : Network) (value : Control shape) : Prop where
  tag : WordBound network value.tag
  quantity : WordBound network value.quantity
  failure : WordBound network value.failure
  a : WordBound network value.a
  b : WordBound network value.b
  c : WordBound network value.c
  d : WordBound network value.d
  e : WordBound network value.e
  firstLength : WordBound network value.firstLength
  secondLength : WordBound network value.secondLength
  first : RowsBound network value.first
  second : RowsBound network value.second

structure ControlRep {shape : BendObliviousState.Shape} (base : Network) (input : Array Bool)
    (expected : Control shape) (network : Network) (actual : Control shape) : Prop where
  tag : WordRep base input expected.tag network actual.tag
  quantity : WordRep base input expected.quantity network actual.quantity
  failure : WordRep base input expected.failure network actual.failure
  a : WordRep base input expected.a network actual.a
  b : WordRep base input expected.b network actual.b
  c : WordRep base input expected.c network actual.c
  d : WordRep base input expected.d network actual.d
  e : WordRep base input expected.e network actual.e
  firstLength : WordRep base input expected.firstLength network actual.firstLength
  secondLength : WordRep base input expected.secondLength network actual.secondLength
  first : RowsRep base input expected.first network actual.first
  second : RowsRep base input expected.second network actual.second

theorem ControlRep.extends {shape : BendObliviousState.Shape} {base first last : Network} {input : Array Bool}
    {expected actual : Control shape} (extension : Extension first last)
    (held : ControlRep base input expected first actual) :
    ControlRep base input expected last actual :=
  ⟨WordRep.extends extension held.tag,
   WordRep.extends extension held.quantity,
   WordRep.extends extension held.failure,
   WordRep.extends extension held.a,
   WordRep.extends extension held.b,
   WordRep.extends extension held.c,
   WordRep.extends extension held.d,
   WordRep.extends extension held.e,
   WordRep.extends extension held.firstLength,
   WordRep.extends extension held.secondLength,
   RowsRep.extends extension held.first,
   RowsRep.extends extension held.second⟩

/-- Actual muxControl implementation: all selected fields retain the original
chosen state values, including fields emitted before later gate blocks. -/
theorem muxControl_at {shape : BendObliviousState.Shape} (base current : Network)
    (input : Array Bool) (inputShape : input.size = base.inputCount)
    (extension : Extension base current) (selector : Nat) (yes no : Control shape)
    (selectorBound : selector < base.inputCount + base.gates.size)
    (yesBound : ControlBound base yes) (noBound : ControlBound base no) :
    let result := (muxControl selector yes no).run current
    Extension current result.2 ∧
    ControlRep base input (if read base input selector then yes else no) result.2 result.1 := by
  let r0 := (mux selector yes.tag no.tag).run current
  have h0 := muxWord_at base current input inputShape extension selector yes.tag no.tag
    selectorBound yesBound.tag noBound.tag
  have e0 : Extension base r0.2 := extension.trans h0.1
  let r1 := (mux selector yes.quantity no.quantity).run r0.2
  have h1 := muxWord_at base r0.2 input inputShape e0 selector yes.quantity no.quantity
    selectorBound yesBound.quantity noBound.quantity
  have e1 : Extension base r1.2 := e0.trans h1.1
  let r2 := (mux selector yes.failure no.failure).run r1.2
  have h2 := muxWord_at base r1.2 input inputShape e1 selector yes.failure no.failure
    selectorBound yesBound.failure noBound.failure
  have e2 : Extension base r2.2 := e1.trans h2.1
  let r3 := (mux selector yes.a no.a).run r2.2
  have h3 := muxWord_at base r2.2 input inputShape e2 selector yes.a no.a
    selectorBound yesBound.a noBound.a
  have e3 : Extension base r3.2 := e2.trans h3.1
  let r4 := (mux selector yes.b no.b).run r3.2
  have h4 := muxWord_at base r3.2 input inputShape e3 selector yes.b no.b
    selectorBound yesBound.b noBound.b
  have e4 : Extension base r4.2 := e3.trans h4.1
  let r5 := (mux selector yes.c no.c).run r4.2
  have h5 := muxWord_at base r4.2 input inputShape e4 selector yes.c no.c
    selectorBound yesBound.c noBound.c
  have e5 : Extension base r5.2 := e4.trans h5.1
  let r6 := (mux selector yes.d no.d).run r5.2
  have h6 := muxWord_at base r5.2 input inputShape e5 selector yes.d no.d
    selectorBound yesBound.d noBound.d
  have e6 : Extension base r6.2 := e5.trans h6.1
  let r7 := (mux selector yes.e no.e).run r6.2
  have h7 := muxWord_at base r6.2 input inputShape e6 selector yes.e no.e
    selectorBound yesBound.e noBound.e
  have e7 : Extension base r7.2 := e6.trans h7.1
  let r8 := (mux selector yes.firstLength no.firstLength).run r7.2
  have h8 := muxWord_at base r7.2 input inputShape e7 selector yes.firstLength no.firstLength
    selectorBound yesBound.firstLength noBound.firstLength
  have e8 : Extension base r8.2 := e7.trans h8.1
  let r9 := (mux selector yes.secondLength no.secondLength).run r8.2
  have h9 := muxWord_at base r8.2 input inputShape e8 selector yes.secondLength no.secondLength
    selectorBound yesBound.secondLength noBound.secondLength
  have e9 : Extension base r9.2 := e8.trans h9.1
  let r10 := (Vector.ofFnM (fun row : Fin shape.argumentSlots => mux selector yes.first[row] no.first[row])).run r9.2
  have h10 := muxRows_at base r9.2 input inputShape e9 selector yes.first no.first
    selectorBound yesBound.first noBound.first
  have e10 : Extension base r10.2 := e9.trans h10.1
  let r11 := (Vector.ofFnM (fun row : Fin shape.argumentSlots => mux selector yes.second[row] no.second[row])).run r10.2
  have h11 := muxRows_at base r10.2 input inputShape e10 selector yes.second no.second
    selectorBound yesBound.second noBound.second
  have e11 : Extension base r11.2 := e10.trans h11.1
  change Extension current r11.2 ∧
    ControlRep base input (if read base input selector then yes else no) r11.2
      ⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1, r6.1, r7.1, r8.1, r9.1, r10.1, r11.1⟩
  refine ⟨h0.1.trans (h1.1.trans (h2.1.trans (h3.1.trans (h4.1.trans (h5.1.trans (h6.1.trans (h7.1.trans (h8.1.trans (h9.1.trans (h10.1.trans (h11.1))))))))))), ?_⟩
  constructor
  · have retained := WordRep.extends (h1.1.trans (h2.1.trans (h3.1.trans (h4.1.trans (h5.1.trans (h6.1.trans (h7.1.trans (h8.1.trans (h9.1.trans (h10.1.trans (h11.1))))))))))) h0.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h2.1.trans (h3.1.trans (h4.1.trans (h5.1.trans (h6.1.trans (h7.1.trans (h8.1.trans (h9.1.trans (h10.1.trans (h11.1)))))))))) h1.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h3.1.trans (h4.1.trans (h5.1.trans (h6.1.trans (h7.1.trans (h8.1.trans (h9.1.trans (h10.1.trans (h11.1))))))))) h2.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h4.1.trans (h5.1.trans (h6.1.trans (h7.1.trans (h8.1.trans (h9.1.trans (h10.1.trans (h11.1)))))))) h3.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h5.1.trans (h6.1.trans (h7.1.trans (h8.1.trans (h9.1.trans (h10.1.trans (h11.1))))))) h4.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h6.1.trans (h7.1.trans (h8.1.trans (h9.1.trans (h10.1.trans (h11.1)))))) h5.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h7.1.trans (h8.1.trans (h9.1.trans (h10.1.trans (h11.1))))) h6.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h8.1.trans (h9.1.trans (h10.1.trans (h11.1)))) h7.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h9.1.trans (h10.1.trans (h11.1))) h8.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h10.1.trans (h11.1)) h9.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := RowsRep.extends (h11.1) h10.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := RowsRep.extends (Extension.refl r11.2) h11.2
    cases selected : read base input selector <;> simpa [selected] using retained

#assert_axioms ControlRep.extends
#assert_axioms muxControl_at
structure StateBound {shape : BendObliviousState.Shape} (network : Network) (value : State shape) : Prop where
  heap : RowsBound network value.heap
  used : WordBound network value.used
  data : WordBound network value.data
  stack : RowsBound network value.stack
  stackLength : WordBound network value.stackLength
  control : ControlBound network value.control
  sourceSteps : WordBound network value.sourceSteps

structure StateRep {shape : BendObliviousState.Shape} (base : Network) (input : Array Bool)
    (expected : State shape) (network : Network) (actual : State shape) : Prop where
  heap : RowsRep base input expected.heap network actual.heap
  used : WordRep base input expected.used network actual.used
  data : WordRep base input expected.data network actual.data
  stack : RowsRep base input expected.stack network actual.stack
  stackLength : WordRep base input expected.stackLength network actual.stackLength
  control : ControlRep base input expected.control network actual.control
  sourceSteps : WordRep base input expected.sourceSteps network actual.sourceSteps

theorem StateRep.extends {shape : BendObliviousState.Shape} {base first last : Network} {input : Array Bool}
    {expected actual : State shape} (extension : Extension first last)
    (held : StateRep base input expected first actual) :
    StateRep base input expected last actual :=
  ⟨RowsRep.extends extension held.heap,
   WordRep.extends extension held.used,
   WordRep.extends extension held.data,
   RowsRep.extends extension held.stack,
   WordRep.extends extension held.stackLength,
   ControlRep.extends extension held.control,
   WordRep.extends extension held.sourceSteps⟩

/-- Actual muxState implementation: all selected fields retain the original
chosen state values, including fields emitted before later gate blocks. -/
theorem muxState_at {shape : BendObliviousState.Shape} (base current : Network)
    (input : Array Bool) (inputShape : input.size = base.inputCount)
    (extension : Extension base current) (selector : Nat) (yes no : State shape)
    (selectorBound : selector < base.inputCount + base.gates.size)
    (yesBound : StateBound base yes) (noBound : StateBound base no) :
    let result := (muxState selector yes no).run current
    Extension current result.2 ∧
    StateRep base input (if read base input selector then yes else no) result.2 result.1 := by
  let r0 := (Vector.ofFnM (fun row : Fin shape.heapSlots => mux selector yes.heap[row] no.heap[row])).run current
  have h0 := muxRows_at base current input inputShape extension selector yes.heap no.heap
    selectorBound yesBound.heap noBound.heap
  have e0 : Extension base r0.2 := extension.trans h0.1
  let r1 := (mux selector yes.used no.used).run r0.2
  have h1 := muxWord_at base r0.2 input inputShape e0 selector yes.used no.used
    selectorBound yesBound.used noBound.used
  have e1 : Extension base r1.2 := e0.trans h1.1
  let r2 := (mux selector yes.data no.data).run r1.2
  have h2 := muxWord_at base r1.2 input inputShape e1 selector yes.data no.data
    selectorBound yesBound.data noBound.data
  have e2 : Extension base r2.2 := e1.trans h2.1
  let r3 := (Vector.ofFnM (fun row : Fin shape.frameSlots => mux selector yes.stack[row] no.stack[row])).run r2.2
  have h3 := muxRows_at base r2.2 input inputShape e2 selector yes.stack no.stack
    selectorBound yesBound.stack noBound.stack
  have e3 : Extension base r3.2 := e2.trans h3.1
  let r4 := (mux selector yes.stackLength no.stackLength).run r3.2
  have h4 := muxWord_at base r3.2 input inputShape e3 selector yes.stackLength no.stackLength
    selectorBound yesBound.stackLength noBound.stackLength
  have e4 : Extension base r4.2 := e3.trans h4.1
  let r5 := (muxControl selector yes.control no.control).run r4.2
  have h5 := muxControl_at base r4.2 input inputShape e4 selector yes.control no.control
    selectorBound yesBound.control noBound.control
  have e5 : Extension base r5.2 := e4.trans h5.1
  let r6 := (mux selector yes.sourceSteps no.sourceSteps).run r5.2
  have h6 := muxWord_at base r5.2 input inputShape e5 selector yes.sourceSteps no.sourceSteps
    selectorBound yesBound.sourceSteps noBound.sourceSteps
  have e6 : Extension base r6.2 := e5.trans h6.1
  change Extension current r6.2 ∧
    StateRep base input (if read base input selector then yes else no) r6.2
      ⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1, r6.1⟩
  refine ⟨h0.1.trans (h1.1.trans (h2.1.trans (h3.1.trans (h4.1.trans (h5.1.trans (h6.1)))))), ?_⟩
  constructor
  · have retained := RowsRep.extends (h1.1.trans (h2.1.trans (h3.1.trans (h4.1.trans (h5.1.trans (h6.1)))))) h0.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h2.1.trans (h3.1.trans (h4.1.trans (h5.1.trans (h6.1))))) h1.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h3.1.trans (h4.1.trans (h5.1.trans (h6.1)))) h2.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := RowsRep.extends (h4.1.trans (h5.1.trans (h6.1))) h3.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (h5.1.trans (h6.1)) h4.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := ControlRep.extends (h6.1) h5.2
    cases selected : read base input selector <;> simpa [selected] using retained
  · have retained := WordRep.extends (Extension.refl r6.2) h6.2
    cases selected : read base input selector <;> simpa [selected] using retained

#assert_axioms StateRep.extends
#assert_axioms muxState_at

#assert_axioms WordRep.extends
#assert_axioms RowsRep.extends
#assert_axioms muxWord_at
#assert_axioms muxRows_at
end Minidregg.Compiler.BendObliviousStateSemantics
