/- Fixed public-schema input generation for the actual Bend controller.
Both choice arms are allocated before a secret root pointer is selected.
Thus input bits cannot select program literals, host allocation schedules, or
heap shapes. This is a Boolean circuit producer, not malicious sharing/bitness.
General loader-to-Denotes/cache/retained-readiness refinement remains separate.
-/
import Compiler.BendObliviousExecution
import Compiler.BendObliviousCodec
import Compiler.BendClosureInput

namespace Minidregg.Compiler.BendObliviousInput
open Minidregg.Theory BendTT
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousProgram BendObliviousMutation
open BendClosureInput
set_option autoImplicit false

inductive Schema where
  | literal (tree : DataTree)
  | pair (quantity : Quan) (first second : Schema)
  | choice (bit : Nat) (yes no : Schema)
  deriving Repr

def isLiteral : DataTree → Bool
  | .label _ | .refl => true
  | .pair .. => false

/-- Every literal retains actual source-code reification; every input selector
is statically in the admitted input-wire domain. -/
inductive ReadySchema (program : BendClosureArena.Program) (inputs : Nat) where
  | literal (pc : Nat) (tree : DataTree) (primitive : isLiteral tree = true)
      (exact : BendClosureArena.CodeDenotes program pc tree.source)
  | pair (quantity : Quan) (first second : ReadySchema program inputs)
  | choice (bit : Fin inputs) (yes no : ReadySchema program inputs)

def validate (program : BendClosureArena.Program) (inputs : Nat) :
    Schema → Option (ReadySchema program inputs)
  | .literal tree => do
    if primitive : isLiteral tree = true then
      let pc ← BendClosureInput.literal program tree
      let witness ← BendClosureCompile.validateCode program (program.code.size+1) pc tree.source
      pure (.literal pc tree primitive witness.exact)
    else none
  | .pair q first second => do
    pure (.pair q (← validate program inputs first) (← validate program inputs second))
  | .choice bit yes no => do
    if valid : bit < inputs then
      pure (.choice ⟨bit,valid⟩ (← validate program inputs yes) (← validate program inputs no))
    else none

def ReadySchema.tree {program : BendClosureArena.Program} {inputs : Nat}
    (input : Vector Bool inputs) : ReadySchema program inputs → DataTree
  | .literal _ tree _ _ => tree
  | .pair q first second => .pair q (first.tree input) (second.tree input)
  | .choice bit yes no => if input[bit] then yes.tree input else no.tree input

/-- Counts BOTH arms, so public capacity does not disclose the chosen arm. -/
def ReadySchema.rows {program : BendClosureArena.Program} {inputs : Nat} :
    ReadySchema program inputs → Nat
  | .literal .. => 1
  | .pair _ first second => first.rows + second.rows + 1
  | .choice _ yes no => yes.rows + no.rows

theorem schema_source_data {program : BendClosureArena.Program} {inputs : Nat}
    (schema : ReadySchema program inputs) (input : Vector Bool inputs) :
    Data (schema.tree input).source := (schema.tree input).source_data

theorem dataTree_substitution (tree : DataTree) (substitution : Subst) :
    Term.sub substitution tree.source = tree.source := by
  induction tree with
  | label => rfl
  | refl => rfl
  | pair q first second ihFirst ihSecond =>
    simp [DataTree.source, Term.sub, ihFirst, ihSecond]

def mapControl {shape : Shape} (f : Nat → Nat) (control : Control shape) : Control shape :=
  ⟨control.tag.map f,control.quantity.map f,control.failure.map f,
    control.a.map f,control.b.map f,control.c.map f,control.d.map f,control.e.map f,
    control.firstLength.map f,control.secondLength.map f,
    control.first.map (fun word => word.map f),control.second.map (fun word => word.map f)⟩

def mapState {shape : Shape} (f : Nat → Nat) (state : State shape) : State shape :=
  ⟨state.heap.map (fun word => word.map f),state.used.map f,state.data.map f,
    state.stack.map (fun word => word.map f),state.stackLength.map f,
    mapControl f state.control,state.sourceSteps.map f⟩

def lower {shape : Shape} {library : BendClosureMachine.Library} {inputs : Nat}
    (zero one : Nat) (rom : ROM shape library) (emptyEnvironment : Word shape.wordBits) :
    ReadySchema library.program inputs → Trial shape →
      Builder (Word shape.wordBits × Trial shape)
  | .literal pc _ _ _, trial => do
    let code ← constant shape.wordBits pc
    closure zero one rom trial code emptyEnvironment
  | .pair q first second, trial => do
    let (first,trial) ← lower zero one rom emptyEnvironment first trial
    let (second,trial) ← lower zero one rom emptyEnvironment second trial
    let tag ← constant 3 4
    let quantity ← constant 2 (BendObliviousProgram.quantityCode q)
    allocate zero one rom trial ⟨tag,quantity,first,second⟩
  | .choice bit yes no, trial => do
    let (yes,trial) ← lower zero one rom emptyEnvironment yes trial
    let (no,trial) ← lower zero one rom emptyEnvironment no trial
    /- Network input wire indices are exactly the Fin input positions. -/
    let pointer ← mux bit.val yes no
    pure (pointer,trial)

/-- Caller supplies only PUBLIC start bits produced from Machine.start. The
validated wrapper below checks this seam; this internal builder is not ingress. -/
def build (shape : Shape) (library : BendClosureMachine.Library) (entry inputs : Nat)
    (binder : Quan) (initialBits : Array Bool) (schema : ReadySchema library.program inputs) :
    Network := Id.run do
  let work : Builder Unit := do
    let zero ← ObliviousNetwork.emit (.constant false)
    let one ← ObliviousNetwork.emit (.constant true)
    let constants ← initialBits.mapM fun bit => ObliviousNetwork.emit (.constant bit)
    let (indices,_) := (stateInputs shape).run 0
    let initial := mapState (fun index => constants[index]?.getD zero) indices
    let rom ← BendObliviousProgram.build shape library
    let emptyEnvironment := Vector.replicate shape.wordBits zero
    let (pointer,trial) ← lower zero one rom emptyEnvironment schema (begin zero one initial)
    let quantity ← constant 2 (BendObliviousProgram.quantityCode binder)
    let (environment,trial) ← bind zero one rom trial quantity pointer emptyEnvironment
    let entry ← constant shape.wordBits entry
    let trial ← go 0 entry environment trial
    let result ← finish initial trial
    modify fun graph => {graph with outputs := #[trial.valid] ++ result.outputs}
  pure (work.run {inputCount := inputs}).2

structure Prepared {book : Book} {template : BendTT.Term}
    (compiled : BendClosureCompile.Compiled book template) (shape : Shape) (inputs : Nat) where
  limits : BendClosureMachine.Limits
  schema : ReadySchema compiled.library.program inputs
  binder : Quan
  initial : BendClosureMachine.State
  started : BendClosureMachine.start limits compiled.library compiled.entry = .ok initial
  initialBits : Array Bool
  encoded : BendObliviousCodec.encode shape initial = some initialBits
  network : Network
  generated : network = build shape compiled.library compiled.entry inputs binder initialBits schema
  valid : network.valid = true

/-- Public source/shape admission. All chosen values remain input wires. This
retains source-code witnesses but does not assert a malicious share protocol. -/
def prepare {book : Book} {template : BendTT.Term}
    (compiled : BendClosureCompile.Compiled book template) (shape : Shape)
    (inputs : Nat) (binder : Quan) (schema : Schema) : Option (Prepared compiled shape inputs) := do
  if fits : shape.heapSlots ≤ 2^shape.wordBits then
    let limits : BendClosureMachine.Limits :=
      ⟨⟨shape.heapSlots,shape.wordBits,fits⟩,shape.frameSlots,shape.argumentSlots⟩
    let schema ← validate compiled.library.program inputs schema
    /- One initial nil row, every schema row, one captured environment row. -/
    if schema.rows + 2 > shape.heapSlots then none else do
      match started : BendClosureMachine.start limits compiled.library compiled.entry with
      | .error _ => none
      | .ok initial =>
        match encoded : BendObliviousCodec.encode shape initial with
        | none => none
        | some initialBits =>
          if initialBits.size != stateWidth shape then none else
            let network := build shape compiled.library compiled.entry inputs binder initialBits schema
            if valid : network.valid = true then
              some ⟨limits,schema,binder,initial,started,initialBits,encoded,network,rfl,valid⟩
            else none
  else none

#assert_axioms schema_source_data
#assert_axioms dataTree_substitution
end Minidregg.Compiler.BendObliviousInput
