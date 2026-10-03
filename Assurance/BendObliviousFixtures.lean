/- Actual complete-controller DAG conformance at native machine boundaries.
These finite executions are compiler-trusting regression evidence, not the
all-program source refinement. Each comparison uses the same emitted network,
actual physical codec and actual Machine.step; no expected-result oracle enters
circuit construction. -/
import Compiler.BendObliviousController
import Compiler.BendObliviousCodec

namespace Minidregg.Assurance.BendObliviousFixtures
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler
set_option autoImplicit false

def shape : BendObliviousState.Shape := ⟨8,4,4,5,8⟩
def limits : Limits := ⟨⟨8,5,by decide⟩,4,4⟩
def library : Library :=
  ⟨⟨#[.lab 0,.lab 1,.lab 2,.rfl,.var 0,.lam .Q1 4,.ann 0 0,
      .lett .Q0 0 4,.lett .Q1 0 4,.app .Q1 5 0,.tup .Q0 0 1,
      .tup .Q1 0 1,.rwt 3 0 1,.prj 5,.mat 1 0 2,.ref 0,
      .app .Q1 5 4,.efq,.lam .Q2 4],#["entry","x","y"],#[]⟩,#[(0,5)]⟩

def base (control : Control) : State :=
  ⟨⟨#[.nil,.closure 0 0,.closure 5 0,.pair .Q1 1 1,
      .environment 1 0,.closure 14 0,.vacant,.vacant],6⟩,
    #[false,true,false,true,false,false,false,false],[],control,4⟩

def replaceFunction (code : Nat) (control : Control) : State :=
  let s := base control
  {s with heap := {s.heap with rows := s.heap.rows.set! 2 (.closure code 0)}}

def cases : List State :=
  (List.range 19).map (fun pc => base (.evaluate pc 4)) ++
  [base (.evaluate 31 0),base (.lookup 0 4 .evaluateValue),
   base (.lookup 1 4 .evaluateValue),base (.lookup 0 0 .evaluateValue),
   base (.lookup 0 4 (.walkArgument .Q1 5 0 2 [])),
   base (.apply .Q1 2 1),replaceFunction 18 (.apply .Q1 2 1),
   replaceFunction 13 (.apply .Q1 2 3),replaceFunction 13 (.apply .Q0 2 3),
   replaceFunction 14 (.apply .Q1 2 1),replaceFunction 14 (.apply .Q1 2 3),
   replaceFunction 0 (.apply .Q1 2 1),base (.apply .Q1 0 1),
   replaceFunction 15 (.unspine 2 2 [(.Q1,1)]),
   base (.unspine 2 2 []),base (.walk 5 0 2 [(.Q1,1)]),
   base (.walk 13 0 2 [(.Q1,3)]),base (.walk 14 0 2 [(.Q1,1)]),
   base (.walk 16 4 2 []),base (.walk 17 0 2 []),
   base (.walk 17 0 2 [(.Q1,1)]),base (.walk 0 0 2 [(.Q1,1)]),
   base (.classify 16 4 2 5 []),base (.classify 16 4 2 16 []),
   base (.complete 1),base (.refused .quantity),
   base (.reverseArguments 0 0 [(.Q1,1)] [(.Q0,2)]),
   base (.installArguments 0 0 [(.Q1,1)])] ++
  ([Frame.function .Q1 0 0,.function .Q0 0 0,.argument .Q1 2,
    .knownArgument .Q1 1,.knownArgument .Q0 1,.lett .Q1 4 0,
    .first .Q1 1 0,.second .Q1 1,.rewrite 1 0].map fun frame =>
      {base (.returned 1) with stack := [frame]}) ++
  [base (.returned 1),
   {base (.evaluate 7 0) with heap := {(base (.evaluate 7 0)).heap with used := 8}},
   {base (.evaluate 7 0) with heap := {(base (.evaluate 7 0)).heap with used := 7}},
   {base (.evaluate 7 0) with heap := {(base (.evaluate 7 0)).heap with used := 7},sourceSteps := 255},
   {replaceFunction 13 (.apply .Q1 2 3) with stack := List.replicate 3 (.rewrite 0 0)},
   {base (.walk 0 0 2 [(.Q1,1)]) with stack := List.replicate 4 (.rewrite 0 0)},
   base (.walk 13 0 2 [(.Q1,3),(.Q1,1),(.Q1,1),(.Q1,1)]),
   {base (.apply .Q1 2 1) with stack := List.replicate 4 (.rewrite 0 0)}]

def runNetwork (network : ObliviousNetwork.Network) (state : State) : Option State := do
  let input ← BendObliviousCodec.encode shape state
  let output ← network.evaluate input
  if output[0]? == some true then
    BendObliviousCodec.decode shape (output.extract 1 output.size)
  else none

def allConform : Bool :=
  match BendObliviousController.network shape library with
  | none => false
  | some network => cases.all fun state =>
    runNetwork network state == some (step limits library state)

def sourceCounterRefused : Bool :=
  match BendObliviousController.network shape library with
  | none => false
  | some network =>
    runNetwork network {base (.evaluate 6 0) with sourceSteps := 255} == none

end Minidregg.Assurance.BendObliviousFixtures
