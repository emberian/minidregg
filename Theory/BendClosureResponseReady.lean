/- Before publishing an external request, qualify actual resumption for every
response admitted by the finite-enum ABI. The operation is pure; qualification
must remain tied to the same retained pending checkpoint until response commit.
It grants no external dispatch authority and does not validate provider receipts.
-/
import Theory.BendClosureResponse
namespace Minidregg.Theory.BendClosureResponse
open BendClosureArena BendClosureMachine
set_option autoImplicit false

structure Ready (limits : Limits) (program : Program) (abi : ABI) (before : State) where
  whenFalse : Resumed program before abi false
  falseExact : resume limits program abi before false = .ok whenFalse
  whenTrue : Resumed program before abi true
  trueExact : resume limits program abi before true = .ok whenTrue

/-- Uses the real response allocator/code decoder for both outcomes, including
actual empty-environment, capacity and data-array checks. No resource-ready flag
or numeric pointer convention is substituted for a successful constructor. -/
def prepare (limits : Limits) (program : Program) (abi : ABI) (before : State) :
    Except Reject (Ready limits program abi before) :=
  match falseExact : resume limits program abi before false with
  | .error reason => .error reason
  | .ok whenFalse =>
    match trueExact : resume limits program abi before true with
    | .error reason => .error reason
    | .ok whenTrue => .ok ⟨whenFalse,falseExact,whenTrue,trueExact⟩

def Ready.response {limits : Limits} {program : Program} {abi : ABI} {before : State}
    (ready : Ready limits program abi before) : (bit : Bool) → Resumed program before abi bit
  | false => ready.whenFalse
  | true => ready.whenTrue

/-- General over every response in the declared finite ABI, not one fixture. -/
theorem Ready.response_exact {limits : Limits} {program : Program} {abi : ABI} {before : State}
    (ready : Ready limits program abi before) (bit : Bool) :
    resume limits program abi before bit = .ok (ready.response bit) := by
  cases bit
  · exact ready.falseExact
  · exact ready.trueExact

#assert_axioms prepare
#assert_axioms Ready.response_exact
end Minidregg.Theory.BendClosureResponse
