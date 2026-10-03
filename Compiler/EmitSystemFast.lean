import Compiler.Emit
import Theory.AssertAxioms

/- Stack-safe system traversal. Each term still uses the original derived
flatten fold; this changes only the list traversal and proves exact equality
of gate order, root order and fresh-wire counter before compiler substitution. -/
namespace Minidregg.Compiler
universe u
variable {F Idx : Type u}

def flattenSystemLoop (system : ConstraintSystem F Idx) (next : Nat)
    (gatesRev : List (Gate F Idx)) (rootsRev : List (WireRef F Idx)) : FlatSystem F Idx :=
  match system with
  | [] => ⟨gatesRev.reverse, rootsRev.reverse, next⟩
  | term :: rest =>
    let result := flatten term next
    flattenSystemLoop rest result.next (result.gates.reverse ++ gatesRev) (result.out :: rootsRev)

def flattenSystemFast (system : ConstraintSystem F Idx) (next : Nat) : FlatSystem F Idx :=
  flattenSystemLoop system next [] []

theorem flattenSystemLoop_eq (system : ConstraintSystem F Idx) (next : Nat)
    (gatesRev : List (Gate F Idx)) (rootsRev : List (WireRef F Idx)) :
    flattenSystemLoop system next gatesRev rootsRev =
      ⟨gatesRev.reverse ++ (flattenSystem system next).gates,
       rootsRev.reverse ++ (flattenSystem system next).roots,
       (flattenSystem system next).next⟩ := by
  induction system generalizing next gatesRev rootsRev with
  | nil => simp [flattenSystemLoop, flattenSystem]
  | cons term rest ih =>
    simp [flattenSystemLoop, flattenSystem, ih, List.reverse_append, List.append_assoc]

@[csimp] theorem flattenSystem_eq_fast : @flattenSystem = @flattenSystemFast := by
  funext F Idx system next
  symm
  simpa [flattenSystemFast] using flattenSystemLoop_eq system next [] []

/-- Explicit entry point also benefits callers whose older object files were
compiled before the csimp theorem became available. -/
def emitFast (ix : Idx → Nat) (nPublic nVars : Nat) (system : ConstraintSystem F Idx) :
    ConstraintDescriptor F :=
  let flat := flattenSystemFast system 0
  { nPublic := nPublic
    nVars := nVars
    nWires := nVars + flat.next
    gates := flat.gates.map (emitGate ix nVars)
    zeros := flat.roots.map (emitWire ix nVars) }

theorem emitFast_eq_emit (ix : Idx → Nat) (nPublic nVars : Nat) (system : ConstraintSystem F Idx) :
    emitFast ix nPublic nVars system = emit ix nPublic nVars system := by
  simp [emitFast, emit, flattenSystem_eq_fast]

#assert_axioms emitFast_eq_emit
#assert_axioms flattenSystemLoop_eq
#assert_axioms flattenSystem_eq_fast
end Minidregg.Compiler
