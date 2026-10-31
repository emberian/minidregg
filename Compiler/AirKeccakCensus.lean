/-
# `Compiler/AirKeccakCensus.lean` — the published costs of `AirKeccak` and `AirCshake`

Checked on every build, so they cannot drift from the emitted systems.

* One round, emitted and shared by `EmitShare.cse`: 12 480 gates, of them 1 600 AND and 10 880
  XOR (an XOR with a constant counts as one), and 1 600 zero checks. Before sharing: 56 000
  gates. A permutation is 24 rounds: 38 400 AND, 261 120 XOR, 38 400 zero checks, and 38 400
  witness bits (rows 1 to 24).
* Under the private root's node customization, the customization prefix is one whole public
  block (`skip = 1`), absorbed into the public `midstate`; every node input up to 135 bytes
  (empty 1, branch 65, leaf 98) is then one permutation in the circuit.
-/
import Compiler.AirCshake
import Compiler.EmitShare
import Compiler.PrivateCellRoot

namespace Minidregg.Compiler.AirKeccakCensus

open Minidregg.Compiler
open Minidregg.Compiler.AirKeccak
open Minidregg.Compiler.AirCshake

set_option autoImplicit false

instance : Hashable F2 := inferInstanceAs (Hashable (Fin 2))

def inpW (t : Fin 25) (z : Fin 64) : Fin 3200 := ⟨t.val * 64 + z.val, by omega⟩
def outW (t : Fin 25) (z : Fin 64) : Fin 3200 := ⟨1600 + t.val * 64 + z.val, by omega⟩

/-- The emitted round 0, over 3200 variables (input row, output row). -/
def round0 : ConstraintDescriptor F2 := emit Fin.val 0 3200 (roundSystem inpW outW (constantOf 0))

/-- Gates, AND gates, XOR gates, zero checks. -/
def census (d : ConstraintDescriptor F2) : Nat × Nat × Nat × Nat :=
  (d.gates.length, (d.gates.filter (fun g => g.op == .mul)).length,
    (d.gates.filter (fun g => g.op == .add)).length, d.zeros.length)

#guard census round0 = (56000, 1600, 54400, 1600)
#guard census (cse round0) = (12480, 1600, 10880, 1600)

open Minidregg.Compiler.PrivateCellRoot (nodeCustomization)

#guard skip nodeCustomization = 1
#guard blocks nodeCustomization 1 - skip nodeCustomization = 1
#guard blocks nodeCustomization 65 - skip nodeCustomization = 1
#guard blocks nodeCustomization 98 - skip nodeCustomization = 1
#guard blocks nodeCustomization 135 - skip nodeCustomization = 1

end Minidregg.Compiler.AirKeccakCensus
