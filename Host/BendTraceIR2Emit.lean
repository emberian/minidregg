import Compiler.BendTraceIR2

/- Offline algebra/serialization conformance vector for the actual IR2 backend.
The existing range gadget is extended by one private Boolean witness that is
independent of the public13. Both values satisfy the same relation. This makes
short-trace coefficient recovery a meaningful privacy falsifier. It is not a
Bend-program demo or proof-admission claim. -/
namespace Minidregg.Host.BendTraceIR2Emit
open Compiler Compiler.BendTraceIR2

def fixtureSystem : ConstraintSystem BabyBear (Fin 6) :=
  rangeGadget 0 (fun i : Fin 4 => ⟨i.val + 1, by omega⟩) ++ [boolGadget 5]

def fixtureDescriptor : ConstraintDescriptor BabyBear :=
  emit Fin.val 1 6 fixtureSystem

def input (secret : Bool) (i : Nat) : BabyBear :=
  match i with
  | 0 => 13
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => if secret then 1 else 0
  | _ => 0

/-- Witness construction reads the emitted gate operations themselves. -/
def wires (secret : Bool) : Nat → BabyBear :=
  fixtureDescriptor.gates.foldl (fun previous gate =>
    Function.update previous gate.out
      (gate.op.denote (gate.a.read previous) (gate.b.read previous))) (input secret)

theorem witness_holds (secret : Bool) : descriptorHolds fixtureDescriptor (wires secret) := by
  cases secret <;> decide

theorem public_pinned (secret : Bool) :
    ∀ i < fixtureDescriptor.nPublic, wires secret i = input false i := by
  intro i hi
  have : i = 0 := by change i < 1 at hi; omega
  subst i
  cases secret <;> decide

theorem hidden_bit_distinct : wires false 5 ≠ wires true 5 := by decide

theorem row_holds (secret : Bool) :
    (lower fixtureDescriptor).Holds (wires secret) (input false) :=
  (lower_correct fixtureDescriptor (wires secret) (input false)).mpr
    ⟨witness_holds secret, public_pinned secret⟩

#assert_axioms witness_holds
#assert_axioms public_pinned
#assert_axioms hidden_bit_distinct
#assert_axioms row_holds

/-- Cached fixture data, checked against the actual emitted gate fold below.
This avoids expensive dynamic evaluation of proof-oriented ZMod operations. -/
def wireValues (secret : Bool) : List Nat :=
  [13, 1, 0, 1, 1, if secret then 1 else 0, 0, 0, 2013265920,
   0, 0, 0, 0, 0, 1, 0, 4, 8, 8, 12, 12, 13, 2013265908, 0,
   if secret then 0 else 2013265920, 0]

theorem wireValues_correct (secret : Bool) :
    wireValues secret = (List.range fixtureDescriptor.nWires).map
      (fun i => (wires secret i).val) := by
  cases secret <;> decide

#assert_axioms wireValues_correct

def csvNat (values : List Nat) : String :=
  String.intercalate "," (values.map toString) ++ "\n"

def csv (values : List BabyBear) : String :=
  String.intercalate "," (values.map (fun value => toString value.val)) ++ "\n"

end Minidregg.Host.BendTraceIR2Emit

open Minidregg.Compiler Minidregg.Compiler.BendTraceIR2 Minidregg.Host.BendTraceIR2Emit

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: BendTraceIR2Emit output-directory")
  let output : System.FilePath := directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "descriptor.json") ((lower fixtureDescriptor).toWire ++ "\n")
  IO.FS.writeFile (output / "trace.csv")
    (csvNat (wireValues true))
  IO.FS.writeFile (output / "alternate-trace.csv")
    (csvNat (wireValues false))
  IO.FS.writeFile (output / "public.csv")
    "13\n"
  IO.FS.writeFile (output / "tampered-public.csv") "14\n"
  IO.println "Emitted IR2 algebra/privacy-falsifier vectors; no Bend source or admission claim"
