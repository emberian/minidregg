/-
# `Compiler.BfvAllModuliKernelCalls` — deployed BFV scalar-product call family

The compressed BFV frontend uses three ordered integer moduli.  This module instantiates
`BignumKernelABI.scalarMulKernelCall` for each one with the common radix-64 / 24-bit scalar
schema.  The two 36-bit moduli use ten product limbs; the 37-bit modulus uses eleven because
its maximum shifted-quotient product does not fit ten.

Every call is still the ordinary emitted `AirModularView.scalarMulGadget`.  Its acceptance
relation is definitionally `descriptorHolds`; the modulus tag and wire spans are only the
Lean-generated first-order witness-call surface.
-/
import Compiler.BignumKernelABI
import Compiler.BfvCompressedEquation

namespace Minidregg.Compiler.BfvAllModuliKernelCalls

open Minidregg.Compiler
open Minidregg.Compiler.BignumKernelABI
open Minidregg.Compiler.BfvCompressedEquation

set_option autoImplicit false

def limbBits : Nat := 6
def scalarBits : Nat := BfvCompressedEquation.quotientBits

/-- Runtime modulus-major order, matching the 384-row frontend. -/
def orderedModulus (i : Fin 3) : RnsModulus :=
  ![RnsModulus.q0, RnsModulus.q1, RnsModulus.q2] i

/-- The minimum deployed product widths for the full shifted scalar interval. -/
def productWidth : RnsModulus -> Nat
  | .q0 => 10
  | .q1 => 10
  | .q2 => 11

theorem orderedModulus_values :
    (orderedModulus 0).value = 68719403009 /\
    (orderedModulus 1).value = 68719230977 /\
    (orderedModulus 2).value = 137438822401 := by
  decide

/-- Every deployed modulus and every maximum 24-bit scalar product fit its selected
canonical radix-64 output word. -/
theorem all_modulus_products_fit (q : RnsModulus) :
    q.value < (2 ^ limbBits) ^ productWidth q /\
    q.value * (2 ^ scalarBits - 1) < (2 ^ limbBits) ^ productWidth q := by
  cases q <;> norm_num [RnsModulus.value, productWidth, limbBits, scalarBits,
    BfvCompressedEquation.quotientBits]

/-- The larger third modulus genuinely needs the eleventh limb for the full shifted
24-bit interval; choosing ten everywhere would be unsound as a capacity claim. -/
theorem q2_max_product_not_width10 :
    (2 ^ limbBits) ^ 10 <=
      RnsModulus.q2.value * (2 ^ scalarBits - 1) := by
  norm_num [RnsModulus.value, limbBits, scalarBits,
    BfvCompressedEquation.quotientBits]

/-- The common field-column no-wrap budgets are independent of which public modulus digits
occupy the call. -/
theorem common_column_budgets :
    (2 ^ limbBits + 1) * 2 ^ scalarBits <= babyBearP /\
    2 ^ limbBits * (2 ^ scalarBits + 1) <= babyBearP := by
  norm_num [limbBits, scalarBits, BfvCompressedEquation.quotientBits, babyBearP]

def kernelCallFor (q : RnsModulus) : KernelCall :=
  scalarMulKernelCall q.value (productWidth q) limbBits scalarBits

def kernelCallAt (i : Fin 3) : KernelCall := kernelCallFor (orderedModulus i)

/-- First-order ordered call list: q0, q1, q2. -/
def orderedCalls : List KernelCall := List.ofFn kernelCallAt

theorem orderedCalls_length : orderedCalls.length = 3 := by
  simp [orderedCalls]

theorem kernelCallAt_schema (i : Fin 3) :
    (kernelCallAt i).abiVersion = 1 /\
    (kernelCallAt i).entry = .constraintDescriptorV1 /\
    (kernelCallAt i).descriptor.nPublic = 0 /\
    (kernelCallAt i).descriptor.nVars =
      scalarMulWireCount (productWidth (orderedModulus i)) limbBits scalarBits /\
    (kernelCallAt i).segments =
      scalarMulSegments (productWidth (orderedModulus i)) limbBits scalarBits /\
    (kernelCallAt i).calls =
      [scalarMulWitnessCall (orderedModulus i).value
        (productWidth (orderedModulus i)) limbBits scalarBits] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem kernelCallAt_fullyWellFormed (i : Fin 3) :
    (kernelCallAt i).FullyWellFormed :=
  scalarMulKernelCall_fullyWellFormed (orderedModulus i).value
    (productWidth (orderedModulus i)) limbBits scalarBits

/-- Acceptance has no call-specific side relation: it remains exactly the nested emitted
descriptor's first-order gate and zero-check relation. -/
theorem kernelCallAt_accepts_iff_descriptor (i : Fin 3)
    (wireValues : Nat -> BabyBear) :
    (kernelCallAt i).Accepts wireValues <->
      descriptorHolds (kernelCallAt i).descriptor wireValues := Iff.rfl

/-- The stronger existential seam is inherited directly from the generic ABI constructor
and the existing `emit` theorem. -/
theorem kernelCallAt_accepts_iff (i : Fin 3)
    (assignment : Fin
      (scalarMulWireCount (productWidth (orderedModulus i)) limbBits scalarBits) ->
        BabyBear) :
    (exists wireValues : Nat -> BabyBear,
      (forall j, wireValues j.val = assignment j) /\
      (kernelCallAt i).Accepts wireValues) <->
      systemAccepts assignment
        (AirModularView.scalarMulGadget (orderedModulus i).value
          (scalarMulWires (productWidth (orderedModulus i)) limbBits scalarBits)) := by
  exact scalarMulKernelCall_accepts_iff (orderedModulus i).value
    (productWidth (orderedModulus i)) limbBits scalarBits assignment

/-! ## Concrete layout teeth -/

example : (kernelCallAt 0).descriptor.nVars = 370 := by decide
example : (kernelCallAt 1).descriptor.nVars = 370 := by decide
example : (kernelCallAt 2).descriptor.nVars = 402 := by decide

example : (kernelCallAt 0).calls =
    [scalarMulWitnessCall 68719403009 10 6 24] := by decide

example : (kernelCallAt 1).calls =
    [scalarMulWitnessCall 68719230977 10 6 24] := by decide

example : (kernelCallAt 2).calls =
    [scalarMulWitnessCall 137438822401 11 6 24] := by decide

/-- info: 'Minidregg.Compiler.BfvAllModuliKernelCalls.all_modulus_products_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_modulus_products_fit
/-- info: 'Minidregg.Compiler.BfvAllModuliKernelCalls.q2_max_product_not_width10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms q2_max_product_not_width10
/-- info: 'Minidregg.Compiler.BfvAllModuliKernelCalls.kernelCallAt_schema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernelCallAt_schema
/-- info: 'Minidregg.Compiler.BfvAllModuliKernelCalls.kernelCallAt_fullyWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernelCallAt_fullyWellFormed
/-- info: 'Minidregg.Compiler.BfvAllModuliKernelCalls.kernelCallAt_accepts_iff_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernelCallAt_accepts_iff_descriptor
/-- info: 'Minidregg.Compiler.BfvAllModuliKernelCalls.kernelCallAt_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernelCallAt_accepts_iff

end Minidregg.Compiler.BfvAllModuliKernelCalls
