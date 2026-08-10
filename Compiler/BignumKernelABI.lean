/-
# `Compiler.BignumKernelABI` — Lean-owned first-order calls for wide arithmetic

`Compiler.Emit` already supplies the executable first-order language: a
`ConstraintDescriptor` is a field modulus, flat add/mul gates, zero checks, and exact buffer
sizes.  Wide arithmetic therefore needs no second arithmetic implementation at the call
boundary.  It needs only a first-order description of how the original-variable prefix is
partitioned so a generic descriptor evaluator can populate its input buffer.

This module adds that missing layout surface.  `KernelCall.Accepts` is definitionally the
existing `descriptorHolds`; segment names and encodings are metadata and cannot change the
relation.  The two concrete calls below are generated from the existing
`AirBignum.addGadget` and `AirModularView.scalarMulGadget`, then passed through `emit`.
Their acceptance theorems are direct instances of `emit_accepts_iff_fin`.
-/
import Compiler.AirModularView

namespace Minidregg.Compiler.BignumKernelABI

open Lean (Json toJson)
open Minidregg.Compiler

set_option autoImplicit false

/-! ## First-order ABI surface -/

inductive Visibility
  | publicInput
  | witness
deriving DecidableEq, Repr

/-- Informational cell encoding.  It describes how a caller populates a segment; all
arithmetic meaning still comes solely from the emitted gates. -/
inductive CellEncoding
  | fieldElement
  | bits
  | radixLimbs (limbBits : Nat)
  | carryDigits (digitBits : Nat)
deriving DecidableEq, Repr

structure WireSegment where
  name : String
  offset : Nat
  length : Nat
  visibility : Visibility
  encoding : CellEncoding
deriving DecidableEq, Repr

structure WireSpan where
  start : Nat
  length : Nat
deriving DecidableEq, Repr

def WireSpan.inBounds (nVars : Nat) (span : WireSpan) : Prop :=
  span.start + span.length <= nVars

/-- A witness-construction request for the existing bignum-add wire shape. -/
structure AddCall where
  width : Nat
  limbBits : Nat
  x : WireSpan
  y : WireSpan
  z : WireSpan
  xBits : WireSpan
  yBits : WireSpan
  zBits : WireSpan
  carry : WireSpan
deriving DecidableEq, Repr

/-- A witness-construction request for the existing public-constant multiplication shape.
`modulus` is a source natural, not a field constant; its canonical radix digits are already
compiled into the nested descriptor. -/
structure ScalarMulConstCall where
  modulus : Nat
  width : Nat
  limbBits : Nat
  quotientBits : Nat
  scalar : WireSpan
  scalarBits : WireSpan
  product : WireSpan
  productBits : WireSpan
  carry : WireSpan
  carryBits : WireSpan
deriving DecidableEq, Repr

inductive WitnessCall
  | add (call : AddCall)
  | scalarMulConst (call : ScalarMulConstCall)
deriving DecidableEq, Repr

/-- There is one generic entry point: evaluate the supplied first-order descriptor.  Gadget
names are deliberately absent, so an implementation cannot dispatch to handwritten
bignum arithmetic. -/
inductive KernelEntry
  | constraintDescriptorV1
deriving DecidableEq, Repr

structure KernelCall where
  abiVersion : Nat
  entry : KernelEntry
  segments : List WireSegment
  calls : List WitnessCall
  descriptor : ConstraintDescriptor BabyBear
deriving DecidableEq

/-- The call relation is exactly the existing descriptor relation.  Layout metadata is not
an alternative semantics. -/
def KernelCall.Accepts (call : KernelCall) (wireValues : Nat -> BabyBear) : Prop :=
  descriptorHolds call.descriptor wireValues

theorem KernelCall.accepts_iff_descriptor (call : KernelCall)
    (wireValues : Nat -> BabyBear) :
    call.Accepts wireValues <-> descriptorHolds call.descriptor wireValues := Iff.rfl

/-- Visibility must agree with the descriptor's public/witness split. -/
def WireSegment.visibilityFits (nPublic : Nat) (segment : WireSegment) : Prop :=
  match segment.visibility with
  | .publicInput => segment.offset + segment.length <= nPublic
  | .witness => nPublic <= segment.offset

/-- Exact tiling of `[cursor,nVars)`.  This is stronger than pairwise disjointness: there
are neither overlaps nor unnamed gaps. -/
def segmentsCoverFrom (nPublic : Nat) : Nat -> List WireSegment -> Nat -> Prop
  | cursor, [], nVars => cursor = nVars
  | cursor, segment :: rest, nVars =>
      segment.offset = cursor /\
      segment.offset + segment.length <= nVars /\
      segment.visibilityFits nPublic /\
      segmentsCoverFrom nPublic (segment.offset + segment.length) rest nVars

structure KernelCall.WellFormed (call : KernelCall) : Prop where
  descriptor : call.descriptor.WellFormed
  layout : segmentsCoverFrom call.descriptor.nPublic 0 call.segments call.descriptor.nVars

def AddCall.WellShaped (nVars : Nat) (call : AddCall) : Prop :=
  call.x.length = call.width /\ call.y.length = call.width /\
  call.z.length = call.width /\ call.xBits.length = call.width * call.limbBits /\
  call.yBits.length = call.width * call.limbBits /\
  call.zBits.length = call.width * call.limbBits /\ call.carry.length = call.width + 1 /\
  ∀ span ∈ [call.x, call.y, call.z, call.xBits, call.yBits, call.zBits, call.carry],
    span.inBounds nVars

def ScalarMulConstCall.WellShaped (nVars : Nat) (call : ScalarMulConstCall) : Prop :=
  call.scalar.length = 1 /\ call.scalarBits.length = call.quotientBits /\
  call.product.length = call.width /\
  call.productBits.length = call.width * call.limbBits /\
  call.carry.length = call.width + 1 /\
  call.carryBits.length = (call.width + 1) * call.quotientBits /\
  ∀ span ∈ [call.scalar, call.scalarBits, call.product, call.productBits,
      call.carry, call.carryBits], span.inBounds nVars

def WitnessCall.WellShaped (nVars : Nat) : WitnessCall -> Prop
  | .add call => call.WellShaped nVars
  | .scalarMulConst call => call.WellShaped nVars

def KernelCall.CallsWellShaped (call : KernelCall) : Prop :=
  ∀ witnessCall ∈ call.calls, witnessCall.WellShaped call.descriptor.nVars

def KernelCall.FullyWellFormed (call : KernelCall) : Prop :=
  call.WellFormed /\ call.CallsWellShaped

/-! ## JSON projection, reusing `descriptorToJson` -/

def visibilityToJson : Visibility -> Json
  | .publicInput => Json.str "public"
  | .witness => Json.str "witness"

def cellEncodingToJson : CellEncoding -> Json
  | .fieldElement => Json.mkObj [("kind", Json.str "field")]
  | .bits => Json.mkObj [("kind", Json.str "bits")]
  | .radixLimbs limbBits =>
      Json.mkObj [("kind", Json.str "radix-limbs"), ("limbBits", toJson limbBits)]
  | .carryDigits digitBits =>
      Json.mkObj [("kind", Json.str "carry-digits"), ("digitBits", toJson digitBits)]

def wireSegmentToJson (segment : WireSegment) : Json :=
  Json.mkObj
    [("name", Json.str segment.name),
     ("offset", toJson segment.offset),
     ("length", toJson segment.length),
     ("visibility", visibilityToJson segment.visibility),
     ("encoding", cellEncodingToJson segment.encoding)]

def wireSpanToJson (span : WireSpan) : Json :=
  Json.mkObj [("start", toJson span.start), ("length", toJson span.length)]

def witnessCallToJson : WitnessCall -> Json
  | .add call =>
      Json.mkObj
        [("op", Json.str "add"), ("width", toJson call.width),
         ("limbBits", toJson call.limbBits), ("x", wireSpanToJson call.x),
         ("y", wireSpanToJson call.y), ("z", wireSpanToJson call.z),
         ("xBits", wireSpanToJson call.xBits), ("yBits", wireSpanToJson call.yBits),
         ("zBits", wireSpanToJson call.zBits), ("carry", wireSpanToJson call.carry)]
  | .scalarMulConst call =>
      Json.mkObj
        [("op", Json.str "scalar-mul-const"),
         ("modulusNat", Json.str (toString call.modulus)),
         ("width", toJson call.width), ("limbBits", toJson call.limbBits),
         ("quotientBits", toJson call.quotientBits),
         ("scalar", wireSpanToJson call.scalar),
         ("scalarBits", wireSpanToJson call.scalarBits),
         ("product", wireSpanToJson call.product),
         ("productBits", wireSpanToJson call.productBits),
         ("carry", wireSpanToJson call.carry),
         ("carryBits", wireSpanToJson call.carryBits)]

def kernelEntryToJson : KernelEntry -> Json
  | .constraintDescriptorV1 => Json.str "constraint-descriptor-v1"

/-- A complete first-order call.  The nested descriptor uses the existing strict canonical
field-constant serializer unchanged. -/
def kernelCallToJson (call : KernelCall) : Json :=
  Json.mkObj
    [("schema", Json.str "minidregg/constraint-kernel-call/v1"),
     ("abiVersion", toJson call.abiVersion),
     ("entry", kernelEntryToJson call.entry),
     ("segments", Json.arr (call.segments.map wireSegmentToJson).toArray),
     ("calls", Json.arr (call.calls.map witnessCallToJson).toArray),
     ("descriptor", descriptorToJson call.descriptor)]

def writeKernelCallJson (path : System.FilePath) (call : KernelCall) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path ((kernelCallToJson call).pretty ++ "\n")

/-! ## Canonical bignum-add variable layout -/

def addXBase : Nat := 0
def addYBase (width : Nat) : Nat := width
def addZBase (width : Nat) : Nat := 2 * width
def addXBitBase (width : Nat) : Nat := 3 * width
def addYBitBase (width limbBits : Nat) : Nat := addXBitBase width + width * limbBits
def addZBitBase (width limbBits : Nat) : Nat := addYBitBase width limbBits + width * limbBits
def addCarryBase (width limbBits : Nat) : Nat := addZBitBase width limbBits + width * limbBits
def addWireCount (width limbBits : Nat) : Nat := addCarryBase width limbBits + (width + 1)

def addWires (width limbBits : Nat) :
    AirBignum.AddWires (Fin (addWireCount width limbBits)) width limbBits where
  x := fun i => ⟨addXBase + i.val, by
    simp [addWireCount, addCarryBase, addZBitBase, addYBitBase, addXBitBase, addXBase]
    omega⟩
  y := fun i => ⟨addYBase width + i.val, by
    simp [addWireCount, addCarryBase, addZBitBase, addYBitBase, addXBitBase, addYBase]
    omega⟩
  z := fun i => ⟨addZBase width + i.val, by
    simp [addWireCount, addCarryBase, addZBitBase, addYBitBase, addXBitBase, addZBase]
    omega⟩
  xBit := fun i j =>
    let ij : Fin (width * limbBits) := finProdFinEquiv (i, j)
    ⟨addXBitBase width + ij.val, by
      have hij := ij.isLt
      unfold addWireCount addCarryBase addZBitBase addYBitBase addXBitBase
      omega⟩
  yBit := fun i j =>
    let ij : Fin (width * limbBits) := finProdFinEquiv (i, j)
    ⟨addYBitBase width limbBits + ij.val, by
      have hij := ij.isLt
      unfold addWireCount addCarryBase addZBitBase addYBitBase addXBitBase
      omega⟩
  zBit := fun i j =>
    let ij : Fin (width * limbBits) := finProdFinEquiv (i, j)
    ⟨addZBitBase width limbBits + ij.val, by
      have hij := ij.isLt
      unfold addWireCount addCarryBase addZBitBase addYBitBase addXBitBase
      omega⟩
  carry := fun i => ⟨addCarryBase width limbBits + i.val, by
    unfold addWireCount
    omega⟩

def addSegments (width limbBits : Nat) : List WireSegment :=
  [{ name := "x", offset := addXBase, length := width,
     visibility := .witness, encoding := .radixLimbs limbBits },
   { name := "y", offset := addYBase width, length := width,
     visibility := .witness, encoding := .radixLimbs limbBits },
   { name := "z", offset := addZBase width, length := width,
     visibility := .witness, encoding := .radixLimbs limbBits },
   { name := "x_bits", offset := addXBitBase width, length := width * limbBits,
     visibility := .witness, encoding := .bits },
   { name := "y_bits", offset := addYBitBase width limbBits, length := width * limbBits,
     visibility := .witness, encoding := .bits },
   { name := "z_bits", offset := addZBitBase width limbBits, length := width * limbBits,
     visibility := .witness, encoding := .bits },
   { name := "carry", offset := addCarryBase width limbBits, length := width + 1,
     visibility := .witness, encoding := .fieldElement }]

def addWitnessCall (width limbBits : Nat) : WitnessCall :=
  .add
    { width := width
      limbBits := limbBits
      x := ⟨addXBase, width⟩
      y := ⟨addYBase width, width⟩
      z := ⟨addZBase width, width⟩
      xBits := ⟨addXBitBase width, width * limbBits⟩
      yBits := ⟨addYBitBase width limbBits, width * limbBits⟩
      zBits := ⟨addZBitBase width limbBits, width * limbBits⟩
      carry := ⟨addCarryBase width limbBits, width + 1⟩ }

def addKernelCall (width limbBits : Nat) : KernelCall where
  abiVersion := 1
  entry := .constraintDescriptorV1
  segments := addSegments width limbBits
  calls := [addWitnessCall width limbBits]
  descriptor := emit Fin.val 0 (addWireCount width limbBits)
    (AirBignum.addGadget (addWires width limbBits))

theorem addKernelCall_wellFormed (width limbBits : Nat) :
    (addKernelCall width limbBits).WellFormed := by
  constructor
  · exact emit_wellFormed Fin.val 0 (addWireCount width limbBits)
      (by omega) (fun i => i.isLt) _
  · simp [addKernelCall, addSegments, segmentsCoverFrom, emit,
      WireSegment.visibilityFits, addWireCount, addCarryBase, addZBitBase,
      addYBitBase, addXBitBase, addZBase, addYBase, addXBase]
    all_goals omega

theorem addKernelCall_fullyWellFormed (width limbBits : Nat) :
    (addKernelCall width limbBits).FullyWellFormed := by
  refine ⟨addKernelCall_wellFormed width limbBits, ?_⟩
  simp [KernelCall.CallsWellShaped, addKernelCall, addWitnessCall,
    WitnessCall.WellShaped, AddCall.WellShaped, WireSpan.inBounds, emit,
    addWireCount, addCarryBase, addZBitBase, addYBitBase, addXBitBase,
    addZBase, addYBase, addXBase]
  all_goals omega

theorem addKernelCall_accepts_iff (width limbBits : Nat)
    (assignment : Fin (addWireCount width limbBits) -> BabyBear) :
    (exists wireValues : Nat -> BabyBear,
      (forall i, wireValues i.val = assignment i) /\
      (addKernelCall width limbBits).Accepts wireValues) <->
      systemAccepts assignment (AirBignum.addGadget (addWires width limbBits)) := by
  exact emit_accepts_iff_fin (addWireCount width limbBits) 0 assignment _

/-! ## Canonical fixed-modulus product variable layout -/

def scalarBase : Nat := 0
def scalarBitBase : Nat := 1
def productBase (quotientBits : Nat) : Nat := scalarBitBase + quotientBits
def productBitBase (width quotientBits : Nat) : Nat := productBase quotientBits + width
def mulCarryBase (width limbBits quotientBits : Nat) : Nat :=
  productBitBase width quotientBits + width * limbBits
def mulCarryBitBase (width limbBits quotientBits : Nat) : Nat :=
  mulCarryBase width limbBits quotientBits + (width + 1)
def scalarMulWireCount (width limbBits quotientBits : Nat) : Nat :=
  mulCarryBitBase width limbBits quotientBits + (width + 1) * quotientBits

def scalarMulWires (width limbBits quotientBits : Nat) :
    AirModularView.ScalarMulWires
      (Fin (scalarMulWireCount width limbBits quotientBits)) width limbBits quotientBits where
  scalar := ⟨scalarBase, by
    unfold scalarMulWireCount mulCarryBitBase mulCarryBase productBitBase productBase
      scalarBitBase scalarBase
    omega⟩
  scalarBit := fun j => ⟨scalarBitBase + j.val, by
    unfold scalarMulWireCount mulCarryBitBase mulCarryBase productBitBase productBase scalarBitBase
    omega⟩
  product := fun i => ⟨productBase quotientBits + i.val, by
    unfold scalarMulWireCount mulCarryBitBase mulCarryBase productBitBase productBase scalarBitBase
    omega⟩
  productBit := fun i j =>
    let ij : Fin (width * limbBits) := finProdFinEquiv (i, j)
    ⟨productBitBase width quotientBits + ij.val, by
      have hij := ij.isLt
      unfold scalarMulWireCount mulCarryBitBase mulCarryBase productBitBase productBase scalarBitBase
      omega⟩
  carry := fun i => ⟨mulCarryBase width limbBits quotientBits + i.val, by
    unfold scalarMulWireCount mulCarryBitBase
    omega⟩
  carryBit := fun i j =>
    let ij : Fin ((width + 1) * quotientBits) := finProdFinEquiv (i, j)
    ⟨mulCarryBitBase width limbBits quotientBits + ij.val, by
      have hij := ij.isLt
      unfold scalarMulWireCount
      omega⟩

def scalarMulSegments (width limbBits quotientBits : Nat) : List WireSegment :=
  [{ name := "scalar", offset := scalarBase, length := 1,
     visibility := .witness, encoding := .fieldElement },
   { name := "scalar_bits", offset := scalarBitBase, length := quotientBits,
     visibility := .witness, encoding := .bits },
   { name := "product", offset := productBase quotientBits, length := width,
     visibility := .witness, encoding := .radixLimbs limbBits },
   { name := "product_bits", offset := productBitBase width quotientBits,
     length := width * limbBits, visibility := .witness, encoding := .bits },
   { name := "carry", offset := mulCarryBase width limbBits quotientBits,
     length := width + 1, visibility := .witness, encoding := .carryDigits quotientBits },
   { name := "carry_bits", offset := mulCarryBitBase width limbBits quotientBits,
     length := (width + 1) * quotientBits,
     visibility := .witness, encoding := .bits }]

def scalarMulWitnessCall (modulus width limbBits quotientBits : Nat) : WitnessCall :=
  .scalarMulConst
    { modulus := modulus
      width := width
      limbBits := limbBits
      quotientBits := quotientBits
      scalar := ⟨scalarBase, 1⟩
      scalarBits := ⟨scalarBitBase, quotientBits⟩
      product := ⟨productBase quotientBits, width⟩
      productBits := ⟨productBitBase width quotientBits, width * limbBits⟩
      carry := ⟨mulCarryBase width limbBits quotientBits, width + 1⟩
      carryBits := ⟨mulCarryBitBase width limbBits quotientBits,
        (width + 1) * quotientBits⟩ }

def scalarMulKernelCall (modulus width limbBits quotientBits : Nat) : KernelCall where
  abiVersion := 1
  entry := .constraintDescriptorV1
  segments := scalarMulSegments width limbBits quotientBits
  calls := [scalarMulWitnessCall modulus width limbBits quotientBits]
  descriptor := emit Fin.val 0 (scalarMulWireCount width limbBits quotientBits)
    (AirModularView.scalarMulGadget modulus (scalarMulWires width limbBits quotientBits))

theorem scalarMulKernelCall_wellFormed (modulus width limbBits quotientBits : Nat) :
    (scalarMulKernelCall modulus width limbBits quotientBits).WellFormed := by
  constructor
  · exact emit_wellFormed Fin.val 0 (scalarMulWireCount width limbBits quotientBits)
      (by omega) (fun i => i.isLt) _
  · simp [scalarMulKernelCall, scalarMulSegments, segmentsCoverFrom, emit,
      WireSegment.visibilityFits, scalarMulWireCount, mulCarryBitBase, mulCarryBase,
      productBitBase, productBase, scalarBitBase, scalarBase]
    all_goals omega

theorem scalarMulKernelCall_fullyWellFormed
    (modulus width limbBits quotientBits : Nat) :
    (scalarMulKernelCall modulus width limbBits quotientBits).FullyWellFormed := by
  refine ⟨scalarMulKernelCall_wellFormed modulus width limbBits quotientBits, ?_⟩
  simp [KernelCall.CallsWellShaped, scalarMulKernelCall, scalarMulWitnessCall,
    WitnessCall.WellShaped, ScalarMulConstCall.WellShaped, WireSpan.inBounds, emit,
    scalarMulWireCount, mulCarryBitBase, mulCarryBase, productBitBase, productBase,
    scalarBitBase, scalarBase]
  all_goals omega

theorem scalarMulKernelCall_accepts_iff (modulus width limbBits quotientBits : Nat)
    (assignment : Fin (scalarMulWireCount width limbBits quotientBits) -> BabyBear) :
    (exists wireValues : Nat -> BabyBear,
      (forall i, wireValues i.val = assignment i) /\
      (scalarMulKernelCall modulus width limbBits quotientBits).Accepts wireValues) <->
      systemAccepts assignment
        (AirModularView.scalarMulGadget modulus
          (scalarMulWires width limbBits quotientBits)) := by
  exact emit_accepts_iff_fin (scalarMulWireCount width limbBits quotientBits) 0 assignment _

/-! ## Computed ABI teeth -/

example : addWireCount 2 2 = 21 := by decide

example : scalarMulWireCount 10 6 24 = 370 := by decide

example : (scalarMulKernelCall 68719403009 10 6 24).descriptor.nVars = 370 := by decide

example : (scalarMulKernelCall 68719403009 10 6 24).segments.map
    (fun segment => segment.offset) = [0, 1, 25, 35, 95, 106] := by decide

/-- info: 'Minidregg.Compiler.BignumKernelABI.KernelCall.accepts_iff_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KernelCall.accepts_iff_descriptor
/-- info: 'Minidregg.Compiler.BignumKernelABI.addKernelCall_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms addKernelCall_wellFormed
/-- info: 'Minidregg.Compiler.BignumKernelABI.addKernelCall_fullyWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms addKernelCall_fullyWellFormed
/-- info: 'Minidregg.Compiler.BignumKernelABI.addKernelCall_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms addKernelCall_accepts_iff
/-- info: 'Minidregg.Compiler.BignumKernelABI.scalarMulKernelCall_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalarMulKernelCall_wellFormed
/-- info: 'Minidregg.Compiler.BignumKernelABI.scalarMulKernelCall_fullyWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalarMulKernelCall_fullyWellFormed
/-- info: 'Minidregg.Compiler.BignumKernelABI.scalarMulKernelCall_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalarMulKernelCall_accepts_iff

end Minidregg.Compiler.BignumKernelABI
