/- Native-selected scalar work envelope, separate from unrestricted raw Core4.
A conservative arithmetic bound suspends BEFORE the primitive, preserving its
exact state. This is a resource observation, never source divergence/refusal. -/
import Theory.ObjectiveBendDemandData
namespace Minidregg.Theory.ObjectiveBendDemandCapacity
open ObjectiveBendDemandMachine ObjectiveBendOpenRecursion
set_option autoImplicit false
structure Profile where
  scalarBits : Nat
  deriving Repr

def bits (n : Nat) : Nat := if n = 0 then 0 else n.log2+1

def valueFits (profile : Profile) : RuntimeValue → Bool
  | .natural n => bits n ≤ profile.scalarBits
  | _ => true

def primitiveFits (profile : Profile) (primitive : Primitive)
    (left right : RuntimeValue) : Bool :=
  valueFits profile left && valueFits profile right &&
    match primitive,left,right with
    | .add,.natural a,.natural b =>
      if a = 0 then true else if b = 0 then true else
        max (bits a) (bits b)+1 ≤ profile.scalarBits
    | .multiply,.natural a,.natural b =>
      if a = 0 || b = 0 || a = 1 || b = 1 then true else
        bits a + bits b ≤ profile.scalarBits
    | _,_,_ => true

/-- Inspect only the pre-transition control/operand values. No arithmetic
result is computed merely to decide whether its allocation would fit. -/
def allows (profile : Profile) (state : State) : Bool :=
  match state.control with
  | .evaluate (.nat n) _ => bits n ≤ profile.scalarBits
  | .enter address => match state.heap[address]? with
    | some (.cached _ value) => valueFits profile value
    | _ => true
  | .returned value =>
    valueFits profile value && match state.stack with
    | .binaryRight primitive left::_ => primitiveFits profile primitive left value
    | _ => true
  | .complete value => valueFits profile value
  | _ => true
inductive InputFailure where
  | noncanonical | capacity
  deriving Repr

/-- A cheap textual length guard precedes Nat parsing. The loose bits+1 digit
bound is conservative for parsing work; the exact bit cap is checked afterward.
The native input codec must use this receiver rather than parsing first. -/
def decodeNatural (profile : Profile) (text : String) : Except InputFailure Nat := do
  if text.utf8ByteSize > profile.scalarBits+1 then throw .capacity
  if text.isEmpty || !text.toList.all (fun c => '0' ≤ c && c ≤ '9') ||
      (text.startsWith "0" && text != "0") then throw .noncanonical
  let some n := text.toNat? | throw .noncanonical
  if bits n > profile.scalarBits then throw .capacity
  pure n
end Minidregg.Theory.ObjectiveBendDemandCapacity
