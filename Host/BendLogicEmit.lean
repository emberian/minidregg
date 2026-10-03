/- Emit and independently check the first fixed Bend source specialization.
All runtime wire computation below is candidate generation. Acceptance reads
Compiler.Emit.descriptorHolds on the emitted object, not a success bit. -/
import Compiler.BendLogicTrace
import Compiler.EmitSerialize
import Mathlib.Algebra.Field.Rat

namespace Minidregg.Host.BendLogicEmit

open Minidregg.Compiler
open Minidregg.Compiler.BendLogicCase
open Minidregg.Compiler.BendLogicSpecialization
open Lean (Json toJson)

/-- Candidate gate evaluation; any mistake is rejected by descriptorHolds. -/
def candidate (d : ConstraintDescriptor BabyBear) (input output : Bool) : Nat → BabyBear :=
  let initial : Nat → BabyBear :=
    fun n => if n = 0 then bit output else if n = 1 then bit input else 0
  d.gates.foldl (fun wires gate =>
    let value := gate.op.denote (gate.a.read wires) (gate.b.read wires)
    fun n => if n = gate.out then value else wires n) initial

def check (p : Plan) (input output : Bool) : Bool :=
  let d := descriptor (F := BabyBear) 1 p
  decide (descriptorHolds d (candidate d input output))

/-- Rat preserves the signed source literals before modular field reduction.
The same generic Air/flatten compiler is instantiated, never reimplemented.
A ring consumer must refuse non-integral constants; this case emits denominator1. -/
def signedWire : DWire Rat → Json
  | .cnst c => Json.mkObj [("z", toJson c.num), ("den", toJson c.den)]
  | .wire n => Json.mkObj [("w", toJson n)]

def signedGate (g : DGate Rat) : Json :=
  Json.mkObj [("op", gateOpToJson g.op), ("a", signedWire g.a),
    ("b", signedWire g.b), ("out", toJson g.out)]

/-- Both relations derive from this one fixed Plan. The constructive face has
one computed output, whereas the relational face includes the output wire and
bit-validity constraints. Physical consumers must preserve this distinction. -/
def artifact : Json :=
  let p := negation
  let d := descriptor (F := BabyBear) 1 p
  let f := flatten (outputExpr (F := BabyBear) p) 0
  let integral := flatten (outputExpr (F := Rat) p) 0
  Json.mkObj
    [("schema", toJson "dregg.bend.literal-enum-case.v1"),
     ("kernelPin", toJson "947db722640c86247849343657bf2f7ef01cb7f1"),
     ("source", toJson ((sourceTerm p).show 0)),
     ("compilerVersion", toJson (1 : Nat)),
     ("onFalse", toJson p.onFalse), ("onTrue", toJson p.onTrue),
     ("signedConstantPolicy", toJson "literal-bool-difference-v1"),
     ("inputWire", toJson (1 : Nat)),
     ("outputWire", toJson (0 : Nat)),
     ("relation", descriptorToJson d),
     ("constructiveIntegerOutput", Json.mkObj
       [("nVars", toJson (2 : Nat)),
        ("nWires", toJson (2 + integral.next)),
        ("gates", Json.arr ((integral.gates.map (emitGate Fin.val 2)).map signedGate).toArray),
        ("output", signedWire (emitWire Fin.val 2 integral.out))]),
     ("constructiveOutput", Json.mkObj
       [("nVars", toJson (2 : Nat)),
        ("nWires", toJson (2 + f.next)),
        ("gates", Json.arr ((f.gates.map (emitGate Fin.val 2)).map dgateToJson).toArray),
        ("output", dwireToJson (emitWire Fin.val 2 f.out))])]

def run : IO Unit := do
  let plans : List Plan := [⟨false,false⟩, ⟨false,true⟩, ⟨true,false⟩, ⟨true,true⟩]
  for p in plans do
    for input in [false, true] do
      unless check p input (p.output input) do
        throw <| IO.userError "honest source output refused by emitted descriptor"
      if check p input (!(p.output input)) then
        throw <| IO.userError "wrong output accepted by emitted descriptor"
  unless (compile (F := BabyBear) 1 (sourceTerm negation) negation).isSome do
    throw <| IO.userError "complete source rejected"
  if (compile (F := BabyBear) 3 (sourceTerm negation) negation).isSome then
    throw <| IO.userError "invalid public split accepted"
  if (compile (F := BabyBear) 1 (.Lab "false") negation).isSome then
    throw <| IO.userError "unrelated source accepted"
  let sourceText := (sourceTerm negation).show 0
  match (Minidregg.Theory.BendTT.Term.parse []).run sourceText.toList with
  | .error why => throw <| IO.userError ("source text parse refused: " ++ why)
  | .ok (parsed, remaining) =>
      unless remaining.all Char.isWhitespace do
        throw <| IO.userError "source parser left trailing non-whitespace"
      unless (compile (F := BabyBear) 1 parsed negation).isSome do
        throw <| IO.userError "parsed actual Bend source failed exact specialization"
  for input in [false, true] do
    let actual := (Minidregg.Theory.BendLiveMachine.executeChecked [] 8 2
      (inputTerm negation input)).outcome
    unless actual == .complete (label (!input))
        (Minidregg.Compiler.BendLogicTrace.sourceCount input) do
      throw <| IO.userError "source machine output/count differs from specialized block"
  IO.eprintln "BEND-LOGIC: all four plans, both inputs, wrong outputs and source/split refusals PASS"
  IO.println artifact.compress

end Minidregg.Host.BendLogicEmit

def main : IO Unit := Minidregg.Host.BendLogicEmit.run
