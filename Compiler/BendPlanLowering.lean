/- Canonical source result to complete native typed Plan. This connects the
actual source data decoder and native payload codecs; it does not turn a Plan
into authority. Receiving additionally binds invocation inputs, current native
admission and a funded versioned charge rule. -/
import Compiler.BendSourceByteCodec
import Compiler.BendWorldPlan
import Compiler.DurableReceiverCodec
import Compiler.BendCoreAdmission
import Theory.BendLiveMachine

namespace Minidregg.Compiler.BendPlanLowering
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.BendTT
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

def stream : StreamCodec BendWorldPlan.Plan :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list BendWorldPlan.effectStream)
      (StreamCodec.product (StreamCodec.list BendWorldPlan.returnStream)
        (StreamCodec.list DurableReceiverCodec.guardStream)))
    (fun p => (p.effects, p.returns, p.reads))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (by intro p; cases p; rfl)
def frame : List UInt8 := "DREGG/BEND/TYPED-PLAN/v1".toUTF8.toList
def encode (plan : BendWorldPlan.Plan) : List UInt8 := frame ++ stream.encode plan
def decode (bytes : List UInt8) : Option BendWorldPlan.Plan :=
  NockProgramCodec.framedDecode frame stream bytes
def sourceTerm (plan : BendWorldPlan.Plan) : BendTT.Term :=
  BendSourceRepresentation.bytesTerm (encode plan)
def lower (result : BendTT.Term) : Option BendWorldPlan.Plan := do
  let bytes ← BendSourceRepresentation.decodeBytes result
  decode bytes

theorem bytes_roundtrip (plan : BendWorldPlan.Plan) : decode (encode plan) = some plan :=
  NockProgramCodec.framedDecode_encode frame stream plan
theorem source_roundtrip (plan : BendWorldPlan.Plan) : lower (sourceTerm plan) = some plan := by
  simp only [lower, sourceTerm, BendSourceRepresentation.decode_bytesTerm,
    bind, Option.bind, bytes_roundtrip]
theorem canonical {bytes : List UInt8} {plan : BendWorldPlan.Plan}
    (h : decode bytes = some plan) : encode plan = bytes :=
  NockProgramCodec.framedDecode_canonical h

/-- This witness is produced from the actual source machine's completed trace
and the actual decoder. Refusal produces no effect certificate. Source counts
remain private diagnostics when the selected profile requires it. -/
structure Evaluated (core : BendCoreAdmission.Checked) (initial : BendTT.Term) where
  result : BendTT.Term
  count : Nat
  trace : BendLiveMachine.Trace core.book count initial result
  value : Value core.book result
  plan : BendWorldPlan.Plan
  decoded : lower result = some plan

def execute (core : BendCoreAdmission.Checked) (classificationTicks steps : Nat)
    (initial : BendTT.Term) : Option (Evaluated core initial) :=
  match BendLiveMachine.executeChecked core.book classificationTicks steps initial with
  | .refused _ _ _ _ => none
  | .complete result count trace value =>
      match decoded : lower result with
      | none => none
      | some plan => some ⟨result, count, trace, value, plan, decoded⟩

structure BoundEffects (core : BendCoreAdmission.Checked) (initial : BendTT.Term)
    (command : Command) where
  evaluated : Evaluated core initial
  exactEffects : BendWorldPlan.matchesCommand evaluated.plan command = true

theorem exact_ordered_native_payloads {core : BendCoreAdmission.Checked} {initial : BendTT.Term}
    {command : Command} (bound : BoundEffects core initial command) :
    bound.evaluated.plan.effects = BendWorldPlan.effectsOf command :=
  BendWorldPlan.ordered_payloads_exact bound.exactEffects

end Minidregg.Compiler.BendPlanLowering
