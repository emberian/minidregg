/- Exact circuit-to-correlation allocation metadata.
This is a canonical plan and shape checker, NOT authority to release material,
a malicious-MPC qualification, or an implementation of durable batch anchoring.
The source receiver must authorize these exact bytes; the independent physical
anchor must consume the complete plan before any row is read or released. -/
import Compiler.ObliviousNetwork
import Compiler.PrivateSuccessorCustodyCodec

namespace Minidregg.Compiler.PrivateCircuitAllocation
open ObliviousNetwork
open Minidregg.Kernel.PrivateSuccessorCustody
open PrivateSuccessorCustodyCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableReceiverCodec
set_option autoImplicit false

structure Plan where
  generation : GenerationKey
  network : Network
  publicTicks : Nat
  /-- Exact source-approved canonical program, input/output, semantic profile
  and protected receiving-context binding. Encoding alone does not approve it. -/
  bindingBytes : List UInt8
  /-- Tick-major, then ascending AND-gate position. All rows are consumed,
  including padded ticks after secret completion or refusal. -/
  rows : List CorrelationId

def andPositions (network : Network) : List Nat :=
  (network.gates.toList.zipIdx).filterMap fun item =>
    match item.1 with
    | .and _ _ => some item.2
    | _ => none

def schedule (plan : Plan) : List (Nat × Nat) :=
  (List.range plan.publicTicks).flatMap fun tick =>
    (andPositions plan.network).map fun position => (tick, position)

def Plan.valid (plan : Plan) : Bool :=
  plan.network.valid && decide plan.rows.Nodup &&
    decide (plan.rows.length = plan.publicTicks * (andPositions plan.network).length)

/-- Purpose is fixed to triples. Coins, holder-output pads and audience pads
need their own separately authorized plans and never alias these row IDs. -/
def allocations (plan : Plan) : List Allocation :=
  plan.rows.map fun row => ⟨row, plan.generation, .triple, .reserved⟩

def assignments (plan : Plan) : List ((Nat × Nat) × CorrelationId) :=
  (schedule plan).zip plan.rows

theorem valid_rows_unique {plan : Plan} (valid : plan.valid = true) :
    plan.rows.Nodup := by
  have checked := valid
  simp only [Plan.valid, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1.2

theorem valid_rows_count {plan : Plan} (valid : plan.valid = true) :
    plan.rows.length = plan.publicTicks * (andPositions plan.network).length := by
  have checked := valid
  simp only [Plan.valid, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.2

theorem schedule_length (plan : Plan) :
    (schedule plan).length =
      plan.publicTicks * (andPositions plan.network).length := by
  have lengthFor : ∀ ticks : Nat,
      ((List.range ticks).flatMap fun tick =>
        (andPositions plan.network).map fun position => (tick, position)).length =
          ticks * (andPositions plan.network).length := by
    intro ticks
    induction ticks with
    | zero => simp
    | succ ticks ih =>
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.length_append, List.length_map]
      rw [ih, Nat.succ_mul]
  exact lengthFor plan.publicTicks

/-- A validated plan cannot silently drop gates or rows through List.zip. -/
theorem valid_assignments_complete {plan : Plan} (valid : plan.valid = true) :
    (assignments plan).length = plan.rows.length := by
  simp only [assignments, List.length_zip, schedule_length,
    ← valid_rows_count valid, Nat.min_self]

def opStream : StreamCodec Op :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))
    (fun op => match op with
      | .constant false => (0, 0, 0)
      | .constant true => (1, 0, 0)
      | .xor left right => (2, left, right)
      | .and left right => (3, left, right))
    (fun code => match code.1 with
      | 1 => .constant true
      | 2 => .xor code.2.1 code.2.2
      | 3 => .and code.2.1 code.2.2
      | _ => .constant false)
    (by intro op; cases op with
        | constant value => cases value <;> rfl
        | xor => rfl
        | and => rfl)

def networkStream : StreamCodec Network :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.list opStream)
        (StreamCodec.list StreamCodec.nat)))
    (fun network => (network.inputCount, network.gates.toList, network.outputs.toList))
    (fun tuple => ⟨tuple.1, tuple.2.1.toArray, tuple.2.2.toArray⟩)
    (by intro network; cases network; simp)

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product generationStream (StreamCodec.product networkStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product bytesStream (StreamCodec.list correlationStream)))))
    (fun plan => (plan.generation, plan.network, plan.publicTicks, plan.bindingBytes, plan.rows))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2⟩)
    (by intro plan; cases plan; rfl)

def frame : List UInt8 := "DREGG.PRIVATE.CIRCUIT.ALLOCATION".toUTF8.toList ++ [1]

def framedPlanStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product bytesStream planStream)
    (fun plan => (frame, plan)) Prod.snd (by intro plan; rfl)

def encode (plan : Plan) : List UInt8 := framedPlanStream.encode plan

/-- Re-encoding excludes alternate operation tags, noncanonical constants,
wrong framing, and unused trailing bytes. It does not certify approval. -/
def decode (bytes : List UInt8) : Option Plan := do
  let plan ← framedPlanStream.toLawful.decode bytes
  if encode plan = bytes then some plan else none

@[simp] theorem decode_encode (plan : Plan) : decode (encode plan) = some plan := by
  have roundtrip := framedPlanStream.decodePrefix_encode plan []
  simp only [List.append_nil] at roundtrip
  simp [decode, encode, StreamCodec.toLawful, roundtrip]

theorem encode_injective {left right : Plan} (same : encode left = encode right) :
    left = right := by
  have parsed := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using parsed

#assert_axioms valid_rows_unique
#assert_axioms valid_rows_count
#assert_axioms schedule_length
#assert_axioms valid_assignments_complete
#assert_axioms decode_encode
#assert_axioms encode_injective
end Minidregg.Compiler.PrivateCircuitAllocation
