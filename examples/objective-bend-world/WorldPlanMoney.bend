# Generic authored application result for canonical Book transfers.
# Every identity is canonical native codec bytes supplied by the authenticated
# input binder. Amounts and scalar values are source Nat, never identity casts.
# Native admission checks funding, current laws/capabilities, and all targets.
import Base
import ./WorldPlanScalarBytes.bend as Scalar

type Transfer is Data:
  Transfer{source: List<&2, Nat>, destination: List<&2, Nat>,
    asset: List<&2, Nat>, amount: Nat}

type ReturnSlot is Data:
  ReturnSlot{name: List<&2, Nat>, valueSchema: List<&2, Nat>,
    encoding: List<&2, Nat>, recipient: List<&2, Nat>,
    keyEpoch: List<&2, Nat>, audience: List<&2, Nat>,
    generation: Nat, payload: List<&2, Nat>}

# One computed batch and its ordered ordinary object transitions.
# The native adapter places the unique carrier by actual target index, so a
# funded carrier may legally be last without changing the source computation.
# Independent returns are committed by the same admitted invocation.
type NativePlan is Data:
  NativePlan{book: Scalar.Ref, operations: List<&2, Transfer>,
    reads: List<&2, Scalar.Ref>, effects: List<&2, Scalar.ScalarEffect>,
    returns: List<&2, ReturnSlot>}

type PlanResult is Data:
  Refused{reason: Nat}
  Planned{plan: NativePlan}

def prepare(book: Scalar.Ref, operations: List<&2, Transfer>,
    reads: List<&2, Scalar.Ref>, effects: List<&2, Scalar.ScalarEffect>,
    returns: List<&2, ReturnSlot>) -> PlanResult:
  Planned{NativePlan{book, operations, reads, effects, returns}}
