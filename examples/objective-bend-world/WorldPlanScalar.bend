# Generic logical output ABI. Ref.resourceID is the actual native identity,
# never the position of a command target. Root is the exact canonical native
# digest codec byte list; receiving binds it to the sampled current cell.
import Base

type Ref is Data:
  Ref{resourceID: Nat, root: List<&2, Nat>}

type Write is Data:
  Write{field: Nat, before: Nat, after: Nat}

type ScalarEffect is Data:
  ScalarEffect{ref: Ref, writes: List<&2, Write>}

type NativePlan is Data:
  NativePlan{reads: List<&2, Ref>, effects: List<&2, ScalarEffect>}

# This constructor is pure candidate data. It cannot submit, authorize, sample
# state or install a write. Native admission remains the sole effect receiver.
def guarded(ref: Ref, writes: List<&2, Write>) -> ScalarEffect:
  ScalarEffect{ref, writes}

def plan(reads: List<&2, Ref>, effects: List<&2, ScalarEffect>) -> NativePlan:
  NativePlan{reads, effects}

law guarded_exact:
  for ref: Ref
  for writes: List<&2, Write>
  {guarded(ref, writes) == ScalarEffect{ref, writes} : ScalarEffect}

def guarded_exact(ref, writes):
  {==}

law plan_exact:
  for reads: List<&2, Ref>
  for effects: List<&2, ScalarEffect>
  {plan(reads, effects) == NativePlan{reads, effects} : NativePlan}

def plan_exact(reads, effects):
  {==}

# Refusal is a distinct inert output, never a successful empty effect list.
type PlanResult is Data:
  Refused{reason: Nat}
  Planned{plan: NativePlan}

def refused(reason: Nat) -> PlanResult:
  Refused{reason}

def planned(reads: List<&2, Ref>, effects: List<&2, ScalarEffect>) -> PlanResult:
  Planned{NativePlan{reads, effects}}

law refusal_exact:
  for reason: Nat
  {refused(reason) == Refused{reason} : PlanResult}

def refusal_exact(reason):
  {==}
