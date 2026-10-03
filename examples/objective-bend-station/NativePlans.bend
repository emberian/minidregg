# Structural adapter to the ONE shared WorldPlanScalar constructor ABI.
# This helper is not an authorized method export or a source evaluation witness.
# Receiving binds the public station wrapper, actual source result and current
# root/authority. Ref.resourceID stays the native identity, never a target index.
import Base
import ./SharedConsequences.bend as Station
import ./WorldPlanScalar.bend as World

def native_ref(ref: Station.Ref) -> World.Ref:
  match ref:
    case Station.Ref{target, root}:
      World.Ref{target, root}

def native_write(write: Station.Write) -> World.Write:
  match write:
    case Station.Write{field, before, after}:
      World.Write{field, before, after}

def native_writes(writes: List<&2, Station.Write>) -> List<&2, World.Write>:
  match writes:
    case Nil{}:
      Nil{}
    case Con{write, rest}:
      Con{native_write(write), native_writes(rest)}

def native_reads(reads: Station.Reads) -> List<&2, World.Ref>:
  match reads:
    case Station.NoReads{}:
      Nil{}
    case Station.ReadRoot{ref, rest}:
      Con{native_ref(ref), native_reads(rest)}

def native_effects(effects: Station.Effects) -> List<&2, World.ScalarEffect>:
  match effects:
    case Station.NoEffects{}:
      Nil{}
    case Station.ScalarEffect{ref, writes, rest}:
      Con{World.guarded(native_ref(ref), native_writes(writes)), native_effects(rest)}

def candidate_plan(candidate: Station.Candidate) -> World.NativePlan:
  match candidate:
    case Station.Candidate{source, reads, effects}:
      World.plan(native_reads(reads), native_effects(effects))

# Structural conversion preserves resource identity, root and every old/new value.
law ref_exact:
  for resourceID: Nat
  for root: List<&2, Nat>
  {native_ref(Station.Ref{resourceID, root}) == World.Ref{resourceID, root} : World.Ref}

def ref_exact(resourceID, root):
  {==}

law write_exact:
  for field: Nat
  for before: Nat
  for after: Nat
  {native_write(Station.Write{field, before, after}) == World.Write{field, before, after} : World.Write}

def write_exact(field, before, after):
  {==}

law effect_order_exact:
  for ref: Station.Ref
  for writes: List<&2, Station.Write>
  for rest: Station.Effects
  {native_effects(Station.ScalarEffect{ref, writes, rest}) ==
    Con{World.guarded(native_ref(ref), native_writes(writes)), native_effects(rest)} : List<&2, World.ScalarEffect>}

def effect_order_exact(ref, writes, rest):
  {==}

# Refusal remains refusal, never an empty successful native Plan.
def result_plan(result: Station.Result) -> World.PlanResult:
  match result:
    case Station.Refused{reason}:
      World.refused(reason)
    case Station.Proposed{candidate}:
      World.Planned{candidate_plan(candidate)}

law refusal_has_no_plan:
  for reason: Nat
  {result_plan(Station.Refused{reason}) == World.Refused{reason} : World.PlanResult}

def refusal_has_no_plan(reason):
  {==}
