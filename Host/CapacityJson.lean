/- The declared envelope's JSON surface, ONE definition: the eighteen
`ObjectiveInvocationClaim.Capacity` lanes as decimal strings, decoded
(`capacity`) and encoded (`capacityJson`), with the field readers every Host
JSON authoring module shares. `Host.SeatJson` and `Host.ObjectiveActivityJson`
both author signed commands whose envelopes are this object; neither keeps a
copy.

Nothing here decides anything: an envelope is judged by the kernel that
covers it (`Config.covers`). -/
import Compiler.ObjectiveInvocationClaim
import Lean.Data.Json

namespace Minidregg.Host.CapacityJson
open Lean (Json toJson)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)
set_option autoImplicit false

abbrev Result := Except String

def decimal (value : Nat) : Json := .str (toString value)

def field (path : String) (json : Json) (name : String) : Result Json :=
  match json.getObjVal? name with
  | .ok value => .ok value
  | .error _ => .error s!"{path}.{name} missing"

/-- A canonical decimal string (no sign, no leading zero, no whitespace). -/
def natOf (path : String) (value : Json) : Result Nat := do
  let some text := value.getStr?.toOption | throw s!"{path} must be a decimal string"
  let some n := text.toNat? | throw s!"{path} must be a decimal string"
  unless toString n == text do throw s!"{path} must be canonical decimal"
  pure n

def nat (path : String) (json : Json) (name : String) : Result Nat := do
  natOf s!"{path}.{name}" (← field path json name)

/-- A declared envelope: the eighteen `Capacity` lanes as decimal strings. -/
def capacity (path : String) (json : Json) : Result Capacity := do
  let n := nat path json
  pure ⟨← n "typeFuel", ← n "sourceTicks", ← n "heap", ← n "stack", ← n "outputNodes", ← n "outputBytes",
    ← n "inputBytes", ← n "scalarBits", ← n "memoryTouches", ← n "proofWork", ← n "feeDebit", ← n "turnBytes",
    ← n "witnessBytes", ← n "storageBytes", ← n "sideEffectCount", ← n "networkBytes", ← n "leaseByteBlocks",
    ← n "incidences"⟩

/-- The eighteen lanes of an envelope, as named decimal strings. -/
def capacityLanes (c : Capacity) : List (String × Json) :=
  [("typeFuel", decimal c.typeFuel),
   ("sourceTicks", decimal c.sourceTicks),
   ("heap", decimal c.heap),
   ("stack", decimal c.stack),
   ("outputNodes", decimal c.outputNodes),
   ("outputBytes", decimal c.outputBytes),
   ("inputBytes", decimal c.inputBytes),
   ("scalarBits", decimal c.scalarBits),
   ("memoryTouches", decimal c.memoryTouches),
   ("proofWork", decimal c.proofWork),
   ("feeDebit", decimal c.feeDebit),
   ("turnBytes", decimal c.turnBytes),
   ("witnessBytes", decimal c.witnessBytes),
   ("storageBytes", decimal c.storageBytes),
   ("sideEffectCount", decimal c.sideEffectCount),
   ("networkBytes", decimal c.networkBytes),
   ("leaseByteBlocks", decimal c.leaseByteBlocks),
   ("incidences", decimal c.incidences)]

def capacityJson (c : Capacity) : Json := .mkObj (capacityLanes c)

/-! ## Round trip: what is encoded decodes to the same envelope -/

theorem getObjVal_mkObj (l : List (String × Json)) (k : String) (v : Json)
    (distinct : l.Pairwise (fun a b => a.1 ≠ b.1)) (mem : (k, v) ∈ l) :
    (Json.mkObj l).getObjVal? k = .ok v := by
  unfold Json.mkObj Json.getObjVal?
  have found : (Std.TreeMap.Raw.ofList l compare)[k]? = some v :=
    Std.TreeMap.Raw.getElem?_ofList_of_mem (cmp := compare) (k := k) (k' := k) (Std.ReflCmp.compare_self)
      (distinct.imp (fun h hc => h (Std.LawfulEqCmp.eq_of_compare hc))) mem
  simp [Std.TreeMap.Raw.get?_eq_getElem?, found]
  rfl

theorem natOf_decimal (path : String) (n : Nat) : natOf path (decimal n) = .ok n := by
  have h : (decimal n).getStr? = .ok n.repr := rfl
  simp [natOf, h, Nat.toNat?_repr, Except.toOption, pure, Except.pure]
  rfl

theorem lane_names_nodup : ["typeFuel", "sourceTicks", "heap", "stack", "outputNodes", "outputBytes",
    "inputBytes", "scalarBits", "memoryTouches", "proofWork", "feeDebit", "turnBytes", "witnessBytes",
    "storageBytes", "sideEffectCount", "networkBytes", "leaseByteBlocks", "incidences"].Nodup := by decide

theorem capacityLanes_distinct (c : Capacity) : (capacityLanes c).Pairwise (fun a b => a.1 ≠ b.1) :=
  (List.pairwise_map (f := Prod.fst)).mp lane_names_nodup

theorem nat_capacityJson (path : String) (c : Capacity) (name : String) (n : Nat)
    (mem : (name, decimal n) ∈ capacityLanes c) : nat path (capacityJson c) name = .ok n := by
  unfold nat field capacityJson
  rw [getObjVal_mkObj _ name _ (capacityLanes_distinct c) mem]
  exact natOf_decimal _ _

/-- **`capacity_capacityJson`**: decoding an encoded envelope returns it, lane for lane. -/
theorem capacity_capacityJson (path : String) (c : Capacity) :
    capacity path (capacityJson c) = .ok c := by
  unfold capacity
  simp only [nat_capacityJson path c "typeFuel" c.typeFuel (by simp [capacityLanes]),
    nat_capacityJson path c "sourceTicks" c.sourceTicks (by simp [capacityLanes]),
    nat_capacityJson path c "heap" c.heap (by simp [capacityLanes]),
    nat_capacityJson path c "stack" c.stack (by simp [capacityLanes]),
    nat_capacityJson path c "outputNodes" c.outputNodes (by simp [capacityLanes]),
    nat_capacityJson path c "outputBytes" c.outputBytes (by simp [capacityLanes]),
    nat_capacityJson path c "inputBytes" c.inputBytes (by simp [capacityLanes]),
    nat_capacityJson path c "scalarBits" c.scalarBits (by simp [capacityLanes]),
    nat_capacityJson path c "memoryTouches" c.memoryTouches (by simp [capacityLanes]),
    nat_capacityJson path c "proofWork" c.proofWork (by simp [capacityLanes]),
    nat_capacityJson path c "feeDebit" c.feeDebit (by simp [capacityLanes]),
    nat_capacityJson path c "turnBytes" c.turnBytes (by simp [capacityLanes]),
    nat_capacityJson path c "witnessBytes" c.witnessBytes (by simp [capacityLanes]),
    nat_capacityJson path c "storageBytes" c.storageBytes (by simp [capacityLanes]),
    nat_capacityJson path c "sideEffectCount" c.sideEffectCount (by simp [capacityLanes]),
    nat_capacityJson path c "networkBytes" c.networkBytes (by simp [capacityLanes]),
    nat_capacityJson path c "leaseByteBlocks" c.leaseByteBlocks (by simp [capacityLanes]),
    nat_capacityJson path c "incidences" c.incidences (by simp [capacityLanes])]
  rfl

#assert_axioms getObjVal_mkObj natOf_decimal capacity_capacityJson

end Minidregg.Host.CapacityJson
