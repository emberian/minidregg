/- Collection of the Core4 demand heap at a yield (design B4/T5).

A yielded activity's checkpoint is its exact machine state, and the demand machine
only ever allocates: every cell a finished demand left behind stays in the heap, so an
activity that loops through yields grows its checkpoint without bound. `collect` keeps
exactly the cells traced from the roots (the control, including the yielded Plan cell,
and every stack frame), compacts them in increasing old-address order, and renames
every address. Addresses past the heap (never present in a lexically valid state) are
renamed by the shift that keeps them past the compacted heap, so collection is total and
its behaviour theorem needs no validity premise.

Costs: marking is a worklist over an `Array Bool` (each cell is traced once, each edge
pushed once), ranking is one `Array.foldl`, compaction one `Array.zip`/`filterMap`, and
renaming touches each kept address once: linear in heap + edges, no list lookups over the
heap.

The behaviour theorem (a renaming simulation: lockstep `stepRaw`, `resume`, bounded runs,
Plan/result extraction) and the typing transfer are in
`Theory.ObjectiveBendDemandCollectProofs` (`ObjectiveProofs`). -/
import Theory.ObjectiveBendDemandMachine
import Theory.AxiomPin
namespace Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
set_option autoImplicit false

/-! ## The addresses a machine object holds -/

def valueAddresses : RuntimeValue → List Nat
  | .closure _ environment => environment
  | .natural _ | .boolean _ | .label _ => []
  | .record fields => fields.map Prod.snd
  | .specification metadata extension => [metadata, extension]
  | .prototype specification target => [specification, target]
  | .variant _ payload => [payload]

def cellAddresses : Cell → List Nat
  | .suspended origin | .evaluating origin => origin.environment
  | .cached origin value => origin.environment ++ valueAddresses value

def frameAddresses : Frame → List Nat
  | .argument _ environment | .extend _ environment | .condition _ _ environment
  | .binaryLeft _ _ environment | .case _ environment | .ifBool _ _ environment => environment
  | .update address => [address]
  | .field _ | .reflect | .metadata | .project => []
  | .binaryRight _ value => valueAddresses value

def controlAddresses : Control → List Nat
  | .evaluate _ environment => environment
  | .enter address | .blackhole address | .yielded address => [address]
  | .returned value | .complete value => valueAddresses value
  | .refused _ => []

/-- The roots: the control (a yielded state's Plan address among them) and every frame. -/
def rootAddresses (state : State) : List Nat :=
  controlAddresses state.control ++ state.stack.flatMap frameAddresses

/-! ## Renaming every address -/

def renameValue (f : Nat → Nat) : RuntimeValue → RuntimeValue
  | .closure body environment => .closure body (environment.map f)
  | .natural value => .natural value
  | .boolean value => .boolean value
  | .label value => .label value
  | .record fields => .record (fields.map fun field => (field.1, f field.2))
  | .specification metadata extension => .specification (f metadata) (f extension)
  | .prototype specification target => .prototype (f specification) (f target)
  | .variant label payload => .variant label (f payload)

def renameClosure (f : Nat → Nat) (closure : Closure) : Closure :=
  ⟨closure.term, closure.environment.map f⟩

def renameCell (f : Nat → Nat) : Cell → Cell
  | .suspended origin => .suspended (renameClosure f origin)
  | .evaluating origin => .evaluating (renameClosure f origin)
  | .cached origin value => .cached (renameClosure f origin) (renameValue f value)

def renameFrame (f : Nat → Nat) : Frame → Frame
  | .argument term environment => .argument term (environment.map f)
  | .update address => .update (f address)
  | .field name => .field name
  | .reflect => .reflect
  | .metadata => .metadata
  | .project => .project
  | .extend fields environment => .extend fields (environment.map f)
  | .condition zero successorBody environment => .condition zero successorBody (environment.map f)
  | .binaryLeft primitive right environment => .binaryLeft primitive right (environment.map f)
  | .binaryRight primitive left => .binaryRight primitive (renameValue f left)
  | .case arms environment => .case arms (environment.map f)
  | .ifBool whenTrue whenFalse environment => .ifBool whenTrue whenFalse (environment.map f)

def renameControl (f : Nat → Nat) : Control → Control
  | .evaluate term environment => .evaluate term (environment.map f)
  | .enter address => .enter (f address)
  | .blackhole address => .blackhole (f address)
  | .returned value => .returned (renameValue f value)
  | .complete value => .complete (renameValue f value)
  | .refused reason => .refused reason
  | .yielded plan => .yielded (f plan)

/-! ## Marking -/

/-- The addresses the cell at `address` holds; nothing past the heap. -/
def children (heap : Array Cell) (address : Nat) : List Nat :=
  match heap[address]? with
  | some cell => cellAddresses cell
  | none => []

/-- Drop the worklist prefix that needs no tracing: marked addresses and addresses
past the heap (those are renamed by the shift, never traced). -/
def pending (marks : Array Bool) : List Nat → List Nat
  | [] => []
  | address :: rest => match marks[address]? with
    | some false => address :: rest
    | _ => pending marks rest

/-- Worklist marking. `fuel` bounds the cells still unmarked (each mark spends one
unit); the worklist is drained between marks, so the recursion is structural and the
fuel provably never runs out first (`markFrom_spec`). -/
def markFrom (heap : Array Cell) : Nat → Array Bool → List Nat → Array Bool
  | 0, marks, _ => marks
  | fuel+1, marks, work => match pending marks work with
    | [] => marks
    | address :: rest =>
      markFrom heap fuel (marks.set! address true) (children heap address ++ rest)

/-- Which cells are live: traced from the roots. -/
def liveMarks (state : State) : Array Bool :=
  markFrom state.heap state.heap.size (Array.replicate state.heap.size false) (rootAddresses state)

/-! ## Compaction -/

/-- One rank step: record the live count so far, count this cell if it is live. -/
def rankStep (acc : Array Nat × Nat) (marked : Bool) : Array Nat × Nat :=
  (acc.1.push acc.2, if marked then acc.2 + 1 else acc.2)

/-- Each old address's new address (the number of live cells before it), and the
number of live cells. -/
def rankTable (marks : Array Bool) : Array Nat × Nat :=
  marks.foldl rankStep (#[], 0)

/-- The renaming: a heap address goes to its rank; an address past the heap keeps
its distance past the end. -/
def relocate (size live : Nat) (table : Array Nat) (address : Nat) : Nat :=
  if address < size then table.getD address 0 else address - size + live

/-- The live cells in increasing old-address order, renamed. -/
def compact (f : Nat → Nat) (heap : Array Cell) (marks : Array Bool) : Array Cell :=
  (heap.zip marks).filterMap fun entry => if entry.2 then some (renameCell f entry.1) else none

/-- The renaming `collect` applies to `state`. -/
def collectRenaming (state : State) : Nat → Nat :=
  let ranked := rankTable (liveMarks state)
  relocate state.heap.size ranked.2 ranked.1

/-- Collect the heap: keep the cells reachable from the roots, compact, rename. A
yielded state stays yielded (at its Plan cell's new address); heap and stack keep
their meaning under the renaming (`Theory.ObjectiveBendDemandCollectProofs`). -/
def collect (state : State) : State :=
  let marks := liveMarks state
  let ranked := rankTable marks
  let f := relocate state.heap.size ranked.2 ranked.1
  ⟨compact f state.heap marks, renameControl f state.control, state.stack.map (renameFrame f)⟩

/-! ## Measurement: collection drops garbage

A yielded state whose heap holds a finished demand's leftovers: cell 1 (a spent argument
thunk) and cell 3 (a cached intermediate) are unreachable; the Plan cell 2 captures cell
0, and the stack's argument frame captures cell 4. -/

def garbageExample : State :=
  ⟨#[.cached ⟨.nat 1, []⟩ (.natural 1), .suspended ⟨.nat 7, []⟩,
     .suspended ⟨.bound 0, [0]⟩, .cached ⟨.nat 9, []⟩ (.natural 9),
     .suspended ⟨.nat 5, []⟩],
   .yielded 2, [.argument (.bound 0) [4]]⟩

theorem garbageExample_heap_size : garbageExample.heap.size = 5 := rfl

/-- Two of five cells are garbage: the collected heap has three. -/
theorem collect_garbageExample_heap_size : (collect garbageExample).heap.size = 3 := by decide +kernel

/-- The yielded Plan cell moved from 2 to 1, and the frame's capture from 4 to 2. -/
theorem collect_garbageExample_roots :
    (match (collect garbageExample).control with | .yielded plan => plan | _ => 99) = 1 ∧
    (collect garbageExample).stack.flatMap frameAddresses = [2] := by decide

#assert_axioms collect_garbageExample_heap_size
#assert_axioms collect_garbageExample_roots

end Minidregg.Theory.ObjectiveBendDemandCollect
