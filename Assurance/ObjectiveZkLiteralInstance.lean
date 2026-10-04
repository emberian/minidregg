import Assurance.ObjectiveZkRefinementAudit
import Assurance.ObjectiveDemandPhysicalChecks
import Compiler.ObjectiveDemandStateEquality
import Theory.AssertCompiled

/- A real `PackedCodec` (hence `PackedRefinement`) for an actual lowered Objective
network: the oblivious tranche's literal controller graph (ObjectiveThunkNetwork +
ObjectiveDemandLiteralNetwork) at the public layout of
`ObjectiveDemandPhysicalChecks.layout` (shape ⟨4,11,2,2⟩, 8 code rows, 4 code
fields, 2 names of ≤ 15 bytes, 2 environments, 2 records).

The decoder is `ObjectiveDemandRegions.state layout`: ONE function of the layout and
the bits. It reads the state region and every table region (code rows, code fields,
names, environments, record fields) from the bits. It has no program parameter, so
ONE codec serves every program prepared for the layout: `regionCodec` is certified
over the reachable rows of five programs at once (`.nat 7`, `.nat 9`, a label, a
Boolean and a closure) and binds each one's code (`region_binds_code`).

Scope, stated exactly: `regionCodec` restricts that decoder to the rows reachable
from the five programs' pinned initial bits. The graph is deterministic and the
arithmetic receivers pin every input bit, so for those programs and inputs every
accepted run is a stepRaw trace. It is checked by compiled evaluation
(`#assert_compiled`); the universal all-rows refinement of the controller is open.

The refuter `externalTables_not_refinement` keeps the failure of the tranche's
earlier decoder, `externalTables` below (the state region read against the tables
of one prepared program, supplied beside the bits): it is the `represents` of NO
PackedRefinement of the graph. The bits of `.nat 9` are represented as
`initial (.nat 7)` and one accepted tick returns `9`. -/
namespace Minidregg.Assurance.ObjectiveZkLiteralInstance
open Minidregg.Compiler Minidregg.Theory
open ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandAdequacy
open ObjectiveBendDemandInvariant
open ObliviousNetwork ObliviousUnroll
open Minidregg.Assurance.ObjectiveBendProofSource
open Minidregg.Assurance.ObjectiveZkRefinementAudit
set_option autoImplicit false

/-! ### Generic per-run certificate: any network, any decoder -/

def next? (network : Network) (bits : Array Bool) : Option (Array Bool) :=
  match network.evaluate bits with
  | some output => if output[0]?.getD false then some (output.extract 1 output.size) else none
  | none => none

def orbit (network : Network) : Nat → Array Bool → List (Array Bool)
  | 0, bits => [bits]
  | fuel+1, bits => bits :: (match next? network bits with
      | some following => orbit network fuel following
      | none => [])

def related (fuel : Nat) (after state : State) : Bool :=
  (ObjectiveDemandStateEquality.state fuel after state).isSome ||
    (ObjectiveDemandStateEquality.state fuel after (stepRaw state)).isSome

def afterChecked (decode : Array Bool → Option State) (fuel : Nat) (state : State)
    (following : Array Bool) : Bool :=
  match decode following with
  | some after => related fuel after state
  | none => false

def stepChecked (network : Network) (decode : Array Bool → Option State) (fuel : Nat)
    (reach : List (Array Bool)) (bits : Array Bool) : Bool :=
  match decode bits, next? network bits with
  | some state, some following =>
      decide (following ∈ reach) && afterChecked decode fuel state following
  | some _, none => true
  | none, _ => false

theorem related_sound {fuel : Nat} {after state : State} (check : related fuel after state = true) :
    after = state ∨ after = stepRaw state := by
  unfold related at check
  rw [Bool.or_eq_true] at check
  rcases check with same | moved
  · obtain ⟨proof, _⟩ := Option.isSome_iff_exists.mp same
    exact Or.inl proof.down
  · obtain ⟨proof, _⟩ := Option.isSome_iff_exists.mp moved
    exact Or.inr proof.down

theorem afterChecked_sound {decode : Array Bool → Option State} {fuel : Nat} {state : State}
    {following : Array Bool} (check : afterChecked decode fuel state following = true) :
    ∃ after, decode following = some after ∧ (after = state ∨ after = stepRaw state) := by
  revert check
  unfold afterChecked
  cases decode following with
  | none => intro check; cases check
  | some after => intro check; exact ⟨after, rfl, related_sound check⟩

theorem stepChecked_sound {network : Network} {decode : Array Bool → Option State} {fuel : Nat}
    {reach : List (Array Bool)} {bits following : Array Bool} {state : State}
    (check : stepChecked network decode fuel reach bits = true)
    (decoded : decode bits = some state) (stepped : next? network bits = some following) :
    following ∈ reach ∧
      ∃ after, decode following = some after ∧ (after = state ∨ after = stepRaw state) := by
  unfold stepChecked at check
  rw [decoded, stepped] at check
  have parts : (decide (following ∈ reach) && afterChecked decode fuel state following) = true :=
    check
  rw [Bool.and_eq_true] at parts
  exact ⟨of_decide_eq_true parts.1, afterChecked_sound parts.2⟩

theorem next?_of_accepted {network : Network} {input output : Array Bool}
    (evaluated : network.evaluate input = some output) (handled : output[0]? = some true) :
    next? network input = some (output.extract 1 output.size) := by
  unfold next?
  rw [evaluated]
  show (if output[0]?.getD false then some (output.extract 1 output.size) else none) =
    some (output.extract 1 output.size)
  rw [handled]
  try rfl

theorem accepted_of_next {network : Network} {bits following : Array Bool}
    (stepped : next? network bits = some following) :
    ∃ output, network.evaluate bits = some output ∧ output[0]? = some true ∧
      following = output.extract 1 output.size := by
  unfold next? at stepped
  split at stepped
  · rename_i output evaluated
    split at stepped
    · rename_i handled
      cases stepped
      refine ⟨output, evaluated, ?_, rfl⟩
      revert handled
      cases output[0]? with
      | none => intro wrong; cases wrong
      | some first => intro bit; cases bit; rfl
    · cases stepped
  · cases stepped

theorem acceptedRun_of_next {network : Network} {bits following final : Array Bool} {ticks : Nat}
    (stepped : next? network bits = some following)
    (rest : AcceptedRun network ticks following final) :
    AcceptedRun network (ticks+1) bits final := by
  obtain ⟨output, evaluated, handled, same⟩ := accepted_of_next stepped
  subst same
  exact .step evaluated handled rest

def reachDecode (decode : Array Bool → Option State) (reach : List (Array Bool))
    (bits : Array Bool) : Option State :=
  if bits ∈ reach then decode bits else none

theorem reachDecode_some {decode : Array Bool → Option State} {reach : List (Array Bool)}
    {bits : Array Bool} {state : State} (decoded : reachDecode decode reach bits = some state) :
    bits ∈ reach ∧ decode bits = some state := by
  unfold reachDecode at decoded
  split at decoded
  · exact ⟨‹_›, decoded⟩
  · cases decoded

/-- A certified reachable set yields a real codec of the network. -/
def certifiedCodec (network : Network) (decode : Array Bool → Option State) (fuel : Nat)
    (reach : List (Array Bool))
    (certified : reach.all (stepChecked network decode fuel reach) = true) :
    PackedCodec network where
  decode := reachDecode decode reach
  acceptedStep := by
    intro input output state evaluated handled decoded
    obtain ⟨member, decodedRaw⟩ := reachDecode_some decoded
    have check := List.all_eq_true.mp certified input member
    obtain ⟨followingMember, after, decodedAfter, moved⟩ :=
      stepChecked_sound check decodedRaw (next?_of_accepted evaluated handled)
    refine ⟨after, ?_, ?_⟩
    · rcases moved with same | stepped
      · rw [same]; exact .administrative state
      · rw [stepped]; exact .transition state
    · unfold reachDecode
      rw [if_pos followingMember]
      exact decodedAfter

/-! ### The actual tranche network, one decoder for every program -/

open ObjectiveDemandPhysicalChecks (layout)

def codeLimits : ObjectiveDemandCode.Limits := ⟨128,32,128⟩
def equalityFuel : Nat := 64

def prepare (source : Term) : Option (ObjectiveDemandPhysical.Prepared source layout) :=
  ObjectiveDemandPhysical.prepare codeLimits layout source

theorem graph_built : (ObjectiveDemandLiteralNetwork.network layout).isSome = true := by
  native_decide

/-- The public graph of the layout. -/
def graph : Network := (ObjectiveDemandLiteralNetwork.network layout).get graph_built

theorem prepared_graph {source : Term} (prepared : ObjectiveDemandPhysical.Prepared source layout) :
    prepared.graph = graph :=
  Option.some.inj (prepared.graphExact.symm.trans (Option.some_get graph_built).symm)

/-- The corrected decoder: the layout and the bits, nothing else. -/
def regionDecode (bits : Array Bool) : Option State := ObjectiveDemandRegions.state layout bits

theorem prepared_nat7 : (prepare (.nat 7)).isSome = true := by native_decide
def nat7 : ObjectiveDemandPhysical.Prepared (.nat 7) layout := (prepare (.nat 7)).get prepared_nat7
theorem prepared_nat9 : (prepare (.nat 9)).isSome = true := by native_decide
def nat9 : ObjectiveDemandPhysical.Prepared (.nat 9) layout := (prepare (.nat 9)).get prepared_nat9
theorem prepared_label : (prepare (.label "private-label")).isSome = true := by native_decide
def labelPrepared : ObjectiveDemandPhysical.Prepared (.label "private-label") layout :=
  (prepare (.label "private-label")).get prepared_label
theorem prepared_boolean : (prepare (.boolean true)).isSome = true := by native_decide
def booleanPrepared : ObjectiveDemandPhysical.Prepared (.boolean true) layout :=
  (prepare (.boolean true)).get prepared_boolean
theorem prepared_closure : (prepare (.lam (.bound 0))).isSome = true := by native_decide
def closurePrepared : ObjectiveDemandPhysical.Prepared (.lam (.bound 0)) layout :=
  (prepare (.lam (.bound 0))).get prepared_closure

def reach : List (Array Bool) :=
  orbit graph 4 nat7.initialBits ++ orbit graph 4 nat9.initialBits ++
  orbit graph 4 labelPrepared.initialBits ++ orbit graph 4 booleanPrepared.initialBits ++
  orbit graph 4 closurePrepared.initialBits

theorem reach_certified : reach.all (stepChecked graph regionDecode equalityFuel reach) = true := by
  native_decide

/-- The instance: one decoder of the actual graph for all five programs, every
accepted tick a stutter or one actual `stepRaw`. -/
def regionCodec : PackedCodec graph :=
  certifiedCodec graph regionDecode equalityFuel reach reach_certified

def regionRefinement : PackedRefinement graph := regionCodec.toRefinement

/-- THE CORRECTED REFINEMENT STATEMENT. A codec of the graph whose decoder, wherever it
answers, IS the layout's one decoder: it reads the state region and the code, code
field, name, environment and record regions of the same bits. No table enters beside
the bits, so its `represents` cannot interpret a row through another program's tables.
`acceptedStep` is still per codec; the universal codec (decode = the layout decoder on
every row) is the open controller obligation. -/
structure LayoutCodec (layout : ObjectiveDemandLayout.Layout) (network : Network)
    extends PackedCodec network where
  bound : ∀ bits state, decode bits = some state →
    ObjectiveDemandRegions.state layout bits = some state

def regionLayoutCodec : LayoutCodec layout graph where
  toPackedCodec := regionCodec
  bound := by
    intro bits state decoded
    exact (reachDecode_some decoded).2

/-- Every layout codec of this layout reads a prepared program's initial bits, if at
all, as THAT program's initial state: the code it runs is the code in its bits. -/
theorem layoutCodec_binds {network : Network} {source : Term} (codec : LayoutCodec layout network)
    (prepared : ObjectiveDemandPhysical.Prepared source layout) {state : State}
    (decoded : codec.decode prepared.initialBits = some state) :
    state = ObjectiveBendDemandMachine.initial source :=
  Option.some.inj ((codec.bound _ _ decoded).symm.trans prepared.initialExact)

theorem orbit_head (network : Network) (fuel : Nat) (bits : Array Bool) :
    bits ∈ orbit network fuel bits := by
  cases fuel with
  | zero => exact List.mem_singleton.mpr rfl
  | succ fuel => exact List.mem_cons.mpr (Or.inl rfl)

/-- The codec reads each program's initial bits as that program's initial state:
the prepared program's translation-validated `initialExact`, on a reachable row. -/
theorem regionCodec_initial {source : Term} (prepared : ObjectiveDemandPhysical.Prepared source layout)
    (member : prepared.initialBits ∈ reach) :
    regionCodec.decode prepared.initialBits = some (ObjectiveBendDemandMachine.initial source) := by
  show reachDecode regionDecode reach prepared.initialBits = _
  unfold reachDecode
  rw [if_pos member]
  exact prepared.initialExact

theorem nat7_member : nat7.initialBits ∈ reach := by
  unfold reach
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (orbit_head _ _ _))))
theorem nat9_member : nat9.initialBits ∈ reach := by
  unfold reach
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (orbit_head _ _ _))))
theorem label_member : labelPrepared.initialBits ∈ reach := by
  unfold reach
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr (orbit_head _ _ _)))

theorem nat7_initial :
    regionCodec.decode nat7.initialBits = some (ObjectiveBendDemandMachine.initial (.nat 7)) :=
  regionCodec_initial nat7 nat7_member

/-- THE BINDING: the same codec reads `.nat 9`'s bits as `initial (.nat 9)`, not as
another program's initial state. The code region is read from the bits. -/
theorem region_binds_code :
    regionCodec.decode nat9.initialBits = some (ObjectiveBendDemandMachine.initial (.nat 9)) :=
  regionCodec_initial nat9 nat9_member

/-- No layout codec represents `.nat 9`'s bits as `.nat 7`'s initial state. -/
theorem layoutCodec_not_foreign {network : Network} (codec : LayoutCodec layout network) :
    codec.decode nat9.initialBits ≠ some (ObjectiveBendDemandMachine.initial (.nat 7)) := by
  intro decoded
  have same := layoutCodec_binds codec nat9 decoded
  have controls := congrArg State.control same
  simp [ObjectiveBendDemandMachine.initial] at controls

def nat7Tick1 : Array Bool := (next? graph nat7.initialBits).getD #[]
def nat7Tick2 : Array Bool := (next? graph nat7Tick1).getD #[]

theorem nat7_step1 : next? graph nat7.initialBits = some nat7Tick1 := by native_decide
theorem nat7_step2 : next? graph nat7Tick1 = some nat7Tick2 := by native_decide
/-- Completion is absorbing in the physical graph: handled stays true, state unchanged. -/
theorem nat7_complete_stutters : next? graph nat7Tick2 = some nat7Tick2 := by native_decide

theorem nat7_run : AcceptedRun graph 2 nat7.initialBits nat7Tick2 :=
  acceptedRun_of_next nat7_step1 (acceptedRun_of_next nat7_step2 (.done _))

theorem nat7_read : regionCodec.read nat7Tick2 = some (.natural 7) := by native_decide

/-- Every accepted run of the actual graph from `.nat 7`'s pinned initial bits, of
any length, whose derived reader answers, yields the Objective source meaning. -/
theorem nat7_observes {ticks : Nat} {output : Array Bool} {observation : Observation}
    (run : AcceptedRun graph ticks nat7.initialBits output)
    (read : regionCodec.read output = some observation) :
    Evaluates (.nat 7) (observationTerm observation) :=
  regionCodec.observes_source (.natural 7) run nat7_initial read

/-- Non-vacuity: the premises are met by an actual two-tick run of the graph. -/
theorem nat7_reaches_source_meaning : Evaluates (.nat 7) (.nat 7) :=
  nat7_observes nat7_run nat7_read

/-- The same codec, a different program: `.nat 9` through the same graph. -/
def nat9Final : Array Bool := (next? graph ((next? graph nat9.initialBits).getD #[])).getD #[]
theorem nat9_step1 : next? graph nat9.initialBits = some ((next? graph nat9.initialBits).getD #[]) := by
  native_decide
theorem nat9_step2 : next? graph ((next? graph nat9.initialBits).getD #[]) = some nat9Final := by
  native_decide
theorem nat9_read : regionCodec.read nat9Final = some (.natural 9) := by native_decide

theorem nat9_reaches_source_meaning : Evaluates (.nat 9) (.nat 9) :=
  regionCodec.observes_source (.natural 9)
    (acceptedRun_of_next nat9_step1 (acceptedRun_of_next nat9_step2 (.done _)))
    region_binds_code nat9_read

/-! ### A label program (its name is read from the names region of the bits) -/

def labelFinal : Array Bool :=
  (next? graph ((next? graph labelPrepared.initialBits).getD #[])).getD #[]

theorem label_step1 : next? graph labelPrepared.initialBits =
    some ((next? graph labelPrepared.initialBits).getD #[]) := by native_decide
theorem label_step2 : next? graph ((next? graph labelPrepared.initialBits).getD #[]) =
    some labelFinal := by
  native_decide
theorem label_read : regionCodec.read labelFinal = some (.label "private-label") := by native_decide

theorem label_reaches_source_meaning : Evaluates (.label "private-label") (.label "private-label") :=
  regionCodec.observes_source (.label "private-label")
    (acceptedRun_of_next label_step1 (acceptedRun_of_next label_step2 (.done _)))
    (regionCodec_initial labelPrepared label_member) label_read

/-! ### Refuter: the earlier decoder (tables beside the bits) is not a refinement -/

/-- The tranche's earlier decoder, kept only as the object of the refuter: the state
region of the bits, interpreted against the tables of ONE prepared program supplied
beside the bits. The code region the graph executes is never read. -/
def externalTables {source : Term} (prepared : ObjectiveDemandPhysical.Prepared source layout)
    (bits : Array Bool) : Option State := do
  let (reference, _) ← ObjectiveDemandStateCodec.decode layout.shape
    (bits.extract 0 layout.shape.inputCount)
  ObjectiveDemandStorage.decode (ObjectiveDemandStorage.initialTables prepared.compiled.program)
    prepared.compiled.decodeDepth reference

def decodesTo (decoded : Option State) (expected : State) : Bool :=
  match decoded with
  | some state => (ObjectiveDemandStateEquality.state equalityFuel state expected).isSome
  | none => false

theorem decodesTo_sound {decoded : Option State} {expected : State}
    (check : decodesTo decoded expected = true) : decoded = some expected := by
  revert check
  cases decoded with
  | none => intro check; cases check
  | some state =>
    intro check
    have found : (ObjectiveDemandStateEquality.state equalityFuel state expected).isSome = true := check
    obtain ⟨proof, _⟩ := Option.isSome_iff_exists.mp found
    rw [proof.down]

/-- `.nat 9`'s pinned bits decode, under `.nat 7`'s tables, to `initial (.nat 7)`. -/
theorem foreign_code_represents_nat7 :
    decodesTo (externalTables nat7 nat9.initialBits) (ObjectiveBendDemandMachine.initial (.nat 7)) = true := by
  native_decide

def foreignTick : Array Bool := (next? graph nat9.initialBits).getD #[]
theorem foreign_step : next? graph nat9.initialBits = some foreignTick := nat9_step1

def returnedNatural : Control → Option Nat
  | .returned (.natural n) => some n
  | _ => none

theorem foreign_returns_nine :
    (externalTables nat7 foreignTick).map (fun state => returnedNatural state.control) =
      some (some 9) := by
  native_decide

/-- An accepted row of the actual graph, pinned to inputs the earlier relation
represents as `initial (.nat 7)`, that is not a stepRaw trace of `.nat 7`. -/
theorem externalTables_not_refinement :
    ¬ ∃ refinement : PackedRefinement graph,
      ∀ bits state, refinement.represents bits state ↔ externalTables nat7 bits = some state := by
  rintro ⟨refinement, agrees⟩
  obtain ⟨output, evaluated, handled, following⟩ := accepted_of_next foreign_step
  have start : refinement.represents nat9.initialBits (ObjectiveBendDemandMachine.initial (.nat 7)) :=
    (agrees _ _).mpr (decodesTo_sound foreign_code_represents_nat7)
  obtain ⟨next, edge, represented⟩ := refinement.acceptedStep evaluated handled start
  have decoded : externalTables nat7 foreignTick = some next := by
    rw [following]
    exact (agrees _ _).mp represented
  have nine := foreign_returns_nine
  rw [decoded] at nine
  have nextNine : returnedNatural next.control = some 9 := Option.some.inj nine
  cases edge with
  | administrative => exact absurd nextNine (by decide)
  | transition => exact absurd nextNine (by decide)

/-- The two decoders disagree on the same bits: the earlier one reads `.nat 9`'s
bits as `.nat 7`'s initial state, the corrected one as `.nat 9`'s. -/
theorem decoders_disagree :
    externalTables nat7 nat9.initialBits = some (ObjectiveBendDemandMachine.initial (.nat 7)) ∧
    regionCodec.decode nat9.initialBits = some (ObjectiveBendDemandMachine.initial (.nat 9)) :=
  ⟨decodesTo_sound foreign_code_represents_nat7, region_binds_code⟩

#assert_axioms related_sound
#assert_axioms afterChecked_sound
#assert_axioms stepChecked_sound
#assert_axioms accepted_of_next
#assert_axioms acceptedRun_of_next
#assert_axioms reachDecode_some
#assert_axioms decodesTo_sound
#assert_axioms orbit_head
#assert_compiled prepared_graph
#assert_compiled regionCodec_initial
#assert_axioms layoutCodec_binds
#assert_compiled layoutCodec_not_foreign
#assert_compiled graph_built
#assert_compiled prepared_nat7
#assert_compiled reach_certified
#assert_compiled nat7_initial
#assert_compiled region_binds_code
#assert_compiled nat7_step1
#assert_compiled nat7_step2
#assert_compiled nat7_complete_stutters
#assert_compiled nat7_run
#assert_compiled nat7_read
#assert_compiled nat7_observes
#assert_compiled nat7_reaches_source_meaning
#assert_compiled nat9_reaches_source_meaning
#assert_compiled label_reaches_source_meaning
#assert_compiled foreign_code_represents_nat7
#assert_compiled foreign_returns_nine
#assert_compiled externalTables_not_refinement
#assert_compiled decoders_disagree
end Minidregg.Assurance.ObjectiveZkLiteralInstance
