import Assurance.ObjectiveBendProofSource

/- Statement audit of `ObjectiveBendProofSource.PackedRefinement` and its corrected
form. Two teeth and one corrected statement:

* `trivialRefinement` — every network inhabits `PackedRefinement` (the administrative
  stutter accepts any relation closed under "same state"). The structure alone
  certifies nothing.
* `trivial_readSound_silent` — with that inhabitant, the receivers' `readSound`
  premise forces the free `readObservation` to answer `none` everywhere, so the
  theorem's source-meaning conjunct is vacuous. Content lives in the conjunction
  (acceptedStep ∧ initial ∧ readSound) and in WHICH reader is supplied.
* `PackedCodec` — a functional decoder; the result reader is DERIVED from it, so
  `readSound` becomes a theorem (`PackedCodec.read_sound`). `constantCodec` shows the
  one remaining obligation: the decoder must be the one the verifier binds to the
  public result wires (a constant decoder is a codec that never reads). -/
namespace Minidregg.Assurance.ObjectiveZkRefinementAudit
open Minidregg.Compiler Minidregg.Theory
open ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandAdequacy
open ObjectiveBendDemandInvariant
open ObliviousNetwork ObliviousUnroll
open Minidregg.Assurance.ObjectiveBendProofSource
set_option autoImplicit false

/-- Every network inhabits `PackedRefinement`. -/
def trivialRefinement (network : Network) : PackedRefinement network where
  represents := fun _ _ => True
  acceptedStep := by
    intro _ _ state _ _ _
    exact ⟨state, .administrative state, trivial⟩

theorem packedRefinement_always_inhabited (network : Network) :
    Nonempty (PackedRefinement network) :=
  ⟨trivialRefinement network⟩

/-- With the trivial relation, any reader that meets the receivers' `readSound`
premise is silent on every bit array: the end-to-end conclusion is then vacuous. -/
theorem trivial_readSound_silent (network : Network)
    (readObservation : Array Bool → Option Observation)
    (readSound : ∀ bits state observation, (trivialRefinement network).represents bits state →
      readObservation bits = some observation →
      state.control = .complete (observationRuntime observation)) :
    ∀ bits, readObservation bits = none := by
  intro bits
  cases read : readObservation bits with
  | none => rfl
  | some observation =>
    have wrong := readSound bits (ObjectiveBendDemandMachine.initial (.nat 0)) observation trivial read
    simp [ObjectiveBendDemandMachine.initial] at wrong

/-- Ground observation of a completed control. -/
def valueObservation : RuntimeValue → Option Observation
  | .natural n => some (.natural n)
  | .boolean b => some (.boolean b)
  | .label s => some (.label s)
  | _ => none

def controlObservation : Control → Option Observation
  | .complete value => valueObservation value
  | _ => none

theorem valueObservation_sound : ∀ {value : RuntimeValue} {observation : Observation},
    valueObservation value = some observation → value = observationRuntime observation
  | .natural _, _, read => by
      simp only [valueObservation, Option.some.injEq] at read; subst read; rfl
  | .boolean _, _, read => by
      simp only [valueObservation, Option.some.injEq] at read; subst read; rfl
  | .label _, _, read => by
      simp only [valueObservation, Option.some.injEq] at read; subst read; rfl
  | .closure _ _, _, read => by simp [valueObservation] at read
  | .record _, _, read => by simp [valueObservation] at read
  | .specification _ _, _, read => by simp [valueObservation] at read
  | .prototype _ _, _, read => by simp [valueObservation] at read

theorem controlObservation_sound : ∀ {control : Control} {observation : Observation},
    controlObservation control = some observation →
    control = .complete (observationRuntime observation)
  | .complete _, _, read => congrArg Control.complete (valueObservation_sound read)
  | .evaluate _ _, _, read => by simp [controlObservation] at read
  | .enter _, _, read => by simp [controlObservation] at read
  | .blackhole _, _, read => by simp [controlObservation] at read
  | .returned _, _, read => by simp [controlObservation] at read
  | .refused _, _, read => by simp [controlObservation] at read

/-- Corrected statement: the physical state is read by ONE function. -/
structure PackedCodec (network : Network) where
  decode : Array Bool → Option State
  acceptedStep : ∀ {input output : Array Bool} {state : State},
    network.evaluate input = some output → output[0]? = some true →
    decode input = some state → ∃ next, Macrostep state next ∧
      decode (output.extract 1 output.size) = some next

def PackedCodec.toRefinement {network : Network} (codec : PackedCodec network) :
    PackedRefinement network where
  represents bits state := codec.decode bits = some state
  acceptedStep := by
    intro _ _ _ evaluated handled represented
    exact codec.acceptedStep evaluated handled represented

/-- The reader is derived from the decoder, never supplied beside it. -/
def PackedCodec.read {network : Network} (codec : PackedCodec network) (bits : Array Bool) :
    Option Observation :=
  (codec.decode bits).bind (fun state => controlObservation state.control)

/-- `readSound` of the existing receivers, now a theorem. -/
theorem PackedCodec.read_sound {network : Network} (codec : PackedCodec network) :
    ∀ bits state observation, codec.toRefinement.represents bits state →
      codec.read bits = some observation →
      state.control = .complete (observationRuntime observation) := by
  intro bits state observation represented read
  have decoded : codec.decode bits = some state := represented
  unfold PackedCodec.read at read
  rw [decoded] at read
  exact controlObservation_sound (control := state.control) read

/-- End to end at the source receiver, with no free relation and no free reader. -/
theorem PackedCodec.observes_source {network : Network} (codec : PackedCodec network)
    {ticks : Nat} {input output : Array Bool} {source : Term} (closed : Scoped 0 source)
    (run : AcceptedRun network ticks input output)
    (start : codec.decode input = some (ObjectiveBendDemandMachine.initial source))
    {observation : Observation} (read : codec.read output = some observation) :
    Evaluates source (observationTerm observation) :=
  completed_observation codec.toRefinement closed run start observation
    (fun state represented => codec.read_sound output state observation represented read)

/-- Tooth for the corrected statement: a constant decoder is a codec whose reader
never answers. The decoder must be the verifier's own result codec. -/
def constantCodec (network : Network) (state : State) : PackedCodec network where
  decode := fun _ => some state
  acceptedStep := by
    intro _ _ current _ _ decoded
    have same : state = current := Option.some.inj decoded
    subst same
    exact ⟨state, .administrative state, rfl⟩

theorem constantCodec_initial_silent (network : Network) (source : Term) (bits : Array Bool) :
    (constantCodec network (ObjectiveBendDemandMachine.initial source)).read bits = none := by
  simp [PackedCodec.read, constantCodec, ObjectiveBendDemandMachine.initial, controlObservation]

#assert_axioms packedRefinement_always_inhabited
#assert_axioms trivial_readSound_silent
#assert_axioms valueObservation_sound
#assert_axioms controlObservation_sound
#assert_axioms PackedCodec.read_sound
#assert_axioms PackedCodec.observes_source
#assert_axioms constantCodec_initial_silent
end Minidregg.Assurance.ObjectiveZkRefinementAudit
