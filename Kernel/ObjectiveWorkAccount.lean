/- The WHOLE-REQUEST work account of an Objective turn (GPT-6 row E).

Every stage a turn costs the validator is measured in a declared unit, declared in the
turn's envelope (`ObjectiveInvocationClaim.Capacity`) and priced by the one tariff
(`ObjectiveTariff.Tariff.workOf`, edition 4):

| stage        | unit                                          | declared field  |
|--------------|-----------------------------------------------|-----------------|
| `frontEnd`   | source bytes of the package the front end replays (parse, elaborate, lower) | `replayBytes` |
| `core`       | bytes of the typed core the replay generates  | `coreBytes`     |
| `check`      | type-checker fuel                             | `typeFuel`      |
| `execution`  | source ticks of the run                       | `sourceTicks`   |
| `extraction` | forcing ticks of the Plan/result extraction   | `extractTicks`  |
| `output`     | bytes of the extracted output                 | `outputBytes`   |
| `domain`     | reads of the turn end's invariant-domain judgment (`ObjectiveDomain.judgeDomains`) | `domainWork` |

Before this module the front end ran on every turn (`ObjectiveActivity.loadProgram`) priced by
nothing: a 1 KB package and a 200 KB package cost a birth the same. The two front-end stages
are what the kernel can know BEFORE it replays: the stored package's source bytes and the
stored artifact's typed core (which an admitted replay must generate byte for byte). So
`uncovered` is computed from the decoded stored pair alone, and a turn whose envelope does not
cover it is refused by name (`ObjectiveActivity.Refusal.workUncovered`) before the replay runs.
The remaining stages are bounded by the budgets the kernel hands the checker, the machine and
the extractor, each compared with the envelope before anything runs (`Config.covers`,
`extractUncovered`). The domain judgment runs last, at the turn's end, and its units are
compared with the charged envelope's `domainWork` there (`ActivitySeatEnd.finish`,
`domainUncovered`, `finish_domain_covered`). -/
import Kernel.ObjectiveTariff
import Compiler.ObjectiveSourcePackage
import Compiler.ObjectiveBendSourceArtifact

namespace Minidregg.Kernel.ObjectiveWorkAccount
open Minidregg.Compiler
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)
set_option autoImplicit false

/-- The stages of one Objective turn, in the order the receiver runs them. -/
inductive Stage where
  | frontEnd
  | core
  | check
  | execution
  | extraction
  | output
  | domain
  deriving DecidableEq, Repr

/-- What an envelope declares for each stage. -/
def declared (envelope : Capacity) : Stage → Nat
  | .frontEnd => envelope.replayBytes
  | .core => envelope.coreBytes
  | .check => envelope.typeFuel
  | .execution => envelope.sourceTicks
  | .extraction => envelope.extractTicks
  | .output => envelope.outputBytes
  | .domain => envelope.domainWork

/-- The front end's input: every module source the replay decodes and parses
(`ObjectiveBendPublication.replayModule`). -/
def sourceBytes (package : ObjectiveSourcePackage.Package) : Nat :=
  (package.modules.map fun m => m.source.length).sum

/-- The front-end stages of a stored pair, known before the replay. -/
def frontEndNeeds (package : ObjectiveSourcePackage.Package) (artifact : ObjectiveBendSourceArtifact.Artifact) :
    Stage → Nat
  | .frontEnd => sourceBytes package
  | .core => artifact.typedCore.length
  | _ => 0

/-- The first front-end stage the envelope does not cover, with what it needs and what is declared. -/
def uncovered (package : ObjectiveSourcePackage.Package) (artifact : ObjectiveBendSourceArtifact.Artifact)
    (envelope : Capacity) : Option (Stage × Nat × Nat) :=
  [Stage.frontEnd, Stage.core].findSome? fun stage =>
    let needed := frontEndNeeds package artifact stage
    if needed ≤ declared envelope stage then none else some (stage, needed, declared envelope stage)

/-- A covered stored pair: both front-end stages within the envelope. -/
theorem uncovered_none {package : ObjectiveSourcePackage.Package} {artifact : ObjectiveBendSourceArtifact.Artifact}
    {envelope : Capacity} (covered : uncovered package artifact envelope = none) :
    sourceBytes package ≤ envelope.replayBytes ∧ artifact.typedCore.length ≤ envelope.coreBytes := by
  unfold uncovered at covered
  simp only [List.findSome?_cons, List.findSome?_nil] at covered
  by_cases a : sourceBytes package ≤ envelope.replayBytes
  · by_cases b : artifact.typedCore.length ≤ envelope.coreBytes
    · exact ⟨a, b⟩
    · simp [frontEndNeeds, declared, a, b] at covered
  · simp [frontEndNeeds, declared, a] at covered

/-- A refused stored pair names a front-end stage whose need exceeds the declaration. -/
theorem uncovered_some {package : ObjectiveSourcePackage.Package} {artifact : ObjectiveBendSourceArtifact.Artifact}
    {envelope : Capacity} {stage : Stage} {needed given : Nat}
    (refused : uncovered package artifact envelope = some (stage, needed, given)) :
    needed = frontEndNeeds package artifact stage ∧ given = declared envelope stage ∧ given < needed := by
  unfold uncovered at refused
  simp only [List.findSome?_cons, List.findSome?_nil] at refused
  by_cases a : sourceBytes package ≤ envelope.replayBytes
  · by_cases b : artifact.typedCore.length ≤ envelope.coreBytes
    · simp [frontEndNeeds, declared, a, b] at refused
    · simp [frontEndNeeds, declared, a, b] at refused
      obtain ⟨rfl, rfl, rfl⟩ := refused
      exact ⟨rfl, rfl, by omega⟩
  · simp [frontEndNeeds, declared, a] at refused
    obtain ⟨rfl, rfl, rfl⟩ := refused
    exact ⟨rfl, rfl, by omega⟩

/-- **Every stage is priced.** Declaring one more unit of ANY stage costs at least its rate
more: no stage is outside the price (a stage left out of `Tariff.workOf` has rate 0 here and
fails the companion instance `workOf_prices_every_stage_unit`). -/
theorem workOf_stage_step (t : ObjectiveTariff.Tariff) (c : Capacity) :
    t.workOf { c with replayBytes := c.replayBytes + 1 } = t.workOf c + t.replayBytes ∧
    t.workOf { c with coreBytes := c.coreBytes + 1 } = t.workOf c + t.coreBytes ∧
    t.workOf { c with typeFuel := c.typeFuel + 1 } = t.workOf c + t.typeFuel ∧
    t.workOf { c with sourceTicks := c.sourceTicks + 1 } = t.workOf c + t.sourceTicks ∧
    t.workOf { c with extractTicks := c.extractTicks + 1 } = t.workOf c + t.extractTicks ∧
    t.workOf { c with outputBytes := c.outputBytes + 1 } = t.workOf c + t.outputBytes ∧
    t.workOf { c with domainWork := c.domainWork + 1 } = t.workOf c + t.domainWork := by
  simp only [ObjectiveTariff.Tariff.workOf, Nat.mul_add, Nat.mul_one]
  omega

/-- The rate a tariff charges per declared unit of a stage. -/
def rate (t : ObjectiveTariff.Tariff) : Stage → Nat
  | .frontEnd => t.replayBytes
  | .core => t.coreBytes
  | .check => t.typeFuel
  | .execution => t.sourceTicks
  | .extraction => t.extractTicks
  | .output => t.outputBytes
  | .domain => t.domainWork

/-- The envelope declaring one unit of `stage` and nothing else. -/
def unitOf : Stage → Capacity
  | .frontEnd => { ObjectiveTariff.zeroCapacity with replayBytes := 1 }
  | .core => { ObjectiveTariff.zeroCapacity with coreBytes := 1 }
  | .check => { ObjectiveTariff.zeroCapacity with typeFuel := 1 }
  | .execution => { ObjectiveTariff.zeroCapacity with sourceTicks := 1 }
  | .extraction => { ObjectiveTariff.zeroCapacity with extractTicks := 1 }
  | .output => { ObjectiveTariff.zeroCapacity with outputBytes := 1 }
  | .domain => { ObjectiveTariff.zeroCapacity with domainWork := 1 }

/-- One declared unit of any stage costs exactly the base plus that stage's rate. -/
theorem workOf_unitOf (t : ObjectiveTariff.Tariff) (stage : Stage) :
    t.workOf (unitOf stage) = t.base + rate t stage := by
  cases stage <;> simp [unitOf, rate, ObjectiveTariff.Tariff.workOf, ObjectiveTariff.zeroCapacity]

/-- An inhabitant: a tariff with a positive rate on every stage prices each stage's unit above
the empty envelope (the premise-free statement above is not vacuous). -/
def Tariff.everyStage : ObjectiveTariff.Tariff := ⟨ObjectiveTariff.tariffVersion,1,1,1,0,0,0,1,1,0,1,1,1⟩

theorem workOf_prices_every_stage_unit (stage : Stage) :
    Tariff.everyStage.workOf ObjectiveTariff.zeroCapacity < Tariff.everyStage.workOf (unitOf stage) := by
  cases stage <;> decide

/-! ### The turn's front-end meter

A turn may replay MANY packages: every frame of a call tree loads its object's method, a send
to an object checks that the target's method is deliverable, an upgrade lowers a migration and
re-births activities. The envelope's `replayBytes` and `coreBytes` are a BUDGET for all of
them, not a cover of each: every replay DRAWS its source bytes and the typed-core bytes it
generates from the one meter, refused by name when the budget left is short. -/

/-- The front end's work a turn has drawn, against what its paying envelope declared. -/
structure Meter where
  /-- The source bytes the envelope declared (`Capacity.replayBytes`). -/
  replayBytes : Nat
  /-- The typed-core bytes the envelope declared (`Capacity.coreBytes`). -/
  coreBytes : Nat
  /-- Every draw, in order: the source bytes a replay parsed and the core bytes it generated. -/
  draws : List (Nat × Nat)
  deriving Repr, DecidableEq

/-- A fresh meter over a paying envelope. -/
def Meter.start (envelope : Capacity) : Meter := ⟨envelope.replayBytes, envelope.coreBytes, []⟩

/-- The source bytes drawn so far. -/
def Meter.source (m : Meter) : Nat := (m.draws.map Prod.fst).sum

/-- The typed-core bytes drawn so far. -/
def Meter.core (m : Meter) : Nat := (m.draws.map Prod.snd).sum

/-- **Draw one replay's work**, refused naming the stage, what it needs and what the budget has
left when it does not fit. -/
def Meter.draw (m : Meter) (source core : Nat) : Except (Stage × Nat × Nat) Meter :=
  if m.replayBytes < m.source + source then .error (.frontEnd, source, m.replayBytes - m.source)
  else if m.coreBytes < m.core + core then .error (.core, core, m.coreBytes - m.core)
  else .ok { m with draws := m.draws ++ [(source, core)] }

/-- Replay a list of draws on a meter, in order (refused at the first that does not fit). -/
def Meter.drawAll (m : Meter) : List (Nat × Nat) → Except (Stage × Nat × Nat) Meter
  | [] => .ok m
  | (source, core) :: rest => do (← m.draw source core).drawAll rest

/-- The draws a meter made after another (its suffix past `before`'s draws). -/
def Meter.since (m before : Meter) : List (Nat × Nat) := m.draws.drop before.draws.length

/-- The meter's draws are within its budget. -/
def Meter.Within (m : Meter) : Prop := m.source ≤ m.replayBytes ∧ m.core ≤ m.coreBytes

theorem Meter.start_within (envelope : Capacity) : (Meter.start envelope).Within := by
  simp [Meter.start, Meter.Within, Meter.source, Meter.core]

/-- **A draw stays within the budget**: an admitted draw keeps the declared budget, appends
exactly its own work, and leaves the total drawn within what the envelope declared. -/
theorem Meter.draw_ok {m m' : Meter} {source core : Nat} (drawn : m.draw source core = .ok m') :
    m'.replayBytes = m.replayBytes ∧ m'.coreBytes = m.coreBytes ∧ m'.draws = m.draws ++ [(source, core)] ∧
      m'.Within := by
  unfold Meter.draw at drawn
  split at drawn
  · cases drawn
  · split at drawn
    · cases drawn
    · cases drawn
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> simp [Meter.source, Meter.core] at * <;> omega

/-- A refused draw names a stage whose need exceeds what the budget has left. -/
theorem Meter.draw_refused {m : Meter} {source core : Nat} {stage : Stage} {needed left : Nat}
    (refused : m.draw source core = .error (stage, needed, left)) :
    (stage = .frontEnd ∧ needed = source ∧ left = m.replayBytes - m.source ∧ m.replayBytes < m.source + source) ∨
    (stage = .core ∧ needed = core ∧ left = m.coreBytes - m.core ∧ m.coreBytes < m.core + core) := by
  unfold Meter.draw at refused
  split at refused
  · cases refused; exact .inl ⟨rfl, rfl, rfl, by assumption⟩
  · split at refused
    · cases refused; exact .inr ⟨rfl, rfl, rfl, by assumption⟩
    · cases refused

/-- Draws compose: a meter reached from another by admitted draws extends its draw list and keeps
its budget (the shape every replay site's draws take, over a whole turn). -/
inductive Meter.Reaches : Meter → Meter → Prop
  | refl (m : Meter) : Meter.Reaches m m
  | draw {m m' m'' : Meter} {source core : Nat} :
      Meter.Reaches m m' → m'.draw source core = .ok m'' → Meter.Reaches m m''

/-- **The whole turn's front end is within its envelope**: every meter reached by admitted
draws from a fresh meter over `envelope` has drawn, summed over all its replays, at most the
source bytes and the typed-core bytes the envelope declared. -/
theorem Meter.Reaches.within {envelope : Capacity} {m : Meter} (reached : Meter.Reaches (Meter.start envelope) m) :
    m.source ≤ envelope.replayBytes ∧ m.core ≤ envelope.coreBytes ∧
      m.replayBytes = envelope.replayBytes ∧ m.coreBytes = envelope.coreBytes := by
  induction reached with
  | refl => simp [Meter.start, Meter.source, Meter.core]
  | draw _ drawn ih =>
    obtain ⟨r, c, _, w⟩ := Meter.draw_ok drawn
    obtain ⟨_, _, r0, c0⟩ := ih
    have r' := r.trans r0
    have c' := c.trans c0
    exact ⟨r' ▸ w.1, c' ▸ w.2, r', c'⟩

/-- An instance: two replays of a 10-byte package with a 4-byte core fit a budget of 20 source
and 8 core bytes; a third is refused naming the source stage with nothing left. -/
theorem meter_third_replay_refused :
    ((Meter.start { ObjectiveTariff.zeroCapacity with replayBytes := 20, coreBytes := 8 }).draw 10 4 >>=
      (·.draw 10 4) >>= (·.draw 10 4)) = .error (.frontEnd, 10, 0) := by decide

/-! ### Instances: the refusal and its plant -/

/-- A ten-byte one-module package whose artifact carries a four-byte typed core. -/
def sample : ObjectiveSourcePackage.Package :=
  ⟨"front-end", [⟨"m", [1,2,3,4,5,6,7,8,9,10], []⟩], 0, "d"⟩
def sampleArtifact : ObjectiveBendSourceArtifact.Artifact :=
  ⟨⟨0⟩, "d", [1,2,3,4], ⟨0⟩, ⟨0⟩, []⟩

/-- **An oversized package is refused by its front-end stage**: an envelope declaring 3 source
bytes against a 10-byte package is refused naming `frontEnd`, 10 needed, 3 declared (plant: leave
`frontEnd` out of `uncovered`'s stages, or price it at 0, and this instance goes red). -/
theorem frontEnd_refuses_oversized :
    uncovered sample sampleArtifact { ObjectiveTariff.zeroCapacity with replayBytes := 3, coreBytes := 4 } =
      some (.frontEnd, 10, 3) := by decide

/-- ... and a generated core larger than declared is refused naming `core`. -/
theorem core_refuses_oversized :
    uncovered sample sampleArtifact { ObjectiveTariff.zeroCapacity with replayBytes := 10, coreBytes := 3 } =
      some (.core, 4, 3) := by decide

/-- ... while an envelope declaring exactly the stored sizes is covered (the premise of
`uncovered_none` is inhabited). -/
theorem exact_envelope_covered :
    uncovered sample sampleArtifact { ObjectiveTariff.zeroCapacity with replayBytes := 10, coreBytes := 4 } =
      none := by decide

#assert_axioms Meter.start_within
#assert_axioms Meter.draw_ok
#assert_axioms Meter.draw_refused
#assert_axioms Meter.Reaches.within
#assert_axioms meter_third_replay_refused
#assert_axioms frontEnd_refuses_oversized
#assert_axioms core_refuses_oversized
#assert_axioms exact_envelope_covered
#assert_axioms uncovered_none
#assert_axioms uncovered_some
#assert_axioms workOf_stage_step
#assert_axioms workOf_unitOf
#assert_axioms workOf_prices_every_stage_unit
end Minidregg.Kernel.ObjectiveWorkAccount
