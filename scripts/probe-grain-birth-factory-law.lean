import Pred.Core

namespace Minidregg.GrainBirthFactoryLawProbe

/-- The installed fixture law lets the owner use the factory, and lets the
worker observe it or use the explicit grain-backed birth mode. -/
def fixtureFactoryLaw : Minidregg.Pred.Pred :=
  .any [
    .eq "request/subject" 7,
    .all [
      .eq "request/subject" 8,
      .any [
        .eq "request/verb" 1,
        .eq "birth/mode/grain-backed" 1]]]

/-- For every old/new policy state, a worker's bare mutation cannot satisfy
the installed factory law when its projection lacks the composite mode slot.
The native public refusal intentionally hides which policy check failed. -/
theorem worker_bare_factory_mutation_refused
    (old new : Minidregg.Pred.State)
    (subject : new.get "request/subject" = some 8)
    (verb : new.get "request/verb" = some 2)
    (bare : new.get "birth/mode/grain-backed" = none) :
    Minidregg.Pred.eval fixtureFactoryLaw old new = false := by
  simp [fixtureFactoryLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith,
    subject, verb, bare]

theorem owner_factory_allowed (old new : Minidregg.Pred.State)
    (subject : new.get "request/subject" = some 7) :
    Minidregg.Pred.eval fixtureFactoryLaw old new = true := by
  simp [fixtureFactoryLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith,
    subject]

theorem worker_grain_backed_factory_allowed (old new : Minidregg.Pred.State)
    (subject : new.get "request/subject" = some 8)
    (mode : new.get "birth/mode/grain-backed" = some 1) :
    Minidregg.Pred.eval fixtureFactoryLaw old new = true := by
  simp [fixtureFactoryLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith,
    subject, mode]

#print axioms worker_bare_factory_mutation_refused
#print axioms owner_factory_allowed
#print axioms worker_grain_backed_factory_allowed

end Minidregg.GrainBirthFactoryLawProbe
