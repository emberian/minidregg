/- A package's `law` declarations, enforced by the object kernel's turns.

A package declares `law NAME: EXPR` (`Compiler.ObjectiveBendLaw`); the front end reads the laws
of its entry module, the source artifact carries them and its identity commits them, and the
receiver's replay recomputes them (`ObjectiveBendPublication.replayAccept`). This module states
what the object kernel does with them:

* **Installed from the pin, never from a request** (`Creation.package_laws`,
  `Adoption.package_laws`): a creation and an ADOPT read the laws of the pinned (next) package
  from its package cell (`packageLawsAt`), refuse a law reading a field the declared state type
  does not hold (`lawField`), and install exactly those laws.
* **Enforced** (`package_law_enforced` and its turn forms): every write of the declared state that
  a birth or a delivery commits, and an object's seed, satisfies every law of the package in the
  law's own meaning (`LawExpr.denote`, over the data).
* **Not removable** (`package_law_not_removable`): the turns that rewrite an object's record keep
  its package laws, except MIGRATE, which installs the laws ADOPT read for the next pin.
* **Teeth** (`capped_tally_teeth`): the laws of `tests/objective-native/CappedTally.obend`
  (`cap: new.total <= 1000`, `grows: monotone(total)`) refuse a write past the cap and a write
  that lowers the total, each naming the package law's clause, and admit an honest write; the
  same writes without the package laws are admitted. -/
import Kernel.ObjectLaw
import Kernel.ObjectiveActivityUpgrade

namespace Minidregg.Kernel.ObjectLawEnforced
open Minidregg.Kernel.ObjectRecord
open Minidregg.Kernel.ObjectLaw
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Compiler.ObjectiveBendLaw
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.ObjectiveActivityWire (Bytes)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Pred (Pred)
set_option autoImplicit false

/-! ## Installed from the pin -/

/-- **An admitted creation installs exactly the pinned package's laws**: the record it commits
(read back from the post-state) carries the laws `packageLawsAt` reads from the pin's package
cell, every field they read is a top-level scalar field of the declared state type, and a seed
satisfies every one of them. -/
theorem Creation.package_laws {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : CreateRequest} (created : Creation config snapshot height request) :
    objectAt config (afterPosts snapshot created.posts) request.object = some (request.record created.laws) ∧
      (request.record created.laws).packageLaws = created.laws ∧
      packageLawsAt config snapshot request.pin = .ok created.laws ∧
      lawFieldIssue request.stateType created.laws = none ∧
      ∀ seed, request.seed = some seed →
        ∀ law ∈ created.laws, law.2.denote (seedFacts request height) none seed = true :=
  ⟨created.object_installed, rfl, created.lawsExact, created.fieldsKnown,
    fun seed seeded => package_law_enforced_seed _ _ _ (created.seedJudged seed seeded)⟩

/-- **An admitted ADOPT pends exactly the next package's laws**, read from the next pin's
package cell, with every field they read a top-level scalar field of the next state type. -/
theorem Adoption.package_laws {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AdoptRequest} (adopted : Adoption config snapshot height request) :
    (request.pending height adopted.laws).packageLaws = adopted.laws ∧
      packageLawsAt config snapshot request.pin = .ok adopted.laws ∧
      lawFieldIssue request.stateType adopted.laws = none :=
  ⟨rfl, adopted.lawsExact, adopted.fieldsKnown⟩

/-! ## Enforced on the turns -/

/-- **`package_law_enforced`, birth**: the write a birth commits satisfies every law of the
object's package. -/
theorem Birth.package_law_enforced {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request)
    (written : StateWritten) (wrote : born.yielded.bind YieldCommit.written = some written) :
    ∃ object, readObject config snapshot request.object = .ok (some object) ∧
      ∀ law ∈ object.packageLaws,
        law.2.denote (factsOf request.subject height request.object request.factsTurn (some request.pin))
          (written.before.map ObjectState.value) written.after.value = true := by
  obtain ⟨object, read, _, admitted⟩ := born.write_judged written wrote
  exact ⟨object, read, ObjectLaw.package_law_enforced object _ _ _ admitted⟩

/-- **`package_law_enforced`, delivery**: the write a delivery commits satisfies every law of the
object's package. -/
theorem Delivery.package_law_enforced {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request)
    (written : StateWritten) (wrote : delivery.yielded.bind YieldCommit.written = some written) :
    ∃ object, readObject config snapshot delivery.record.object = .ok (some object) ∧
      ∀ law ∈ object.packageLaws,
        law.2.denote (factsOf delivery.record.escrow.payer height delivery.record.object 2
          (some delivery.record.pin)) (written.before.map ObjectState.value) written.after.value = true := by
  obtain ⟨object, read, admitted⟩ := delivery.write_judged written wrote
  exact ⟨object, read, ObjectLaw.package_law_enforced object _ _ _ admitted⟩

/-! ## Not removable -/

theorem recount_packageLaws (record : ObjectRecord) (pin activity : Digest) (before after : Bool) :
    (recount record pin activity before after).packageLaws = record.packageLaws := by
  unfold recount ObjectRecord.retain ObjectRecord.release
  split
  · exact bump_packageLaws _ _ _
  · split
    · exact bump_packageLaws _ _ _
    · rfl

/-- **`package_law_not_removable`.** The record writes of the object kernel are the creation's
(`Creation.package_laws`: the pinned package's laws), the counters' (`recount`, and a birth's
`birthCount`), ADOPT's (`adoptedRecord`) and MIGRATE's (`successor`). All but MIGRATE keep the
package laws; MIGRATE installs the pending ones, which ADOPT read from the next pin's package
cell (`Adoption.package_laws`). No request field carries package laws, so no turn can omit,
loosen or replace them. -/
theorem package_law_not_removable :
    (∀ (record : ObjectRecord) (pin activity : Digest) (before after : Bool),
      (recount record pin activity before after).packageLaws = record.packageLaws) ∧
    (∀ (record : ObjectRecord) (request : BirthRequest) (activity : Digest) (awaits : Bool),
      (birthCount record request activity awaits).packageLaws = record.packageLaws) ∧
    (∀ (record : ObjectRecord) (next : Pending) (deadline : Nat),
      (adoptedRecord record next deadline).packageLaws = record.packageLaws) ∧
    (∀ (record : ObjectRecord) (next : Pending), (record.successor next).packageLaws = next.packageLaws) := by
  refine ⟨recount_packageLaws, ?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
  intro record request activity awaits
  unfold birthCount
  rw [recount_packageLaws]
  split
  · rfl
  · exact bump_packageLaws _ _ _

/-! ## Teeth: the capped tally

The laws the front end reads from `tests/objective-native/CappedTally.obend` (the executable
check `tests/objective-native/PackageLaw.lean` compares them with these, byte for byte through
the published artifact). The creator's law is the empty conjunction (it admits everything). -/

def cappedLaws : List (String × LawExpr) :=
  [("cap", .leC (.field "total") 1000), ("grows", .monotone "total")]

def tallyType : Minidregg.Theory.ObjectiveBendTypes.Ty := .field "total" .natural .emptyRow

def cappedRecord (laws : List (String × LawExpr)) : ObjectRecord :=
  ⟨⟨1⟩, ⟨7⟩, tallyType, 1, Pred.all [], laws, .frozen, 0, 0, 0, 0, .steady, []⟩

def tallyAt (total : Nat) : Data := .record [("total", .natural total)]

def writeFacts : Facts := ⟨some ⟨40⟩, 5, 1, 1, none, some 7⟩

/-- **Capped-tally teeth, both ways.** Under the package laws: 5 → 7 is admitted; 5 → 1001 is
refused at the `cap` clause (`[1, 0]`: the package laws are the effective law's second clause),
reading 1001; 7 → 5 is refused at the `grows` clause (`[1, 1]`), reading 7 then 5. Without the
package laws (the same object, the same permissive creator law) both bad writes are admitted, so
the refusals are the package's. A state type without `total` is refused at creation naming it. -/
theorem capped_tally_teeth :
    accepted (admitWrite (cappedRecord cappedLaws) writeFacts (some (tallyAt 5)) (tallyAt 7)) = true ∧
      leafOf (admitWrite (cappedRecord cappedLaws) writeFacts (some (tallyAt 5)) (tallyAt 1001)) =
        some ⟨[1, 0], .le "state/total" 1000, some 5, some 1001⟩ ∧
      leafOf (admitWrite (cappedRecord cappedLaws) writeFacts (some (tallyAt 7)) (tallyAt 5)) =
        some ⟨[1, 1], .monotone "state/total", some 7, some 5⟩ ∧
      accepted (admitWrite (cappedRecord []) writeFacts (some (tallyAt 5)) (tallyAt 1001)) = true ∧
      accepted (admitWrite (cappedRecord []) writeFacts (some (tallyAt 7)) (tallyAt 5)) = true ∧
      lawFieldIssue (.field "count" .natural .emptyRow) cappedLaws = some "total" ∧
      lawFieldIssue tallyType cappedLaws = none := by
  decide +kernel

#assert_axioms Creation.package_laws
#assert_axioms Adoption.package_laws
#assert_axioms Birth.package_law_enforced
#assert_axioms Delivery.package_law_enforced
#assert_axioms recount_packageLaws
#assert_axioms package_law_not_removable
#assert_axioms capped_tally_teeth
end Minidregg.Kernel.ObjectLawEnforced
