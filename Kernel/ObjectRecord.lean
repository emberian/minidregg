/- The object record: what an object IS to the kernel, and the one judgment every
write of its declared state passes.

An object is a native resource (`id`, a cell the authority layer issues
capabilities on; never a package hash). Its record names:

* `pin`: the package its new activities and calls run (`package`, the
  `ObjectiveBendSourceArtifact.identity` of a published package);
* `schemaVersion`: the version of the declared-state schema, bumped only by a
  migration (it is not the write counter of the state cell);
* `law`: the decidable predicate (`Pred`) that judges every write of the
  declared state, over the projected old and new views plus the request facts.
  The judged law is `ObjectRecord.effectiveLaw`: `all [pinClause pin, law]`, the
  kernel's package pin FIRST, which the creator's `law` can neither omit nor
  loosen (the clause is not stored, it is derived from `pin`);
* `upgrade`: who may re-pin the object, as a policy that may only tighten;
* `continuity`: bumped by every re-pin and every law change;
* `payer`: the Book account that funds the record and the state cell. The payer
  is never authority: no function here reads it to decide anything;
* `stateType`: the declared state type (a first-order `Ty`, its bytes by
  `ObjectStateType.tyStream`): every write is typed at it (`admitWrite`);
* `live`, `rebirths`: the COUNTERS of the object's awaiting activities, by class
  (`classOf`): `live` those pinned to `pin` (while draining, minus the ones chosen
  for rebirth), `rebirths` the ones chosen for REBIRTH (after a migration, every
  awaiting activity pinned to another package: only chosen ones can be). While
  draining, `Pending.live` counts the activities born on the next package. Every
  turn that starts an awaiting activity calls `retain`, every turn that ends one
  `release` (the ONE pair of functions; `Kernel.ObjectiveActivity` calls them);
* `phase`: `steady`, or `draining next deadline` after an ADOPT: the next pin,
  state type, migration, law and policy (`Pending`) wait for the old activities
  to end (or be aborted at `deadline`) and for the MIGRATE turn.

There is no list of activities: an object's activities are the record cells
keyed by it, so nothing here goes stale when an activity is disposed of; the
counters are what the upgrade turns read (the kernel cannot enumerate cells).

The judgment (`admitWrite`). A write of declared state from `old` to `new` is
admitted exactly when both values project to law views (`project`) and the
object's law evaluates true on them (`admitWrite_ok_iff`). A refusal names the
first failing clause of the law, computed on the same views by
`LawLeaf.of`, so it is an explanation of that evaluation and not a
second decision (`admitWrite_lawDenied_fails`). Typing the new value at the
declared state type stays with the caller, which holds the checked program
(`ObjectiveActivity.typeData`): this module decides the law half only.

Views. A state value projects to scalar slots under `state/`: a natural is its
value, a boolean 0 or 1, a record's fields nest by `.`, a variant sets
`<path>@<label>` to 1 and nests its payload under `<path>.<label>`, a label
projects nothing. A field or variant name containing `.`, `@` or `/` does not
project (no two paths can alias). The request facts sit under `request/`, with
the names `CanonicalRuntimeProfileCore.requestSlots` uses for the same facts. -/
import Pred.Core
import Pred.Leaf
import Compiler.RefusalReason
import Kernel.ObjectiveActivityWire
import Theory.CanonicalResourceKernel
import Theory.AssertAxioms
import Kernel.ObjectStateType
import Compiler.ObjectiveInvocationClaim

namespace Minidregg.Kernel.ObjectRecord
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.ObjectiveActivityWire (Bytes framed framed_roundTrip)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Pred (Pred State Slot eval)
open Minidregg.Theory.ObjectiveBendTypes (Ty)
open Minidregg.Kernel.ObjectStateType (typedAt tyStream)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity capacityStream)
set_option autoImplicit false

/-! ## The record -/

/-- Who may re-pin an object. `frozen`: nobody, ever. `governed authority floors`:
a request whose facts satisfy `authority` may re-pin, and every law the object
ever has must entail each floor (checked by the upgrade turn). -/
inductive UpgradePolicy where
  | frozen
  | governed (authority : Pred) (floors : List Pred)
  deriving DecidableEq, Repr

/-- An adopted upgrade that has not migrated yet: what the object becomes at
MIGRATE. -/
structure Pending where
  /-- The next package (never the current pin: activities are told apart by pin). -/
  pin : Digest
  /-- The next declared state type. -/
  stateType : Ty
  /-- The migration: a declaration of the next package (`old -> new`), or `none`
  for the identity, which ADOPT admits only when the old state type is a value
  subtype of the new (`ObjectStateType.stateSubtype`). -/
  migration : Option String
  /-- The old state's fields the migration drops on purpose (linearity, trap 3). -/
  dropped : List String
  law : Pred
  upgrade : UpgradePolicy
  /-- The activities chosen at ADOPT to be ended and re-born on the next package. -/
  rebirth : List Digest
  /-- The declared envelope of ONE run of the migration (covered at ADOPT); every
  drained write that runs it, and MIGRATE, pays its public price. -/
  envelope : Capacity
  /-- The height of the ADOPT: the `request/height` of the migration's judgment. -/
  adoptedAt : Nat
  /-- Awaiting activities born on `pin` while draining. -/
  live : Nat
  deriving DecidableEq, Repr

/-- Where an object stands in an upgrade. -/
inductive UpgradePhase where
  /-- No upgrade under way. -/
  | steady
  /-- ADOPTed: `next` waits for the old activities to end (or be aborted at
  `deadline`) and for MIGRATE. -/
  | draining (next : Pending) (deadline : Nat)
  deriving DecidableEq, Repr

structure ObjectRecord where
  id : Digest
  pin : Digest
  stateType : Ty
  schemaVersion : Nat
  law : Pred
  upgrade : UpgradePolicy
  continuity : Nat
  payer : Minidregg.Theory.CanonicalResourceKernel.AccountId
  live : Nat
  rebirths : Nat
  phase : UpgradePhase
  deriving DecidableEq, Repr

/-- The package new activities and calls of the object run: the pin, or, while
draining, the next pin (only an identity migration admits them then). -/
def ObjectRecord.activePin (record : ObjectRecord) : Digest :=
  match record.phase with
  | .steady => record.pin
  | .draining next _ => next.pin

/-- The package identities whose code may write the object's state: the pin, and while
draining the next pin too (old activities write as the old package, identity-migration
births and calls as the next one). -/
def ObjectRecord.pins (record : ObjectRecord) : List Nat :=
  match record.phase with
  | .steady => [record.pin.value]
  | .draining next _ => [record.pin.value, next.pin.value]

/-! ## Live counters -/

/-- The counter an awaiting activity (its pin, its id) is counted in. -/
inductive LiveClass where
  | live
  | rebirth
  | pending
  deriving DecidableEq, Repr

/-- **The class of an activity** under an object record. While draining: born on
the next pin, `pending`; chosen for rebirth, `rebirth`; otherwise `live`. Steady:
pinned to the record's pin, `live`; otherwise (left over from a migration, so
chosen for rebirth) `rebirth`. -/
def ObjectRecord.classOf (record : ObjectRecord) (pin activity : Digest) : LiveClass :=
  match record.phase with
  | .draining next _ =>
      if pin = next.pin then .pending else if activity ∈ next.rebirth then .rebirth else .live
  | .steady => if pin = record.pin then .live else .rebirth

/-- The value of one counter. -/
def ObjectRecord.count (record : ObjectRecord) : LiveClass → Nat
  | .live => record.live
  | .rebirth => record.rebirths
  | .pending => match record.phase with
    | .draining next _ => next.live
    | .steady => 0

/-- Apply `f` to one counter (a steady record has no pending counter). -/
def ObjectRecord.bump (record : ObjectRecord) (f : Nat → Nat) : LiveClass → ObjectRecord
  | .live => { record with live := f record.live }
  | .rebirth => { record with rebirths := f record.rebirths }
  | .pending => match record.phase with
    | .draining next deadline => { record with phase := .draining { next with live := f next.live } deadline }
    | .steady => record

/-- **The one retain**: a turn that leaves a new activity awaiting counts it. -/
def ObjectRecord.retain (record : ObjectRecord) (pin activity : Digest) : ObjectRecord :=
  record.bump (· + 1) (record.classOf pin activity)

/-- **The one release**: a turn that ends an awaiting activity (an ending delivery,
an abandonment, an abort, a rebirth of the old one) uncounts it. -/
def ObjectRecord.release (record : ObjectRecord) (pin activity : Digest) : ObjectRecord :=
  record.bump (· - 1) (record.classOf pin activity)

theorem bump_pin (record : ObjectRecord) (f : Nat → Nat) (c : LiveClass) :
    (record.bump f c).pin = record.pin := by
  cases c <;> simp only [ObjectRecord.bump] <;> (try split) <;> rfl

theorem bump_classOf (record : ObjectRecord) (f : Nat → Nat) (c : LiveClass) :
    (record.bump f c).classOf = record.classOf := by
  funext pin activity
  cases c with
  | live => rfl
  | rebirth => rfl
  | pending =>
    unfold ObjectRecord.bump
    cases phase : record.phase with
    | steady => simp only
    | draining next deadline => simp [ObjectRecord.classOf, phase]

/-- A bump changes exactly its own counter. -/
theorem bump_count (record : ObjectRecord) (f : Nat → Nat) (c : LiveClass)
    (draining : c = .pending → ∃ next deadline, record.phase = .draining next deadline) (other : LiveClass) :
    (record.bump f c).count other = if other = c then f (record.count other) else record.count other := by
  cases c with
  | live => cases other <;> simp [ObjectRecord.bump, ObjectRecord.count]
  | rebirth => cases other <;> simp [ObjectRecord.bump, ObjectRecord.count]
  | pending =>
    obtain ⟨next, deadline, phase⟩ := draining rfl
    cases other <;> simp [ObjectRecord.bump, ObjectRecord.count, phase]

/-- Every counter but the bumped one, and every field the judgment reads, is
kept: the pin, the law, the state type, the policy, the payer. -/
theorem bump_keeps (record : ObjectRecord) (f : Nat → Nat) (c : LiveClass) :
    (record.bump f c).pin = record.pin ∧ (record.bump f c).law = record.law ∧
      (record.bump f c).stateType = record.stateType ∧ (record.bump f c).upgrade = record.upgrade ∧
      (record.bump f c).payer = record.payer ∧ (record.bump f c).activePin = record.activePin := by
  cases c <;> simp only [ObjectRecord.bump] <;> (try split) <;>
    simp_all [ObjectRecord.activePin]

/-- A bump keeps the pins. -/
theorem bump_pins (record : ObjectRecord) (f : Nat → Nat) (c : LiveClass) :
    (record.bump f c).pins = record.pins := by
  cases c <;> simp only [ObjectRecord.bump] <;> (try split) <;> simp_all [ObjectRecord.pins]

/-- A steady record never counts an activity `pending`. -/
theorem classOf_steady_ne_pending (record : ObjectRecord) (steady : record.phase = .steady)
    (pin activity : Digest) : record.classOf pin activity ≠ .pending := by
  unfold ObjectRecord.classOf
  rw [steady]
  dsimp only
  split <;> simp

/-- **`retain` counts the activity in its class**, by one, and nothing else. -/
theorem retain_count (record : ObjectRecord) (pin activity : Digest) (c : LiveClass) :
    (record.retain pin activity).count c =
      if c = record.classOf pin activity then record.count c + 1 else record.count c := by
  unfold ObjectRecord.retain
  apply bump_count
  intro pending
  cases phase : record.phase with
  | steady => exact absurd pending (classOf_steady_ne_pending record phase pin activity)
  | draining next deadline => exact ⟨next, deadline, rfl⟩

/-- **`release` uncounts the activity in its class**, by one, and nothing else. -/
theorem release_count (record : ObjectRecord) (pin activity : Digest) (c : LiveClass) :
    (record.release pin activity).count c =
      if c = record.classOf pin activity then record.count c - 1 else record.count c := by
  unfold ObjectRecord.release
  apply bump_count
  intro pending
  cases phase : record.phase with
  | steady => exact absurd pending (classOf_steady_ne_pending record phase pin activity)
  | draining next deadline => exact ⟨next, deadline, rfl⟩

/-! ## The package pin: a kernel clause no creator law can remove -/

/-- **The kernel's package-pin clause for an object pinned to `pin`**: the write is made
by code of exactly that package (`objectivePin` over the one identity `pin.value`; `-1`,
the slot of a write no package made, never passes). The ONE construction of the clause:
the creation judges with it and the upgrade turns re-pin through it. -/
def pinClause (pin : Digest) : Pred :=
  Minidregg.Pred.objectivePin [pin.value]

/-- **The law that judges every write of an object's declared state**: the kernel's pin
clause FIRST, then the creator's law. Removal is impossible by construction: the clause is
not a stored field a creator or a later turn could omit or rewrite, it is a function of the
record's `pin`, and the judge (`admitWrite`) reads only this. A refusal by the pin is the
leaf at path `[0]` (`unpinned_write_names_pin`). -/
def ObjectRecord.effectiveLaw (record : ObjectRecord) : Pred :=
  Pred.all [Minidregg.Pred.objectivePin record.pins, record.law]

/-- The effective law leads with the pin clause of exactly the pinned packages
(`pins`: the pin; while draining also the next pin). -/
theorem effectiveLaw_leads_with_pin (record : ObjectRecord) :
    record.effectiveLaw = Pred.all (Minidregg.Pred.objectivePin record.pins :: [record.law]) := rfl

/-- Steady, the clause is exactly `pinClause record.pin`. -/
theorem effectiveLaw_steady (record : ObjectRecord) (steady : record.phase = .steady) :
    record.effectiveLaw = Pred.all [pinClause record.pin, record.law] := by
  simp [ObjectRecord.effectiveLaw, ObjectRecord.pins, steady, pinClause]

/-- **No creator law removes the pin**: whatever `law` an object is created with, a view
the effective law accepts is one the pin clause accepts (and the creator's law accepts). -/
theorem effectiveLaw_accepts_iff (record : ObjectRecord) (old new : State) :
    eval record.effectiveLaw old new = true ↔
      eval (Minidregg.Pred.objectivePin record.pins) old new = true ∧ eval record.law old new = true := by
  unfold ObjectRecord.effectiveLaw
  rw [Minidregg.Pred.eval_all]
  simp

/-! ## Upgrade policy: it may only tighten -/

/-- `authority'` admits no request `authority` refuses, syntactically: it is
`authority` itself, or `all [authority, extra]`. -/
def strengthens (authority authority' : Pred) : Bool :=
  authority' == authority ||
    match authority' with
    | .allL (.cons first (.cons _ .nil)) => first == authority
    | _ => false

/-- `next` is at least as strict as `current`: frozen stays frozen; a governed
policy may become frozen, or keep every floor (adding more) while its authority
is kept or conjoined with an extra condition. -/
def UpgradePolicy.permits : UpgradePolicy → UpgradePolicy → Bool
  | .frozen, .frozen => true
  | .frozen, .governed _ _ => false
  | .governed _ _, .frozen => true
  | .governed authority floors, .governed authority' floors' =>
      floors.all (fun floor => floors'.contains floor) && strengthens authority authority'

/-- Nothing loosens `frozen`. -/
theorem frozen_absorbing (next : UpgradePolicy) (allowed : UpgradePolicy.permits .frozen next = true) :
    next = .frozen := by
  cases next with
  | frozen => rfl
  | governed _ _ => simp [UpgradePolicy.permits] at allowed

/-- A strengthened authority admits only requests the old one admitted. -/
theorem strengthens_sound (authority authority' : Pred) (kept : strengthens authority authority' = true)
    (old new : State) (holds : eval authority' old new = true) : eval authority old new = true := by
  unfold strengthens at kept
  simp only [Bool.or_eq_true, beq_iff_eq] at kept
  rcases kept with same | conj
  · subst same; exact holds
  · split at conj
    · rename_i first second
      simp only [beq_iff_eq] at conj
      subst conj
      simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith, Minidregg.Pred.evalWithAll, Bool.and_eq_true] at holds
      simpa [Minidregg.Pred.eval] using holds.1
    · cases conj

/-- A tightening never admits an upgrader the current policy refused, and never
drops a floor. -/
theorem permits_tightens (authority authority' : Pred) (floors floors' : List Pred)
    (allowed : UpgradePolicy.permits (.governed authority floors) (.governed authority' floors') = true) :
    (∀ floor ∈ floors, floor ∈ floors') ∧
      ∀ old new : State, eval authority' old new = true → eval authority old new = true := by
  simp only [UpgradePolicy.permits, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at allowed
  exact ⟨allowed.1, strengthens_sound authority authority' allowed.2⟩

/-! ## Law views -/

/-- A field or variant name that cannot alias another path. -/
def plainName (name : String) : Bool :=
  !name.isEmpty && name.all (fun c => c != '.' && c != '@' && c != '/')

mutual
/-- The scalar slots of a state value at `path`; `none` if a name is not plain. -/
def slotsOf (path : String) : Data → Option (List (Slot × Int))
  | .natural value => some [(path, Int.ofNat value)]
  | .boolean value => some [(path, if value then 1 else 0)]
  | .label _ => some []
  | .record fields => fieldSlots path fields
  | .variant label payload =>
      if plainName label then do
        let inner ← slotsOf (path ++ "." ++ label) payload
        pure ((path ++ "@" ++ label, 1) :: inner)
      else none
/-- The slots of a record's fields, in order. -/
def fieldSlots (path : String) : List (String × Data) → Option (List (Slot × Int))
  | [] => some []
  | (name, value) :: rest =>
      if plainName name then do
        let here ← slotsOf (path ++ "." ++ name) value
        let later ← fieldSlots path rest
        pure (here ++ later)
      else none
end

/-- The state slots of a declared-state value: under `state/` (the top-level
record's fields directly, so a field `count` is `state/count`). -/
def stateSlots : Data → Option (List (Slot × Int))
  | .record fields => fieldSlotsTop fields
  | other => slotsOf "state" other
where
  fieldSlotsTop : List (String × Data) → Option (List (Slot × Int))
    | [] => some []
    | (name, value) :: rest =>
        if plainName name then do
          let here ← slotsOf ("state/" ++ name) value
          let later ← fieldSlotsTop rest
          pure (here ++ later)
        else none

/-- The facts of the request a write is judged under. -/
structure Facts where
  /-- The subject whose authority the write carries. `none` in a nested call
  frame that no scoped grant of the signer covers (`Kernel.ObjectiveCall`): the
  signer's authority does not flow to callees it did not grant, so the slot
  `request/subject` is ABSENT and every atom reading it fails closed. -/
  subject : Option SubjectId
  height : Nat
  /-- The object the write is about (its id's value). -/
  target : Nat
  /-- Which kernel turn writes (or, for an ADOPT, asks): 1 birth, 2 delivery, 3 (unused:
  there is no direct write of declared state), 4 creation (the seed), 5 a call frame,
  6 MIGRATE (the migration's judgment, `migrateFacts`), 7 ADOPT (the upgrade authority's
  facts), 8 an abort after the drain deadline, 9 a rebirth's first segment. -/
  turn : Nat
  /-- The object whose frame called the writing frame (`request/caller`); `none`
  (slot absent) when the write is not a nested call frame's. A callee's law
  names the callers it admits with this slot: an object's facet, as a clause. -/
  caller : Option Nat
  /-- The identity (`ObjectiveBendSourceArtifact.identity`, the value of an object's
  `pin`) of the Objective package whose code is making the write: a birth, a
  delivery, a call frame and a delivered message run the package their object or
  activity pins, and say so here. `none` for a write no package code made (the
  direct holder write, `turn` 3): the slot then reads `-1`, never an identity. -/
  artifact : Option Nat
  deriving DecidableEq, Repr

/-- The value of `Pred.objectiveArtifactSlot`: the writing package's identity, or `-1`
(never an identity, which is a natural number) when no package code writes. The same
encoding as `Kernel.DeclaredResourceController.objectiveArtifactValue`. -/
def Facts.artifactValue (facts : Facts) : Int :=
  match facts.artifact with
  | some artifact => Int.ofNat artifact
  | none => -1

/-- The request slots of a write. `objective/artifact` is the FIRST block, so no later
projection (a `state/` slot, a `request/` slot) can shadow it (`State.get` reads the first
match), exactly as in the resource route's law states (`objectiveSlots`). -/
def Facts.slots (facts : Facts) : List (Slot × Int) :=
  (Minidregg.Pred.objectiveArtifactSlot, facts.artifactValue) ::
  ((facts.subject.map (fun subject => ("request/subject", Int.ofNat subject.value))).toList ++
  [("request/height", Int.ofNat facts.height),
   ("request/target", Int.ofNat facts.target),
   ("request/turn", Int.ofNat facts.turn)] ++
  (facts.caller.map (fun caller => ("request/caller", Int.ofNat caller))).toList)

/-- The (old, new) views a write is judged on. A first write has no old state:
its old view holds the request facts only. -/
def views (facts : Facts) (old : Option Data) (new : Data) : Option (State × State) := do
  let before ← match old with
    | none => some []
    | some value => stateSlots value
  let after ← stateSlots new
  pure (⟨facts.slots ++ before⟩, ⟨facts.slots ++ after⟩)

/-! ## The judgment -/

inductive WriteRefusal where
  /-- The new value is not typed at the object's declared state type. -/
  | illTyped
  /-- A value does not project (a name that is not plain). -/
  | unprojectable
  /-- The object's law rejects the write; the first failing clause. -/
  | lawDenied (leaf : LawLeaf)
  /-- While draining: the write's state, migrated, is refused by the NEXT record's
  judgment (the one MIGRATE will make): its reason. -/
  | upgradeConflict (reason : WriteRefusal)
  /-- While draining under a migration term, a write judged without running it
  (a call frame): never admitted (`ObjectRecord.admitsNew` refuses such frames first). -/
  | unmigrated
  deriving DecidableEq, Repr

/-- Judge a write by `law` on its views: the one judgment, parameterised by which law. -/
def judgeLaw (law : Pred) (facts : Facts) (old : Option Data) (new : Data) : Except WriteRefusal Unit :=
  match views facts old new with
  | none => .error .unprojectable
  | some (before, after) =>
      match LawLeaf.of law before after with
      | none => .ok ()
      | some leaf => .error (.lawDenied leaf)

/-- The judgment every write of an object's declared state passes after the object exists:
its effective law (the kernel's pin clause, then the creator's law), then the new value is
typed at the declared state type. -/
def admitWrite (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data) :
    Except WriteRefusal Unit :=
  match judgeLaw record.effectiveLaw facts old new with
  | .error reason => .error reason
  | .ok () => if typedAt record.stateType new then .ok () else .error .illTyped

/-- The judgment of an object's INITIAL state, at its creation: the creator's law alone. The pin
governs the writes after the object exists; at creation no package has run, so the pin clause
would refuse every seed. The seed is judged over `old = none`, so an object cannot be born
violating its own state clauses; and it is typed at the declared state type. -/
def admitSeed (record : ObjectRecord) (facts : Facts) (seed : Data) : Except WriteRefusal Unit :=
  match judgeLaw record.law facts none seed with
  | .error reason => .error reason
  | .ok () => if typedAt record.stateType seed then .ok () else .error .illTyped

/-- **A write is admitted exactly when the law accepts its views.** -/
theorem judgeLaw_ok_iff (law : Pred) (facts : Facts) (old : Option Data) (new : Data) :
    judgeLaw law facts old new = .ok () ↔
      ∃ before after, views facts old new = some (before, after) ∧ eval law before after = true := by
  unfold judgeLaw
  cases viewed : views facts old new with
  | none => simp
  | some pair =>
      obtain ⟨before, after⟩ := pair
      cases named : LawLeaf.of law before after with
      | none =>
          have accepts := (LawLeaf.of_none_iff law before after).mp named
          simp [named, accepts]
      | some leaf =>
          have rejects : eval law before after ≠ true := by
            intro accepts
            have := (LawLeaf.of_none_iff law before after).mpr accepts
            rw [named] at this; cases this
          simp [named, rejects]

/-- **A refusal names a clause of the law that is false on the same views.** -/
theorem judgeLaw_lawDenied_fails (law : Pred) (facts : Facts) (old : Option Data) (new : Data)
    (leaf : LawLeaf) (refused : judgeLaw law facts old new = .error (.lawDenied leaf)) :
    ∃ before after, views facts old new = some (before, after) ∧
      law.subterm leaf.path = some leaf.clause ∧ eval leaf.clause before after = false := by
  unfold judgeLaw at refused
  cases viewed : views facts old new with
  | none => simp [viewed] at refused
  | some pair =>
      obtain ⟨before, after⟩ := pair
      rw [viewed] at refused
      cases named : LawLeaf.of law before after with
      | none => simp [named] at refused
      | some found =>
          simp only [named, Except.error.injEq, WriteRefusal.lawDenied.injEq] at refused
          subst refused
          obtain ⟨at_, _, fails⟩ := LawLeaf.of_fails law before after found named
          exact ⟨before, after, rfl, at_, fails⟩

theorem typedAfter_ok {law : Except WriteRefusal Unit} {type : Ty} {new : Data} :
    (match law with
      | .error reason => .error reason
      | .ok () => if typedAt type new then .ok () else .error .illTyped : Except WriteRefusal Unit) = .ok () ↔
      law = .ok () ∧ typedAt type new = true := by
  cases law with
  | error reason => simp
  | ok u => cases u; by_cases typed : typedAt type new = true <;> simp [typed]

/-- **A write is admitted exactly when the effective law (the pin clause, then the
creator's law) accepts its views and the new value is typed at the declared state type.** -/
theorem admitWrite_ok_iff (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data) :
    admitWrite record facts old new = .ok () ↔
      (∃ before after, views facts old new = some (before, after) ∧
        eval record.effectiveLaw before after = true) ∧ typedAt record.stateType new = true := by
  unfold admitWrite
  rw [typedAfter_ok, judgeLaw_ok_iff]

/-- **A refusal names a clause of the effective law that is false on the same views.** -/
theorem admitWrite_lawDenied_fails (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data)
    (leaf : LawLeaf) (refused : admitWrite record facts old new = .error (.lawDenied leaf)) :
    ∃ before after, views facts old new = some (before, after) ∧
      record.effectiveLaw.subterm leaf.path = some leaf.clause ∧ eval leaf.clause before after = false := by
  unfold admitWrite at refused
  cases judged : judgeLaw record.effectiveLaw facts old new with
  | error reason =>
    rw [judged] at refused
    cases refused
    exact judgeLaw_lawDenied_fails record.effectiveLaw facts old new leaf judged
  | ok u =>
    cases u
    rw [judged] at refused
    simp only at refused
    split at refused <;> cases refused

/-- **A seed is admitted exactly when the CREATOR'S law accepts its views** (no pin clause:
nothing has run yet) and it is typed at the declared state type. -/
theorem admitSeed_ok_iff (record : ObjectRecord) (facts : Facts) (seed : Data) :
    admitSeed record facts seed = .ok () ↔
      (∃ before after, views facts none seed = some (before, after) ∧ eval record.law before after = true) ∧
        typedAt record.stateType seed = true := by
  unfold admitSeed
  rw [typedAfter_ok, judgeLaw_ok_iff]

/-- **A refused seed names the creator's clause that is false on the seed's views.** -/
theorem admitSeed_lawDenied_fails (record : ObjectRecord) (facts : Facts) (seed : Data) (leaf : LawLeaf)
    (refused : admitSeed record facts seed = .error (.lawDenied leaf)) :
    ∃ before after, views facts none seed = some (before, after) ∧
      record.law.subterm leaf.path = some leaf.clause ∧ eval leaf.clause before after = false := by
  unfold admitSeed at refused
  cases judged : judgeLaw record.law facts none seed with
  | error reason =>
    rw [judged] at refused
    cases refused
    exact judgeLaw_lawDenied_fails record.law facts none seed leaf judged
  | ok u =>
    cases u
    rw [judged] at refused
    simp only at refused
    split at refused <;> cases refused

/-- An admitted write is typed at the declared state type. -/
theorem admitWrite_typed {record : ObjectRecord} {facts : Facts} {old : Option Data} {new : Data}
    (admitted : admitWrite record facts old new = .ok ()) : typedAt record.stateType new = true :=
  ((admitWrite_ok_iff record facts old new).mp admitted).2

/-- The judgment reads the law, the pins and the state type only: counters and the payer
are not read. -/
theorem admitWrite_bump (record : ObjectRecord) (f : Nat → Nat) (c : LiveClass) (facts : Facts)
    (old : Option Data) (new : Data) :
    admitWrite (record.bump f c) facts old new = admitWrite record facts old new := by
  obtain ⟨_, law, stateType, _⟩ := bump_keeps record f c
  simp only [admitWrite, ObjectRecord.effectiveLaw, bump_pins, law, stateType]

/-- **The payer is not authority**: the judgment does not read it. -/
theorem admitWrite_payer_irrelevant (record : ObjectRecord) (payer : Minidregg.Theory.CanonicalResourceKernel.AccountId)
    (facts : Facts) (old : Option Data) (new : Data) :
    admitWrite { record with payer := payer } facts old new = admitWrite record facts old new := rfl

/-! ## The pin in the views -/

/-- The shape of a write's views: the request slots first, then the state slots. -/
theorem views_shape (facts : Facts) (old : Option Data) (new : Data) (before after : State)
    (viewed : views facts old new = some (before, after)) :
    ∃ b a, before = ⟨facts.slots ++ b⟩ ∧ after = ⟨facts.slots ++ a⟩ := by
  unfold views at viewed
  cases old with
  | none =>
    cases h : stateSlots new with
    | none => simp [h] at viewed
    | some a =>
      simp [h] at viewed
      exact ⟨[], a, by simp [← viewed.1], by simp [← viewed.2]⟩
  | some value =>
    cases hv : stateSlots value with
    | none => simp [hv] at viewed
    | some b =>
      cases h : stateSlots new with
      | none => simp [hv, h] at viewed
      | some a =>
        simp [hv, h] at viewed
        exact ⟨b, a, viewed.1.symm, viewed.2.symm⟩

/-- **The artifact slot is exact**: in both views of every write, `objective/artifact`
reads the writing package's identity, or `-1` when no package code writes, whatever the
state slots are (it is the first block, and no `state/` or `request/` slot shares its name). -/
theorem views_artifact_slot (facts : Facts) (old : Option Data) (new : Data) (before after : State)
    (viewed : views facts old new = some (before, after)) :
    before.get Minidregg.Pred.objectiveArtifactSlot = some facts.artifactValue ∧
      after.get Minidregg.Pred.objectiveArtifactSlot = some facts.artifactValue := by
  obtain ⟨b, a, rfl, rfl⟩ := views_shape facts old new before after viewed
  simp [State.get, Facts.slots]

/-- **A write made by the pinned package passes the pin.** Its artifact is the pin's
identity, so the clause accepts every view of it: the pin never refuses the package it pins. -/
theorem pinClause_accepts_run (pin : Digest) (facts : Facts) (old : Option Data) (new : Data)
    (ran : facts.artifact = some pin.value) (before after : State)
    (viewed : views facts old new = some (before, after)) :
    eval (pinClause pin) before after = true := by
  obtain ⟨_, slotAfter⟩ := views_artifact_slot facts old new before after viewed
  unfold pinClause
  rw [Minidregg.Pred.eval_objectivePin]
  exact ⟨pin.value, List.mem_singleton_self _, by rw [slotAfter]; simp [Facts.artifactValue, ran]⟩

/-- **A write made by one of the object's packages passes its pins** (`ObjectRecord.pins`):
its artifact is one of them, so the clause accepts every view of it. -/
theorem objectivePin_accepts_run (pins : List Nat) (facts : Facts) (old : Option Data) (new : Data)
    (artifact : Nat) (ran : facts.artifact = some artifact) (member : artifact ∈ pins) (before after : State)
    (viewed : views facts old new = some (before, after)) :
    eval (Minidregg.Pred.objectivePin pins) before after = true := by
  obtain ⟨_, slotAfter⟩ := views_artifact_slot facts old new before after viewed
  rw [Minidregg.Pred.eval_objectivePin]
  exact ⟨artifact, member, by rw [slotAfter]; simp [Facts.artifactValue, ran]⟩

/-- The package an object runs for new activities is one of its pins. -/
theorem activePin_mem_pins (record : ObjectRecord) : record.activePin.value ∈ record.pins := by
  unfold ObjectRecord.activePin ObjectRecord.pins
  split <;> simp

/-- A pin clause leading an `all` names itself, at path `[0]`, when the step reads `-1`. -/
theorem all_pin_names_pin (artifacts : List Nat) (rest : List Pred) (old new : State)
    (unclaimed : new.get Minidregg.Pred.objectiveArtifactSlot = some (-1)) :
    LawLeaf.of (Pred.all (Minidregg.Pred.objectivePin artifacts :: rest)) old new =
      some ⟨[0], Minidregg.Pred.objectivePin artifacts, old.get Minidregg.Pred.objectiveArtifactSlot,
        some (-1)⟩ := by
  have refused := Minidregg.Pred.objectivePin_refuses_unclaimed artifacts old new unclaimed
  have leaf : Minidregg.Pred.firstFailingLeaf (Pred.all (Minidregg.Pred.objectivePin artifacts :: rest))
      old new = some [0] := by
    unfold Minidregg.Pred.eval at refused
    unfold Minidregg.Pred.objectivePin at refused ⊢
    simp only [Minidregg.Pred.firstFailingLeaf, Minidregg.Pred.Pred.all, Minidregg.Pred.PredList.ofList,
      Minidregg.Pred.leafWith, Minidregg.Pred.leafWithAll, refused]
    rfl
  simp only [LawLeaf.of, leaf, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  unfold Minidregg.Pred.objectivePin
  simp [Minidregg.Pred.Pred.subterm, Minidregg.Pred.PredList.subterm, Minidregg.Pred.Pred.all,
    Minidregg.Pred.PredList.ofList, LawLeaf.explained, LawLeaf.slotOf, unclaimed]

/-- **An ordinary write is refused, naming the pin.** A write no package code made
(`artifact = none`: the slot reads `-1`) to ANY object is refused at the clause
`pinClause pin`, path `[0]`, whatever the creator's law, the old state and the new value
(when they project at all; otherwise `unprojectable` refuses it). -/
theorem unpinned_write_names_pin (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data)
    (unpinned : facts.artifact = none) (before after : State)
    (viewed : views facts old new = some (before, after)) :
    admitWrite record facts old new = .error (.lawDenied
      ⟨[0], Minidregg.Pred.objectivePin record.pins, before.get Minidregg.Pred.objectiveArtifactSlot, some (-1)⟩) := by
  obtain ⟨_, slotAfter⟩ := views_artifact_slot facts old new before after viewed
  have unclaimed : after.get Minidregg.Pred.objectiveArtifactSlot = some (-1) := by
    rw [slotAfter]; simp [Facts.artifactValue, unpinned]
  have named : LawLeaf.of record.effectiveLaw before after =
      some ⟨[0], Minidregg.Pred.objectivePin record.pins, before.get Minidregg.Pred.objectiveArtifactSlot, some (-1)⟩ :=
    all_pin_names_pin record.pins [record.law] before after unclaimed
  simp only [admitWrite, judgeLaw, viewed, named]

/-- A write no package code made is never admitted, for every object and value. -/
theorem unpinned_write_refused (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data)
    (unpinned : facts.artifact = none) : admitWrite record facts old new ≠ .ok () := by
  intro admitted
  obtain ⟨⟨before, after, viewed, _⟩, _⟩ := (admitWrite_ok_iff record facts old new).mp admitted
  have named := unpinned_write_names_pin record facts old new unpinned before after viewed
  rw [named] at admitted
  cases admitted

/-! ### Teeth (kernel-decided, not evaluated by the compiler)

An object pinned to package 7 whose creator's law is the empty conjunction (the most
permissive law there is). `leafOf` / `accepted` read the verdict of `admitWrite`. -/

def teethRecord : ObjectRecord := ⟨⟨1⟩, ⟨7⟩, .natural, 1, Pred.all [], .frozen, 0, 0, 0, 0, .steady⟩

def teethFacts (artifact : Option Nat) : Facts := ⟨some ⟨40⟩, 5, 1, 3, none, artifact⟩

def leafOf : Except WriteRefusal Unit → Option LawLeaf
  | .error (.lawDenied leaf) => some leaf
  | _ => none

def accepted : Except WriteRefusal Unit → Bool
  | .ok () => true
  | _ => false

/-- Under a permit-all creator law: a write no package made is refused at the pin
(path `[0]`, the slot reading `-1`); a write by the wrong package is refused at the pin
(reading 8); a write by package 7 is admitted. -/
theorem pin_teeth :
    leafOf (admitWrite teethRecord (teethFacts none) none (.natural 1)) =
        some ⟨[0], pinClause ⟨7⟩, some (-1), some (-1)⟩ ∧
      leafOf (admitWrite teethRecord (teethFacts (some 8)) none (.natural 1)) =
        some ⟨[0], pinClause ⟨7⟩, some 8, some 8⟩ ∧
      accepted (admitWrite teethRecord (teethFacts (some 7)) none (.natural 1)) = true := by
  decide +kernel

/-- An object whose creator's law pins its state to 5. -/
def teethSeedRecord : ObjectRecord := { teethRecord with law := Pred.eq "state" 5 }

/-- **Seed teeth.** The initial state is judged by the creator's law and NOT by the pin: a
permit-all object's seed is admitted though no package made it (the same value as a write is
refused at the pin), and a seed the creator's law refuses is refused at the creator's clause
(the root leaf, reading 6), and 5 is admitted. Both directions. -/
theorem seed_teeth :
    accepted (admitSeed teethRecord (teethFacts none) (.natural 1)) = true ∧
      accepted (admitWrite teethRecord (teethFacts none) none (.natural 1)) = false ∧
      accepted (admitSeed teethSeedRecord (teethFacts none) (.natural 5)) = true ∧
      leafOf (admitSeed teethSeedRecord (teethFacts none) (.natural 6)) =
        some ⟨[], Pred.eq "state" 5, none, some 6⟩ := by
  decide +kernel

/-! ## The upgrade: the next record, the migration's facts, the drained judgment -/

/-- **The record MIGRATE installs**: the next pin, state type, law and policy;
the schema version and the continuity each one higher; the pending activities
become the live ones; steady. The rebirth counter is kept (those activities are
re-born on the new pin by their own turns). -/
def ObjectRecord.successor (record : ObjectRecord) (next : Pending) : ObjectRecord :=
  { record with
    pin := next.pin
    stateType := next.stateType
    schemaVersion := record.schemaVersion + 1
    law := next.law
    upgrade := next.upgrade
    continuity := record.continuity + 1
    live := next.live
    phase := .steady }

/-- **The facts of the migration's judgment** (turn 6): a function of the object
and the pending upgrade only (no subject, the ADOPT height, no caller), so a
drained write judged under them is judged exactly as MIGRATE will judge the same
state. The artifact is the next package: the migrated state is the next package's (its
migration declaration, or the identity it adopted), so the next record's pin clause admits it. -/
def migrateFacts (target : Nat) (next : Pending) : Facts :=
  ⟨none, next.adoptedAt, target, 6, none, some next.pin.value⟩

/-- New births and calls are admitted: always when steady; while draining only
under the identity migration, which requires the old state type to be a value
subtype of the new (so a new-package activity never has its state rewritten
under it at MIGRATE). -/
def ObjectRecord.admitsNew (record : ObjectRecord) : Bool :=
  match record.phase with
  | .steady => true
  | .draining next _ => next.migration.isNone && ObjectStateType.stateSubtype record.stateType next.stateType

/-- An activity pinned to `pin` may run (be delivered, exhausted): steady, only
the record's pin (an activity left on another pin waits for its REBIRTH); while
draining, the old pin and the next one. -/
def ObjectRecord.runs (record : ObjectRecord) (pin : Digest) : Bool :=
  match record.phase with
  | .steady => pin == record.pin
  | .draining next _ => pin == record.pin || pin == next.pin

/-- **The judgment of a write that runs no migration** (a call frame's, a
delivered message's): `admitWrite`, and while draining under the identity, the
next record's judgment of the new state under the migration's facts. Under a
migration term it refuses (`unmigrated`): such writes are refused before they run. -/
def ObjectRecord.judge (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data) :
    Except WriteRefusal Unit :=
  match admitWrite record facts old new with
  | .error reason => .error reason
  | .ok () =>
    match record.phase with
    | .steady => .ok ()
    | .draining next _ =>
      match next.migration with
      | some _ => .error .unmigrated
      | none =>
        match admitWrite (record.successor next) (migrateFacts facts.target next) (some new) new with
        | .ok () => .ok ()
        | .error reason => .error (.upgradeConflict reason)

/-- A judged write is admitted by the record's own law. -/
theorem judge_admits {record : ObjectRecord} {facts : Facts} {old : Option Data} {new : Data}
    (judged : record.judge facts old new = .ok ()) : admitWrite record facts old new = .ok () := by
  unfold ObjectRecord.judge at judged
  split at judged
  · cases judged
  · assumption

/-- A steady record's judgment is `admitWrite`. -/
theorem judge_steady {record : ObjectRecord} (steady : record.phase = .steady) (facts : Facts) (old : Option Data)
    (new : Data) : record.judge facts old new = admitWrite record facts old new := by
  unfold ObjectRecord.judge
  cases admitted : admitWrite record facts old new with
  | error reason => rfl
  | ok u => cases u; simp [steady]

/-- While draining, a judged write's state is one MIGRATE (under the identity)
admits. -/
theorem judge_draining {record : ObjectRecord} {next : Pending} {deadline : Nat}
    (draining : record.phase = .draining next deadline) {facts : Facts} {old : Option Data} {new : Data}
    (judged : record.judge facts old new = .ok ()) :
    next.migration = none ∧
      admitWrite (record.successor next) (migrateFacts facts.target next) (some new) new = .ok () := by
  unfold ObjectRecord.judge at judged
  split at judged
  · cases judged
  · rw [draining] at judged
    simp only at judged
    split at judged
    · cases judged
    · rename_i none_
      refine ⟨none_, ?_⟩
      split at judged
      · assumption
      · cases judged

/-- The judgment of a write that runs no migration: everything it reads but the
payer, so the payer is never authority. -/
theorem judge_payer_irrelevant (record : ObjectRecord) (payer : Minidregg.Theory.CanonicalResourceKernel.AccountId)
    (facts : Facts) (old : Option Data) (new : Data) :
    ({ record with payer := payer } : ObjectRecord).judge facts old new = record.judge facts old new := rfl

/-- A package the object still runs is one of its pins. -/
theorem runs_mem_pins {record : ObjectRecord} {pin : Digest} (runs : record.runs pin = true) :
    pin.value ∈ record.pins := by
  unfold ObjectRecord.runs at runs
  unfold ObjectRecord.pins
  split at runs
  · rename_i steady
    simp at runs; simp [runs]
  · rename_i next deadline draining
    simp at runs
    rcases runs with same | same <;> simp [same]

/-! ## The record's bytes -/

def upgradeStream : StreamCodec UpgradePolicy :=
  StreamCodec.xmap
    (StreamCodec.sum ObjectiveActivityWire.unitStream
      (StreamCodec.product LawLeaf.predStream (StreamCodec.list LawLeaf.predStream)))
    (fun policy => match policy with
      | .frozen => .inl ()
      | .governed authority floors => .inr (authority, floors))
    (fun wire => match wire with
      | .inl () => .frozen
      | .inr (authority, floors) => .governed authority floors)
    (by intro policy; cases policy <;> rfl)

def pendingStream : StreamCodec Pending :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product tyStream
      (StreamCodec.product (StreamCodec.option ObjectiveActivityWire.stringStream)
      (StreamCodec.product (StreamCodec.list ObjectiveActivityWire.stringStream)
      (StreamCodec.product LawLeaf.predStream (StreamCodec.product upgradeStream
      (StreamCodec.product (StreamCodec.list digestStream) (StreamCodec.product capacityStream
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))))
    (fun p => (p.pin, p.stateType, p.migration, p.dropped, p.law, p.upgrade, p.rebirth, p.envelope,
      p.adoptedAt, p.live))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2.1,
      w.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2⟩)
    (by intro p; cases p; rfl)

def phaseStream : StreamCodec UpgradePhase :=
  StreamCodec.xmap
    (StreamCodec.sum ObjectiveActivityWire.unitStream (StreamCodec.product pendingStream StreamCodec.nat))
    (fun phase => match phase with
      | .steady => .inl ()
      | .draining next deadline => .inr (next, deadline))
    (fun wire => match wire with
      | .inl () => .steady
      | .inr (next, deadline) => .draining next deadline)
    (by intro phase; cases phase <;> rfl)

def recordStream : StreamCodec ObjectRecord :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product tyStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product LawLeaf.predStream
      (StreamCodec.product upgradeStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat phaseStream))))))))))
    (fun r => (r.id, r.pin, r.stateType, r.schemaVersion, r.law, r.upgrade, r.continuity, r.payer,
      r.live, r.rebirths, r.phase))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2.1,
      w.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2.2⟩)
    (by intro r; cases r; rfl)

/-- v2: the record carries the declared state type, the live counters and the
upgrade phase. A v1 record does not decode (its frame differs): `readObject`
refuses it `objectCodec`, so a v1 world is re-genesised, never reinterpreted. -/
def recordFrame : Bytes := "DREGG/OBJECTIVE/OBJECT-RECORD/v2".toUTF8.toList
def recordCodec := framed recordFrame recordStream
def encodeRecord (record : ObjectRecord) : Bytes := recordCodec.encode record
def decodeRecord (bytes : Bytes) : Option ObjectRecord := recordCodec.decode bytes

theorem record_roundTrip (record : ObjectRecord) : decodeRecord (encodeRecord record) = some record :=
  framed_roundTrip _ _ record

#assert_axioms frozen_absorbing
#assert_axioms strengthens_sound
#assert_axioms permits_tightens
#assert_axioms judgeLaw_ok_iff
#assert_axioms judgeLaw_lawDenied_fails
#assert_axioms admitSeed_ok_iff
#assert_axioms admitSeed_lawDenied_fails
#assert_axioms admitWrite_ok_iff
#assert_axioms admitWrite_lawDenied_fails
#assert_axioms admitWrite_payer_irrelevant
#assert_axioms effectiveLaw_leads_with_pin
#assert_axioms effectiveLaw_accepts_iff
#assert_axioms views_shape
#assert_axioms views_artifact_slot
#assert_axioms pinClause_accepts_run
#assert_axioms all_pin_names_pin
#assert_axioms unpinned_write_names_pin
#assert_axioms unpinned_write_refused
#assert_axioms pin_teeth
#assert_axioms seed_teeth

#assert_axioms admitWrite_typed
#assert_axioms typedAfter_ok
#assert_axioms bump_pins
#assert_axioms objectivePin_accepts_run
#assert_axioms activePin_mem_pins
#assert_axioms runs_mem_pins
#assert_axioms effectiveLaw_steady
#assert_axioms admitWrite_bump
#assert_axioms bump_pin
#assert_axioms bump_classOf
#assert_axioms bump_count
#assert_axioms bump_keeps
#assert_axioms classOf_steady_ne_pending
#assert_axioms retain_count
#assert_axioms release_count
#assert_axioms judge_admits
#assert_axioms judge_steady
#assert_axioms judge_draining
#assert_axioms judge_payer_irrelevant
#assert_axioms record_roundTrip
end Minidregg.Kernel.ObjectRecord
