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
  is never authority: no function here reads it to decide anything.

There is no list of activities: an object's activities are the record cells
keyed by it, so nothing here goes stale when an activity is disposed of.

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

namespace Minidregg.Kernel.ObjectRecord
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.ObjectiveActivityWire (Bytes framed framed_roundTrip)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Pred (Pred State Slot eval)
set_option autoImplicit false

/-! ## The record -/

/-- Who may re-pin an object. `frozen`: nobody, ever. `governed authority floors`:
a request whose facts satisfy `authority` may re-pin, and every law the object
ever has must entail each floor (checked by the upgrade turn). -/
inductive UpgradePolicy where
  | frozen
  | governed (authority : Pred) (floors : List Pred)
  deriving DecidableEq, Repr

structure ObjectRecord where
  id : Digest
  pin : Digest
  schemaVersion : Nat
  law : Pred
  upgrade : UpgradePolicy
  continuity : Nat
  payer : Minidregg.Theory.CanonicalResourceKernel.AccountId
  deriving DecidableEq, Repr

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
  Pred.all [pinClause record.pin, record.law]

/-- The effective law leads with the pin clause of exactly the pinned package. -/
theorem effectiveLaw_leads_with_pin (record : ObjectRecord) :
    record.effectiveLaw = Pred.all (pinClause record.pin :: [record.law]) := rfl

/-- **No creator law removes the pin**: whatever `law` an object is created with, a view
the effective law accepts is one the pin clause accepts (and the creator's law accepts). -/
theorem effectiveLaw_accepts_iff (record : ObjectRecord) (old new : State) :
    eval record.effectiveLaw old new = true ↔
      eval (pinClause record.pin) old new = true ∧ eval record.law old new = true := by
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
  /-- Which kernel turn writes: 1 birth, 2 delivery, 3 (unused: there is no direct write of
  declared state), 4 creation (the seed), 5 a call frame. -/
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
  /-- A value does not project (a name that is not plain). -/
  | unprojectable
  /-- The object's law rejects the write; the first failing clause. -/
  | lawDenied (leaf : LawLeaf)
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
its effective law (the kernel's pin clause, then the creator's law). -/
def admitWrite (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data) :
    Except WriteRefusal Unit :=
  judgeLaw record.effectiveLaw facts old new

/-- The judgment of an object's INITIAL state, at its creation: the creator's law alone. The pin
governs the writes after the object exists; at creation no package has run, so the pin clause
would refuse every seed. The seed is judged over `old = none`, so an object cannot be born
violating its own state clauses. -/
def admitSeed (record : ObjectRecord) (facts : Facts) (seed : Data) : Except WriteRefusal Unit :=
  judgeLaw record.law facts none seed

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

/-- **A write is admitted exactly when the effective law (the pin clause, then the
creator's law) accepts its views.** -/
theorem admitWrite_ok_iff (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data) :
    admitWrite record facts old new = .ok () ↔
      ∃ before after, views facts old new = some (before, after) ∧
        eval record.effectiveLaw before after = true :=
  judgeLaw_ok_iff record.effectiveLaw facts old new

/-- **A refusal names a clause of the effective law that is false on the same views.** -/
theorem admitWrite_lawDenied_fails (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data)
    (leaf : LawLeaf) (refused : admitWrite record facts old new = .error (.lawDenied leaf)) :
    ∃ before after, views facts old new = some (before, after) ∧
      record.effectiveLaw.subterm leaf.path = some leaf.clause ∧ eval leaf.clause before after = false :=
  judgeLaw_lawDenied_fails record.effectiveLaw facts old new leaf refused

/-- **A seed is admitted exactly when the CREATOR'S law accepts its views** (no pin clause:
nothing has run yet). -/
theorem admitSeed_ok_iff (record : ObjectRecord) (facts : Facts) (seed : Data) :
    admitSeed record facts seed = .ok () ↔
      ∃ before after, views facts none seed = some (before, after) ∧ eval record.law before after = true :=
  judgeLaw_ok_iff record.law facts none seed

/-- **A refused seed names the creator's clause that is false on the seed's views.** -/
theorem admitSeed_lawDenied_fails (record : ObjectRecord) (facts : Facts) (seed : Data) (leaf : LawLeaf)
    (refused : admitSeed record facts seed = .error (.lawDenied leaf)) :
    ∃ before after, views facts none seed = some (before, after) ∧
      record.law.subterm leaf.path = some leaf.clause ∧ eval leaf.clause before after = false :=
  judgeLaw_lawDenied_fails record.law facts none seed leaf refused

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
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at viewed
  obtain ⟨b, -, a, -, hb, ha⟩ := viewed
  exact ⟨b, a, hb.symm, ha.symm⟩

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
      ⟨[0], pinClause record.pin, before.get Minidregg.Pred.objectiveArtifactSlot, some (-1)⟩) := by
  obtain ⟨_, slotAfter⟩ := views_artifact_slot facts old new before after viewed
  have unclaimed : after.get Minidregg.Pred.objectiveArtifactSlot = some (-1) := by
    rw [slotAfter]; simp [Facts.artifactValue, unpinned]
  have named : LawLeaf.of record.effectiveLaw before after =
      some ⟨[0], pinClause record.pin, before.get Minidregg.Pred.objectiveArtifactSlot, some (-1)⟩ :=
    all_pin_names_pin [record.pin.value] [record.law] before after unclaimed
  simp only [admitWrite, judgeLaw, viewed, named]

/-- A write no package code made is never admitted, for every object and value. -/
theorem unpinned_write_refused (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data)
    (unpinned : facts.artifact = none) : admitWrite record facts old new ≠ .ok () := by
  intro admitted
  obtain ⟨before, after, viewed, _⟩ := (admitWrite_ok_iff record facts old new).mp admitted
  have named := unpinned_write_names_pin record facts old new unpinned before after viewed
  rw [named] at admitted
  cases admitted

/-! ### Teeth (kernel-decided, not evaluated by the compiler)

An object pinned to package 7 whose creator's law is the empty conjunction (the most
permissive law there is). `leafOf` / `accepted` read the verdict of `admitWrite`. -/

def teethRecord : ObjectRecord := ⟨⟨1⟩, ⟨7⟩, 1, Pred.all [], .frozen, 0, 0⟩

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

def recordStream : StreamCodec ObjectRecord :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product LawLeaf.predStream
      (StreamCodec.product upgradeStream (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))
    (fun r => (r.id, r.pin, r.schemaVersion, r.law, r.upgrade, r.continuity, r.payer))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2⟩)
    (by intro r; cases r; rfl)

def recordFrame : Bytes := "DREGG/OBJECTIVE/OBJECT-RECORD/v1".toUTF8.toList
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
#assert_axioms record_roundTrip
end Minidregg.Kernel.ObjectRecord
