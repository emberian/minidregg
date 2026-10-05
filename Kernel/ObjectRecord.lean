/- The object record: what an object IS to the kernel, and the one judgment every
write of its declared state passes.

An object is a native resource (`id`, a cell the authority layer issues
capabilities on; never a package hash). Its record names:

* `pin`: the package its new activities and calls run (`package`, the
  `ObjectiveBendSourceArtifact.identity` of a published package);
* `schemaVersion`: the version of the declared-state schema, bumped only by a
  migration (it is not the write counter of the state cell);
* `law`: the decidable predicate (`Pred`) that judges every write of the
  declared state, over the projected old and new views plus the request facts;
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
  /-- Which kernel turn writes: 1 birth, 2 delivery, 3 direct write, 4 creation,
  5 a call frame. -/
  turn : Nat
  /-- The object whose frame called the writing frame (`request/caller`); `none`
  (slot absent) when the write is not a nested call frame's. A callee's law
  names the callers it admits with this slot: an object's facet, as a clause. -/
  caller : Option Nat
  deriving DecidableEq, Repr

def Facts.slots (facts : Facts) : List (Slot × Int) :=
  (facts.subject.map (fun subject => ("request/subject", Int.ofNat subject.value))).toList ++
  [("request/height", Int.ofNat facts.height),
   ("request/target", Int.ofNat facts.target),
   ("request/turn", Int.ofNat facts.turn)] ++
  (facts.caller.map (fun caller => ("request/caller", Int.ofNat caller))).toList

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

/-- The judgment every write of an object's declared state passes. -/
def admitWrite (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data) :
    Except WriteRefusal Unit :=
  match views facts old new with
  | none => .error .unprojectable
  | some (before, after) =>
      match LawLeaf.of record.law before after with
      | none => .ok ()
      | some leaf => .error (.lawDenied leaf)

/-- **A write is admitted exactly when the law accepts its views.** -/
theorem admitWrite_ok_iff (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data) :
    admitWrite record facts old new = .ok () ↔
      ∃ before after, views facts old new = some (before, after) ∧ eval record.law before after = true := by
  unfold admitWrite
  cases viewed : views facts old new with
  | none => simp
  | some pair =>
      obtain ⟨before, after⟩ := pair
      cases named : LawLeaf.of record.law before after with
      | none =>
          have accepts := (LawLeaf.of_none_iff record.law before after).mp named
          simp [named, accepts]
      | some leaf =>
          have rejects : eval record.law before after ≠ true := by
            intro accepts
            have := (LawLeaf.of_none_iff record.law before after).mpr accepts
            rw [named] at this; cases this
          simp [named, rejects]

/-- **A refusal names a clause of the law that is false on the same views.** -/
theorem admitWrite_lawDenied_fails (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data)
    (leaf : LawLeaf) (refused : admitWrite record facts old new = .error (.lawDenied leaf)) :
    ∃ before after, views facts old new = some (before, after) ∧
      record.law.subterm leaf.path = some leaf.clause ∧ eval leaf.clause before after = false := by
  unfold admitWrite at refused
  cases viewed : views facts old new with
  | none => simp [viewed] at refused
  | some pair =>
      obtain ⟨before, after⟩ := pair
      rw [viewed] at refused
      cases named : LawLeaf.of record.law before after with
      | none => simp [named] at refused
      | some found =>
          simp only [named, Except.error.injEq, WriteRefusal.lawDenied.injEq] at refused
          subst refused
          obtain ⟨at_, _, fails⟩ := LawLeaf.of_fails record.law before after found named
          exact ⟨before, after, rfl, at_, fails⟩

/-- **The payer is not authority**: the judgment does not read it. -/
theorem admitWrite_payer_irrelevant (record : ObjectRecord) (payer : Minidregg.Theory.CanonicalResourceKernel.AccountId)
    (facts : Facts) (old : Option Data) (new : Data) :
    admitWrite { record with payer := payer } facts old new = admitWrite record facts old new := rfl

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
#assert_axioms admitWrite_ok_iff
#assert_axioms admitWrite_lawDenied_fails
#assert_axioms admitWrite_payer_irrelevant
#assert_axioms record_roundTrip
end Minidregg.Kernel.ObjectRecord
