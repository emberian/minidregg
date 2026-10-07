/-
# Kernel.ReceivingLawFixture -- the Receiver's law judgement has teeth

A fixture family `bypass` over the deployed `Kernel.Receiving` pipeline (the real
`Family.receiver`, the real loaded durable state of an empty seed) whose
`prepare` judges NO law: it writes the cells it is told to, with whatever law
step it is told to project.  The fixture law source (`laws`) classifies cell 1
as a `declaredObject` whose committed law is `all [objectivePin [7]]`, cell 2 as
a `streamEntry`, cell 4 as the `system` cell, cell 5 as a law-bearing birth whose export law is the same pin, and
nothing else.  It runs at `Id` under an empty-transcript oracle (the bypass family makes
no signature claims) and an exact-append token.

* `bypass_refused_names_pin` -- a non-Objective write (artifact `-1`) to cell 1
  is refused `law (lawDenied 1 ⟨[0], objectivePin [7], -1, -1⟩)`: the clause.
* `bypass_commits_without_judgement` -- the same ingress, through the same
  receiver with ONLY the law judgement removed, commits (the mutation is real).
* `lawful_commits` -- a write the pin admits (artifact 7) to cell 1, with the
  kernel-only cell 2 written by a family its row names, commits: the premise
  of `receive_committed_lawful` and `kernelOnly_writers_sound` is inhabited,
  and both are instantiated on it.
* `noStep_refused`, `foreignWriter_refused`, `unclassified_refused`,
  `registryMismatch_refused`, `birth_noStep_refused` -- every other refusal arm.
* `birth_denied_names_pin` / `birth_commits_without_judgement` / `birth_lawful_commits` -- the
  bypass tooth for BIRTHS: a newborn (cell 5) is judged by its export law, refused at
  its clause with the judgement, committed without it, and committed when lawful.
* `lawSource_birth_denied_names_pin` / `lawSource_birth_lawful_commits` /
  `lawSource_inPlace_foreign_refused` -- a law source (`kernelOnlyOrBorn`): born by
  the pay-enrol family under its export law (refused at the clause, or committed),
  and written in place by it refused by name (only `PolicyInstall` writes one).

The law source here is a fixture; the deployed one is `Laws.physical`, whose
resolution is the DRC's (`ReceivingLaw.physical_resolve_some_iff`), installed
by `receiveLoaded` (`Receiving.Family.receiveLoaded_laws`).
-/
import Kernel.Receiving
import Theory.AcceptedCellEffectWitness
import Theory.AssertCompiled

namespace Minidregg.Kernel.ReceivingLawFixture

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalCellRegistry (Kind FamilyId)
open Minidregg.Compiler.CanonicalPolicyAdmission (PolicyStepContext)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.Receiving
open Minidregg.Kernel.ReceivingLaw (Laws ResolvedLaw LawFault Unavailable Lawful)
open Minidregg.Theory.Receiving (SigQuery Receiver Vouchers)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## The loaded state: an empty seed, through the deployed loader -/

def seed : DurableReceiver.Seed := ⟨[], [], fun _ => 0⟩

def durable? : Option Durable := (DurableReceiverIO.loadSeed rootBytes ⟨0⟩ seed).toOption

theorem durable_loads : durable?.isSome = true := by native_decide

@[irreducible] def durable : Durable := durable?.get durable_loads

/-- The fixture transaction. -/
def txId : Digest := ⟨777⟩

theorem fresh_check : (durable?.map fun loaded => (lookup loaded.snapshot txId).isNone) = some true := by
  native_decide

theorem fresh : lookup durable.snapshot txId = none := by
  have checked := fresh_check
  obtain ⟨value, loaded⟩ := Option.isSome_iff_exists.mp durable_loads
  have same : durable = value := by
    unfold durable
    exact Option.some.inj ((Option.some_get durable_loads).trans loaded)
  rw [same]
  rw [loaded] at checked
  simpa [Option.isNone_iff_eq_none] using checked

/-! ## The law step: a real `PolicyStepContext`, both views naming one artifact -/

open Minidregg.Theory.AcceptedCellEffectWitness in
open Minidregg.Theory.CellStateWitness in
/-- The witness family's candidate: its honest patch, validated at the cell's own root. -/
noncomputable def candidate :
    Minidregg.Theory.PolicyInstall.Candidate family cell () () where
  preStateBound := rfl
  modeEvidence := ()
  validated := cell_root ▸ honestPatch_accepted.choose
  postcondition := by
    have := (cell_root ▸ honestPatch_accepted.choose :
      Minidregg.Theory.CellState.ValidatedPatch materializer cell cell.root honestPatch).resultAt
    exact this

/-- A law state whose Objective slot is `artifact`. -/
def stateWith (artifact : Int) : Minidregg.Pred.State :=
  ⟨[(Minidregg.Pred.objectiveArtifactSlot, artifact)]⟩

/-- The projected step of a write made under `artifact` (`-1`: no Objective claim). -/
noncomputable def stepAt (artifact : Int) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (fun _ => stateWith artifact) ⟨0⟩ candidate

theorem stepAt_old (artifact : Int) : (stepAt artifact).oldState = stateWith artifact := rfl
theorem stepAt_new (artifact : Int) : (stepAt artifact).newState = stateWith artifact := rfl

/-! ## The law source -/

def pinned : Nat := 7

/-- Cell 1's committed law: the package pin, first. -/
def law : Minidregg.Pred.Pred := Minidregg.Pred.Pred.all [Minidregg.Pred.objectivePin [pinned]]

def laws : Laws Durable where
  kindOf _ write :=
    match write.cellId.value with
    | 1 => some .declaredObject
    | 2 => some .streamEntry
    | 4 => some .system
    | 5 => some .declaredObject
    | 6 => some .policySource
    | 7 => some .policySource
    | 8 => some .declaredObject
    | _ => none
  birth _ write := write.cellId.value == 5 || write.cellId.value == 6 || write.cellId.value == 8
  resolve _ target _ := if target = 1 then some ⟨law, true, true, true, true, []⟩ else none
  -- Cell 5 is a newborn whose export law is the same pin.
  -- Cells 5 and 6 are newborns (6 a law source) whose export law is the same pin.
  resolveBirth _ _ write _ :=
    if write.cellId.value = 5 ∨ write.cellId.value = 6 then some ⟨law, true, true, true, true, []⟩
    -- Cell 8 is an unparented newborn: its export law is NEUTRAL (no root).
    else if write.cellId.value = 8 then some ⟨.all [], true, true, true, false, []⟩
    else none

/-! ## The bypass family: writes, projects, judges nothing -/

def write (durable : Durable) (cell : Nat) : DataWrite :=
  ⟨⟨cell⟩, durable.snapshot.model.roots ⟨cell⟩, rootBytes [cell.toUInt8], [cell.toUInt8]⟩

def bypass (id : FamilyId) (cells : List Nat) (stepFor : Nat → Option PolicyStepContext) :
    Family where
  id := id
  Env := Unit
  Ingress := Unit
  Command := Unit
  Reject := Unit
  rejectRepr := inferInstance
  Prepared := fun _ _ _ => Unit
  decode := fun _ => some ()
  bytes := fun _ => []
  command := fun _ => ()
  claims := fun _ _ _ => .ok []
  prepare := fun _ _ _ _ => .ok ()
  writes := fun {_} {durable} {_} _ => cells.map (write durable)
  writes_bound := by
    intro _ durable _ _ written member
    obtain ⟨cell, -, rfl⟩ := List.mem_map.mp member
    rfl
  lawStep := fun _ written _ => stepFor written.cellId.value
  observed := fun _ => []
  physicalPostLaw := fun _ => true
  txId := fun _ _ => txId
  event := fun _ _ => ⟨1, ⟨0⟩, ⟨0⟩, []⟩
  nullifiers := fun _ _ => []
  subject := fun _ => none
  witnessBytes := fun _ => 0

/-- The fixture's oracle: an empty transcript (the fixture families make no
signature claims, so it is never consulted). -/
def oracle : CredentialSignatureIO.Oracle Id := .recorded CredentialSignatureIO.Transcript.empty

/-- The fixture family's receiver, judged by the fixture laws. -/
abbrev judged (F : Family) := F.receiver laws oracle

/-- The same receiver with the law judgement REMOVED: the mutation the tooth runs. -/
def unjudged (F : Family) : Receiver journal (CredentialSignatureAdmission.receiverVerify oracle) :=
  { F.receiver laws oracle with lawFault := fun _ => none }

abbrev Exact : Durable → DataIntent rootBytes → Type := fun _ _ => Unit

def append : (state : Durable) → (intent : DataIntent rootBytes) →
    Id (Receiver.Commit (Exact state intent) Unit) :=
  fun _ _ => pure (.exact ())

/-- An object write under `artifact`, beside a stream entry (no step). -/
noncomputable def objectStep (artifact : Int) : Nat → Option PolicyStepContext :=
  fun cell => if cell = 1 then some (stepAt artifact) else none


/-! ## The teeth -/

/-- The fixture's laws read no source cell: they add no guard. -/
theorem writeGuards_nil (patch : List DataWrite) (written : DataWrite)
    (step : Option PolicyStepContext) :
    ReceivingLaw.writeGuards laws durable patch written step = [] := by
  unfold ReceivingLaw.writeGuards ReceivingLaw.lawOf
  split
  · split <;> (try simp only [laws]) <;> (repeat' split) <;> rfl
  · rfl

/-- The bypass family's physical shape holds on the fixture state, for any two
distinct cells, whatever it projects. -/
theorem shape_ok (id : FamilyId) (stepFor : Nat → Option PolicyStepContext)
    (a : Nat := 1) (b : Nat := 2) (distinct : a ≠ b := by decide) :
    Family.shape (F := bypass id [a, b] stepFor) (env := ()) (durable := durable) (command := ())
      laws () = true := by
  simp only [Family.shape, Family.readGuards, bypass, ReceivingLaw.lawGuards_uniform, writeGuards_nil]
  simp [write, Receiver.guardsOff, distinct]

/-- The law judgement of the bypass family on the fixture state, write by write. -/
theorem fault_eq (id : FamilyId) (stepFor : Nat → Option PolicyStepContext)
    (a : Nat := 1) (b : Nat := 2) :
    Family.lawFault (F := bypass id [a, b] stepFor) (env := ()) (durable := durable) (command := ())
      laws () =
      (ReceivingLaw.judgeWrite laws id durable (ReceivingLaw.authorizerStepsOf laws durable [write durable a, write durable b] (fun written => stepFor written.cellId.value))
      [write durable a, write durable b] (write durable a)
          (stepFor a)).or
        (ReceivingLaw.judgeWrite laws id durable (ReceivingLaw.authorizerStepsOf laws durable [write durable a, write durable b] (fun written => stepFor written.cellId.value))
      [write durable a, write durable b] (write durable b)
          (stepFor b)) := by
  simp only [Family.lawFault, bypass, ReceivingLaw.lawFault_uniform, List.map_cons, List.map_nil,
    List.findSome?_cons, List.findSome?_nil]
  change _ = (ReceivingLaw.judgeWrite laws id durable (ReceivingLaw.authorizerStepsOf laws durable [write durable a, write durable b] (fun written => stepFor written.cellId.value))
      [write durable a, write durable b] (write durable a)
      (stepFor (write durable a).cellId.value)).or
    (ReceivingLaw.judgeWrite laws id durable (ReceivingLaw.authorizerStepsOf laws durable [write durable a, write durable b] (fun written => stepFor written.cellId.value))
      [write durable a, write durable b] (write durable b)
      (stepFor (write durable b).cellId.value))
  generalize ReceivingLaw.judgeWrite laws id durable (ReceivingLaw.authorizerStepsOf laws durable [write durable a, write durable b] (fun written => stepFor written.cellId.value))
      [write durable a, write durable b] (write durable a)
    (stepFor (write durable a).cellId.value) = first
  generalize ReceivingLaw.judgeWrite laws id durable (ReceivingLaw.authorizerStepsOf laws durable [write durable a, write durable b] (fun written => stepFor written.cellId.value))
      [write durable a, write durable b] (write durable b)
    (stepFor (write durable b).cellId.value) = second
  cases first <;> cases second <;> rfl

theorem fault_pin :
    Family.lawFault (F := bypass .declaredResourceController [1, 2] (objectStep (-1))) (env := ())
      (durable := durable) (command := ()) laws () =
      some (.lawDenied 1 ⟨[0], Minidregg.Pred.objectivePin [pinned], some (-1), some (-1)⟩) := by
  rw [fault_eq]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, objectStep, CanonicalCellRegistry.Kind.lawClass,
    stepAt_old, stepAt_new]
  decide

/-! ## The pipeline on the fixture state -/

section Pipeline

variable {verify : SigQuery → Id (Except String Bool)} (R : Receiver journal verify)
  {env : R.Env} {ingress : R.Ingress} {prepared : R.Prepared env durable (R.command ingress)}

theorem admitVia_error {reason : Theory.Receiving.Refusal R.Reject R.Fault}
    (noClaims : R.claims env durable ingress = .ok [])
    (refused : R.admit env durable ingress Vouchers.empty = .error reason)
    (noObserved : R.observations env durable ingress = .ok [] := by rfl) :
    R.admitVia env durable ingress = pure (.error reason) := by
  unfold Receiver.admitVia
  simp only [noClaims, noObserved, Receiver.verifyAll, Receiver.observeAll, pure_bind]
  split
  · rename_i reason' admitted
    rw [refused] at admitted
    cases admitted
    rfl
  · rename_i accepted admitted
    rw [refused] at admitted
    cases admitted

theorem admitVia_ok
    (noClaims : R.claims env durable ingress = .ok [])
    (prepares : R.prepare Vouchers.empty env durable (R.command ingress) = .ok prepared)
    (shaped : R.shape prepared = true) (lawful : R.lawFault prepared = none)
    (noObserved : R.observations env durable ingress = .ok [] := by rfl) :
    ∃ admission, R.admitVia env durable ingress = pure (.ok admission) := by
  unfold Receiver.admitVia
  simp only [noClaims, noObserved, Receiver.verifyAll, Receiver.observeAll, pure_bind]
  split
  · rename_i reason admitted
    obtain ⟨accepted, ok, -⟩ := R.admit_ok_of noClaims (by simp) prepares shaped lawful
    rw [ok] at admitted
    cases admitted
  · exact ⟨_, rfl⟩

/-- On the fixture state, an ingress that decodes, is fresh, needs no signature,
prepares and passes the physical shape is decided by the law judgement alone:
refused naming the fault ... -/
theorem receive_faulted {fault : R.Fault}
    (decoded : R.decode [] = some ingress) (isFresh : R.replay env durable ingress = none)
    (noClaims : R.claims env durable ingress = .ok [])
    (prepares : R.prepare Vouchers.empty env durable (R.command ingress) = .ok prepared)
    (shaped : R.shape prepared = true) (faulted : R.lawFault prepared = some fault)
    (noObserved : R.observations env durable ingress = .ok [] := by rfl) :
    R.receive append env durable [] = pure (.refused (.law fault)) := by
  have refused := R.admit_law_refused (vouchers := Vouchers.empty) noClaims (by simp) prepares
    shaped faulted
  unfold Receiver.receive
  simp only [decoded, isFresh, admitVia_error R noClaims refused noObserved]
  rfl

/-- ... or committed. -/
theorem receive_lawful
    (decoded : R.decode [] = some ingress) (isFresh : R.replay env durable ingress = none)
    (noClaims : R.claims env durable ingress = .ok [])
    (prepares : R.prepare Vouchers.empty env durable (R.command ingress) = .ok prepared)
    (shaped : R.shape prepared = true) (lawful : R.lawFault prepared = none)
    (noObserved : R.observations env durable ingress = .ok [] := by rfl) :
    ∃ admission witness,
      R.receive append env durable [] = pure (.committed ingress admission witness) := by
  obtain ⟨admission, admitted⟩ := admitVia_ok R noClaims prepares shaped lawful noObserved
  refine ⟨admission, (), ?_⟩
  unfold Receiver.receive
  simp only [decoded, isFresh, admitted, pure_bind]
  rfl

end Pipeline

theorem bypass_fresh' (id : FamilyId) (stepFor : Nat → Option PolicyStepContext) (a b : Nat) :
    ((bypass id [a, b] stepFor).receiver laws oracle).replay () durable () = none := by
  simp [Receiver.replay, Family.receiver, journal, bypass, fresh]

theorem bypass_fresh (id : FamilyId) (stepFor : Nat → Option PolicyStepContext) :
    ((bypass id [1, 2] stepFor).receiver laws oracle).replay () durable () = none :=
  bypass_fresh' id stepFor 1 2

/-! ## The teeth -/

/-- **The bypass is refused, naming the clause.**  A family that writes the
law-bearing cell 1 under a non-Objective step and judges nothing in `prepare`
is refused by the Receiver: `lawDenied` at the pin, path `[0]`, reading `-1`. -/
theorem bypass_refused_names_pin :
    ((bypass .declaredResourceController [1, 2] (objectStep (-1))).receiver laws oracle).receive
        append () durable [] =
      pure (.refused (.law (.lawDenied 1
        ⟨[0], Minidregg.Pred.objectivePin [pinned], some (-1), some (-1)⟩))) :=
  receive_faulted _ rfl (bypass_fresh .declaredResourceController (objectStep (-1))) rfl rfl
    (shape_ok .declaredResourceController (objectStep (-1))) fault_pin

/-- **Remove the judgement and the same ingress commits.**  The mutant receiver
is the bypass family's own receiver with only `lawFault` replaced by `none`; the
same bytes on the same state COMMIT (asserted: the outcome is `committed`), so
the refusal above is the Receiver's law judgement and nothing else. -/
theorem bypass_commits_without_judgement :
    ∃ admission witness,
      (unjudged (bypass .declaredResourceController [1, 2] (objectStep (-1)))).receive
          append () durable [] = pure (.committed () admission witness) :=
  receive_lawful _ rfl (bypass_fresh .declaredResourceController (objectStep (-1))) rfl rfl
    (shape_ok .declaredResourceController (objectStep (-1))) rfl

theorem fault_lawful :
    Family.lawFault (F := bypass .declaredResourceController [1, 2] (objectStep pinned))
      (env := ()) (durable := durable) (command := ()) laws () = none := by
  rw [fault_eq]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, objectStep, CanonicalCellRegistry.Kind.lawClass,
    stepAt_old, stepAt_new]
  decide

/-- **A lawful write commits**: the pin admits the Objective step on cell 1, and
the kernel-only stream entry (cell 2) is written by a family its row names. -/
theorem lawful_commits :
    ∃ admission witness,
      ((bypass .declaredResourceController [1, 2] (objectStep pinned)).receiver laws oracle).receive
          append () durable [] = pure (.committed () admission witness) :=
  receive_lawful _ rfl (bypass_fresh .declaredResourceController (objectStep pinned)) rfl rfl
    (shape_ok .declaredResourceController (objectStep pinned)) fault_lawful

/-- `receive_committed_lawful` and `kernelOnly_writers_sound`, instantiated on
the committed fixture: their premise is inhabited. -/
theorem lawful_commits_judged :
    ∃ admission witness,
      ((bypass .declaredResourceController [1, 2] (objectStep pinned)).receiver laws oracle).receive
          append () durable [] = pure (.committed () admission witness) ∧
      (∀ written (member : written ∈ (bypass .declaredResourceController [1, 2]
          (objectStep pinned)).writes (env := ()) (durable := durable) (command := ())
            admission.accepted.prepared),
        Lawful laws .declaredResourceController durable
          ((bypass .declaredResourceController [1, 2] (objectStep pinned)).writes (env := ())
            (durable := durable) (command := ()) admission.accepted.prepared) written
          ((bypass .declaredResourceController [1, 2] (objectStep pinned)).lawStep
            (env := ()) (durable := durable) (command := ()) admission.accepted.prepared written
            member)) ∧
      (∀ written ∈ (bypass .declaredResourceController [1, 2] (objectStep pinned)).writes
          (env := ()) (durable := durable) (command := ()) admission.accepted.prepared,
        ∀ (kind : Kind) (writers : List FamilyId),
        laws.kindOf durable written = some kind → kind.lawClass = .kernelOnly writers →
          FamilyId.declaredResourceController ∈ writers) := by
  obtain ⟨admission, witness, committed⟩ := lawful_commits
  exact ⟨admission, witness, committed,
    Family.receive_committed_lawful (bypass .declaredResourceController [1, 2] (objectStep pinned))
      committed,
    Family.kernelOnly_writers_sound (bypass .declaredResourceController [1, 2] (objectStep pinned))
      committed⟩

/-! ## Every other refusal arm -/

/-- A law-bearing write with no step is refused, not admitted. -/
theorem noStep_refused :
    ((bypass .declaredResourceController [1, 2] (fun _ => none)).receiver laws oracle).receive
        append () durable [] = pure (.refused (.law (.lawUnavailable 1 .noStep))) := by
  refine receive_faulted _ rfl (bypass_fresh .declaredResourceController (fun _ => none)) rfl rfl
    (shape_ok .declaredResourceController (fun _ => none)) ?_
  change Family.lawFault (F := bypass .declaredResourceController [1, 2] (fun _ => none))
    (env := ()) (durable := durable)
    (command := ()) laws () = _
  rw [fault_eq]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, CanonicalCellRegistry.Kind.lawClass]
  rfl

/-- A family not named in the `streamEntry` row writing one is refused. -/
theorem foreignWriter_refused :
    ((bypass .clockTick [1, 2] (objectStep pinned)).receiver laws oracle).receive
        append () durable [] =
      pure (.refused (.law (.kernelOnlyForeignWriter 2 .streamEntry .clockTick))) := by
  refine receive_faulted _ rfl (bypass_fresh .clockTick (objectStep pinned)) rfl rfl
    (shape_ok .clockTick (objectStep pinned)) ?_
  change Family.lawFault (F := bypass .clockTick [1, 2] (objectStep pinned))
    (env := ()) (durable := durable)
    (command := ()) laws () = _
  rw [fault_eq]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, objectStep, CanonicalCellRegistry.Kind.lawClass,
    stepAt_old, stepAt_new]
  decide

/-- A step offered for a kernel-only cell is a registry mismatch. -/
theorem registryMismatch_refused :
    ((bypass .declaredResourceController [1, 2] (fun _ => some (stepAt pinned))).receiver laws oracle).receive
        append () durable [] =
      pure (.refused (.law (.registryMismatch 2 .streamEntry))) := by
  refine receive_faulted _ rfl (bypass_fresh .declaredResourceController (fun _ => some (stepAt pinned))) rfl rfl
    (shape_ok .declaredResourceController (fun _ => some (stepAt pinned))) ?_
  change Family.lawFault (F := bypass .declaredResourceController [1, 2] (fun _ => some (stepAt pinned)))
    (env := ()) (durable := durable)
    (command := ()) laws () = _
  rw [fault_eq]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, CanonicalCellRegistry.Kind.lawClass,
    stepAt_old, stepAt_new]
  decide

/-- A write to a cell no registry row classifies is refused (fail-closed). -/
theorem unclassified_refused :
    ((bypass .declaredResourceController [9, 2] (fun _ => none)).receiver laws oracle).receive
        append () durable [] = pure (.refused (.law (.unclassified 9))) := by
  refine receive_faulted _ rfl (bypass_fresh' .declaredResourceController (fun _ => none) 9 2) rfl rfl
    (shape_ok .declaredResourceController (fun _ => none) 9 2) ?_
  change Family.lawFault (F := bypass .declaredResourceController [9, 2] (fun _ => none))
    (env := ())
    (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 9 2]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws]
  rfl

/-- A newborn's step: only the birth (cell 5, or `born`) gets one, under `artifact`. -/
noncomputable def bornStep (artifact : Int) (born : Nat := 5) : Nat → Option PolicyStepContext :=
  fun cell => if cell = born then some (stepAt artifact) else none

/-- **A birth is judged by its export law, not skipped**: a family that bears cell
5 and judges nothing is refused by the Receiver at the export law's clause. -/
theorem birth_denied_names_pin :
    ((bypass .declaredResourceController [5, 2] (bornStep (-1))).receiver laws oracle).receive
        append () durable [] =
      pure (.refused (.law (.lawDenied 5
        ⟨[0], Minidregg.Pred.objectivePin [pinned], some (-1), some (-1)⟩))) := by
  refine receive_faulted _ rfl (bypass_fresh' .declaredResourceController (bornStep (-1)) 5 2) rfl
    rfl (shape_ok .declaredResourceController (bornStep (-1)) 5 2) ?_
  change Family.lawFault (F := bypass .declaredResourceController [5, 2] (bornStep (-1)))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 5 2]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, bornStep,
    CanonicalCellRegistry.Kind.lawClass, stepAt_old, stepAt_new]
  decide

/-- Remove the judgement and the same birth commits (the mutation is real). -/
theorem birth_commits_without_judgement :
    ∃ admission witness,
      (unjudged (bypass .declaredResourceController [5, 2] (bornStep (-1)))).receive
          append () durable [] = pure (.committed () admission witness) :=
  receive_lawful _ rfl (bypass_fresh' .declaredResourceController (bornStep (-1)) 5 2) rfl rfl
    (shape_ok .declaredResourceController (bornStep (-1)) 5 2) rfl

/-- A birth its export law admits commits. -/
theorem birth_lawful_commits :
    ∃ admission witness,
      ((bypass .declaredResourceController [5, 2] (bornStep pinned)).receiver laws oracle).receive
          append () durable [] = pure (.committed () admission witness) := by
  refine receive_lawful _ rfl (bypass_fresh' .declaredResourceController (bornStep pinned) 5 2) rfl
    rfl (shape_ok .declaredResourceController (bornStep pinned) 5 2) ?_
  change Family.lawFault (F := bypass .declaredResourceController [5, 2] (bornStep pinned))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 5 2]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, bornStep,
    CanonicalCellRegistry.Kind.lawClass, stepAt_old, stepAt_new]
  decide

/-- A birth with no step is refused, not admitted. -/
theorem birth_noStep_refused :
    ((bypass .declaredResourceController [5, 2] (fun _ => none)).receiver laws oracle).receive
        append () durable [] = pure (.refused (.law (.lawUnavailable 5 .noStep))) := by
  refine receive_faulted _ rfl (bypass_fresh' .declaredResourceController (fun _ => none) 5 2) rfl
    rfl (shape_ok .declaredResourceController (fun _ => none) 5 2) ?_
  change Family.lawFault (F := bypass .declaredResourceController [5, 2] (fun _ => none))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 5 2]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, CanonicalCellRegistry.Kind.lawClass]
  rfl

/-! ### Law sources (`kernelOnlyOrBorn`): born under the export law, else only `PolicyInstall` -/

/-- **A law source born by a family that is not its writer is judged by its export
law**: the pay-enrol family bearing law source 6 under a step its export law
refuses is refused at the export law's clause. -/
theorem lawSource_birth_denied_names_pin :
    ((bypass .payEnrol [6, 2] (bornStep (-1) 6)).receiver laws oracle).receive
        append () durable [] =
      pure (.refused (.law (.lawDenied 6
        ⟨[0], Minidregg.Pred.objectivePin [pinned], some (-1), some (-1)⟩))) := by
  refine receive_faulted _ rfl (bypass_fresh' .payEnrol (bornStep (-1) 6) 6 2) rfl
    rfl (shape_ok .payEnrol (bornStep (-1) 6) 6 2) ?_
  change Family.lawFault (F := bypass .payEnrol [6, 2] (bornStep (-1) 6))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 6 2]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, bornStep,
    CanonicalCellRegistry.Kind.lawClass, stepAt_old, stepAt_new]
  decide

/-- A step for law source 6 and the object cell 1 it governs, under `artifact`. -/
noncomputable def sourceStep (artifact : Int) : Nat → Option PolicyStepContext :=
  fun cell => if cell = 1 ∨ cell = 6 then some (stepAt artifact) else none

/-- The same law-source birth, admitted by its export law (beside a lawful write of
the object it governs), commits. -/
theorem lawSource_birth_lawful_commits :
    ∃ admission witness,
      ((bypass .payEnrol [6, 1] (sourceStep pinned)).receiver laws oracle).receive
          append () durable [] = pure (.committed () admission witness) := by
  refine receive_lawful _ rfl (bypass_fresh' .payEnrol (sourceStep pinned) 6 1) rfl
    rfl (shape_ok .payEnrol (sourceStep pinned) 6 1) ?_
  change Family.lawFault (F := bypass .payEnrol [6, 1] (sourceStep pinned))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 6 1]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, sourceStep,
    CanonicalCellRegistry.Kind.lawClass, stepAt_old, stepAt_new]
  decide

/-- **A live law source is written in place only by `PolicyInstall`**: the pay-enrol
family writing live law source 7 is refused by name, whatever it projects. -/
theorem lawSource_inPlace_foreign_refused :
    ((bypass .payEnrol [7, 2] (fun _ => none)).receiver laws oracle).receive
        append () durable [] =
      pure (.refused (.law (.kernelOnlyForeignWriter 7 .policySource .payEnrol))) := by
  refine receive_faulted _ rfl (bypass_fresh' .payEnrol (fun _ => none) 7 2) rfl
    rfl (shape_ok .payEnrol (fun _ => none) 7 2) ?_
  change Family.lawFault (F := bypass .payEnrol [7, 2] (fun _ => none))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 7 2]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws,
    CanonicalCellRegistry.Kind.lawClass]
  decide

/-! ### Neutral births: named by a judged authorizer, or refused -/

theorem write_cellId (durable : Durable) (cell : Nat) : (write durable cell).cellId = ⟨cell⟩ := rfl

/-- A step whose new state names newborn 8 (`ReceivingLaw.namesBirth`) beside the
pinned artifact. -/
def stateNaming : Minidregg.Pred.State :=
  ⟨(ReceivingLaw.birthSlot 8, Int.ofNat (write durable 8).exactPost.value) :: (stateWith pinned).slots⟩

noncomputable def namingStep : PolicyStepContext :=
  PolicyStepContext.ofCandidate (fun _ => stateNaming) ⟨0⟩ candidate

theorem namingStep_old : namingStep.oldState = stateNaming := rfl
theorem namingStep_new : namingStep.newState = stateNaming := rfl

/-- The naming step names newborn 8 (its id and exact post root). -/
theorem namingStep_names : ReceivingLaw.namesBirth namingStep (write durable 8) = true := by
  simp [ReceivingLaw.namesBirth, namingStep_new, stateNaming, Minidregg.Pred.State.get, write_cellId]

/-- Object cell 1 under `forObject`, newborn 8 under the pinned step. -/
noncomputable def authorizedStep (forObject : PolicyStepContext) : Nat → Option PolicyStepContext :=
  fun cell => if cell = 1 then some forObject else if cell = 8 then some (stepAt pinned) else none

/-- **A neutral birth with no authorizer is refused by name**: newborn 8 beside a
kernel-only stream entry (no law-bearing write names it). -/
theorem neutral_unauthorized_refused :
    ((bypass .declaredResourceController [8, 2] (bornStep pinned 8)).receiver laws oracle).receive
        append () durable [] = pure (.refused (.law (.neutralBirthUnjudged 8))) := by
  refine receive_faulted _ rfl (bypass_fresh' .declaredResourceController (bornStep pinned 8) 8 2) rfl
    rfl (shape_ok .declaredResourceController (bornStep pinned 8) 8 2) ?_
  change Family.lawFault (F := bypass .declaredResourceController [8, 2] (bornStep pinned 8))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 8 2]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.authorizerStepsOf, ReceivingLaw.authorizes, ReceivingLaw.lawOf, write, laws,
    bornStep, CanonicalCellRegistry.Kind.lawClass]
  rfl

/-- **Smuggling is refused**: a patch with a legitimate, judged object write (cell
1 under the pin) and a neutral newborn 8 its step does NOT name refuses the
newborn by name. -/
theorem neutral_smuggled_refused :
    ((bypass .declaredResourceController [1, 8] (authorizedStep (stepAt pinned))).receiver laws
        oracle).receive append () durable [] = pure (.refused (.law (.neutralBirthUnjudged 8))) := by
  refine receive_faulted _ rfl
    (bypass_fresh' .declaredResourceController (authorizedStep (stepAt pinned)) 1 8) rfl
    rfl (shape_ok .declaredResourceController (authorizedStep (stepAt pinned)) 1 8) ?_
  change Family.lawFault (F := bypass .declaredResourceController [1, 8] (authorizedStep (stepAt pinned)))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 1 8]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.authorizerStepsOf, ReceivingLaw.authorizes, ReceivingLaw.namesBirth,
    ReceivingLaw.birthSlot,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write, laws, authorizedStep,
    CanonicalCellRegistry.Kind.lawClass, stepAt_old, stepAt_new, stateWith,
    Minidregg.Pred.State.get]
  decide

/-- **The control commits**: the same newborn, named (id and post root) by the
step the object's pin law judged. -/
theorem neutral_named_commits :
    ∃ admission witness,
      ((bypass .declaredResourceController [1, 8] (authorizedStep namingStep)).receiver laws
          oracle).receive append () durable [] = pure (.committed () admission witness) := by
  refine receive_lawful _ rfl (bypass_fresh' .declaredResourceController (authorizedStep namingStep) 1 8)
    rfl rfl (shape_ok .declaredResourceController (authorizedStep namingStep) 1 8) ?_
  change Family.lawFault (F := bypass .declaredResourceController [1, 8] (authorizedStep namingStep))
    (env := ()) (durable := durable) (command := ()) laws () = _
  rw [fault_eq _ _ 1 8]
  simp [ReceivingLaw.judgeWrite, ReceivingLaw.judgeKernel, ReceivingLaw.judgeBearing,
    ReceivingLaw.authorizerStepsOf, ReceivingLaw.authorizes, namingStep_names,
    ReceivingLaw.judgeLaw, ReceivingLaw.lawOf, write_cellId, laws,
    authorizedStep, CanonicalCellRegistry.Kind.lawClass, namingStep_old, namingStep_new,
    stepAt_old, stepAt_new]
  decide

#assert_compiled durable_loads
#assert_compiled unclassified_refused
#assert_compiled birth_denied_names_pin
#assert_compiled birth_commits_without_judgement
#assert_compiled birth_lawful_commits
#assert_compiled birth_noStep_refused
#assert_compiled lawSource_birth_denied_names_pin
#assert_compiled lawSource_birth_lawful_commits
#assert_compiled lawSource_inPlace_foreign_refused
#assert_compiled neutral_unauthorized_refused
#assert_compiled neutral_smuggled_refused
#assert_compiled neutral_named_commits
#assert_compiled namingStep_names
#assert_compiled writeGuards_nil
#assert_compiled fresh
#assert_compiled bypass_refused_names_pin
#assert_compiled bypass_commits_without_judgement
#assert_compiled lawful_commits_judged
#assert_compiled noStep_refused
#assert_compiled foreignWriter_refused
#assert_compiled registryMismatch_refused
#assert_compiled shape_ok
#assert_compiled fault_pin
#assert_compiled receive_faulted
#assert_compiled receive_lawful

end Minidregg.Kernel.ReceivingLawFixture
