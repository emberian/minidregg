/-
# Kernel.Run — the kernel checks a run by re-executing it, on any registered evaluator

(K-RAN, NOCK §2.4–§2.5; made generic by K-EVAL E2, EVAL §1.4.) A runner submits
field writes together with a `RunClaim`: the program it ran, the sample it ran on
(the evaluator's input bytes), the output it got (the evaluator's output bytes) and
the metered step count. The program record names its evaluator
(`NockProgramCodec.Program.evaluator`, covered by `programId`); the kernel resolves it
against the compiled-in registry (`resolve`: an id no entry has refuses
`unknownEvaluator`, an entry the operator disabled `evaluatorDisabled`) and admits
the writes only when its own run on that evaluator agrees:

1. the claimed sample is byte-equal to the kernel's `E.sampleOf` (else `sampleStale`;
   under a `pinned` context the refusal names the first ABI slot whose value the
   claim's sample does not hold, `E.staleField`);
2. the claimed steps fit the program's ABI fuel (else `fuelExceeded`);
3. the evaluator's oracle, given exactly the claimed steps as fuel, answers (else
   `crash k` / `exhausted k`, naming the count) in exactly that many steps (else
   `stepsMismatch k`);
4. the output bytes are the claimed bytes (else `outputMismatch`);
5. the output decodes against `abi.outputs` (`E.writesOf`, else `outputMalformed`),
   and the command's writes are exactly the decoded writes: a write the output does
   not name refuses `writeNotInOutput`, a decoded write the command omits refuses
   `outputNotWritten`.

`checkRun` and `dryRun` take a `Machine` (an evaluator's data); the theorems take an
`Evaluator` and are proved once here over `E.Spec`, then instantiated at Nock under
their K-RAN / K-RUN-PIN names in `Run.nock`. The decided poles run `checkRun` on
`Machine.nock`. Nock's own pieces (N16's `subjectFormula`, the oracle,
`decodeWrites`, `staleField`) are `Kernel.NockEntry`.

The claimed step count is the runner's fuel AND the fee it signs for: the kernel
never charges a count the runner did not sign, and the count is the evaluator's
(`steps_equal_oracle`), independent of the claim's fuel.
-/
import Compiler.Evaluator
import Kernel.NockProgramCell

namespace Minidregg.Kernel.Run
open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel.NockProgramCell
set_option autoImplicit false

/-! ## The claim and the refusals -/

/-- What a runner signs beside its command. -/
structure RunClaim where
  programId : Digest
  /-- The bytes of the sample the runner ran on (the kernel's op-133/134 sample). -/
  sampleJam : List UInt8
  /-- The bytes of the product the runner got. -/
  outputJam : List UInt8
  /-- The evaluator's metered count: the run's fuel and the fee. -/
  steps : Nat
  deriving DecidableEq, Repr

inductive Refusal where
  | programUnknown
  /-- The program record names an evaluator id no compiled-in entry has (K-EVAL). -/
  | unknownEvaluator
  /-- The program's evaluator is compiled in and the operator disabled it. -/
  | evaluatorDisabled
  | libraryUnknown
  /-- A library cell names another evaluator than the program run over it. -/
  | libraryEvaluator
  | libraryNested
  | programMalformed
  /-- The record's params do not decode on its evaluator (E3, `Machine.decodeParams`). -/
  | paramsMalformed
  | sampleUnavailable
  /-- NC-2: a sample value above its slot's declared maximum (`SampleSlot.max`). -/
  | fieldOverMax
  /-- The claimed sample is not the kernel's. Under a `pinned` context (K-RUN-PIN)
  it names the key of the first ABI slot whose value moved (`staleField`). -/
  | sampleStale (field : Option String)
  | fuelExceeded
  | crash (steps : Nat)
  | exhausted (steps : Nat)
  | stepsMismatch (steps : Nat)
  | outputMismatch
  | outputMalformed
  | writeNotInOutput
  | outputNotWritten
  /-- N11 (`Kernel.NockDoor`): the door's refusals. -/
  | doorProgram
  | notDoor
  | stateMalformed
  | eventMalformed
  | doorShape
  | effectNotWrite
  /-- A door ABI under an evaluator that has no doors (`Machine.door = none`, E4). -/
  | doorUnsupported
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .programUnknown => "programUnknown"
  | .unknownEvaluator => "unknownEvaluator"
  | .evaluatorDisabled => "evaluatorDisabled"
  | .libraryUnknown => "libraryUnknown"
  | .libraryEvaluator => "libraryEvaluator"
  | .libraryNested => "libraryNested"
  | .programMalformed => "programMalformed"
  | .paramsMalformed => "paramsMalformed"
  | .sampleUnavailable => "sampleUnavailable"
  | .fieldOverMax => "fieldOverMax"
  | .sampleStale _ => "sampleStale"
  | .fuelExceeded => "fuelExceeded"
  | .crash _ => "crash"
  | .exhausted _ => "exhausted"
  | .stepsMismatch _ => "stepsMismatch"
  | .outputMismatch => "outputMismatch"
  | .outputMalformed => "outputMalformed"
  | .writeNotInOutput => "writeNotInOutput"
  | .outputNotWritten => "outputNotWritten"
  | .doorProgram => "doorProgram"
  | .notDoor => "notDoor"
  | .stateMalformed => "stateMalformed"
  | .eventMalformed => "eventMalformed"
  | .doorShape => "doorShape"
  | .effectNotWrite => "effectNotWrite"
  | .doorUnsupported => "doorUnsupported"

/-- An accepted run: the product, its count, and the writes it names. -/
structure Verdict (Output : Type) where
  output : Output
  steps : Nat
  writes : List FieldWrite
  deriving DecidableEq, Repr

/-- What the controller keeps of an accepted run, whatever the evaluator: the
product's bytes, the count, the writes. -/
structure Accepted where
  output : List UInt8
  steps : Nat
  writes : List FieldWrite
  deriving DecidableEq, Repr

def Verdict.erase (M : Machine) (verdict : Verdict M.Output) : Accepted :=
  ⟨M.encodeOutput verdict.output, verdict.steps, verdict.writes⟩

def require {α : Type} (reason : Refusal) : Option α → Except Refusal α
  | none => .error reason
  | some a => .ok a

@[simp] theorem require_some {α : Type} (reason : Refusal) (a : α) :
    require reason (some a) = .ok a := rfl
@[simp] theorem require_none {α : Type} (reason : Refusal) :
    require reason (none : Option α) = .error reason := rfl

/-! ## The registry at run time

The registry is compiled in (`Evaluator.registry`); an operator may disable an
entry (`disabled`, a profile parameter the runtime semantics commits); nothing
adds one. A program naming any id outside the registry is refused by name. -/

def Refusal.ofUnresolved : Evaluator.Unresolved → Refusal
  | .unknownEvaluator => .unknownEvaluator
  | .evaluatorDisabled => .evaluatorDisabled

/-- The run's resolution is the registry's (`Compiler.Evaluator.resolve`, which a record's
birth also meets), its refusals named in the run's vocabulary. -/
def resolve (disabled : List Digest) (id : Digest) : Except Refusal Evaluator :=
  (Evaluator.resolve disabled id).mapError Refusal.ofUnresolved

/-- **`resolve_registered`**: what `resolve` admits is a compiled-in entry with
exactly the named id, not disabled. Never friend-extensible. -/
theorem resolve_registered {disabled : List Digest} {id : Digest} {E : Evaluator}
    (h : resolve disabled id = .ok E) :
    E ∈ Evaluator.registry ∧ E.id = id ∧ E.id ∉ disabled := by
  unfold resolve at h
  cases hr : Evaluator.resolve disabled id with
  | error e => rw [hr] at h; simp [Except.mapError] at h
  | ok E' => rw [hr] at h; cases h; exact Evaluator.resolve_registered hr

theorem resolve_unknown {disabled : List Digest} {id : Digest}
    (absent : ∀ E ∈ Evaluator.registry, E.id ≠ id) :
    resolve disabled id = .error .unknownEvaluator := by
  unfold resolve; rw [Evaluator.resolve_unknown absent]; rfl

/-- Pole: an id that is not Nock's is refused `unknownEvaluator`, whatever is disabled. -/
theorem pole_unknownEvaluator (disabled : List Digest) (id : Digest)
    (other : id ≠ Evaluator.nock.id) : resolve disabled id = .error .unknownEvaluator := by
  unfold resolve; rw [Evaluator.pole_unknownEvaluator disabled id other]; rfl

/-- The refusal pole is inhabited: of the ids 0 and 1, at least one is not Nock's. -/
theorem unknownEvaluator_inhabited (disabled : List Digest) :
    ∃ id, resolve disabled id = .error .unknownEvaluator := by
  obtain ⟨id, h⟩ := Evaluator.unknownEvaluator_inhabited disabled
  exact ⟨id, by unfold resolve; rw [h]; rfl⟩

/-- Pole: Nock's id resolves to Nock unless the operator disabled it. -/
theorem nock_found :
    Evaluator.registry.find? (fun E => decide (E.id = Evaluator.nock.id)) = some Evaluator.nock :=
  Evaluator.nock_found

theorem pole_nock_resolves (disabled : List Digest) (enabled : Evaluator.nock.id ∉ disabled) :
    resolve disabled Evaluator.nock.id = .ok Evaluator.nock := by
  unfold resolve; rw [Evaluator.pole_nock_resolves disabled enabled]; rfl

/-- Pole: disabled by the operator, Nock is refused `evaluatorDisabled`. -/
theorem pole_evaluatorDisabled :
    resolve [Evaluator.nock.id] Evaluator.nock.id = .error .evaluatorDisabled := by
  unfold resolve
  rw [Evaluator.pole_evaluatorDisabled _ (List.mem_singleton_self _)]; rfl

/-- Every library cell names the program's own evaluator. -/
def librariesAgree (program : Program) (libraries : List Program) : Bool :=
  libraries.all fun library => decide (library.evaluator = program.evaluator)

/-! ## The decision -/

/-- The library codes, refused if a library names libraries of its own. -/
def libraryCodes (M : Machine) (libraries : List Program) : Except Refusal (List M.Code) :=
  libraries.mapM fun library =>
    if library.abi.libraries.isEmpty then require .programMalformed (M.decode library.jam)
    else .error .libraryNested

/-- **`checkRun`**: re-execute `program` (with its loaded `libraries`) on the
kernel's `sample` and decide `claim` against the command's `writes`. -/
def checkRun (M : Machine) (program : Program) (libraries : List Program) (sample : M.Input)
    (claim : RunClaim) (writes : List FieldWrite) : Except Refusal (Verdict M.Output) := do
  if claim.sampleJam ≠ M.encodeInput sample then
    throw (.sampleStale (M.staleField program.abi sample claim.sampleJam))
  if program.abi.fuel < claim.steps then throw .fuelExceeded
  -- C5: hold check here (K-RUN-HOLD: a claim above the free threshold needs a hold;
  -- the steps are fixed and bounded by the ABI fuel from this line on).
  let code ← require .programMalformed (M.decode program.jam)
  let params ← require .paramsMalformed (M.decodeParams program.params)
  let libs ← libraryCodes M libraries
  match M.oracle claim.steps (M.entry params code libs sample) with
  | .crash k => throw (.crash k)
  | .exhausted k => throw (.exhausted k)
  | .ok out k =>
    if k ≠ claim.steps then throw (.stepsMismatch k)
    if M.encodeOutput out ≠ claim.outputJam then throw .outputMismatch
    let decoded ← require .outputMalformed (M.writesOf program.abi out)
    if !writes.all (· ∈ decoded) then throw .writeNotInOutput
    if !decoded.all (· ∈ writes) then throw .outputNotWritten
    pure ⟨out, k, decoded⟩

/-- The run of `program` on `sample` that the kernel would perform: its term, when
the program, its params and its libraries decode. -/
def runOf (M : Machine) (program : Program) (libraries : List Program) (sample : M.Input) :
    Option M.Term :=
  match M.decode program.jam, M.decodeParams program.params, libraryCodes M libraries with
  | some code, some params, .ok libs => some (M.entry params code libs sample)
  | _, _, _ => none

/-! ## Op 134: the runner's dry run

The kernel's sample for client-supplied participant values at the Host's
current logical height, and the oracle's answer at the ABI fuel: what a runner
copies into its claim. It reads no target cell (values are the runner's own
signed views), so it discloses nothing a program cell does not. -/

inductive DryRun where
  | missingProgram
  | ambiguousValues
  | refused (reason : Refusal)
  | ran (sample : List UInt8) (result : Ran (List UInt8)) (writes : Option (List FieldWrite))

/-- The dry run once the program, its evaluator and its libraries are loaded. -/
def dryRunOn (M : Machine) (program : Program) (libraries : List Program) (ctx : Context)
    (targets : List Nat) (read : Nat → String → Option Int) : DryRun :=
  match M.sampleOf program.abi ctx targets read with
  | none => .refused .sampleUnavailable
  | some sample =>
    match M.decode program.jam, M.decodeParams program.params, libraryCodes M libraries with
    | some code, some params, .ok libs =>
      -- C5: hold check here (K-RUN-HOLD: a dry run above the free threshold
      -- needs a hold before the oracle runs at the ABI fuel).
      let result := M.oracle program.abi.fuel (M.entry params code libs sample)
      .ran (M.encodeInput sample)
        (match result with
         | .ok out k => .ok (M.encodeOutput out) k
         | .crash k => .crash k
         | .exhausted k => .exhausted k)
        (match result with
         | .ok out _ => M.writesOf program.abi out
         | _ => none)
    | none, _, _ => .refused .programMalformed
    | _, none, _ => .refused .paramsMalformed
    | _, _, .error reason => .refused reason

def dryRun (disabled : List Digest) (domain : Digest)
    (directory : CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (id : Digest) (ctx : Context) (targets : List Nat) (values : List (Nat × String × Int)) :
    DryRun :=
  match CanonicalCellRegistry.loadProgram domain directory id with
  | none => .missingProgram
  | some program =>
    match resolve disabled program.evaluator with
    | .error reason => .refused reason
    | .ok E =>
      if program.abi.door.isSome then .refused .doorProgram
      else if (values.map fun v => (v.1, v.2.1)).Nodup then
        match program.abi.libraries.mapM fun library =>
            require .libraryUnknown (CanonicalCellRegistry.loadProgram domain directory library) with
        | .error reason => .refused reason
        | .ok libraries =>
          if librariesAgree program libraries then
            dryRunOn E.toMachine program libraries ctx targets (readOf values)
          else .refused .libraryEvaluator
      else .ambiguousValues

/-! ## Theorems, once for every evaluator -/

/-- **`checkRun_sound`** (NOCK §3.3, over any evaluator): an accepted claim names the
kernel's own sample; the writes are EXACTLY the writes the program's product names,
and that product is a derivation (`E.Spec`) of the kernel's run; the steps are the
oracle's and within the ABI fuel. -/
theorem checkRun_sound {E : Evaluator} {program : Program} {libraries : List Program}
    {sample : E.Input} {claim : RunClaim} {writes : List FieldWrite} {verdict : Verdict E.Output}
    (accepted : checkRun E.toMachine program libraries sample claim writes = .ok verdict) :
    ∃ t, runOf E.toMachine program libraries sample = some t ∧
      E.Spec t verdict.output ∧
      E.writesOf program.abi verdict.output = some verdict.writes ∧
      (∀ w, w ∈ writes ↔ w ∈ verdict.writes) ∧
      claim.sampleJam = E.encodeInput sample ∧
      claim.outputJam = E.encodeOutput verdict.output ∧
      verdict.steps = claim.steps ∧ claim.steps ≤ program.abi.fuel ∧
      E.run claim.steps t = .ok verdict.output ∧
      E.steps claim.steps t = verdict.steps := by
  unfold checkRun at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  rename_i hsample
  split at accepted
  · cases accepted
  rename_i hfuel
  cases hcore : E.decode program.jam with
  | none => simp [hcore, require] at accepted
  | some core =>
    simp only [hcore, require] at accepted
    cases hparams : E.decodeParams program.params with
    | none => simp [hparams] at accepted
    | some params =>
      simp only [hparams] at accepted
      cases hlibs : libraryCodes E.toMachine libraries with
      | error e => simp [hlibs] at accepted
      | ok libs =>
        simp only [hlibs] at accepted
        split at accepted
        · cases accepted
        · cases accepted
        · rename_i out k horacle
          split at accepted
          · cases accepted
          rename_i hk
          split at accepted
          · cases accepted
          rename_i hout
          cases hdec : E.writesOf program.abi out with
          | none => simp [hdec] at accepted
          | some decoded =>
            simp only [hdec] at accepted
            split at accepted
            · cases accepted
            rename_i hwr
            split at accepted
            · cases accepted
            rename_i hdw
            cases accepted
            obtain ⟨hrun, hsteps⟩ := E.oracle_ok horacle
            have hk' : k = claim.steps := Classical.byContradiction hk
            refine ⟨_, ?_, E.run_sound hrun, hdec, ?_, Classical.byContradiction hsample,
              (Classical.byContradiction hout).symm, hk', by omega, hrun, hsteps⟩
            · simp [runOf, hcore, hparams, hlibs]
            · intro w
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hwr hdw
              rw [List.all_eq_true] at hwr hdw
              exact ⟨fun m => by simpa using hwr w m, fun m => by simpa using hdw w m⟩

/-- **`no_accepted_of_output_mismatch`** (NOCK §3.3, the T8 statement, over any
evaluator): a successful evaluation authorizes nothing by itself. If the command's
writes differ from the writes the program's actual product names, no claim —
whatever output, steps or sample it asserts — is accepted. -/
theorem no_accepted_of_output_mismatch {E : Evaluator} {program : Program}
    {libraries : List Program} {sample : E.Input} {writes : List FieldWrite} {t : E.Term}
    {out : E.Output} {decoded : List FieldWrite}
    (run : runOf E.toMachine program libraries sample = some t) (derives : E.Spec t out)
    (names : E.writesOf program.abi out = some decoded)
    (differ : ∃ w, ¬ (w ∈ writes ↔ w ∈ decoded)) (claim : RunClaim) (verdict : Verdict E.Output) :
    checkRun E.toMachine program libraries sample claim writes ≠ .ok verdict := by
  intro accepted
  obtain ⟨t', run', step', dec', same, -⟩ := checkRun_sound accepted
  rw [run] at run'
  cases run'
  have hv : verdict.output = out := E.spec_deterministic step' derives
  rw [hv, names] at dec'
  cases dec'
  obtain ⟨w, hw⟩ := differ
  exact hw (same w)

/-- A completed run's count is stable under more fuel. -/
theorem steps_of_run {E : Evaluator} {fuel fuel' : Nat} {t : E.Term} {v : E.Output}
    (h : E.run fuel t = .ok v) (le : fuel ≤ fuel') : E.steps fuel' t = E.steps fuel t :=
  E.steps_stable (by rw [h]; simp) le

/-- **`checkRun_deterministic`**: two accepted claims for one program and one
sample agree on the product, the decoded writes, the output bytes and the steps
— whatever fuel or writes each brought. -/
theorem checkRun_deterministic {E : Evaluator} {program : Program} {libraries : List Program}
    {sample : E.Input} {claim claim' : RunClaim} {writes writes' : List FieldWrite}
    {verdict verdict' : Verdict E.Output}
    (accepted : checkRun E.toMachine program libraries sample claim writes = .ok verdict)
    (accepted' : checkRun E.toMachine program libraries sample claim' writes' = .ok verdict') :
    verdict = verdict' ∧ claim.outputJam = claim'.outputJam ∧ claim.steps = claim'.steps := by
  obtain ⟨t, run, step, dec, -, -, out, hs, -, ran, steps⟩ := checkRun_sound accepted
  obtain ⟨t', run', step', dec', -, -, out', hs', -, ran', steps'⟩ := checkRun_sound accepted'
  rw [run] at run'
  cases run'
  have ho : verdict.output = verdict'.output := E.spec_deterministic step step'
  have hw : verdict.writes = verdict'.writes := by
    rw [ho, dec'] at dec; exact (Option.some.inj dec).symm
  have hk : verdict.steps = verdict'.steps := by
    rw [← steps, ← steps', ← steps_of_run ran (Nat.le_max_left claim.steps claim'.steps),
      ← steps_of_run ran' (Nat.le_max_right claim.steps claim'.steps)]
  refine ⟨?_, by rw [out, out', ho], by omega⟩
  cases verdict; cases verdict'
  simp_all

/-- **`steps_equal_oracle`**: the count an accepted run is charged is the
evaluator's count at the program's ABI fuel — a function of the program and the
sample alone, never of the claim — and the claim signed exactly that count. -/
theorem steps_equal_oracle {E : Evaluator} {program : Program} {libraries : List Program}
    {sample : E.Input} {claim : RunClaim} {writes : List FieldWrite} {verdict : Verdict E.Output}
    (accepted : checkRun E.toMachine program libraries sample claim writes = .ok verdict) :
    ∃ t, runOf E.toMachine program libraries sample = some t ∧
      verdict.steps = E.steps program.abi.fuel t ∧ claim.steps = verdict.steps := by
  obtain ⟨t, run, -, -, -, -, -, hs, fuel, ran, steps⟩ := checkRun_sound accepted
  exact ⟨t, run, by rw [steps_of_run ran fuel, steps], hs.symm⟩

/-- **`pinned_claim_stale_on_field_change`** (K-RUN-PIN, at the run, over any
evaluator): a claim computed on a pinned program's sample, re-checked after exactly
one named slot changed value, refuses `sampleStale` naming THAT slot's key — at
whatever context the kernel now runs. -/
theorem pinned_claim_stale_on_field_change {E : Evaluator} {program : Program}
    {libraries : List Program} {ctx ctx' : Context} {targets : List Nat}
    {read read' : Nat → String → Option Int} {sample sample' : E.Input} {claim : RunClaim}
    {writes : List FieldWrite} {slot : SampleSlot}
    (pinned : program.abi.context = .pinned)
    (claimed : E.sampleOf program.abi ctx targets read = some sample)
    (current : E.sampleOf program.abi ctx' targets read' = some sample')
    (computed : claim.sampleJam = E.encodeInput sample)
    (named : slot ∈ program.abi.sample)
    (changed : read slot.target slot.slot ≠ read' slot.target slot.slot)
    (only : ∀ s ∈ program.abi.sample, s ≠ slot → read s.target s.slot = read' s.target s.slot) :
    checkRun E.toMachine program libraries sample' claim writes =
      .error (.sampleStale (some slot.key)) := by
  obtain ⟨differ, names⟩ := E.staleField_names pinned claimed current named changed only
  have hne : claim.sampleJam ≠ E.encodeInput sample' := by
    rw [computed]; intro e; exact differ (E.encodeInput_injective e)
  have hstale : E.staleField program.abi sample' claim.sampleJam = some slot.key := by
    rw [computed]; exact names
  unfold checkRun
  simp only [bind, Except.bind]
  rw [if_pos hne, hstale]

/-! ## The same theorems at Nock (K-RAN's and K-RUN-PIN's statements)

Each is the generic theorem at `E := Evaluator.nock`, unfolded: `E.Spec` is
`Theory.Nock.Step`, the term is `(subject, formula)`, the bytes are jams. -/

namespace nock

open Minidregg.Kernel.NockEntry (decodeWrites)

theorem checkRun_sound {program : Program} {libraries : List Program} {sample : Noun}
    {claim : RunClaim} {writes : List FieldWrite} {verdict : Verdict Noun}
    (accepted : checkRun Machine.nock program libraries sample claim writes = .ok verdict) :
    ∃ s f, runOf Machine.nock program libraries sample = some (s, f) ∧
      Nock.Step s f verdict.output ∧
      decodeWrites program.abi verdict.output = some verdict.writes ∧
      (∀ w, w ∈ writes ↔ w ∈ verdict.writes) ∧
      claim.sampleJam = Noun.jam sample ∧
      claim.outputJam = Noun.jam verdict.output ∧
      verdict.steps = claim.steps ∧ claim.steps ≤ program.abi.fuel ∧
      Nock.run claim.steps s f = .ok verdict.output ∧
      Nock.steps claim.steps s f = verdict.steps := by
  obtain ⟨⟨s, f⟩, h⟩ := Run.checkRun_sound (E := Evaluator.nock) accepted
  exact ⟨s, f, h⟩

theorem no_accepted_of_output_mismatch {program : Program} {libraries : List Program}
    {sample : Noun} {writes : List FieldWrite} {s f out : Noun} {decoded : List FieldWrite}
    (run : runOf Machine.nock program libraries sample = some (s, f)) (derives : Nock.Step s f out)
    (names : decodeWrites program.abi out = some decoded)
    (differ : ∃ w, ¬ (w ∈ writes ↔ w ∈ decoded)) (claim : RunClaim) (verdict : Verdict Noun) :
    checkRun Machine.nock program libraries sample claim writes ≠ .ok verdict :=
  Run.no_accepted_of_output_mismatch (E := Evaluator.nock) (t := (s, f)) run derives names differ
    claim verdict

theorem steps_of_run {fuel fuel' : Nat} {s f v : Noun} (h : Nock.run fuel s f = .ok v)
    (le : fuel ≤ fuel') : Nock.steps fuel' s f = Nock.steps fuel s f :=
  Run.steps_of_run (E := Evaluator.nock) (t := (s, f)) h le

theorem checkRun_deterministic {program : Program} {libraries : List Program} {sample : Noun}
    {claim claim' : RunClaim} {writes writes' : List FieldWrite} {verdict verdict' : Verdict Noun}
    (accepted : checkRun Machine.nock program libraries sample claim writes = .ok verdict)
    (accepted' : checkRun Machine.nock program libraries sample claim' writes' = .ok verdict') :
    verdict = verdict' ∧ claim.outputJam = claim'.outputJam ∧ claim.steps = claim'.steps :=
  Run.checkRun_deterministic (E := Evaluator.nock) accepted accepted'

theorem steps_equal_oracle {program : Program} {libraries : List Program} {sample : Noun}
    {claim : RunClaim} {writes : List FieldWrite} {verdict : Verdict Noun}
    (accepted : checkRun Machine.nock program libraries sample claim writes = .ok verdict) :
    ∃ s f, runOf Machine.nock program libraries sample = some (s, f) ∧
      verdict.steps = Nock.steps program.abi.fuel s f ∧ claim.steps = verdict.steps := by
  obtain ⟨⟨s, f⟩, h⟩ := Run.steps_equal_oracle (E := Evaluator.nock) accepted
  exact ⟨s, f, h⟩

theorem pinned_claim_stale_on_field_change {program : Program} {libraries : List Program}
    {ctx ctx' : Context} {targets : List Nat} {read read' : Nat → String → Option Int}
    {sample sample' : Noun} {claim : RunClaim} {writes : List FieldWrite} {slot : SampleSlot}
    (pinned : program.abi.context = .pinned)
    (claimed : sampleOf program.abi ctx targets read = some sample)
    (current : sampleOf program.abi ctx' targets read' = some sample')
    (computed : claim.sampleJam = Noun.jam sample)
    (named : slot ∈ program.abi.sample)
    (changed : read slot.target slot.slot ≠ read' slot.target slot.slot)
    (only : ∀ s ∈ program.abi.sample, s ≠ slot → read s.target s.slot = read' s.target s.slot) :
    checkRun Machine.nock program libraries sample' claim writes =
      .error (.sampleStale (some slot.key)) :=
  Run.pinned_claim_stale_on_field_change (E := Evaluator.nock) pinned claimed current computed
    named changed only

end nock

/-! ## Poles: small programs from NOCK-THEORY's corpus, decided by the kernel

`incCore` is a core whose arm 2 yields a gate writing `~[['k' +(sample)]]`
(NOCK-THEORY's increment `[4 0 6]` as the gate's battery); `decCore` writes
`~[['k' (dec sample)]]` with NOCK-THEORY's decrement `decF`; `crashCore`'s gate
reads axis 0. Each runs through `checkRun` on Nock's machine exactly as the controller
calls it (`checkProgram` hands `checkRun` the resolved evaluator's `toMachine`, which for
Nock is `Machine.nock`, `Evaluator.nock_toMachine`). The statements are K-RAN's and
K-RUN-PIN's with the machine named. -/

/-- The fixtures' records name evaluator `⟨0⟩`: `checkRun` is handed its machine and
never reads `program.evaluator` (resolving the id is `checkClaim`'s, by `resolve`), and
naming Nock's real id here would pull the hash's axioms into every decided pole. -/
def fixtureEvaluator : Digest := ⟨0⟩

/-- `[[[1 'k'] battery] 1 0]`: a one-entry output list. -/
def writeK (value : Noun) : Noun :=
  .cell (.cell (Nock.op 1 (.atom 107)) value) (Nock.op 1 (.atom 0))

/-- A core `[[1 gate] 0]` over the gate `[battery [0 0]]`. -/
def coreOf (battery : Noun) : Noun :=
  .cell (Nock.op 1 (.cell battery (.cell (.atom 0) (.atom 0)))) (.atom 0)

def incCore : Noun := coreOf (writeK (Nock.op 4 (Nock.op 0 (.atom 6))))
def decCore : Noun :=
  coreOf (writeK (Nock.op 2 (.cell (Nock.op 0 (.atom 6)) (Nock.op 1 Nock.decF))))
def crashCore : Noun := coreOf (Nock.op 0 (.atom 0))

def kAbi (fuel : Nat) : Abi :=
  { version := 1, fuel := fuel, sample := [],
    outputs := [{ key := "k", target := 0, field := 1, type := .nat }], libraries := [] }

/-- Nock's params: arm 2 (the bare gate). -/
def gateParams : List UInt8 := NockEntry.encodeParams ⟨2⟩

def prog (core : Noun) (fuel : Nat) : Program := ⟨fixtureEvaluator, Noun.jam core, kAbi fuel, gateParams⟩

def claimOf (sample out : Noun) (steps : Nat) : RunClaim :=
  ⟨⟨0⟩, Noun.jam sample, Noun.jam out, steps⟩

def outK (n : Nat) : Noun := .cell (.cell (.atom 107) (.atom n)) (.atom 0)

def refusalOf {Output : Type} : Except Refusal (Verdict Output) → Option Refusal
  | .error r => some r
  | .ok _ => none

def writesOf {Output : Type} : Except Refusal (Verdict Output) → Option (List FieldWrite)
  | .error _ => none
  | .ok v => some v.writes

def libProgram : Program :=
  ⟨fixtureEvaluator, Noun.jam (Nock.op 0 (.atom 1)), { kAbi 100 with libraries := [⟨0⟩] }, gateParams⟩

def W (value : Int) : FieldWrite := ⟨0, 1, value⟩

set_option maxRecDepth 100000

/-- Accepted: increment on 41 writes `k := 42` in 14 steps. -/
theorem pole_accepts :
    writesOf (checkRun Machine.nock (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 14) [W 42]) =
      some [W 42] := by decide +kernel
/-- Accepted: decrement on 3 writes `k := 2` in 51 steps. -/
theorem pole_decrement_accepts :
    writesOf (checkRun Machine.nock (prog decCore 100) [] (.atom 3) (claimOf (.atom 3) (outK 2) 51) [W 2]) =
      some [W 2] := by decide +kernel
/-- Accepted with a library (N16): the program `[0 1]` over the library subject
is the library's core, so the run is increment's plus 7 steps of library plumbing. -/
theorem pole_library_accepts :
    writesOf (checkRun Machine.nock libProgram [prog incCore 100] (.atom 41) (claimOf (.atom 41) (outK 42) 21)
      [W 42]) = some [W 42] := by decide +kernel
theorem pole_libraryNested :
    refusalOf (checkRun Machine.nock libProgram [libProgram] (.atom 41) (claimOf (.atom 41) (outK 42) 21)
      [W 42]) = some .libraryNested := by decide +kernel
theorem pole_outputMismatch :
    refusalOf (checkRun Machine.nock (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 43) 14) [W 43]) =
      some .outputMismatch := by decide +kernel
theorem pole_sampleStale :
    refusalOf (checkRun Machine.nock (prog incCore 100) [] (.atom 41) (claimOf (.atom 40) (outK 42) 14) [W 42]) =
      some (.sampleStale none) := by decide +kernel
theorem pole_fuelExceeded :
    refusalOf (checkRun Machine.nock (prog incCore 10) [] (.atom 41) (claimOf (.atom 41) (outK 42) 14) [W 42]) =
      some .fuelExceeded := by decide +kernel
theorem pole_crash :
    refusalOf (checkRun Machine.nock (prog crashCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 100) [W 42]) =
      some (.crash 9) := by decide +kernel
theorem pole_exhausted :
    refusalOf (checkRun Machine.nock (prog decCore 100) [] (.atom 3) (claimOf (.atom 3) (outK 2) 20) [W 2]) =
      some (.exhausted 20) := by decide +kernel
theorem pole_stepsMismatch :
    refusalOf (checkRun Machine.nock (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 20) [W 42]) =
      some (.stepsMismatch 14) := by decide +kernel
theorem pole_writeNotInOutput :
    refusalOf (checkRun Machine.nock (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 14)
      [W 42, ⟨0, 2, 7⟩]) = some .writeNotInOutput := by decide +kernel
/-- The record's params bytes are not Nock's: refused by name before anything runs. -/
theorem pole_paramsMalformed :
    refusalOf (checkRun Machine.nock { prog incCore 100 with params := [7] } [] (.atom 41)
      (claimOf (.atom 41) (outK 42) 14) [W 42]) = some .paramsMalformed := by decide +kernel
theorem pole_outputNotWritten :
    refusalOf (checkRun Machine.nock (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 14) []) =
      some .outputNotWritten := by decide +kernel

/-! ### Pinned against live (K-RUN-PIN)

`slotCore`'s gate writes `k := +(n)`, where `n` is the sample's first ABI slot
(axis 109 of the gate with one target). The claim is computed once, at height 16
by signer 7 on `stateA`; it is re-checked at height 23 by signer 9 on `stateB`
(same `f/2`, different unnamed field). -/

def slotCore : Noun := coreOf (writeK (Nock.op 4 (Nock.op 0 (.atom 109))))
def slotN : SampleSlot := { target := 0, slot := "f/2", key := "n", type := .nat }
def slotAbi (mode : ContextMode) : Abi := { kAbi 100 with context := mode, sample := [slotN] }
def slotProgram (context : ContextMode) : Program :=
  ⟨fixtureEvaluator, Noun.jam slotCore, slotAbi context, gateParams⟩
def sampleAt (context : ContextMode) (ctx : Context) (read : Nat → String → Option Int) : Noun :=
  (sampleOf (slotAbi context) ctx [11] read).getD (.atom 0)
def stateC : Nat → String → Option Int := fun _ s => if s = "f/2" then some 40 else some 1
def claimAt16 (context : ContextMode) : RunClaim :=
  claimOf (sampleAt context ⟨16, 7, 0⟩ stateA) (outK 42) 14

/-- Pinned: the height-16 claim is accepted at height 23. -/
theorem pole_pinned_other_height :
    writesOf (checkRun Machine.nock (slotProgram .pinned) [] (sampleAt .pinned ⟨23, 9, 0⟩ stateB)
      (claimAt16 .pinned) [W 42]) = some [W 42] := by decide +kernel
/-- Live: the same claim at height 23 is stale, and names no field. -/
theorem pole_live_other_height :
    refusalOf (checkRun Machine.nock (slotProgram .live) [] (sampleAt .live ⟨23, 9, 0⟩ stateB)
      (claimAt16 .live) [W 42]) = some (.sampleStale none) := by decide +kernel
/-- Pinned, with the named field moved (41 → 40): stale, naming `n`. -/
theorem pole_pinned_field_stale :
    refusalOf (checkRun Machine.nock (slotProgram .pinned) [] (sampleAt .pinned ⟨23, 9, 0⟩ stateC)
      (claimAt16 .pinned) [W 41]) = some (.sampleStale (some "n")) := by decide +kernel
/-- A `noun` output writes the jam atom of `[3 7]`, which a `noun` sample reads back. -/
theorem pole_noun_output :
    (NockEntry.decodeValue .noun (.cell (.atom 3) (.atom 7))).bind (encodeValue .noun) =
      some (.cell (.atom 3) (.atom 7)) := by decide +kernel

end Minidregg.Kernel.Run

/-- info: 'Minidregg.Kernel.Run.checkRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.checkRun_sound
/-- info: 'Minidregg.Kernel.Run.nock.checkRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.nock.checkRun_sound
/-- info: 'Minidregg.Kernel.Run.no_accepted_of_output_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.no_accepted_of_output_mismatch
/-- info: 'Minidregg.Kernel.Run.nock.no_accepted_of_output_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.nock.no_accepted_of_output_mismatch
/-- info: 'Minidregg.Kernel.Run.steps_of_run' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.steps_of_run
/-- info: 'Minidregg.Kernel.Run.nock.steps_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.nock.steps_of_run
/-- info: 'Minidregg.Kernel.Run.checkRun_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.checkRun_deterministic
/-- info: 'Minidregg.Kernel.Run.nock.checkRun_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.nock.checkRun_deterministic
/-- info: 'Minidregg.Kernel.Run.steps_equal_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.steps_equal_oracle
/-- info: 'Minidregg.Kernel.Run.nock.steps_equal_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.nock.steps_equal_oracle
/-- info: 'Minidregg.Kernel.Run.pinned_claim_stale_on_field_change' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pinned_claim_stale_on_field_change
/-- info: 'Minidregg.Kernel.Run.nock.pinned_claim_stale_on_field_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.nock.pinned_claim_stale_on_field_change
/-- info: 'Minidregg.Kernel.Run.resolve_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.resolve_registered
/-- info: 'Minidregg.Kernel.Run.resolve_unknown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.resolve_unknown
/-- info: 'Minidregg.Kernel.Run.pole_unknownEvaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_unknownEvaluator
/-- info: 'Minidregg.Kernel.Run.unknownEvaluator_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.unknownEvaluator_inhabited
/-- info: 'Minidregg.Kernel.Run.pole_nock_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_nock_resolves
/-- info: 'Minidregg.Kernel.Run.pole_evaluatorDisabled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_evaluatorDisabled
/-- info: 'Minidregg.Kernel.Run.nock_found' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.nock_found
/-- info: 'Minidregg.Kernel.Run.pole_accepts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_accepts
/-- info: 'Minidregg.Kernel.Run.pole_decrement_accepts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_decrement_accepts
/-- info: 'Minidregg.Kernel.Run.pole_library_accepts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_library_accepts
/-- info: 'Minidregg.Kernel.Run.pole_libraryNested' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_libraryNested
/-- info: 'Minidregg.Kernel.Run.pole_outputMismatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_outputMismatch
/-- info: 'Minidregg.Kernel.Run.pole_sampleStale' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_sampleStale
/-- info: 'Minidregg.Kernel.Run.pole_fuelExceeded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_fuelExceeded
/-- info: 'Minidregg.Kernel.Run.pole_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_crash
/-- info: 'Minidregg.Kernel.Run.pole_exhausted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_exhausted
/-- info: 'Minidregg.Kernel.Run.pole_stepsMismatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_stepsMismatch
/-- info: 'Minidregg.Kernel.Run.pole_writeNotInOutput' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_writeNotInOutput
/-- info: 'Minidregg.Kernel.Run.pole_outputNotWritten' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_outputNotWritten
/-- info: 'Minidregg.Kernel.Run.pole_pinned_other_height' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_pinned_other_height
/-- info: 'Minidregg.Kernel.Run.pole_live_other_height' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_live_other_height
/-- info: 'Minidregg.Kernel.Run.pole_pinned_field_stale' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_pinned_field_stale
/-- info: 'Minidregg.Kernel.Run.pole_noun_output' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_noun_output
/-- info: 'Minidregg.Kernel.Run.pole_paramsMalformed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Run.pole_paramsMalformed
