/-
# Kernel.NockRun — the kernel checks a run by re-executing it (NOCK §2.4, §2.5)

A runner submits field writes together with a `RunClaim`: the program it ran,
the sample it ran on (jam bytes), the output it got (jam bytes) and the Lean
step count. The kernel admits the writes only when its own run agrees:

1. the claimed sample is byte-equal to the kernel's `sampleOf` (else `sampleStale`);
2. the claimed steps fit the program's ABI fuel (else `fuelExceeded`);
3. `Theory.Nock`'s evaluator, given exactly the claimed steps as fuel, answers
   (else `crash k` / `exhausted k`, naming the count) in exactly that many steps
   (else `stepsMismatch k`);
4. the output jam is the claimed jam (else `outputMismatch`);
5. the output decodes against `abi.outputs` (else `outputMalformed`), and the
   command's writes are exactly the decoded writes: a write the output does not
   name refuses `writeNotInOutput`, a decoded write the command omits refuses
   `outputNotWritten`.

The claimed step count is the runner's fuel AND the fee it signs for: the
kernel never charges a count the runner did not sign, and the count is the
oracle's (`steps_equal_oracle`), independent of the claim's fuel.

## Run-time shape of libraries (NOCK N16)

A program without libraries is a core: the run is `*[[P sample] slam(arm)]`,
exactly NOCK-RUNNER's formula. A program WITH libraries `L₁ … Lₖ` (ABI order,
which `programId` covers) is a formula over the library subject
`lib = [L₁ [L₂ … Lₖ]]` (right-nested; `L₁` alone when `k = 1`): the core is
`*[lib P]`, and the run is

    *[[lib [P sample]]  [7 [[2 [0 2] 0 6] 0 7] slam(arm)]]

which computes `[*[lib P] sample]` and slams it. Library nouns are the cue of
the library cells' jams, used as they are (a library's own libraries are not
resolved: `libraryNested`).

## The oracle is the export

`oracle fuel s f` runs `Theory.Nock.exec` once. `oracle_is_export` proves the
byte entry point `@[export minidregg_nock_run_jammed]` (`runJammed`) answers the
same status, the same steps and the jam of the same product on `jam [s f]`.
-/
import Kernel.NockProgramCell
import Theory.Nock

namespace Minidregg.Kernel.NockRun
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel.NockProgramCell
set_option autoImplicit false

/-! ## The claim and the refusals -/

/-- What a runner signs beside its command. -/
structure RunClaim where
  programId : Digest
  /-- The jam of the sample the runner ran on (the kernel's op-119/120 sample). -/
  sampleJam : List UInt8
  /-- The jam of the product the runner got. -/
  outputJam : List UInt8
  /-- Lean `Theory.Nock.steps`: the run's fuel and the metered count. -/
  steps : Nat
  deriving DecidableEq, Repr

inductive Refusal where
  | programUnknown
  | libraryUnknown
  | libraryNested
  | programMalformed
  | sampleUnavailable
  | sampleStale
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
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .programUnknown => "programUnknown"
  | .libraryUnknown => "libraryUnknown"
  | .libraryNested => "libraryNested"
  | .programMalformed => "programMalformed"
  | .sampleUnavailable => "sampleUnavailable"
  | .sampleStale => "sampleStale"
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

/-- One object-field write: field `field` of the command's `target`-th target
(0-based, the signed target order) becomes `value`. -/
structure FieldWrite where
  target : Nat
  field : Nat
  value : Int
  deriving DecidableEq, Repr

/-! ## Decoding the product against `abi.outputs` -/

/-- A Nock list of `[key value]` with atom keys. -/
def entriesOf : Noun → Option (List (Nat × Noun))
  | .atom 0 => some []
  | .cell (.cell (.atom k) v) rest => (entriesOf rest).map ((k, v) :: ·)
  | _ => none

def decodeValue : SlotType → Noun → Option Int
  | .nat, .atom n => some (.ofNat n)
  | .nat, .cell _ _ => none
  | .int, n => n.toInt?

def decodeEntry (outputs : List OutputSlot) (entry : Nat × Noun) : Option FieldWrite :=
  match outputs.find? (fun o => cordValue o.key.toUTF8.toList == entry.1) with
  | none => none
  | some o => (decodeValue o.type entry.2).map fun value => ⟨o.target, o.field, value⟩

/-- The writes a product names. Each `(target, field)` at most once. -/
def decodeWrites (abi : Abi) (out : Noun) : Option (List FieldWrite) := do
  let entries ← entriesOf out
  let writes ← entries.mapM (decodeEntry abi.outputs)
  if (writes.map fun w => (w.target, w.field)).Nodup then some writes else none

/-! ## The subject and formula (N16) -/

/-- `[L₁ [L₂ … Lₖ]]`. -/
def libraryNoun : List Noun → Noun
  | [] => .atom 0
  | [l] => l
  | l :: rest => .cell l (libraryNoun rest)

/-- `[7 [[2 [0 2] 0 6] 0 7] slam]`: build `[*[lib P] sample]`, then slam it. -/
def libraryFormula (arm : Nat) : Noun :=
  Nock.op 7 (.cell (.cell (Nock.op 2 (.cell (Nock.op 0 (.atom 2)) (Nock.op 0 (.atom 6))))
    (Nock.op 0 (.atom 7))) (Nock.slam arm))

def subjectFormula (arm : Nat) (program : Noun) (libraries : List Noun) (sample : Noun) :
    Noun × Noun :=
  match libraries with
  | [] => (.cell program sample, Nock.slam arm)
  | _ => (.cell (libraryNoun libraries) (.cell program sample), libraryFormula arm)

/-! ## The oracle -/

inductive Ran where
  | ok (out : Noun) (steps : Nat)
  | crash (steps : Nat)
  | exhausted (steps : Nat)
  deriving DecidableEq, Repr

/-- One evaluation of `*[s f]` with `fuel` steps. -/
def oracle (fuel : Nat) (s f : Noun) : Ran :=
  match Nock.exec fuel fuel s f with
  | .ok v r => .ok v (fuel - r)
  | .crash r => .crash (fuel - r)
  | .exhausted => .exhausted fuel

/-- **The oracle is the export.** `runJammed` (behind `@[export
minidregg_nock_run_jammed]`) answers the oracle's status and steps on `jam [s f]`,
and its output bytes are the jam of the oracle's product. -/
theorem oracle_is_export (fuel : Nat) (s f : Noun) :
    Nock.runJammed fuel (Noun.jam (.cell s f)) =
      match oracle fuel s f with
      | .ok v k => .ok k (Noun.jam v)
      | .crash k => .crash k
      | .exhausted k => .exhausted k := by
  simp only [Nock.runJammed, oracle, Noun.cue_jam]
  cases Nock.exec fuel fuel s f <;> rfl

theorem oracle_ok_step {fuel : Nat} {s f v : Noun} {k : Nat} (h : oracle fuel s f = .ok v k) :
    Nock.Step s f v ∧ Nock.run fuel s f = .ok v ∧ Nock.steps fuel s f = k := by
  unfold oracle at h
  split at h
  · rename_i v' r he
    cases h
    refine ⟨(Nock.exec_sound _ _ _ _).1 _ _ he, ?_, ?_⟩
    · unfold Nock.run; rw [he]
    · unfold Nock.steps; rw [he]
  · cases h
  · cases h

/-! ## The decision -/

structure Verdict where
  output : Noun
  steps : Nat
  writes : List FieldWrite
  deriving DecidableEq, Repr

def require {α : Type} (reason : Refusal) : Option α → Except Refusal α
  | none => .error reason
  | some a => .ok a

@[simp] theorem require_some {α : Type} (reason : Refusal) (a : α) :
    require reason (some a) = .ok a := rfl
@[simp] theorem require_none {α : Type} (reason : Refusal) :
    require reason (none : Option α) = .error reason := rfl

/-- The library nouns, refused if a library names libraries of its own. -/
def libraryNouns (libraries : List Program) : Except Refusal (List Noun) :=
  libraries.mapM fun library =>
    if library.abi.libraries.isEmpty then require .programMalformed (Noun.cue library.jam)
    else .error .libraryNested

/-- **`checkRun`**: re-execute `program` (with its loaded `libraries`) on the
kernel's `sample` and decide `claim` against the command's `writes`. -/
def checkRun (program : Program) (libraries : List Program) (sample : Noun)
    (claim : RunClaim) (writes : List FieldWrite) : Except Refusal Verdict := do
  if claim.sampleJam ≠ Noun.jam sample then throw .sampleStale
  if program.abi.fuel < claim.steps then throw .fuelExceeded
  let core ← require .programMalformed (Noun.cue program.jam)
  let libs ← libraryNouns libraries
  let sf := subjectFormula program.abi.arm core libs sample
  match oracle claim.steps sf.1 sf.2 with
  | .crash k => throw (.crash k)
  | .exhausted k => throw (.exhausted k)
  | .ok out k =>
    if k ≠ claim.steps then throw (.stepsMismatch k)
    if Noun.jam out ≠ claim.outputJam then throw .outputMismatch
    let decoded ← require .outputMalformed (decodeWrites program.abi out)
    if !writes.all (· ∈ decoded) then throw .writeNotInOutput
    if !decoded.all (· ∈ writes) then throw .outputNotWritten
    pure ⟨out, k, decoded⟩

/-- The run of `program` on `sample` that the kernel would perform: its subject
and formula, when the program and its libraries cue. -/
def runOf (program : Program) (libraries : List Program) (sample : Noun) : Option (Noun × Noun) :=
  match Noun.cue program.jam, libraryNouns libraries with
  | some core, .ok libs => some (subjectFormula program.abi.arm core libs sample)
  | _, _ => none

/-! ## Op 134: the runner's dry run

The kernel's sample for client-supplied participant values at the Host's
current logical height, and the oracle's answer at the ABI fuel: what a runner
copies into its claim. It reads no target cell (values are the runner's own
signed views), so it discloses nothing a program cell does not. -/

inductive DryRun where
  | missingProgram
  | ambiguousValues
  | refused (reason : Refusal)
  | ran (sample : List UInt8) (result : Ran) (writes : Option (List FieldWrite))

def dryRun (domain : Digest) (directory : CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (id : Digest) (ctx : Context) (targets : List Nat) (values : List (Nat × String × Int)) :
    DryRun :=
  match CanonicalCellRegistry.loadProgram domain directory id with
  | none => .missingProgram
  | some program =>
    if program.abi.door.isSome then .refused .doorProgram
    else if (values.map fun v => (v.1, v.2.1)).Nodup then
      match program.abi.libraries.mapM fun library =>
          require .libraryUnknown (CanonicalCellRegistry.loadProgram domain directory library) with
      | .error reason => .refused reason
      | .ok libraries =>
        match sampleOf program.abi ctx targets (readOf values) with
        | none => .refused .sampleUnavailable
        | some sample =>
          match Noun.cue program.jam, libraryNouns libraries with
          | some core, .ok nouns =>
            let sf := subjectFormula program.abi.arm core nouns sample
            let result := oracle program.abi.fuel sf.1 sf.2
            .ran (Noun.jam sample) result
              (match result with
               | .ok out _ => decodeWrites program.abi out
               | _ => none)
          | none, _ => .refused .programMalformed
          | _, .error reason => .refused reason
    else .ambiguousValues

/-! ## Theorems -/

/-- **`checkRun_sound`** (NOCK §3.3): an accepted claim names the kernel's own
sample; the writes are EXACTLY the writes the program's product names, and that
product is a Nock 4K derivation of the kernel's run; the steps are the oracle's
and within the ABI fuel. -/
theorem checkRun_sound {program : Program} {libraries : List Program} {sample : Noun}
    {claim : RunClaim} {writes : List FieldWrite} {verdict : Verdict}
    (accepted : checkRun program libraries sample claim writes = .ok verdict) :
    ∃ s f, runOf program libraries sample = some (s, f) ∧
      Nock.Step s f verdict.output ∧
      decodeWrites program.abi verdict.output = some verdict.writes ∧
      (∀ w, w ∈ writes ↔ w ∈ verdict.writes) ∧
      claim.sampleJam = Noun.jam sample ∧
      claim.outputJam = Noun.jam verdict.output ∧
      verdict.steps = claim.steps ∧ claim.steps ≤ program.abi.fuel ∧
      Nock.run claim.steps s f = .ok verdict.output ∧
      Nock.steps claim.steps s f = verdict.steps := by
  unfold checkRun at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  rename_i hsample
  split at accepted
  · cases accepted
  rename_i hfuel
  cases hcore : Noun.cue program.jam with
  | none => simp [hcore, require] at accepted
  | some core =>
    simp only [hcore, require] at accepted
    cases hlibs : libraryNouns libraries with
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
        cases hdec : decodeWrites program.abi out with
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
          obtain ⟨hstep, hrun, hsteps⟩ := oracle_ok_step horacle
          have hk' : k = claim.steps := Classical.byContradiction hk
          refine ⟨_, _, ?_, hstep, hdec, ?_, Classical.byContradiction hsample,
            (Classical.byContradiction hout).symm, hk', by omega, hrun, hsteps⟩
          · simp [runOf, hcore, hlibs]
          · intro w
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hwr hdw
            rw [List.all_eq_true] at hwr hdw
            exact ⟨fun m => by simpa using hwr w m, fun m => by simpa using hdw w m⟩

/-- **`no_accepted_of_output_mismatch`** (NOCK §3.3, the T8 statement): a
successful Nock evaluation authorizes nothing by itself. If the command's
writes differ from the writes the program's actual product names, no claim —
whatever output, steps or sample it asserts — is accepted. -/
theorem no_accepted_of_output_mismatch {program : Program} {libraries : List Program}
    {sample : Noun} {writes : List FieldWrite} {s f out : Noun} {decoded : List FieldWrite}
    (run : runOf program libraries sample = some (s, f)) (derives : Nock.Step s f out)
    (names : decodeWrites program.abi out = some decoded)
    (differ : ∃ w, ¬ (w ∈ writes ↔ w ∈ decoded)) (claim : RunClaim) (verdict : Verdict) :
    checkRun program libraries sample claim writes ≠ .ok verdict := by
  intro accepted
  obtain ⟨s', f', run', step', dec', same, -⟩ := checkRun_sound accepted
  rw [run] at run'
  cases run'
  have hv : verdict.output = out := Nock.step_deterministic step' derives
  rw [hv, names] at dec'
  cases dec'
  obtain ⟨w, hw⟩ := differ
  exact hw (same w)

/-- A completed run's count is stable under more fuel. -/
theorem steps_of_run {fuel fuel' : Nat} {s f v : Noun} (h : Nock.run fuel s f = .ok v)
    (le : fuel ≤ fuel') : Nock.steps fuel' s f = Nock.steps fuel s f :=
  Nock.steps_stable (by rw [h]; simp) le

/-- **`checkRun_deterministic`**: two accepted claims for one program and one
sample agree on the product, the decoded writes, the output jam and the steps
— whatever fuel or writes each brought. -/
theorem checkRun_deterministic {program : Program} {libraries : List Program} {sample : Noun}
    {claim claim' : RunClaim} {writes writes' : List FieldWrite} {verdict verdict' : Verdict}
    (accepted : checkRun program libraries sample claim writes = .ok verdict)
    (accepted' : checkRun program libraries sample claim' writes' = .ok verdict') :
    verdict = verdict' ∧ claim.outputJam = claim'.outputJam ∧ claim.steps = claim'.steps := by
  obtain ⟨s, f, run, step, dec, -, -, out, hs, -, ran, steps⟩ := checkRun_sound accepted
  obtain ⟨s', f', run', step', dec', -, -, out', hs', -, ran', steps'⟩ := checkRun_sound accepted'
  rw [run] at run'
  cases run'
  have ho : verdict.output = verdict'.output := Nock.step_deterministic step step'
  have hw : verdict.writes = verdict'.writes := by
    rw [ho, dec'] at dec; exact (Option.some.inj dec).symm
  have hk : verdict.steps = verdict'.steps := by
    rw [← steps, ← steps', ← steps_of_run ran (Nat.le_max_left claim.steps claim'.steps),
      ← steps_of_run ran' (Nat.le_max_right claim.steps claim'.steps)]
  refine ⟨?_, by rw [out, out', ho], by omega⟩
  cases verdict; cases verdict'
  simp_all

/-- **`steps_equal_oracle`**: the count an accepted run is charged is the
oracle's count at the program's ABI fuel — a function of the program and the
sample alone, never of the claim — and the claim signed exactly that count. -/
theorem steps_equal_oracle {program : Program} {libraries : List Program} {sample : Noun}
    {claim : RunClaim} {writes : List FieldWrite} {verdict : Verdict}
    (accepted : checkRun program libraries sample claim writes = .ok verdict) :
    ∃ s f, runOf program libraries sample = some (s, f) ∧
      verdict.steps = Nock.steps program.abi.fuel s f ∧ claim.steps = verdict.steps := by
  obtain ⟨s, f, run, -, -, -, -, -, hs, fuel, ran, steps⟩ := checkRun_sound accepted
  exact ⟨s, f, run, by rw [steps_of_run ran fuel, steps], hs.symm⟩


/-! ## Poles: small programs from NOCK-THEORY's corpus, decided by the kernel

`incCore` is a core whose arm 2 yields a gate writing `~[['k' +(sample)]]`
(NOCK-THEORY's increment `[4 0 6]` as the gate's battery); `decCore` writes
`~[['k' (dec sample)]]` with NOCK-THEORY's decrement `decF`; `crashCore`'s gate
reads axis 0. Each runs through `checkRun` exactly as the controller calls it. -/

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
  { version := 1, arm := 2, fuel := fuel, sample := [],
    outputs := [{ key := "k", target := 0, field := 1, type := .nat }], libraries := [] }

def prog (core : Noun) (fuel : Nat) : Program := ⟨Noun.jam core, kAbi fuel⟩

def claimOf (sample out : Noun) (steps : Nat) : RunClaim :=
  ⟨⟨0⟩, Noun.jam sample, Noun.jam out, steps⟩

def outK (n : Nat) : Noun := .cell (.cell (.atom 107) (.atom n)) (.atom 0)

def refusalOf : Except Refusal Verdict → Option Refusal
  | .error r => some r
  | .ok _ => none

def writesOf : Except Refusal Verdict → Option (List FieldWrite)
  | .error _ => none
  | .ok v => some v.writes

def libProgram : Program :=
  ⟨Noun.jam (Nock.op 0 (.atom 1)), { kAbi 100 with libraries := [⟨0⟩] }⟩

def W (value : Int) : FieldWrite := ⟨0, 1, value⟩

set_option maxRecDepth 100000

/-- Accepted: increment on 41 writes `k := 42` in 14 steps. -/
theorem pole_accepts :
    writesOf (checkRun (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 14) [W 42]) =
      some [W 42] := by decide +kernel
/-- Accepted: decrement on 3 writes `k := 2` in 51 steps. -/
theorem pole_decrement_accepts :
    writesOf (checkRun (prog decCore 100) [] (.atom 3) (claimOf (.atom 3) (outK 2) 51) [W 2]) =
      some [W 2] := by decide +kernel
/-- Accepted with a library (N16): the program `[0 1]` over the library subject
is the library's core, so the run is increment's plus 7 steps of library plumbing. -/
theorem pole_library_accepts :
    writesOf (checkRun libProgram [prog incCore 100] (.atom 41) (claimOf (.atom 41) (outK 42) 21)
      [W 42]) = some [W 42] := by decide +kernel
theorem pole_libraryNested :
    refusalOf (checkRun libProgram [libProgram] (.atom 41) (claimOf (.atom 41) (outK 42) 21)
      [W 42]) = some .libraryNested := by decide +kernel
theorem pole_outputMismatch :
    refusalOf (checkRun (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 43) 14) [W 43]) =
      some .outputMismatch := by decide +kernel
theorem pole_sampleStale :
    refusalOf (checkRun (prog incCore 100) [] (.atom 41) (claimOf (.atom 40) (outK 42) 14) [W 42]) =
      some .sampleStale := by decide +kernel
theorem pole_fuelExceeded :
    refusalOf (checkRun (prog incCore 10) [] (.atom 41) (claimOf (.atom 41) (outK 42) 14) [W 42]) =
      some .fuelExceeded := by decide +kernel
theorem pole_crash :
    refusalOf (checkRun (prog crashCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 100) [W 42]) =
      some (.crash 9) := by decide +kernel
theorem pole_exhausted :
    refusalOf (checkRun (prog decCore 100) [] (.atom 3) (claimOf (.atom 3) (outK 2) 20) [W 2]) =
      some (.exhausted 20) := by decide +kernel
theorem pole_stepsMismatch :
    refusalOf (checkRun (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 20) [W 42]) =
      some (.stepsMismatch 14) := by decide +kernel
theorem pole_writeNotInOutput :
    refusalOf (checkRun (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 14)
      [W 42, ⟨0, 2, 7⟩]) = some .writeNotInOutput := by decide +kernel
theorem pole_outputNotWritten :
    refusalOf (checkRun (prog incCore 100) [] (.atom 41) (claimOf (.atom 41) (outK 42) 14) []) =
      some .outputNotWritten := by decide +kernel

end Minidregg.Kernel.NockRun

/-- info: 'Minidregg.Kernel.NockRun.oracle_is_export' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.oracle_is_export
/-- info: 'Minidregg.Kernel.NockRun.oracle_ok_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.oracle_ok_step
/-- info: 'Minidregg.Kernel.NockRun.checkRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.checkRun_sound
/-- info: 'Minidregg.Kernel.NockRun.no_accepted_of_output_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.no_accepted_of_output_mismatch
/-- info: 'Minidregg.Kernel.NockRun.steps_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.steps_of_run
/-- info: 'Minidregg.Kernel.NockRun.checkRun_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.checkRun_deterministic
/-- info: 'Minidregg.Kernel.NockRun.steps_equal_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.steps_equal_oracle
/-- info: 'Minidregg.Kernel.NockRun.pole_accepts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_accepts
/-- info: 'Minidregg.Kernel.NockRun.pole_decrement_accepts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_decrement_accepts
/-- info: 'Minidregg.Kernel.NockRun.pole_library_accepts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_library_accepts
/-- info: 'Minidregg.Kernel.NockRun.pole_libraryNested' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_libraryNested
/-- info: 'Minidregg.Kernel.NockRun.pole_outputMismatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_outputMismatch
/-- info: 'Minidregg.Kernel.NockRun.pole_sampleStale' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_sampleStale
/-- info: 'Minidregg.Kernel.NockRun.pole_fuelExceeded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_fuelExceeded
/-- info: 'Minidregg.Kernel.NockRun.pole_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_crash
/-- info: 'Minidregg.Kernel.NockRun.pole_exhausted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_exhausted
/-- info: 'Minidregg.Kernel.NockRun.pole_stepsMismatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_stepsMismatch
/-- info: 'Minidregg.Kernel.NockRun.pole_writeNotInOutput' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_writeNotInOutput
/-- info: 'Minidregg.Kernel.NockRun.pole_outputNotWritten' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_outputNotWritten
