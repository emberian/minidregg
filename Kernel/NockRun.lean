/-
# Kernel.NockRun — the kernel checks a run by re-executing it (NOCK §2.4, §2.5)

A runner submits field writes together with a `RunClaim`: the program it ran,
the sample it ran on (jam bytes), the output it got (jam bytes) and the Lean
step count. The kernel admits the writes only when its own run agrees:

1. the claimed sample is byte-equal to the kernel's `sampleOf` (else `sampleStale`;
   under a `pinned` context the refusal names the first ABI slot whose value the
   claim's sample does not hold, `staleField`);
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
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .programUnknown => "programUnknown"
  | .libraryUnknown => "libraryUnknown"
  | .libraryNested => "libraryNested"
  | .programMalformed => "programMalformed"
  | .sampleUnavailable => "sampleUnavailable"
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
  | .noun, n => if (Noun.jam n).length ≤ nounMaxBytes then some (.ofNat (jamAtom n)) else none

/-- **`noun_output_roundtrip`** (K-RUN-PIN): a `noun` output is written as the
jam atom of the product's noun, within the birth-source bound, and a `noun`
sample slot reading that field gets the same noun back — so one program's noun
output is the next program's (or the next segment's) noun input, unaltered. -/
theorem noun_output_roundtrip {n : Noun} {value : Int} (written : decodeValue .noun n = some value) :
    value = .ofNat (jamAtom n) ∧ (Noun.jam n).length ≤ nounMaxBytes ∧
      encodeValue .noun value = some n := by
  simp only [decodeValue] at written
  split at written
  · rename_i bound
    cases written
    exact ⟨rfl, bound, ofJamAtom_jamAtom n⟩
  · cases written

/-- A `noun` output above the bound writes nothing. -/
theorem noun_output_bounded {n : Noun} (big : nounMaxBytes < (Noun.jam n).length) :
    decodeValue .noun n = none := by
  simp [decodeValue]; omega

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

/-! ## Which field a stale pinned claim missed -/

/-- The items of a null-terminated Nock list. -/
def listItems : Noun → Option (List Noun)
  | .atom 0 => some []
  | .cell x rest => (listItems rest).map (x :: ·)
  | _ => none

theorem listItems_nockList : ∀ (items : List Noun), listItems (nockList items) = some items
  | [] => rfl
  | x :: rest => by simp [nockList, listItems, listItems_nockList rest]

/-- The key of the first slot whose kernel entry is not the claimed entry. -/
def firstStale : List SampleSlot → List Noun → List Noun → Option String
  | slot :: rest, k :: ks, c :: cs => if k = c then firstStale rest ks cs else some slot.key
  | slot :: _, _ :: _, [] => some slot.key
  | _, _, _ => none

/-- Under `pinned`, the key of the first ABI slot whose entry in the claimed
sample differs from the kernel's `sample`, when the two agree on everything
before the slots (the context and the target entries). `none` under `live`,
where the height alone moves the sample, and when the claim differs elsewhere. -/
def staleField (abi : Abi) (sample : Noun) (claimed : List UInt8) : Option String :=
  match abi.context, sample, Noun.cue claimed with
  | .pinned, .cell kc kernelList, some (.cell cc claimedList) =>
    match listItems kernelList, listItems claimedList with
    | some ks, some cs =>
      let offset := ks.length - abi.sample.length
      if kc = cc ∧ ks.take offset = cs.take offset then
        firstStale abi.sample (ks.drop offset) (cs.drop offset)
      else none
    | _, _ => none
  | _, _, _ => none

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
  if claim.sampleJam ≠ Noun.jam sample then
    throw (.sampleStale (staleField program.abi sample claim.sampleJam))
  if program.abi.fuel < claim.steps then throw .fuelExceeded
  -- C5: hold check here (K-RUN-HOLD: a claim above the free threshold needs a hold;
  -- the steps are fixed and bounded by the ABI fuel from this line on).
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
            -- C5: hold check here (K-RUN-HOLD: a dry run above the free threshold
            -- needs a hold before the oracle runs at the ABI fuel).
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

/-! ## A stale pinned claim names its field (K-RUN-PIN) -/

theorem firstStale_only {read read' : Nat → String → Option Int} {slot : SampleSlot} :
    ∀ {slots : List SampleSlot} {ns ns' : List Noun},
      sampleSlots read slots = some ns → sampleSlots read' slots = some ns' →
      slot ∈ slots → read slot.target slot.slot ≠ read' slot.target slot.slot →
      (∀ s ∈ slots, s ≠ slot → read s.target s.slot = read' s.target s.slot) →
      firstStale slots ns' ns = some slot.key
  | [], _, _, _, _, member, _, _ => by cases member
  | s :: rest, ns, ns', h, h', member, changed, only => by
    obtain ⟨v, n, tail, hv, he, hr, rfl⟩ := sampleSlots_cons h
    obtain ⟨v', n', tail', hv', he', hr', rfl⟩ := sampleSlots_cons h'
    by_cases same : s = slot
    · subst same
      have differ : ¬ (Noun.cell (cord s.key) n' = Noun.cell (cord s.key) n) := by
        intro e
        simp only [Noun.cell.injEq, true_and] at e
        subst e
        exact changed (by rw [hv, hv', encodeValue_injective he he'])
      simp only [firstStale, if_neg differ]
    · obtain rfl : v = v' := Option.some.inj ((hv.symm.trans (only s (List.mem_cons_self ..) same)).trans hv')
      obtain rfl : n' = n := Option.some.inj (he'.symm.trans he)
      have m : slot ∈ rest := by
        rcases List.mem_cons.mp member with e | m
        · exact absurd e.symm same
        · exact m
      simp only [firstStale, if_pos rfl]
      exact firstStale_only hr hr' m changed (fun t mt nt => only t (List.mem_cons_of_mem _ mt) nt)

/-- **`pinned_claim_stale_on_field_change`** (K-RUN-PIN, at the run): a claim
computed on a pinned program's sample, re-checked after exactly one named slot
changed value, refuses `sampleStale` naming THAT slot's key — at whatever
context the kernel now runs. -/
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
    checkRun program libraries sample' claim writes = .error (.sampleStale (some slot.key)) := by
  have hne : claim.sampleJam ≠ Noun.jam sample' := by
    rw [computed]
    intro e
    have same := Noun.jam_injective e
    subst same
    exact changed ((sampleOf_injective claimed current).2.2 slot named)
  have hstale : staleField program.abi sample' claim.sampleJam = some slot.key := by
    unfold sampleOf at claimed current
    split at claimed
    · rename_i inRange
      rw [if_pos inRange] at current
      cases hs : sampleSlots read program.abi.sample with
      | none => rw [hs] at claimed; cases claimed
      | some ns =>
        cases hs' : sampleSlots read' program.abi.sample with
        | none => rw [hs'] at current; cases current
        | some ns' =>
          rw [hs] at claimed
          rw [hs'] at current
          simp only [Option.map_some, Option.some.injEq] at claimed current
          subst claimed
          subst current
          have len := sampleSlots_length hs
          have len' := sampleSlots_length hs'
          have off : (targetEntries 0 targets ++ ns').length - program.abi.sample.length =
              (targetEntries 0 targets).length := by
            simp only [List.length_append, len']; omega
          have takeK : (targetEntries 0 targets ++ ns').take (targetEntries 0 targets).length =
              targetEntries 0 targets := List.take_left' rfl
          have takeC : (targetEntries 0 targets ++ ns).take (targetEntries 0 targets).length =
              targetEntries 0 targets := List.take_left' rfl
          have dropK : (targetEntries 0 targets ++ ns').drop (targetEntries 0 targets).length =
              ns' := List.drop_left' rfl
          have dropC : (targetEntries 0 targets ++ ns).drop (targetEntries 0 targets).length =
              ns := List.drop_left' rfl
          unfold staleField
          rw [computed, Noun.cue_jam, pinned]
          simp only [listItems_nockList, contextOf]
          rw [off, takeK, takeC, dropK, dropC, if_pos (by simp)]
          exact firstStale_only hs hs' named changed only
    · cases claimed
  unfold checkRun
  simp only [bind, Except.bind]
  rw [if_pos hne, hstale]

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
      some (.sampleStale none) := by decide +kernel
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

/-! ### Pinned against live (K-RUN-PIN)

`slotCore`'s gate writes `k := +(n)`, where `n` is the sample's first ABI slot
(axis 109 of the gate with one target). The claim is computed once, at height 16
by signer 7 on `stateA`; it is re-checked at height 23 by signer 9 on `stateB`
(same `f/2`, different unnamed field). -/

def slotCore : Noun := coreOf (writeK (Nock.op 4 (Nock.op 0 (.atom 109))))
def slotN : SampleSlot := { target := 0, slot := "f/2", key := "n", type := .nat }
def slotAbi (mode : ContextMode) : Abi := { kAbi 100 with context := mode, sample := [slotN] }
def slotProgram (context : ContextMode) : Program := ⟨Noun.jam slotCore, slotAbi context⟩
def sampleAt (context : ContextMode) (ctx : Context) (read : Nat → String → Option Int) : Noun :=
  (sampleOf (slotAbi context) ctx [11] read).getD (.atom 0)
def stateC : Nat → String → Option Int := fun _ s => if s = "f/2" then some 40 else some 1
def claimAt16 (context : ContextMode) : RunClaim :=
  claimOf (sampleAt context ⟨16, 7, 0⟩ stateA) (outK 42) 14

/-- Pinned: the height-16 claim is accepted at height 23. -/
theorem pole_pinned_other_height :
    writesOf (checkRun (slotProgram .pinned) [] (sampleAt .pinned ⟨23, 9, 0⟩ stateB)
      (claimAt16 .pinned) [W 42]) = some [W 42] := by decide +kernel
/-- Live: the same claim at height 23 is stale, and names no field. -/
theorem pole_live_other_height :
    refusalOf (checkRun (slotProgram .live) [] (sampleAt .live ⟨23, 9, 0⟩ stateB)
      (claimAt16 .live) [W 42]) = some (.sampleStale none) := by decide +kernel
/-- Pinned, with the named field moved (41 → 40): stale, naming `n`. -/
theorem pole_pinned_field_stale :
    refusalOf (checkRun (slotProgram .pinned) [] (sampleAt .pinned ⟨23, 9, 0⟩ stateC)
      (claimAt16 .pinned) [W 41]) = some (.sampleStale (some "n")) := by decide +kernel
/-- A `noun` output writes the jam atom of `[3 7]`, which a `noun` sample reads back. -/
theorem pole_noun_output :
    (decodeValue .noun (.cell (.atom 3) (.atom 7))).bind (encodeValue .noun) =
      some (.cell (.atom 3) (.atom 7)) := by decide +kernel

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
/-- info: 'Minidregg.Kernel.NockRun.noun_output_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.noun_output_roundtrip
/-- info: 'Minidregg.Kernel.NockRun.noun_output_bounded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.noun_output_bounded
/-- info: 'Minidregg.Kernel.NockRun.listItems_nockList' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.listItems_nockList
/-- info: 'Minidregg.Kernel.NockRun.firstStale_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.firstStale_only
/-- info: 'Minidregg.Kernel.NockRun.pinned_claim_stale_on_field_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pinned_claim_stale_on_field_change
/-- info: 'Minidregg.Kernel.NockRun.pole_pinned_other_height' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_pinned_other_height
/-- info: 'Minidregg.Kernel.NockRun.pole_live_other_height' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_live_other_height
/-- info: 'Minidregg.Kernel.NockRun.pole_pinned_field_stale' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_pinned_field_stale
/-- info: 'Minidregg.Kernel.NockRun.pole_noun_output' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockRun.pole_noun_output
