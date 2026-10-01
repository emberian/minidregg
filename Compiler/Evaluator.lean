/-
# Compiler.Evaluator — the kernel referees user programs by re-execution; Nock is entry #1

The kernel admits a run by running it again. It does not care which language the
program is in, only that the language comes with the facts re-execution needs.
`Evaluator` is those facts as a structure: a machine (`Term`, `Spec`, `Crash`, a
fueled `run` with its metered `steps`), the theorems that make its answer a
verdict about the term, and the byte entry point the Host calls. `registry` is
the list of evaluators the kernel is compiled with.

**The registry rule.** Every field is required. An evaluator whose run cannot be
shown sound, complete, deterministic, crash-honest, fuel-monotone and
step-stable cannot be written down, so cannot be registered. In particular
`exhausted_says_nothing` is required: the evaluator must exhibit a term that has
a value and still runs out of fuel at some budget, i.e. its exhaustion outcome is
a third answer, distinct from crash. An interpreter that reports running out of
fuel as a failure of the term (as `Theory.EvmFragment` does, with
`.fail "out of fuel"`) has no such term and is not a referee.

**Nock (`Evaluator.nock`)** fills every field with a landed `Theory.Nock` /
`Theory.Noun` definition or theorem: the machine term is `[subject formula]`
as a pair, `Spec`/`Crash` are `Nock.Step`/`Nock.Crash`, `run`/`steps` are
`Nock.run`/`Nock.steps`, the byte entry point is `Nock.runJammed` behind
`@[export minidregg_nock_run_jammed] Nock.runJammedBytes`. Nothing is re-proved:
the proofs below are the landed theorems, at most repackaged (a pair for `s f`).

**The kernel's run (E2).** The referee (`Kernel.Run`) needs, beyond the machine:
the `entry` that turns a program record (its decoded code, its ABI, its
libraries' code) and a sample into a term; the single-pass `oracle`, which keeps
the step count on a crash and on exhaustion (`Theory.Eval.Ran`) and is the byte
export by theorem (`oracle_is_export`); `writesOf`, the writes a product names;
and the sample: `sampleOf`, `overMax`, `staleField` with the facts the pinned/live
theorems use. Nock's are `Kernel.NockEntry` (moved out of `Kernel.NockRun`) and
`Kernel.NockProgramCell.Sample`, both below this file, so `Kernel.Run` imports it
without a cycle.

**`Machine` / `Evaluator`.** The data an evaluator computes with is `Machine`; the
facts are `Evaluator extends Machine`. The referee's functions take a `Machine`
(`Kernel.Run.checkRun E.toMachine`), so a decided pole on Nock's run names
`Machine.nock` — data only — and its `#print axioms` is the run's, not the
proof fields' (`Evaluator.nock` carries `Classical.choice` through `run_sound`).

**Not here yet** (EVAL §1.4, lanes E3–E4): `Params`/`decodeParams` (the ABI's
`arm` and `libraries` are still `Abi` fields, so `entry` reads the `Abi`), the
`Sample` record with a layout-indexed `encodeSample` (E1 §4.2.4; `sampleOf` /
`overMax` / `staleField` here are its current, layout-indexed shape), and the `door`.
-/
import Kernel.NockEntry
import Theory.TypedAuthorization
import Compiler.Sp800185Cshake256

namespace Minidregg.Compiler

open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.NockProgramCodec (Abi SampleSlot)
open Minidregg.Kernel.NockProgramCell (Context)

set_option autoImplicit false

/-- What an evaluator computes with: the machine, its byte forms, and the kernel's
run (entry, oracle, writes, sample). No facts; those are `Evaluator`'s. -/
structure Machine where
  /-- The registry name, e.g. `"nock"`. -/
  name : String
  /-- The semantics version; a change in what `Spec` means is a new evaluator. -/
  semantics : String
  -- The machine
  /-- What one run evaluates (Nock: the pair `(subject, formula)`). -/
  Term : Type
  /-- A run's value (Nock: `Noun`). -/
  Output : Type
  /-- The fueled interpreter. -/
  run : Nat → Term → Except Outcome Output
  /-- The metered count of a run at a fuel (the fee a runner signs). -/
  steps : Nat → Term → Nat
  -- Bytes ⇄ values
  /-- A decoded program (Nock: `Noun`). -/
  Code : Type
  decode : List UInt8 → Option Code
  canonical : List UInt8 → Bool
  /-- The sample as the machine sees it (Nock: `Noun`); a claim carries its bytes. -/
  Input : Type
  encodeInput : Input → List UInt8
  /-- A claim carries the output's bytes. -/
  encodeOutput : Output → List UInt8
  -- The byte entry point the Host calls
  /-- Decoding a serialized term (Nock: the cue of a cell `[s f]`). -/
  decodeTerm : List UInt8 → Option Term
  /-- Serializing a term (Nock: the jam of `[s f]`). -/
  encodeTerm : Term → List UInt8
  runBytes : Nat → List UInt8 → ByteRun
  /-- The `@[export]`ed C ABI function. -/
  exportFn : UInt64 → ByteArray → ByteArray
  -- The kernel's run
  /-- The term the kernel runs: the program's code under its ABI, over its
  libraries' code (ABI order), on the sample (Nock: N16's `subjectFormula`). -/
  entry : Abi → Code → List Code → Input → Term
  /-- One fueled evaluation in a single pass, the count kept on every outcome. -/
  oracle : Nat → Term → Ran Output
  /-- The writes a product names against the ABI's outputs (Nock: `decodeWrites`). -/
  writesOf : Abi → Output → Option (List FieldWrite)
  -- The sample (E3 reshapes this into `Sample` + a layout-indexed `encodeSample`)
  /-- The kernel's sample for a command: its context, its targets, the read slots. -/
  sampleOf : Abi → Context → List Nat → (Nat → String → Option Int) → Option Input
  /-- The first slot whose value lies above its declared maximum (NC-2). -/
  overMax : (Nat → String → Option Int) → List SampleSlot → Option SampleSlot
  /-- Which named slot a stale claim's sample missed (K-RUN-PIN), when it can say. -/
  staleField : Abi → Input → List UInt8 → Option String

/-- What an evaluator must bring to be a referee. -/
structure Evaluator extends Machine where
  /-- The big-step semantics: `Spec t o` ≙ "`t` evaluates to `o`". -/
  Spec : Term → Output → Prop
  /-- "`t` reaches a rule whose precondition fails": a property of the term. -/
  Crash : Term → Prop
  -- The machine against its semantics
  run_sound : ∀ {fuel : Nat} {t : Term} {o : Output}, run fuel t = .ok o → Spec t o
  run_complete : ∀ {t : Term} {o : Output}, Spec t o →
    ∃ n, ∀ fuel, n ≤ fuel → run fuel t = .ok o ∧ steps fuel t = n
  spec_deterministic : ∀ {t : Term} {o o' : Output}, Spec t o → Spec t o' → o = o'
  run_crash_iff : ∀ {t : Term}, (∃ fuel, run fuel t = .error .crash) ↔ Crash t
  crash_not_spec : ∀ {t : Term} {o : Output}, Crash t → Spec t o → False
  run_fuel_monotone : ∀ {fuel fuel' : Nat} {t : Term} {o : Output},
    run fuel t = .ok o → fuel ≤ fuel' → run fuel' t = .ok o
  steps_stable : ∀ {fuel fuel' : Nat} {t : Term},
    run fuel t ≠ .error .exhausted → fuel ≤ fuel' → steps fuel' t = steps fuel t
  /-- **The pole.** Exhaustion is a third answer: some term with a value runs out
  of fuel. Required; an evaluator that cannot exhibit it is not registrable. -/
  exhausted_says_nothing : ∃ (t : Term) (fuel : Nat) (o : Output),
    run fuel t = .error .exhausted ∧ Spec t o
  -- Bytes ⇄ values, fail-closed and canonical
  canonical_unique : ∀ {bs bs' : List UInt8}, canonical bs = true → canonical bs' = true →
    decode bs = decode bs' → bs = bs'
  encodeInput_injective : Function.Injective encodeInput
  /-- Injectivity makes byte equality of outputs a statement about values. -/
  encodeOutput_injective : Function.Injective encodeOutput
  -- The byte entry point
  runBytes_sound : ∀ {fuel : Nat} {input out : List UInt8} {k : Nat},
    runBytes fuel input = .ok k out →
      ∃ t o, decodeTerm input = some t ∧ Spec t o ∧ out = encodeOutput o
  runBytes_crash_sound : ∀ {fuel : Nat} {input : List UInt8} {k : Nat},
    runBytes fuel input = .crash k → ∃ t, decodeTerm input = some t ∧ Crash t
  /-- The exported function is `runBytes` in `ByteRun.toBytes` form. -/
  export_is_run : ∀ (fuel : UInt64) (input : ByteArray),
    exportFn fuel input = ⟨(runBytes fuel.toNat input.toList).toBytes.toArray⟩
  decodeTerm_encodeTerm : ∀ t, decodeTerm (encodeTerm t) = some t
  -- The oracle is the machine, in one pass, and the export
  oracle_ok : ∀ {fuel : Nat} {t : Term} {o : Output} {k : Nat},
    oracle fuel t = .ok o k → run fuel t = .ok o ∧ steps fuel t = k
  oracle_crash : ∀ {fuel : Nat} {t : Term} {k : Nat}, oracle fuel t = .crash k → Crash t
  oracle_exhausted : ∀ {fuel : Nat} {t : Term} {k : Nat},
    oracle fuel t = .exhausted k → run fuel t = .error .exhausted ∧ k = fuel
  /-- **The oracle is the export**: the byte entry point on a serialized term answers
  the oracle's status and steps, and the serialized product. -/
  oracle_is_export : ∀ (fuel : Nat) (t : Term),
    runBytes fuel (encodeTerm t) = (oracle fuel t).toByteRun encodeOutput
  -- The sample
  sampleOf_overMax : ∀ {abi : Abi} {ctx : Context} {targets : List Nat}
    {read : Nat → String → Option Int} {slot : SampleSlot},
    overMax read abi.sample = some slot → sampleOf abi ctx targets read = none
  /-- `overMax` reads only the named slots. -/
  overMax_congr : ∀ {read read' : Nat → String → Option Int} {slots : List SampleSlot},
    (∀ s ∈ slots, read s.target s.slot = read' s.target s.slot) →
      overMax read slots = overMax read' slots
  /-- A pinned sample is a function of the named slots and the targets alone. -/
  sampleOf_pinned_of_fields : ∀ {abi : Abi}, abi.context = .pinned →
    ∀ (ctx ctx' : Context) (targets : List Nat) {read read' : Nat → String → Option Int},
      (∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot) →
        sampleOf abi ctx targets read = sampleOf abi ctx' targets read'
  /-- Moving exactly one named slot of a pinned program moves its sample, and
  `staleField` names that slot on the earlier sample's bytes. -/
  staleField_names : ∀ {abi : Abi} {ctx ctx' : Context} {targets : List Nat}
    {read read' : Nat → String → Option Int} {s s' : Input} {slot : SampleSlot},
    abi.context = .pinned → sampleOf abi ctx targets read = some s →
    sampleOf abi ctx' targets read' = some s' → slot ∈ abi.sample →
    read slot.target slot.slot ≠ read' slot.target slot.slot →
    (∀ x ∈ abi.sample, x ≠ slot → read x.target x.slot = read' x.target x.slot) →
    s ≠ s' ∧ staleField abi s' (encodeInput s) = some slot.key

namespace Evaluator

/-! ## Identity -/

/-- `DREGG.EVALUATOR/v1` -/
def idCustomization : List UInt8 :=
  [68, 82, 69, 71, 71, 46, 69, 86, 65, 76, 85, 65, 84, 79, 82, 47, 118, 49]

theorem idCustomization_spells : idCustomization = "DREGG.EVALUATOR/v1".toUTF8.toList := by
  decide +kernel

/-- cSHAKE256 over `name ‖ 0 ‖ semantics`: the registry key. Derived from the
name and the semantics version, never chosen, so an entry cannot claim another's id. -/
def idOf (name semantics : String) : Digest :=
  (Sp800185Cshake256.hash idCustomization
    (name.toUTF8.toList ++ [0] ++ semantics.toUTF8.toList)).digest

def id (E : Evaluator) : Digest := idOf E.name E.semantics

end Evaluator

/-! ## Nock, entry #1 -/

/-- A serialized Nock term is the jam of the cell `[subject formula]`. -/
def nockDecodeTerm (bs : List UInt8) : Option (Noun × Noun) :=
  match Noun.cue bs with
  | some (.cell s f) => some (s, f)
  | _ => none

/-- Nock's machine: `Theory.Nock` and `Theory.Noun`, the kernel's run from
`Kernel.NockEntry`, the sample from `Kernel.NockProgramCell.Sample`. -/
@[reducible] def Machine.nock : Machine where
  name := "nock"
  semantics := "4K/Theory.Nock/v1"
  Term := Noun × Noun
  Output := Noun
  run fuel t := Nock.run fuel t.1 t.2
  steps fuel t := Nock.steps fuel t.1 t.2
  Code := Noun
  decode := Noun.cue
  canonical := Noun.canonical
  Input := Noun
  encodeInput := Noun.jam
  encodeOutput := Noun.jam
  decodeTerm := nockDecodeTerm
  encodeTerm t := Noun.jam (.cell t.1 t.2)
  runBytes := Nock.runJammed
  exportFn := Nock.runJammedBytes
  entry abi code libs sample := Kernel.NockEntry.subjectFormula abi.arm code libs sample
  oracle fuel t := Kernel.NockEntry.oracle fuel t.1 t.2
  writesOf := Kernel.NockEntry.decodeWrites
  sampleOf := Kernel.NockProgramCell.sampleOf
  overMax := Kernel.NockProgramCell.overMax
  staleField := Kernel.NockEntry.staleField

namespace Evaluator

def nock : Evaluator where
  toMachine := Machine.nock
  Spec t o := Nock.Step t.1 t.2 o
  Crash t := Nock.Crash t.1 t.2
  run_sound h := Nock.run_sound h
  run_complete h := Nock.run_complete h
  spec_deterministic h h' := Nock.step_deterministic h h'
  run_crash_iff := Nock.run_crash_iff
  crash_not_spec hc hs := Nock.crash_not_step hc hs
  run_fuel_monotone h hle := Nock.run_fuel_monotone h hle
  steps_stable h hle := Nock.steps_stable h hle
  exhausted_says_nothing := by
    obtain ⟨s, f, fuel, v, h, hs⟩ := Nock.exhausted_says_nothing
    exact ⟨(s, f), fuel, v, h, hs⟩
  canonical_unique h h' he := Noun.canonical_unique h h' he
  encodeInput_injective _ _ h := Noun.jam_injective h
  encodeOutput_injective _ _ h := Noun.jam_injective h
  runBytes_sound h := by
    obtain ⟨s, f, v, hc, hs, ho, -⟩ := Nock.runJammed_sound h
    exact ⟨(s, f), v, by show nockDecodeTerm _ = _; simp only [nockDecodeTerm, hc], hs, ho⟩
  runBytes_crash_sound h := by
    obtain ⟨s, f, hc, hs⟩ := Nock.runJammed_crash_sound h
    exact ⟨(s, f), by show nockDecodeTerm _ = _; simp only [nockDecodeTerm, hc], hs⟩
  export_is_run _ _ := rfl
  decodeTerm_encodeTerm t := by
    show nockDecodeTerm (Noun.jam (.cell t.1 t.2)) = some t
    simp [nockDecodeTerm, Noun.cue_jam]
  oracle_ok h := by
    obtain ⟨-, hr, hs⟩ := Kernel.NockEntry.oracle_ok_step h
    exact ⟨hr, hs⟩
  oracle_crash h := Kernel.NockEntry.oracle_crash h
  oracle_exhausted h := Kernel.NockEntry.oracle_exhausted h
  oracle_is_export fuel t := by
    show Nock.runJammed fuel (Noun.jam (.cell t.1 t.2)) =
      (Kernel.NockEntry.oracle fuel t.1 t.2).toByteRun Noun.jam
    rw [Kernel.NockEntry.oracle_is_export]
    cases Kernel.NockEntry.oracle fuel t.1 t.2 <;> rfl
  sampleOf_overMax h := Kernel.NockProgramCell.sampleOf_overMax_refused _ _ _ _ h
  overMax_congr agree := Kernel.NockProgramCell.overMax_congr agree
  sampleOf_pinned_of_fields := fun {_} pinned ctx ctx' targets {_ _} agree =>
    Kernel.NockProgramCell.sampleOf_pinned_of_fields pinned ctx ctx' targets agree
  staleField_names pinned claimed current named changed only :=
    Kernel.NockEntry.staleField_names pinned claimed current named changed only

theorem nock_toMachine : nock.toMachine = Machine.nock := rfl

/-! ## The registry -/

/-- The evaluators the kernel is compiled with. Adding one is adding a term here;
a missing field is a build failure. An operator may disable an entry
(`Kernel.Run.resolve`'s `disabled`, committed in the runtime profile); no one adds
one at run time: a program naming any other id is refused `unknownEvaluator`. -/
def registry : List Evaluator := [nock]

theorem registry_ids_distinct : (registry.map Evaluator.id).Nodup := by
  simp [registry]

theorem nock_registered : nock ∈ registry := by
  simp [registry]

/-- What the runtime profile commits of the registry: each entry's name and
semantics version (its id is their hash), in registry order. -/
def registryManifest : List (List UInt8) :=
  registry.map fun E => E.name.toUTF8.toList ++ [0] ++ E.semantics.toUTF8.toList

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.Evaluator.nock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nock
/-- info: 'Minidregg.Compiler.Evaluator.registry_ids_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registry_ids_distinct
/-- info: 'Minidregg.Compiler.Evaluator.nock_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nock_registered
/-- info: 'Minidregg.Compiler.Evaluator.idCustomization_spells' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms idCustomization_spells
/-- info: 'Minidregg.Compiler.Evaluator.nock_toMachine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nock_toMachine

end Evaluator

/-- info: 'Minidregg.Compiler.Machine.nock' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Machine.nock

end Minidregg.Compiler
