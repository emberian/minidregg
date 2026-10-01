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

**Not here yet** (EVAL §1.4, lanes E2–E4): the ABI entry (`subjectFormula`,
libraries, `Params`), the single-pass `oracle` and `oracle_is_export`, `writesOf`
(`decodeWrites`), the `Sample` record and its encoding, `decodeParams`, and the
`door`. They live in `Kernel.NockRun` / `Kernel.NockProgramCell` /
`Kernel.NockDoor` today; this file imports only `Theory` and the hash, so that
`Kernel.Run` (E2) can import it.
-/
import Theory.Nock
import Theory.TypedAuthorization
import Compiler.Sp800185Cshake256

namespace Minidregg.Compiler

open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- What an evaluator must bring to be a referee. -/
structure Evaluator where
  /-- The registry name, e.g. `"nock"`. -/
  name : String
  /-- The semantics version; a change in what `Spec` means is a new evaluator. -/
  semantics : String
  -- The machine
  /-- What one run evaluates (Nock: the pair `(subject, formula)`). -/
  Term : Type
  /-- A run's value (Nock: `Noun`). -/
  Output : Type
  /-- The big-step semantics: `Spec t o` ≙ "`t` evaluates to `o`". -/
  Spec : Term → Output → Prop
  /-- "`t` reaches a rule whose precondition fails": a property of the term. -/
  Crash : Term → Prop
  /-- The fueled interpreter. -/
  run : Nat → Term → Except Outcome Output
  /-- The metered count of a run at a fuel (the fee a runner signs). -/
  steps : Nat → Term → Nat
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
  /-- A decoded program (Nock: `Noun`). -/
  Code : Type
  decode : List UInt8 → Option Code
  canonical : List UInt8 → Bool
  canonical_unique : ∀ {bs bs' : List UInt8}, canonical bs = true → canonical bs' = true →
    decode bs = decode bs' → bs = bs'
  /-- The sample as the machine sees it (Nock: `Noun`); a claim carries its bytes. -/
  Input : Type
  encodeInput : Input → List UInt8
  encodeInput_injective : Function.Injective encodeInput
  /-- A claim carries the output's bytes; injectivity makes byte equality a
  statement about values. -/
  encodeOutput : Output → List UInt8
  encodeOutput_injective : Function.Injective encodeOutput
  -- The byte entry point the Host calls
  /-- Decoding a serialized term (Nock: the cue of a cell `[s f]`). -/
  decodeTerm : List UInt8 → Option Term
  runBytes : Nat → List UInt8 → ByteRun
  runBytes_sound : ∀ {fuel : Nat} {input out : List UInt8} {k : Nat},
    runBytes fuel input = .ok k out →
      ∃ t o, decodeTerm input = some t ∧ Spec t o ∧ out = encodeOutput o
  runBytes_crash_sound : ∀ {fuel : Nat} {input : List UInt8} {k : Nat},
    runBytes fuel input = .crash k → ∃ t, decodeTerm input = some t ∧ Crash t
  /-- The `@[export]`ed C ABI function. -/
  exportFn : UInt64 → ByteArray → ByteArray
  /-- The exported function is `runBytes` in `ByteRun.toBytes` form. -/
  export_is_run : ∀ (fuel : UInt64) (input : ByteArray),
    exportFn fuel input = ⟨(runBytes fuel.toNat input.toList).toBytes.toArray⟩

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

/-! ## Nock, entry #1 -/

/-- A serialized Nock term is the jam of the cell `[subject formula]`. -/
def nockDecodeTerm (bs : List UInt8) : Option (Noun × Noun) :=
  match Noun.cue bs with
  | some (.cell s f) => some (s, f)
  | _ => none

def nock : Evaluator where
  name := "nock"
  semantics := "4K/Theory.Nock/v1"
  Term := Noun × Noun
  Output := Noun
  Spec t o := Nock.Step t.1 t.2 o
  Crash t := Nock.Crash t.1 t.2
  run fuel t := Nock.run fuel t.1 t.2
  steps fuel t := Nock.steps fuel t.1 t.2
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
  Code := Noun
  decode := Noun.cue
  canonical := Noun.canonical
  canonical_unique h h' he := Noun.canonical_unique h h' he
  Input := Noun
  encodeInput := Noun.jam
  encodeInput_injective _ _ h := Noun.jam_injective h
  encodeOutput := Noun.jam
  encodeOutput_injective _ _ h := Noun.jam_injective h
  decodeTerm := nockDecodeTerm
  runBytes := Nock.runJammed
  runBytes_sound h := by
    obtain ⟨s, f, v, hc, hs, ho, -⟩ := Nock.runJammed_sound h
    exact ⟨(s, f), v, by simp only [nockDecodeTerm, hc], hs, ho⟩
  runBytes_crash_sound h := by
    obtain ⟨s, f, hc, hs⟩ := Nock.runJammed_crash_sound h
    exact ⟨(s, f), by simp only [nockDecodeTerm, hc], hs⟩
  exportFn := Nock.runJammedBytes
  export_is_run _ _ := rfl

/-! ## The registry -/

/-- The evaluators the kernel is compiled with. Adding one is adding a term here;
a missing field is a build failure. -/
def registry : List Evaluator := [nock]

theorem registry_ids_distinct : (registry.map Evaluator.id).Nodup := by
  simp [registry]

theorem nock_registered : nock ∈ registry := by
  simp [registry]

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.Evaluator.nock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nock
/-- info: 'Minidregg.Compiler.Evaluator.registry_ids_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registry_ids_distinct
/-- info: 'Minidregg.Compiler.Evaluator.nock_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nock_registered
/-- info: 'Minidregg.Compiler.Evaluator.idCustomization_spells' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms idCustomization_spells

end Evaluator
end Minidregg.Compiler
